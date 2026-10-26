#!/usr/bin/env python3
"""Differential test of the frozen preserved program order against MoRDor.

For each litmus test, MoRDor exports its executions (``executions``: events,
``fwd``, ``we`` and ``ppo`` of each). The program is translated as in
``es_diff.py`` and handed to ``smrd-es`` together with each execution's events,
justified events and forwarding context; ``smrd-es`` evaluates lean4-smrd's
``Execution.ppo`` (``PpoEval.ppoEval``, equal to it under the hypotheses of
``PpoEval.ppoEval_iff``) and the script compares the two relations.

* Event ids are matched by order: both tools number events in the order the
  program is interpreted. MoRDor's ``Init`` and ``Terminal`` events have no
  counterpart and are dropped, with the pairs they are in (``ppo_init``); the
  match is checked on each event's type and location.
* lean4-smrd's ``X`` holds the elided events, MoRDor's execution does not: ``X``
  is MoRDor's events with the targets of ``fwd`` and ``we`` added back.
* ``J`` is the non-elided writes of the execution.
* Executions whose shared context elides an event twice (MoRDor unites the
  justifications' contexts without asking for unique predecessors) are not
  executions of lean4-smrd (``FwdCtx.WF``) and are left out.
* A forwarding context of depth more than one is flattened, each elided event
  under the root of its chain: ``≼`` sees ``δ`` only through ``remap_δ``.

Only loop-free programs with global locations (no pointers, no allocations),
no RMWs and no fences are compared (the hypotheses of ``ppoEval_iff``); others are reported as ``skip``.
Each execution is ``agree`` or ``differ``; a computed closure that is not
closed is ``open``.

Usage::

    ppo_diff.py [--mordor PATH] [--smrd-es PATH] [-v] TEST.lit ...
"""

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import es_diff  # noqa: E402

DEFAULT_SMRD_ES = HERE.parent / ".lake" / "build" / "bin" / "smrd-es"
DEFAULT_MORDOR = HERE.parent.parent / "mordor" / "_build" / "default" / "cli" / "main.exe"
TIMEOUT = 300

LEAN_TYPE = {"R": "R", "W": "W", "Fence": "F", "Branch": "B", "Alloc": "A", "Dealloc": "D"}
MORDOR_TYPE = {"R": "R", "W": "W", "F": "F", "Fence": "F", "B": "B", "Branch": "B",
               "Malloc": "A", "Free": "D"}


def run(cmd):
    return subprocess.run(cmd, capture_output=True, text=True, timeout=TIMEOUT)


def compare(test, args, tmp):
    isa = Path(tmp) / "prog.isa.json"
    exe = Path(tmp) / "mordor.exec.json"
    esm = Path(tmp) / "mordor.es.json"
    prog = Path(tmp) / "prog.lean.json"
    r = run([args.mordor, "parse", "--single", str(test), "--output-mode", "isa",
             "--output-file", str(isa), "--error", "--no-progress", "--allow-unknown-model"])
    if r.returncode != 0:
        return "error", f"mordor parse failed: {r.stderr.strip()[-300:]}", []
    try:
        tr = es_diff.Translator(json.loads(isa.read_text()))
        tr.bound = 2
        lean_prog = tr.program()
    except es_diff.Unsupported as u:
        return "skip", str(u), []
    if lean_prog.get("cut"):
        return "skip", "loops", []
    r = run([args.mordor, "interpret", "--single", str(test), "--output-mode", "json",
             "--output-file", str(esm), "--error", "--no-progress", "--allow-unknown-model"])
    if r.returncode != 0:
        return "error", f"mordor interpret failed: {r.stderr.strip()[-300:]}", []
    mstruct = json.loads(esm.read_text())["structure"]
    r = run([args.mordor, "executions", "--single", str(test), "--output-file", str(exe),
             "--error", "--no-progress", "--allow-unknown-model"])
    if r.returncode != 0:
        return "error", f"mordor executions failed: {r.stderr.strip()[-300:]}", []
    mexecs = json.loads(exe.read_text())["executions"]

    # the Lean event structure, to match ids
    prog.write_text(json.dumps(lean_prog))
    r = run([str(args.smrd_es), str(prog), "2"])
    if r.returncode != 0:
        return "error", f"smrd-es failed: {r.stderr.strip()[-300:]}", []
    les = json.loads(r.stdout)
    mev = [e for e in sorted(mstruct["events"], key=lambda e: e["id"])
           if e["type"] not in ("Init", "Terminal")]
    lev = sorted(les["events"], key=lambda e: e["id"])
    if len(mev) != len(lev):
        return "error", f"{len(mev)} MoRDor events, {len(lev)} lean4-smrd events", []
    if any(l["kind"]["type"] in ("Alloc", "Dealloc") for l in lev):
        return "skip", "allocations", []
    for m, l in zip(mev, lev):
        if MORDOR_TYPE.get(m["type"]) != LEAN_TYPE[l["kind"]["type"]]:
            return "error", f"event {m['id']} ({m['type']}) vs {l['id']} ({l['kind']['type']})", []
        if l["kind"]["type"] in ("R", "W", "Dealloc"):
            g = l["kind"]["loc"].get("loc", {}).get("global")
            if g is None or l["kind"]["loc"]["loc"].get("off", 0) != 0:
                return "skip", "locations other than globals", []
            if not (m["loc"] and m["loc"].get("reg") == g):
                return "error", f"event {m['id']} at {m['loc']} vs {l['id']} at {g}", []
        if l["kind"]["type"] in ("Alloc", "Dealloc"):
            return "skip", "allocations", []
        if m["type"] in ("F", "Fence") or l["kind"]["type"] == "Fence":
            return "skip", "fences", []
    if les["rmw"]:
        return "skip", "RMWs", []
    idmap = {m["id"]: l["id"] for m, l in zip(mev, lev)}
    kind = {l["id"]: l["kind"]["type"] for l in lev}

    def mp(pairs):
        return sorted({(idmap[a], idmap[b]) for a, b in pairs if a in idmap and b in idmap})

    lexecs, mppo, notes, nonwf, kept = [], [], set(), [], []
    for x in mexecs:
        fwd, we = mp(x.get("fwd", [])), mp(x.get("we", []))
        elided = {b for _, b in fwd + we}
        X = sorted({idmap[e["id"]] for e in x["events"] if e["id"] in idmap} | elided)
        # remap_δ follows chains; lean4-smrd's ≼ depends on δ only through
        # remap_δ (and ψ_δ, which PpoEval assumes satisfiable), so the context
        # is flattened to depth one, each elided event under its root.
        pred = {}
        for a, b in fwd + we:
            if b in pred and pred[b] != a:
                nonwf.append(x["id"])
            pred[b] = a
        if x["id"] in nonwf:
            continue

        def root(e, seen=()):
            if e in seen:
                raise ValueError("cyclic forwarding context")
            return root(pred[e], seen + (e,)) if e in pred else e
        try:
            flat = sorted((root(b), b) for b in pred)
        except ValueError as err:
            return "error", str(err), []
        deep = {a for a, _ in fwd + we} & elided
        fwd = [p for p in flat if p[1] in {b for _, b in fwd}]
        we = [p for p in flat if p not in fwd]
        if deep:
            notes.add("forwarding contexts of depth > 1 flattened")
        J = [e for e in X if kind[e] == "W" and e not in elided]
        lexecs.append({"X": X, "J": J, "f": fwd, "we": we})
        kept.append(x)
        mppo.append(mp(x["ppo"]))
    prog.write_text(json.dumps({**lean_prog, "executions": lexecs}))
    r = run([str(args.smrd_es), str(prog), "2"])
    if r.returncode != 0:
        return "error", f"smrd-es failed: {r.stderr.strip()[-300:]}", []
    out = json.loads(r.stdout)
    rows = []
    if nonwf:
        notes.add(f"{len(nonwf)} executions whose context elides an event twice (not WF in lean4-smrd) left out")
    for x, lx, m, l, closed in zip(kept, lexecs, mppo, out["ppo"], out["closed"]):
        l = sorted(map(tuple, l))
        st = "open" if not closed else "agree" if l == m else "differ"
        rows.append({"exec": x["id"], "status": st, "X": lx["X"], "f": lx["f"], "we": lx["we"],
                     "mordor": m, "lean": l,
                     "mordor_only": sorted(set(m) - set(l)), "lean_only": sorted(set(l) - set(m))})
    status = "agree" if all(r["status"] == "agree" for r in rows) else "differ"
    return status, "; ".join(sorted(notes)), rows


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("tests", nargs="+")
    ap.add_argument("--mordor", default=os.environ.get("MORDOR", str(DEFAULT_MORDOR)))
    ap.add_argument("--smrd-es", default=str(DEFAULT_SMRD_ES))
    ap.add_argument("-v", "--verbose", action="store_true")
    ap.add_argument("--json", help="write per-test results to this file")
    args = ap.parse_args()
    results, bad = {}, False
    for test in es_diff.tests_of(args.tests):
        with tempfile.TemporaryDirectory() as tmp:
            status, detail, rows = compare(test, args, tmp)
        results[str(test)] = {"status": status, "detail": detail, "executions": rows}
        n_ok = sum(r["status"] == "agree" for r in rows)
        print(f"{status:7} {test}  ({n_ok}/{len(rows)} executions agree){'  ' + detail if detail else ''}")
        for r in rows:
            if args.verbose or r["status"] != "agree":
                print(f"   exec {r['exec']}: {r['status']}  X={r['X']} f={r['f']} we={r['we']}")
                print(f"      ppo      {r['lean']}")
                if r["status"] != "agree":
                    print(f"      mordor only {r['mordor_only']}  lean only {r['lean_only']}")
        bad |= status in ("differ", "error")
    if args.json:
        Path(args.json).write_text(json.dumps(results, indent=1))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
