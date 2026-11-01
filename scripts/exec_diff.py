#!/usr/bin/env python3
"""Differential test of MoRDor's executions against lean4-smrd's axioms.

For each litmus test, MoRDor exports its executions (``executions``: the events
of each, and ``po``, ``dp``, ``ppo``, ``rf``, ``rmw``, ``co``, ``fwd``, ``we``).
Each execution is translated into the primitives the axioms are functions of
(``AxiomEval.PrimsL``) and handed to ``smrd-ax`` (AxExport.lean), which decides
No-Thin-Air, the coherence order, ``CoherenceT``, RC11's ``Coherence``,
``CoherenceV``, ``CoherenceP`` and Atomicity on the finite relations (each
decision proved equal to the axiom in ``Smrd.AxiomEval``).

The test checks soundness: every execution MoRDor admits satisfies the axioms.
It does not check that MoRDor finds every execution (justifications range over
semantic predicates and are not computed).

The translation:

* MoRDor's execution holds ``X ∖ †``: it drops the events ``fwd`` and ``we``
  elide. The test therefore checks the *transformed* execution, the events
  MoRDor exports with ``† = ∅``, on which ``CoherenceT`` is RC11's coherence
  (``CoherenceT.coherentT_iff_coherent``), as sMRD's axiom is RC11's over
  ``X ∖ †``. The elided events have no edges into a cycle of ``DP ∪ ≼ ∪ rf``
  (``φ``: no ``rf`` or ``DP`` out of an elided event), so No-Thin-Air is
  unaffected.
* ``Init`` and ``Terminal`` events have no counterpart and are dropped with
  their pairs. A read that reads from ``Init`` reads from a virtual initialising
  write of its location instead: one per location, ``⊑``-before and ``≼``-before
  every event (as ``Init`` is), and ``co``-before every write to the location.
  This is the execution of the program with its initialisation made explicit.
* ``X`` is the reads, writes, allocations and deallocations; fences go to
  ``X_F`` (``F``). ``W_rel`` is a write of mode ``Release``,
  ``ReleaseAcquire`` or ``SC``, ``R_acq`` likewise, and the fence classes by
  ``fmod``.
* ``DP ∪ ≼`` is MoRDor's ``dp ∪ ppo``.
* MoRDor enumerates a test's executions under the model of its first
  assertion; the test replaces the assertions by ``[SMRD]`` (``--own-model``
  keeps them: under a model weaker than RC11 the axioms then fail, a check
  that the test can fail).
* Same location: locations are compared after substituting the equalities
  ``(α = e)`` of the execution's predicates for read symbols; equal normal
  forms are the same location; distinct globals, distinct allocations (when
  the execution frees nothing), a global and an allocation, and one base at
  two offsets are distinct, as are an integer and an address and a pair the
  predicates state distinct. An
  execution with a pair of writes neither decides is skipped (``loc?``).

Tests with non-atomic accesses (sMRD has none), ``consume`` accesses or locks
(no counterpart in lean4-smrd) are skipped.

Each execution is ``ok`` or fails some axioms. ``DP ∪ ≼ ⊄ ⊑`` is not an axiom,
and is reported per execution as a diagnostic (``ppo⊄po``). MoRDor's Write
Elision elides an initialising write into a thread across a fork, which
lean4-smrd PR #28 forbids, and remapping then moves the write's ``≼`` and
``DP`` pairs into another thread. A pair outside ``⊑`` whose source is not a
write that elides across a fork is counted as a failure.

Usage::

    exec_diff.py [--mordor PATH] [--smrd-ax PATH] [-j N] [--timeout S] [--own-model] [-v]
                 [--json OUT] TEST.lit|DIR ...

Exit status 0 unless an execution fails an axiom or a test errors.
"""

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import es_diff  # noqa: E402

DEFAULT_SMRD_AX = HERE.parent / ".lake" / "build" / "bin" / "smrd-ax"
DEFAULT_MORDOR = HERE.parent.parent / "mordor" / "_build" / "default" / "cli" / "main.exe"

REL = {"Release", "ReleaseAcquire", "SC"}
ACQ = {"Acquire", "ReleaseAcquire", "SC"}
AXIOMS = ["nta", "coOrder", "cohT", "cohV", "cohP", "atom"]
VIRTUAL_BASE = 1_000_000


# --- locations ---------------------------------------------------------------

TOKEN = re.compile(r"\s*(!=|<=|>=|==|[()+\-*/=<>]|\d+|[A-Za-z_][A-Za-z_0-9]*|[^\s()+\-*/=<>!]+)")


def tokens(s):
    out, i = [], 0
    while i < len(s):
        m = TOKEN.match(s, i)
        if not m:
            raise ValueError(f"cannot read {s!r}")
        out.append(m.group(1))
        i = m.end()
    return out


def parse(s):
    """A MoRDor expression as a tree: names, ints, (op, a, b)."""
    toks = tokens(s)
    pos = 0

    def expr():
        nonlocal pos
        t = toks[pos]
        pos += 1
        if t == "(":
            a = expr()
            if toks[pos] == ")":
                pos += 1
                return a
            op = toks[pos]
            pos += 1
            b = expr()
            if toks[pos] != ")":
                raise ValueError(f"cannot read {s!r}")
            pos += 1
            return (op, a, b)
        return int(t) if t.isdigit() else t

    e = expr()
    if pos != len(toks):
        raise ValueError(f"cannot read {s!r}")
    return e


def is_global(n):
    return isinstance(n, str) and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", n) is not None


def is_sym(n):
    """A read symbol (Greek), as opposed to a global or an allocation."""
    return isinstance(n, str) and re.fullmatch(r"[\u0370-\u03ff]+'*", n) is not None


def linear(e, subst, depth=0):
    """A linear form {base: coeff} with the constant under key 1, or None."""
    if depth > 50:
        return None
    if isinstance(e, int):
        return {1: e}
    if isinstance(e, str):
        if e in subst:
            return linear(subst[e], subst, depth + 1)
        return {e: 1}
    op, a, b = e
    la, lb = linear(a, subst, depth + 1), linear(b, subst, depth + 1)
    if la is None or lb is None:
        return None
    if op in ("+", "-"):
        s = -1 if op == "-" else 1
        out = dict(la)
        for k, v in lb.items():
            out[k] = out.get(k, 0) + s * v
        return {k: v for k, v in out.items() if v != 0 or k == 1}
    return None


def norm(l):
    return tuple(sorted((str(k), v) for k, v in l.items() if v != 0))


class Locs:
    """Same-location decisions under an execution's predicates."""

    def __init__(self, predicates, frees):
        self.subst, self.ne = {}, set()
        self.frees = frees
        parent = {}

        def find(a):
            while parent.get(a, a) != a:
                a = parent[a]
            return a
        eqs = []
        for p in predicates:
            try:
                e = parse(p)
            except (ValueError, IndexError):
                continue
            if isinstance(e, tuple) and e[0] == "=":
                eqs.append(e[1:])
        for a, b in eqs:
            if not isinstance(a, tuple) and not isinstance(b, tuple):
                parent[find(a)] = find(b)
        classes = {}
        for a in list(parent) + [b for _, b in eqs if not isinstance(b, tuple)]:
            classes.setdefault(find(a), set()).add(a)
        for members in classes.values():
            rank = lambda m: (0 if isinstance(m, int) else 1 if not is_sym(m) else 2, str(m))
            rep = min(members, key=rank)
            for m in members:
                if m != rep and is_sym(m):
                    self.subst[m] = rep
        for a, b in eqs:
            for u, v in ((a, b), (b, a)):
                if is_sym(u) and u not in self.subst and isinstance(v, tuple):
                    self.subst[u] = v
        for p in predicates:
            try:
                e = parse(p)
            except (ValueError, IndexError):
                continue
            if isinstance(e, tuple) and e[0] == "!=":
                la, lb = linear(e[1], self.subst), linear(e[2], self.subst)
                if la is not None and lb is not None:
                    self.ne.add(frozenset([norm(la), norm(lb)]))

    def form(self, s):
        try:
            return linear(parse(s), self.subst)
        except (ValueError, IndexError):
            return None

    def same(self, s1, s2):
        """True, False, or None (undecided)."""
        if s1 == s2:
            return True
        l1, l2 = self.form(s1), self.form(s2)
        if l1 is None or l2 is None:
            return None
        n1, n2 = norm(l1), norm(l2)
        if n1 == n2:
            return True
        if frozenset([n1, n2]) in self.ne:
            return False
        b1 = {k: v for k, v in l1.items() if k != 1 and v != 0}
        b2 = {k: v for k, v in l2.items() if k != 1 and v != 0}
        if len(b1) == 1 and len(b2) == 1 and list(b1.values()) == [1] and list(b2.values()) == [1]:
            (k1,), (k2,) = b1, b2
            if k1 == k2:
                return False                      # one base, two offsets
            if not is_sym(k1) and not is_sym(k2) and (is_global(k1) or is_global(k2) or not self.frees):
                return False                      # distinct globals / allocations
        if not b1 and not b2:
            return False                          # distinct integers
        if (not b1 and len(b2) == 1 and not is_sym(next(iter(b2)))) or \
                (not b2 and len(b1) == 1 and not is_sym(next(iter(b1)))):
            return False                          # an integer is no address
        return None


# --- translation ---------------------------------------------------------------

class Skip(Exception):
    pass


def translate(x, thread):
    """The primitives of an execution (``PrimsL``) and diagnostics."""
    evs = {e["id"]: e for e in x["events"]}
    for e in evs.values():
        if e["type"] in ("L", "U"):
            raise Skip("locks")
        if "Nonatomic" in (e["rmod"], e["wmod"]):
            raise Skip("non-atomic accesses")
        if "Consume" in (e["rmod"], e["wmod"], e["fmod"]):
            raise Skip("consume")
        if e["type"] not in ("I", "T", "R", "W", "F", "A", "D"):
            raise Skip(f"event type {e['type']}")
    keep = {i for i, e in evs.items() if e["type"] not in ("I", "T")}
    init = [i for i, e in evs.items() if e["type"] == "I"]

    def mp(name):
        return [(a, b) for a, b in x.get(name, []) if a in keep and b in keep]

    X = sorted(i for i in keep if evs[i]["type"] != "F")
    W = sorted(i for i in keep if evs[i]["type"] == "W")
    R = sorted(i for i in keep if evs[i]["type"] == "R")
    F = sorted(i for i in keep if evs[i]["type"] == "F")
    loc = {i: evs[i].get("location") for i in keep}
    po, rf, rmw, co = mp("po"), mp("rf"), mp("rmw"), mp("co")
    dep = sorted(set(mp("ppo")) | set(mp("dp")))
    notes = []

    # reads from Init: virtual initialising writes
    init_reads = [(a, b) for a, b in x.get("rf", []) if a in init and b in keep]
    virt = {}
    if init_reads:
        ppo_from_init = {b for a, b in x.get("ppo", []) if a in init and b in keep}
        for _, r in init_reads:
            l = loc[r]
            if l not in virt:
                v = VIRTUAL_BASE + len(virt)
                virt[l] = v
                loc[v] = l
                X.append(v)
                W.append(v)
                po += [(v, e) for e in keep]
                dep += [(v, e) for e in ppo_from_init]
            rf.append((virt[l], r))
        notes.append("reads from Init")

    frees = any(evs[i]["type"] == "D" for i in keep)
    L = Locs(x.get("predicates", []), frees)
    acc = sorted(i for i in keep | set(virt.values()) if loc.get(i) is not None and
                 (i in virt.values() or evs[i]["type"] in ("R", "W")))
    sl = []
    for a in acc:
        for b in acc:
            if a == b:
                continue
            s = L.same(loc[a], loc[b])
            if s is None:
                if a in W and b in W:
                    raise Skip(f"locations {loc[a]} and {loc[b]} undecided")
                continue
            if s:
                sl.append((a, b))
    # the virtual writes are co-first at their location
    for l, v in virt.items():
        co += [(v, w) for w in W if w != v and (v, w) in set(sl)]

    def cls(ids, kind, field, modes):
        return sorted(i for i in ids if i in evs and evs[i]["type"] == kind and evs[i][field] in modes)

    q = {"X": X, "W": W, "R": R, "F": F,
         "RelW": cls(W, "W", "wmod", REL), "AcqR": cls(R, "R", "rmod", ACQ),
         "RelF": cls(F, "F", "fmod", REL), "AcqF": cls(F, "F", "fmod", ACQ),
         "el": [], "po": po, "rf": rf, "rmw": rmw, "sl": sl, "dep": dep, "co": co}
    pos = set(po)
    # Write Elision across a fork: the eliding write and the elided one in
    # different threads (lean4-smrd PR #28 forbids it, MoRDor does not)
    fork_we = {a for a, e in x.get("we", []) if thread.get(a) != thread.get(e)}
    npo = sorted(p for p in dep if p not in pos)
    diag = {"ppo_not_po": npo,
            "ppo_not_po_other": [p for p in npo if p[0] not in fork_we],
            "elided": sorted({b for _, b in x.get("fwd", []) + x.get("we", [])})}
    return q, diag, notes


# --- driver ------------------------------------------------------------------

def run(cmd, timeout):
    return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)


def smrd_only(src):
    """The program with its assertions replaced by sMRD's model: MoRDor
    enumerates executions under the model of a test's first assertion. A test
    may open with a header (``[...]`` or ``key=value`` lines, then ``%%``); a test without assertions is under
    sMRD already."""
    lines = src.splitlines()
    seps = [i for i, l in enumerate(lines) if l.strip().startswith("%%")]
    content = [l.strip() for l in lines if l.strip() and not l.strip().startswith("//")]
    if content and re.match(r"\[|[A-Za-z_]\w*\s*=(?!=)", content[0]):
        seps = seps[1:]
    if not seps:
        return src
    return "\n".join(lines[:seps[0]] + ["%%", "[SMRD]", ""])


def check(test, args):
    with tempfile.TemporaryDirectory() as tmp:
        exe = Path(tmp) / "mordor.exec.json"
        inp = Path(tmp) / "prims.json"
        lit = Path(tmp) / test.name
        src = test.read_text()
        lit.write_text(src if args.own_model else smrd_only(src))
        try:
            r = run([args.mordor, "executions", "--single", str(lit), "--output-file", str(exe),
                     "--error", "--no-progress", "--allow-unknown-model"], args.timeout)
        except subprocess.TimeoutExpired:
            return {"status": "timeout", "detail": f"mordor executions > {args.timeout}s", "executions": []}
        if r.returncode != 0 or not exe.exists():
            return {"status": "error", "detail": f"mordor executions failed: {r.stderr.strip()[-300:]}",
                    "executions": []}
        mexecs = json.loads(exe.read_text())["executions"]
        rows, qs, skipped, notes = [], [], {}, set()
        thread = {e["id"]: e.get("thread") for x in mexecs for e in x["events"]}
        for x in mexecs:
            try:
                q, diag, n = translate(x, thread)
            except Skip as s:
                if str(s) in ("locks", "non-atomic accesses", "consume") or str(s).startswith("event type"):
                    return {"status": "skip", "detail": str(s), "executions": []}
                skipped[x["id"]] = str(s)
                continue
            notes.update(n)
            qs.append(q)
            rows.append({"exec": x["id"], **diag})
        if qs:
            inp.write_text(json.dumps({"executions": qs}))
            r = run([str(args.smrd_ax), str(inp)], args.timeout)
            if r.returncode != 0:
                return {"status": "error", "detail": f"smrd-ax failed: {r.stderr.strip()[-300:]}",
                        "executions": rows}
            for row, v in zip(rows, json.loads(r.stdout)["results"]):
                row["verdicts"] = v
                row["fails"] = [a for a in AXIOMS if not v[a]] + ([] if v["cert"] else ["cert"])
        if skipped:
            notes.add(f"{len(skipped)} executions skipped: " + "; ".join(sorted(set(skipped.values()))))
        failing = [r for r in rows if r["fails"]]
        if any(r["ppo_not_po_other"] for r in rows):
            failing = True
        status = "fail" if failing else ("ok" if rows else "skip")
        return {"status": status, "detail": "; ".join(sorted(notes)), "executions": rows,
                "skipped": skipped, "total": len(mexecs)}


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("tests", nargs="+")
    ap.add_argument("--mordor", default=os.environ.get("MORDOR", str(DEFAULT_MORDOR)))
    ap.add_argument("--smrd-ax", default=str(DEFAULT_SMRD_AX))
    ap.add_argument("--timeout", type=int, default=120, help="seconds per tool run")
    ap.add_argument("-j", "--jobs", type=int, default=1)
    ap.add_argument("--own-model", action="store_true",
                    help="enumerate under each test's own model instead of sMRD's")
    ap.add_argument("-v", "--verbose", action="store_true")
    ap.add_argument("--json", help="write per-test results to this file")
    args = ap.parse_args()
    tests = list(es_diff.tests_of(args.tests))
    with ThreadPoolExecutor(args.jobs) as pool:
        res = list(pool.map(lambda t: check(t, args), tests))
    results, counts, bad = {}, {}, False
    tot = {"executions": 0, "checked": 0, "ok": 0, "ppo_not_po": 0, "other": 0}
    for test, r in zip(tests, res):
        results[str(test)] = r
        counts[r["status"]] = counts.get(r["status"], 0) + 1
        rows = r["executions"]
        tot["executions"] += r.get("total", 0)
        tot["checked"] += len(rows)
        tot["ok"] += sum(not x.get("fails") for x in rows)
        tot["ppo_not_po"] += sum(bool(x["ppo_not_po"]) for x in rows)
        tot["other"] += sum(bool(x["ppo_not_po_other"]) for x in rows)
        npp = sum(bool(x["ppo_not_po"]) for x in rows)
        line = f"{r['status']:7} {test}"
        if rows:
            line += f"  ({sum(not x.get('fails') for x in rows)}/{len(rows)} executions ok"
            line += f", {npp} with ppo⊄po)" if npp else ")"
        if r["detail"]:
            line += "  " + r["detail"]
        print(line)
        for x in rows:
            if x.get("fails") or x["ppo_not_po_other"] or (args.verbose and x["ppo_not_po"]):
                print(f"   exec {x['exec']}: fails {x.get('fails')}  ppo⊄po {x['ppo_not_po']}"
                      f"  elided {x['elided']}")
        bad |= r["status"] in ("fail", "error")
    print("tests:", ", ".join(f"{v} {k}" for k, v in sorted(counts.items())))
    print(f"executions: {tot['executions']} exported, {tot['checked']} checked, {tot['ok']} ok, "
          f"{tot['ppo_not_po']} with DP ∪ ≼ ⊄ ⊑ ({tot['ppo_not_po'] - tot['other']} from write "
          f"elision across a fork, {tot['other']} other)")
    if args.json:
        Path(args.json).write_text(json.dumps(results, indent=1))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
