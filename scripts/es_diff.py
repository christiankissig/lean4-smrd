#!/usr/bin/env python3
"""Differential test of the event structure semantics against MoRDor.

For each litmus test, MoRDor exports the program (``parse --output-mode isa``)
and its event structure (``interpret --output-mode json``). The program is
translated into the input of ``smrd-es`` (EsExport.lean), which runs lean4-smrd's
``denote``. The two event structures are compared up to the renaming of event
ids and symbols:

* MoRDor's ``Init`` and ``Terminal`` events have no counterpart and are dropped;
* program order is read as a forest, each event under its immediate
  po-predecessor, and children are compared as a multiset;
* an event's label is its action -- type, memory order, location, value,
  condition -- with each symbol replaced by the distance, up the forest, to the
  event introducing it, so that neither ids nor symbol names matter;
* expressions are brought to Lean's connectives (``a != b`` is ``!(a = b)``,
  ``a < b`` is ``!(b <= a)``, ...).

Usage::

    es_diff.py [--mordor PATH] [--bound N] [--smrd-es PATH] [-v] TEST.lit|DIR ...

Each test is reported as ``agree``; ``equiv`` (the same structure, with
expressions that differ syntactically but agree on every valuation over a small
domain, under C's reading of the operators); ``value`` (the same structure,
with some expression not equivalent); ``differ`` (the structures differ);
``pruned`` (agree once the events of lean4-smrd's structure that MoRDor does not
generate are dropped: those on an unsatisfiable path, and branches the path
decides); ``branches`` (agree on every event but the branch events, which
MoRDor elides where the path decides them, unevenly); ``cut`` (loop programs
that agree, with lean4-smrd at bound n + 1 and its last loop bodies cut, the
shape of MoRDor's ``Blocked`` check); ``ub-model`` (differ, under a model whose UB optimisation folds
``e / !r`` to ``e``, which ``denote`` does not); ``skip`` (a construct
lean4-smrd's syntax lacks) or ``error``.

Exit status 0 unless a test is ``value``, ``differ`` or ``error``.
"""

import argparse
import difflib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_SMRD_ES = HERE.parent / ".lake" / "build" / "bin" / "smrd-es"
DEFAULT_MORDOR = HERE.parent.parent / "mordor" / "_build" / "default" / "cli" / "main.exe"


class Unsupported(Exception):
    """The program uses a construct lean4-smrd's syntax does not have."""


# ---------------------------------------------------------------------------
# Expressions, in the isa grammar of MoRDor's exports
# ---------------------------------------------------------------------------

ARITH = {"add", "sub", "mul", "div", "band", "bxor", "bor"}


def norm(e):
    """Bring an isa-grammar expression to Lean's connectives."""
    (k, v), = e.items()
    if k in ("int", "reg", "sym", "bool", "var"):
        return {k: v}
    if k == "not":
        return {"not": norm(v)}
    if k == "or" and isinstance(v, list) and len(v) != 2:
        if not v:
            return {"bool": False}
        acc = norm(v[0])
        for x in v[1:]:
            acc = {"or": [acc, norm(x)]}
        return acc
    if isinstance(v, list) and len(v) == 2:
        a, b = norm(v[0]), norm(v[1])
        if k in ARITH or k in ("eq", "le", "and", "or"):
            return {k: [a, b]}
        if k == "neq":
            return {"not": {"eq": [a, b]}}
        if k == "lt":
            return {"not": {"le": [b, a]}}
        if k == "gt":
            return {"not": {"le": [a, b]}}
        if k == "ge":
            return {"le": [b, a]}
    raise Unsupported(f"expression {k}")


# ---------------------------------------------------------------------------
# Programs: MoRDor's isa export -> smrd-es input
# ---------------------------------------------------------------------------

ORDERS = {"rlx": "rlx", "acq": "acq", "rel": "rel", "sc": "sc"}


def order(o):
    if o not in ORDERS:
        raise Unsupported(f"memory order {o}")
    return ORDERS[o]


def pexpr(e):
    e = norm(e)
    (k, v), = e.items()
    if k == "reg":
        return e
    if k == "int":
        return {"int": int(v)}
    if k == "bool":
        raise Unsupported("boolean literal in a program expression")
    if k == "sym":
        raise Unsupported("symbol in a program expression")
    if k == "not":
        return {"not": pexpr(v)}
    return {k: [pexpr(v[0]), pexpr(v[1])]}


def seq(stmts):
    stmts = [s for s in stmts if s["op"] != "skip"]
    if not stmts:
        return {"op": "skip"}
    acc = stmts[-1]
    for s in reversed(stmts[:-1]):
        acc = {"op": "seq", "a": s, "b": acc}
    return acc


def par(threads):
    acc = threads[-1]
    for t in reversed(threads[:-1]):
        acc = {"op": "par", "a": t, "b": acc}
    return acc


class Translator:
    def __init__(self, doc):
        self.doc = doc
        self.globals = set()
        self.free = set()
        self.do_loops = set()
        self.while_loops = set()
        for instr in self.instrs():
            c = instr["command"]
            if c["op"] in ("ReadVar", "WriteVar", "ReadRef"):
                self.globals.add(c["var"])

    def instrs(self):
        def walk(body):
            for i in body:
                yield i
                c = i["command"]
                for k in ("then", "else", "body"):
                    if k in c:
                        yield from walk(c[k])
                for t in c.get("threads", []):
                    yield from walk(t)
        yield from walk(self.doc["init"])
        for t in self.doc["threads"]:
            yield from walk(t["body"])

    def var(self, e, what):
        """A location that lean4-smrd's RMWs take: a global variable."""
        if set(e) == {"reg"} and e["reg"] in self.globals:
            return e["reg"]
        raise Unsupported(f"{what} on a location other than a global variable")

    def body(self, instrs):
        ops = [i["command"]["op"] for i in instrs]
        if "Par" in ops[:-1]:
            raise Unsupported("statements after a parallel block")
        return seq([self.instr(i) for i in instrs])

    def instr(self, i):
        c = i["command"]
        op = c["op"]
        if op == "Set":
            return {"op": "assign", "dst": c["dst"], "expr": pexpr(c["expr"])}
        if op == "ReadRef":
            return {"op": "addrOf", "dst": c["dst"], "var": c["var"]}
        if op == "ReadVar":
            return {"op": "load", "order": order(c["order"]), "dst": c["dst"], "var": c["var"],
                    "volatile": c.get("volatile", False)}
        if op == "WriteVar":
            return {"op": "store", "order": order(c["order"]), "var": c["var"],
                    "val": pexpr(c["val"]), "volatile": c.get("volatile", False)}
        if op == "ReadPtr":
            return {"op": "loadPtr", "order": order(c["order"]), "dst": c["dst"],
                    "ptr": pexpr(c["ptr"]), "volatile": c.get("volatile", False)}
        if op == "WritePtr":
            return {"op": "storePtr", "order": order(c["order"]), "ptr": pexpr(c["ptr"]),
                    "val": pexpr(c["val"]), "volatile": c.get("volatile", False)}
        if op == "Faa":
            # rmw_op carries MoRDor's RMW mode; "normal" is a plain FADD
            if c.get("rmw_op") not in (None, "normal"):
                raise Unsupported(f"fetch-and-{c.get('rmw_op')}")
            return {"op": "fadd", "order_r": order(c["order_r"]), "order_w": order(c["order_w"]),
                    "dst": c["dst"], "var": self.var(c["loc"], "FADD"),
                    "addend": pexpr(c["addend"])}
        if op == "Cas":
            return {"op": "cas", "order_r": order(c["order_r"]), "order_w": order(c["order_w"]),
                    "dst": c["dst"], "var": self.var(c["loc"], "CAS"),
                    "expected": pexpr(c["expected"]), "new": pexpr(c["new"])}
        if op == "Alloc":
            if c["dst"] in self.globals:
                raise Unsupported("malloc into a global")
            return {"op": "malloc", "dst": c["dst"], "size": pexpr(c["size"])}
        if op == "Free":
            return {"op": "free", "ptr": c["ptr"]}
        if op == "Fence":
            return {"op": "fence", "order": order(c["order"])}
        if op == "If":
            return {"op": "ite", "cond": pexpr(c["cond"]), "a": self.body(c["then"]),
                    "b": self.body(c["else"])}
        if op == "Par":
            return par([self.body(t) for t in c["threads"]])
        if op == "Do":
            # `do B while c` is `B; while c B`.
            self.do_loops.add(c["loop_id"] + 1)
            b = self.body(c["body"])
            return seq([b, {"op": "while", "loop": c["loop_id"] + 1, "cond": pexpr(c["cond"]),
                            "body": b}])
        if op == "While":
            # LoopId 0 is reserved in lean4-smrd for "outside every loop".
            self.while_loops.add(c["loop_id"] + 1)
            return {"op": "while", "loop": c["loop_id"] + 1, "cond": pexpr(c["cond"]),
                    "body": self.body(c["body"])}
        raise Unsupported(op)

    @staticmethod
    def regs(e):
        if isinstance(e, str):  # Free's operand is a register name
            return {e}
        (k, v), = e.items()
        if k == "reg":
            return {v}
        if isinstance(v, dict):
            return Translator.regs(v)
        if isinstance(v, list):
            return set().union(*[Translator.regs(x) for x in v if isinstance(x, dict)])
        return set()

    def check_regs(self, body, assigned):
        """Registers definitely assigned after `body`. A register read before it
        is assigned is a free variable in MoRDor, and is collected in `free`:
        smrd-es starts it out holding a symbol of its own."""
        for i in body:
            c = i["command"]
            if c["op"] == "Do":
                # the body runs once before the condition is read
                assigned = self.check_regs(c["body"], set(assigned))
            reads = set()
            for k in ("expr", "val", "ptr", "addend", "expected", "new", "size", "cond"):
                if k in c:
                    reads |= self.regs(c[k])
            if c["op"] in ("Faa", "Cas"):
                reads |= self.regs(c["loc"]) - self.globals
            reads -= self.globals
            self.free |= reads - assigned
            if c["op"] == "If":
                a = self.check_regs(c["then"], set(assigned))
                b = self.check_regs(c["else"], set(assigned))
                assigned = a & b
            elif c["op"] == "While":
                self.check_regs(c["body"], set(assigned))
            elif c["op"] == "Par":
                for t in c["threads"]:
                    self.check_regs(t, set(assigned))
            elif "dst" in c:
                assigned.add(c["dst"])
        return assigned

    def program(self):
        # The isa document has no place for statements after a parallel block
        # and lists them under `init`; their source lines give them away.
        first = min((i["loc"][0] for t in self.doc["threads"] for i in t["body"]
                     if i.get("loc")), default=None)
        if first is not None and any(i.get("loc") and i["loc"][0] > first
                                     for i in self.doc["init"]):
            raise Unsupported("statements after a parallel block")
        assigned = self.check_regs(self.doc["init"], set())
        for t in self.doc["threads"]:
            self.check_regs(t["body"], set(assigned))
        init = [self.instr(i) for i in self.doc["init"]]
        threads = [self.body(t["body"]) for t in self.doc["threads"]]
        if threads:
            init.append(par(threads))
        # MoRDor's bound n runs a loop's body at most n times and then checks
        # the condition once more (its `Blocked` check): the run stops if it
        # holds and leaves the loop if not. In denote's terms that is the bound
        # n + 1 with the last body cut off (`cut_last_bodies`); a `do` loop's
        # first body lies outside the `while`, which so gets n.
        bounds = {l: self.bound + 1 for l in self.while_loops}
        bounds.update({l: self.bound for l in self.do_loops})
        return {"program": seq(init), "free": sorted(self.free),
                "bounds": [[l, b] for l, b in sorted(bounds.items())],
                "cut": {str(l): b - 1 for l, b in bounds.items() if b > 0}}


# ---------------------------------------------------------------------------
# Event structures: canonical forests
# ---------------------------------------------------------------------------

def forest(events, po):
    """Children of each event under its immediate po-predecessor, and the roots."""
    ids = set(events)
    preds = {e: set() for e in ids}
    for a, b in po:
        if a in ids and b in ids:
            preds[b].add(a)
    parent = {}
    for e, ps in preds.items():
        # the immediate predecessor is the one every other predecessor precedes
        imm = [p for p in ps if all(q == p or q in preds[p] for q in ps)]
        parent[e] = imm[0] if imm else None
    children = {e: [] for e in ids}
    roots = []
    for e in ids:
        (children[parent[e]] if parent[e] is not None else roots).append(e)
    return parent, children, roots


def ancestry(parent, e):
    path = [e]
    while parent[path[-1]] is not None:
        path.append(parent[path[-1]])
    return path


def canon_expr(e, path, origin):
    """Replace symbols by their distance up `path`; locations by their name."""
    (k, v), = e.items()
    if k == "sym" and isinstance(v, int) and v >= FREE_BASE:
        return ("free", FREE[v - FREE_BASE])
    if k == "sym" and path is None:
        return ("sym", v)
    if k == "sym":
        o = origin(v)
        return ("sym", path.index(o)) if o in path else ("sym?", str(v))
    if k == "reg" or k == "var":
        return ("free", v) if v in FREE else ("glob", v)
    if k == "loc":
        if "global" in v:
            return ("glob", v["global"]) if v.get("off", 0) == 0 else ("glob+", v["global"], v["off"])
        return ("heap", v["heap"], v.get("off", 0))
    if k == "int":
        return ("int", int(v))
    if k == "bool":
        return ("bool", v)
    if k == "not":
        return ("not", canon_expr(v, path, origin))
    return (k, canon_expr(v[0], path, origin), canon_expr(v[1], path, origin))


# Expressions are compared semantically where the forests differ only in them,
# under C's reading of the program's operators, which is MoRDor's: `!n` is
# `n == 0`, booleans are 0 and 1, and division by zero is undefined (UB).

UB = "UB"

# Symbols of free registers in smrd-es (EsExport.freeBase), and the free
# registers of the test being compared.
FREE_BASE = 1000000
FREE = []


def domain(*exprs):
    """Values to try for the symbols: small numbers and the constants around."""
    vals = {0, 1, 2, 3}

    def consts(e):
        if e[0] == "int":
            vals.update((e[1] - 1, e[1], e[1] + 1))
        for x in e[1:]:
            if isinstance(x, tuple):
                consts(x)
    for e in exprs:
        consts(e)
    return sorted(v for v in vals if v >= 0)


def ev(e, env):
    k = e[0]
    if k == "int":
        return e[1]
    if k == "bool":
        return int(e[1])
    if k == "glob":
        return ("loc", e[1], 0)
    if k == "glob+":
        return ("loc", e[1], e[2])
    if k == "heap":
        return ("heap", e[1], e[2])
    if k == "sym":
        return env[e[1]]
    if k in ("sym?", "free"):
        return env[e]
    if k == "not":
        a = ev(e[1], env)
        return UB if a == UB else int(a == 0)
    a, b = ev(e[1], env), ev(e[2], env)
    if UB in (a, b):
        return UB
    if k == "eq":
        return int(a == b)
    if k in ("add", "sub") and isinstance(a, tuple) and isinstance(b, int):
        off = a[2] + b if k == "add" else a[2] - b
        return UB if off < 0 else (a[0], a[1], off)
    if k == "add" and isinstance(b, tuple) and isinstance(a, int):
        return (b[0], b[1], b[2] + a)
    if isinstance(a, tuple) or isinstance(b, tuple):
        return UB
    if k == "le":
        return int(a <= b)
    if k == "and":
        return int(bool(a) and bool(b))
    if k == "or":
        return int(bool(a) or bool(b))
    if k == "add":
        return a + b
    if k == "sub":
        return a - b
    if k == "mul":
        return a * b
    if k == "div":
        return UB if b == 0 else a // b
    if k == "band":
        return a & b
    if k == "bor":
        return a | b
    if k == "bxor":
        return a ^ b
    raise ValueError(k)


def syms_of(e):
    if e[0] in ("sym", "sym?", "free"):
        return {e[1] if e[0] == "sym" else e}
    return set().union(*[syms_of(x) for x in e[1:] if isinstance(x, tuple)])


def equivalent(a, b):
    """Whether two canonical expressions agree on every valuation over a small
    domain."""
    import itertools
    xs = sorted(syms_of(a) | syms_of(b), key=repr)
    if len(xs) > 5:
        return None
    for vs in itertools.product(domain(a, b), repeat=len(xs)):
        env = dict(zip(xs, vs))
        if ev(a, env) != ev(b, env):
            return False
    return True


def exprs_of(label):
    """The expressions in a label, and the label with them erased."""
    t = eval(label)
    shape, exprs = [], []
    for x in t:
        if isinstance(x, tuple):
            exprs.append(x)
            shape.append("_")
        else:
            shape.append(x)
    return tuple(shape), exprs


def pair(lean, mordor):
    """Pair the events of two forests of the same shape, expressions erased.
    Returns the pairs of differing expressions, or None if the shapes differ."""
    def shape_render(children, label, e):
        kids = sorted(shape_render(children, label, c) for c in children[e])
        return repr(exprs_of(label(e))[0]) + "{" + ",".join(kids) + "}"

    out = []

    def go(c1, l1, n1, c2, l2, n2):
        s1 = sorted(n1, key=lambda e: shape_render(c1, l1, e))
        s2 = sorted(n2, key=lambda e: shape_render(c2, l2, e))
        if [shape_render(c1, l1, e) for e in s1] != [shape_render(c2, l2, e) for e in s2]:
            return False
        for a, b in zip(s1, s2):
            ea, eb = exprs_of(l1(a))[1], exprs_of(l2(b))[1]
            out.extend((x, y) for x, y in zip(ea, eb) if x != y)
            if not go(c1, l1, c1[a], c2, l2, c2[b]):
                return False
        return True
    (c1, r1, l1), (c2, r2, l2) = lean, mordor
    return out if go(c1, l1, r1, c2, l2, r2) else None


def render(children, roots, label):
    def go(e):
        kids = sorted(go(c) for c in children[e])
        return label(e) + ("{" + ", ".join(kids) + "}" if kids else "")
    return sorted(go(r) for r in roots)


def pretty(children, roots, label):
    lines = []

    def go(e, d):
        lines.append("  " * d + label(e))
        for c in sorted(children[e], key=lambda c: render(children, [c], label)):
            go(c, d + 1)
    for r in sorted(roots, key=lambda r: render(children, [r], label)):
        go(r, 0)
    return lines


def satisfiable(conds):
    """Whether some valuation over a small domain makes every condition true;
    None when there are too many symbols to try."""
    import itertools
    xs = sorted(set().union(*[syms_of(c) for c in conds]) if conds else set(), key=repr)
    if len(xs) > 6:
        return None
    for vs in itertools.product(domain(*conds), repeat=len(xs)):
        env = dict(zip(xs, vs))
        if all(ev(c, env) not in (0, UB) for c in conds):
            return True
    return False


def prune(es, decided="path"):
    """Drop the events MoRDor does not generate: those whose path condition is
    unsatisfiable, and branch events whose outcome is decided -- with
    `decided="const"` those whose condition mentions no symbol (MoRDor
    evaluates it away), with `decided="path"` also those the path condition
    decides. MoRDor drops some of the latter and keeps others, so `classify`
    tries both. Program order is transitive, so the forest of what is
    left hangs the children of a dropped branch under its parent."""
    absolute = lambda e: canon_expr(e, None, None)

    def path(ev_):
        return [absolute(g["cond"]) if g["pos"] else ("not", absolute(g["cond"]))
                for g in ev_["guards"]]
    drop = set()
    for e in es["events"]:
        if satisfiable(path(e)) is False:
            drop.add(e["id"])
        elif e["kind"]["type"] == "Branch":
            c = absolute(e["kind"]["cond"])
            if decided == "none":
                pass
            elif decided == "const":
                if not syms_of(c):
                    drop.add(e["id"])
            elif satisfiable(path(e) + [c]) is False or satisfiable(path(e) + [("not", c)]) is False:
                drop.add(e["id"])
    return drop


def lean_canon(es, pruned=frozenset()):
    events = {e["id"]: e for e in es["events"] if e["id"] not in pruned}
    parent, children, roots = forest(events, es["po"])

    def label(i):
        e, k = events[i], events[i]["kind"]
        path = ancestry(parent, i)
        x = lambda ex: canon_expr(ex, path, lambda s: s)
        t = k["type"]
        if t == "R":
            body = (t, k["order"], x(k["loc"]), k["volatile"])
        elif t == "W":
            body = (t, k["order"], x(k["loc"]), x(k["val"]), k["volatile"])
        elif t == "Fence":
            body = (t, k["order"])
        elif t == "Branch":
            body = (t, norm_cond(x(k["cond"])))
        elif t == "Alloc":
            body = (t, x(k["size"]))
        else:
            body = (t, x(k["loc"]))
        return repr(body)
    return children, roots, label


def norm_cond(c):
    return c


MORDOR_ORDER = {"rlx": "rlx", "acq": "acq", "rel": "rel", "sc": "sc"}


def mordor_canon(doc, branches=True):
    s = doc["structure"]
    drop = ("Init", "Terminal") if branches else ("Init", "Terminal", "Branch")
    keep = {e["id"]: e for e in s["events"] if e["type"] not in drop}
    parent, children, roots = forest(keep, s["po"])
    origin_of = s["origin"]

    def label(i):
        e = keep[i]
        path = ancestry(parent, i)
        x = lambda ex: canon_expr(norm(ex), path, lambda sym: origin_of.get(sym))
        t = e["type"]
        if t == "R":
            body = (t, e["rmod"], x(e["loc"]), e["volatile"])
        elif t == "W":
            body = (t, e["wmod"], x(e["loc"]), x(e["wval"]), e["volatile"])
        elif t == "Fence":
            body = (t, e["fmod"])
        elif t == "Branch":
            body = (t, x(e["cond"]))
        elif t == "Alloc":
            body = (t, x(e["wval"]))
        else:
            body = (t, x(e["loc"]) if e["loc"] else None)
        return repr(body)
    return children, roots, label


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

TIMEOUT = 120


class Timeout(Exception):
    pass


def run(cmd):
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        raise Timeout(f"{Path(cmd[0]).name} {cmd[1] if len(cmd) > 1 else ''} took over {TIMEOUT}s")


# MoRDor's models with `ubopt` set (Context's model table): the interpreter
# assumes no division by zero and folds `e / !r` to `e`.
UB_MODELS = {"ub11", "rc11ub", "immub"}


def ub_model(test):
    """Whether an assertion of the test names a UB-optimising model."""
    import re
    text = Path(test).read_text(errors="replace")
    tail = text[text.index("%%"):] if "%%" in text else ""
    return any(m.strip().lower() in UB_MODELS
               for group in re.findall(r"\[([^\]]*)\]", tail) for m in group.split(","))


def compare(test, args, tmp):
    isa = Path(tmp) / "prog.isa.json"
    esm = Path(tmp) / "mordor.es.json"
    prog = Path(tmp) / "prog.lean.json"
    r = run([args.mordor, "parse", "--single", str(test), "--output-mode", "isa",
             "--output-file", str(isa), "--error", "--no-progress", "--allow-unknown-model"])
    if r.returncode != 0 or not isa.exists():
        return "error", f"mordor parse failed: {r.stderr.strip()[-300:]}"
    try:
        tr = Translator(json.loads(isa.read_text()))
        tr.bound = args.bound
        lean_prog = tr.program()
    except Unsupported as u:
        return "skip", str(u)
    FREE[:] = lean_prog["free"]
    prog.write_text(json.dumps(lean_prog))
    r = run([args.mordor, "interpret", "--single", str(test), "--output-mode", "json",
             "--output-file", str(esm), "--step-counter-per-loop", str(args.bound),
             "--error", "--no-progress", "--allow-unknown-model"])
    if r.returncode != 0 or not esm.exists():
        return "error", f"mordor interpret failed: {r.stderr.strip()[-300:]}"
    r = run([str(args.smrd_es), str(prog), str(args.bound)])
    if r.returncode != 0:
        return "error", f"smrd-es failed: {r.stderr.strip()[-300:]}"
    lean_es = cut_last_bodies(json.loads(r.stdout), lean_prog["cut"])
    status, detail = classify(lean_es, json.loads(esm.read_text()))
    if status == "agree" and lean_prog["cut"]:
        return "cut", "agree with denote at bound n + 1, its last loop bodies cut"
    if status in ("value", "differ") and ub_model(test):
        return "ub-model", detail
    return status, detail


def cut_last_bodies(es, cut):
    """Drop the events of iteration `cut[ℓ]` of each loop `ℓ` other than its
    head: the head then leads only out of the loop, as MoRDor's `Blocked`
    check does. A head is the `Branch` at the program counter of the loop's
    first event of iteration 0."""
    if not cut:
        return es
    head = {}
    for e in sorted(es["events"], key=lambda e: e["id"]):
        for l, k in e["iter"]:
            if str(l) in cut and k == 0 and str(l) not in head:
                head[str(l)] = e["pc"]

    def keep(e):
        for l, k in e["iter"]:
            if str(l) in cut and k == cut[str(l)]:
                is_head = (e["kind"]["type"] == "Branch" and e["pc"] == head.get(str(l))
                           and e["iter"][-1] == [l, k])
                if not is_head:
                    return False
        return True
    events = [e for e in es["events"] if keep(e)]
    ids = {e["id"] for e in events}
    return {**es, "events": events, "po": [p for p in es["po"] if p[0] in ids and p[1] in ids]}


def classify(lean_es, mordor_doc):
    lean = lean_canon(lean_es)
    mordor = mordor_canon(mordor_doc)
    if render(*lean) == render(*mordor):
        return "agree", ""
    for decided in ("const", "path"):
        pruned = prune(lean_es, decided)
        if pruned:
            lean = lean_canon(lean_es, pruned)
            if render(*lean) == render(*mordor):
                return "pruned", (f"{len(pruned)} infeasible or decided ({decided})"
                                  " events dropped from lean4-smrd's")
    diff = "\n".join(difflib.unified_diff(pretty(*mordor), pretty(*lean), "mordor",
                                          "lean4-smrd", lineterm=""))
    pairs = pair(lean, mordor)
    if pairs is not None:
        verdicts = [equivalent(a, b) for a, b in pairs]
        if all(v is True for v in verdicts):
            return "equiv", diff
        return "value", diff + "\n" + "\n".join(
            f"  lean {a}  vs  mordor {b}: {'equivalent' if v else 'NOT equivalent' if v is False else 'too many symbols'}"
            for (a, b), v in zip(pairs, verdicts))
    # MoRDor elides some branches the path decides and keeps others; failing
    # everything above, compare the events that are not branches, on the paths
    # lean4-smrd's structure can take.
    infeasible = prune(lean_es, "none")
    no_branches = infeasible | {e["id"] for e in lean_es["events"]
                                if e["kind"]["type"] == "Branch"}
    if render(*lean_canon(lean_es, no_branches)) == render(*mordor_canon(mordor_doc, False)):
        return "branches", "agree on every event but the branches"
    return "differ", diff


def tests_of(paths):
    for p in map(Path, paths):
        if p.is_dir():
            yield from sorted(p.rglob("*.lit"))
        else:
            yield p


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("tests", nargs="+")
    ap.add_argument("--mordor", default=os.environ.get("MORDOR", str(DEFAULT_MORDOR)))
    ap.add_argument("--smrd-es", default=str(DEFAULT_SMRD_ES))
    ap.add_argument("--bound", type=int, default=2)
    ap.add_argument("--timeout", type=int, default=120, help="seconds per tool run")
    ap.add_argument("-v", "--verbose", action="store_true", help="print diffs and skip reasons")
    ap.add_argument("--json", help="write per-test results to this file")
    args = ap.parse_args()
    global TIMEOUT
    TIMEOUT = args.timeout
    results = {}
    counts = {}
    for test in tests_of(args.tests):
        with tempfile.TemporaryDirectory() as tmp:
            try:
                status, detail = compare(test, args, tmp)
            except Timeout as t:
                status, detail = "timeout", str(t)
        results[str(test)] = {"status": status, "detail": detail}
        counts[status] = counts.get(status, 0) + 1
        print(f"{status:7} {test}" + (f"  ({detail})" if status in ("skip", "error", "timeout") and not args.verbose else ""))
        if args.verbose and detail:
            print(detail)
    print(" ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    if args.json:
        Path(args.json).write_text(json.dumps(results, indent=1))
    return 1 if counts.get("differ") or counts.get("value") or counts.get("error") else 0


if __name__ == "__main__":
    sys.exit(main())
