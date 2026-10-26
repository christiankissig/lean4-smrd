import Lean.Data.Json
import Smrd.EventStructureSemantics
import Smrd.PpoEval

/-!
# `smrd-es`: the event structure of a program, as JSON

Reads a program (`Stmt`) as JSON, runs the event structure semantics `denote`
under a uniform per-loop step-counter, and prints the event structure as JSON.
This is the Lean side of the differential test against MoRDor
(`scripts/es_diff.py`), which translates MoRDor's program export into the input
format below and compares the two event structures up to the renaming of event
ids and symbols.

```
smrd-es <program.json> [<bound>]     # bound defaults to 2
```

The input is a statement, or `{"program": <statement>, "free": [r, ...],
"bounds": [[ℓ, n], ...]}`; `bounds` overrides the step-counter of loop `ℓ`. Each
register in `free` starts out holding its own symbol `freeBase + i`, which no
event introduces, instead of `0` (an unassigned register reads as `0` in
`denote`). This is how MoRDor reads a register used before it is assigned: as
an unknown.

## Input

Statements are objects tagged by `op`:
`skip`, `seq {a, b}`, `par {a, b}`, `ite {cond, a, b}`, `while {loop, cond, body}`,
`assign {dst, expr}`, `load {order, dst, var, volatile}`, `store {order, var, val, volatile}`,
`addrOf {dst, var}`, `loadPtr {order, dst, ptr, volatile}`,
`storePtr {order, ptr, val, volatile}`, `fence {order}`,
`fadd {order_r, order_w, dst, var, addend}`, `cas {order_r, order_w, dst, var, expected, new}`,
`malloc {dst, size}`, `free {ptr}`.
Orders are `rlx`, `acq`, `rel`, `sc`. Program expressions are `{"reg": r}`,
`{"int": n}`, `{"<op>": [a, b]}` for `op` among `add sub mul div band bxor bor eq le and or`,
and `{"not": a}`.

## Output

`{"events": [...], "po": [[a, b], ...], "rmw": [{"r", "cond", "w"}, ...]}`, each
event `{"id", "thread", "pc", "iter": [[loop, k], ...], "kind", "guards"}`, its kind
tagged by `type` (`R`, `W`, `Fence`, `Branch`, `Alloc`, `Dealloc`) and each guard
`{"branch", "cond", "pos"}`. Expressions are `{"int": n}`, `{"bool": b}`,
`{"loc": {"global": x | "heap": n, "off": n}}`, `{"sym": α}` (the id of the event
introducing it), `{"<op>": [a, b]}` and `{"not": a}`.

## Frozen `≼` (`scripts/ppo_diff.py`)

If the input object has `"executions": [{"X": [...], "J": [...], "f": [[a, b], ...],
"we": [[a, b], ...]}, ...]` -- the events of `X`, the ids of the justified events,
and the forwarding context -- the output has `"ppo": [[[a, b], ...], ...]`, each
execution's `≼` computed by `PpoEval.ppoEval` (MoRDor's frozen `ppo`; equal to
`Execution.ppo` under the hypotheses of `PpoEval.ppoEval_iff`), and
`"closed": [b, ...]`, whether `closedB` holds of it.
-/

open Lean

namespace EsExport

/-! ## Reading programs -/

def field (j : Json) (k : String) : Except String Json := j.getObjVal? k

def str (j : Json) (k : String) : Except String String := do (← field j k).getStr?

def nat (j : Json) (k : String) : Except String Nat := do (← field j k).getNat?

def bool? (j : Json) (k : String) : Except String Bool :=
  match j.getObjVal? k with
  | .ok b => b.getBool?
  | .error _ => pure false

def memOrd : String → Except String MemOrd
  | "rlx" => pure .rlx
  | "acq" => pure .acq
  | "rel" => pure .rel
  | "sc"  => pure .sc
  | o     => throw s!"unknown memory order {o}"

def ord (j : Json) (k : String) : Except String MemOrd := do memOrd (← str j k)

def arithOp : String → Option ArithOp
  | "add" => some .add | "sub" => some .sub | "mul" => some .mul | "div" => some .div
  | "band" => some .band | "bxor" => some .bxor | "bor" => some .bor
  | _ => none

partial def pexpr (j : Json) : Except String PExpr := do
  let .obj kvs := j | throw s!"expression expected: {j.compress}"
  let [(k, v)] := kvs.toList | throw s!"expression with one key expected: {j.compress}"
  let two : Except String (PExpr × PExpr) := do
    let #[a, b] ← v.getArr? | throw s!"two operands expected: {j.compress}"
    pure (← pexpr a, ← pexpr b)
  match k with
  | "reg" => return .reg (← v.getStr?)
  | "int" => return .num (← v.getNat?)
  | "not" => return .not (← pexpr v)
  | "eq"  => let (a, b) ← two; return .eq a b
  | "le"  => let (a, b) ← two; return .le a b
  | "and" => let (a, b) ← two; return .and a b
  | "or"  => let (a, b) ← two; return .or a b
  | k => match arithOp k with
    | some op => do let (a, b) ← two; return .bin op a b
    | none => throw s!"unknown expression {k}"

partial def stmt (j : Json) : Except String Stmt := do
  let e (k : String) := do pexpr (← field j k)
  let s (k : String) := do stmt (← field j k)
  match ← str j "op" with
  | "skip"     => return .skip
  | "seq"      => return .seq (← s "a") (← s "b")
  | "par"      => return .par (← s "a") (← s "b")
  | "ite"      => return .ite (← e "cond") (← s "a") (← s "b")
  | "while"    => return .while (← nat j "loop") (← e "cond") (← s "body")
  | "assign"   => return .assign (← str j "dst") (← e "expr")
  | "load"     => return .load (← ord j "order") (← str j "dst") (← str j "var") (← bool? j "volatile")
  | "store"    => return .store (← ord j "order") (← str j "var") (← e "val") (← bool? j "volatile")
  | "addrOf"   => return .addrOf (← str j "dst") (← str j "var")
  | "loadPtr"  => return .loadPtr (← ord j "order") (← str j "dst") (← e "ptr") (← bool? j "volatile")
  | "storePtr" => return .storePtr (← ord j "order") (← e "ptr") (← e "val") (← bool? j "volatile")
  | "fence"    => return .fence (← ord j "order")
  | "fadd"     => return .fadd (← ord j "order_r") (← ord j "order_w") (← str j "dst")
                    (← str j "var") (← e "addend")
  | "cas"      => return .cas (← ord j "order_r") (← ord j "order_w") (← str j "dst")
                    (← str j "var") (← e "expected") (← e "new")
  | "malloc"   => return .malloc (← str j "dst") (← e "size")
  | "free"     => return .free (← str j "ptr")
  | op         => throw s!"unknown statement {op}"

/-! ## Writing event structures -/

def memOrdStr : MemOrd → String
  | .rlx => "rlx" | .acq => "acq" | .rel => "rel" | .sc => "sc"

def arithOpStr : ArithOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div"
  | .band => "band" | .bxor => "bxor" | .bor => "bor"

def valJson : Val → Json
  | .num n  => Json.mkObj [("int", n)]
  | .bool b => Json.mkObj [("bool", b)]
  | .loc ⟨.global x, off⟩ => Json.mkObj [("loc", Json.mkObj [("global", x), ("off", off)])]
  | .loc ⟨.heap n, off⟩   => Json.mkObj [("loc", Json.mkObj [("heap", n), ("off", off)])]

def exprJson : Expr → Json
  | .val v      => valJson v
  | .sym α      => Json.mkObj [("sym", α)]
  | .bin op a b => Json.mkObj [(arithOpStr op, Json.arr #[exprJson a, exprJson b])]
  | .eq a b     => Json.mkObj [("eq", Json.arr #[exprJson a, exprJson b])]
  | .le a b     => Json.mkObj [("le", Json.arr #[exprJson a, exprJson b])]
  | .not a      => Json.mkObj [("not", exprJson a)]
  | .and a b    => Json.mkObj [("and", Json.arr #[exprJson a, exprJson b])]
  | .or a b     => Json.mkObj [("or", Json.arr #[exprJson a, exprJson b])]

def kindJson : EventKind → Json
  | .read o l α v   => Json.mkObj [("type", "R"), ("order", memOrdStr o), ("loc", exprJson l),
                         ("sym", α), ("volatile", v)]
  | .write o l e v  => Json.mkObj [("type", "W"), ("order", memOrdStr o), ("loc", exprJson l),
                         ("val", exprJson e), ("volatile", v)]
  | .fence o        => Json.mkObj [("type", "Fence"), ("order", memOrdStr o)]
  | .branch c       => Json.mkObj [("type", "Branch"), ("cond", exprJson c)]
  | .alloc α sz     => Json.mkObj [("type", "Alloc"), ("sym", α), ("size", exprJson sz)]
  | .dealloc l      => Json.mkObj [("type", "Dealloc"), ("loc", exprJson l)]

def eventJson (e : Event) : Json :=
  Json.mkObj
    [ ("id", e.id), ("thread", e.label.thread), ("pc", toJson e.label.pc),
      ("iter", Json.arr (e.label.iter.toArray.map fun (l, k) => toJson [l, k])),
      ("kind", kindJson e.kind),
      ("guards", Json.arr (e.guards.toArray.map fun g =>
        Json.mkObj [("branch", g.branch), ("cond", exprJson g.cond), ("pos", g.pos)])) ]

def esJson (es : EventStructure) : Json :=
  Json.mkObj
    [ ("events", Json.arr (es.events.toArray.map eventJson)),
      ("po", Json.arr (es.po.toArray.map fun (a, b) => toJson [a, b])),
      ("rmw", Json.arr (es.rmw.toArray.map fun r =>
        Json.mkObj [("r", r.r), ("cond", exprJson r.cond), ("w", r.w)])) ]

/-- The symbols the free registers start out holding, above every event id. -/
def freeBase : Nat := 1000000

/-- A program, the registers it reads before assigning them, and the loops whose
    step-counter differs from the uniform one. -/
def input (j : Json) : Except String (Stmt × List Reg × List (LoopId × Nat)) := do
  match j.getObjVal? "program" with
  | .ok p =>
      let free ← match j.getObjVal? "free" with
        | .ok f => do (← f.getArr?).toList.mapM (·.getStr?)
        | .error _ => pure []
      let bounds ← match j.getObjVal? "bounds" with
        | .ok b => do (← b.getArr?).toList.mapM fun e => do
            let #[l, n] ← e.getArr? | throw "bounds: [loop, n] pairs expected"
            pure (← l.getNat?, ← n.getNat?)
        | .error _ => pure []
      return (← stmt p, free, bounds)
  | .error _ => return (← stmt j, [], [])

/-- `denote`, with each free register starting out holding its own symbol. -/
def denoteFree (n : Bounds) (P : Stmt) (free : List Reg) : EventStructure :=
  let ρ : RegState := free.zipIdx.map fun (r, i) => (r, Expr.sym (freeBase + i))
  (interp n ⟨0, []⟩ [] P ρ (fun _ _ => pure .empty) []).run' {}

def pairs (j : Json) (k : String) : Except String (List (EventId × EventId)) := do
  match j.getObjVal? k with
  | .ok a => (← a.getArr?).toList.mapM fun e => do
      let #[x, y] ← e.getArr? | throw s!"{k}: pairs expected"
      pure (← x.getNat?, ← y.getNat?)
  | .error _ => pure []

def nats (j : Json) (k : String) : Except String (List Nat) := do
  (← (← field j k).getArr?).toList.mapM (·.getNat?)

/-- An execution for `ppoEval`: its events, its justified events (only their
    ids matter), and its forwarding context. -/
def execution (es : EventStructure) (j : Json) :
    Except String (List EventId × List Justification × FwdCtx) := do
  let X ← nats j "X"
  let J ← nats j "J"
  let js := J.filterMap fun w => (es.ev w).map fun e => (⟨Expr.tt, [], {}, e⟩ : Justification)
  return (X, js, ⟨← pairs j "f", ← pairs j "we"⟩)

def ppoJson (es : EventStructure) (ex : List Json) : Except String (Json × Json) := do
  let rs ← ex.mapM fun j => do
    let (X, J, δ) ← execution es j
    let L := PpoEval.ppoEval es X J δ
    let closed := PpoEval.closedB (PpoEval.stepL es X J δ) L
    pure (Json.arr (L.toArray.map fun (a, b) => toJson [a, b]), Json.bool closed)
  return (Json.arr (rs.toArray.map (·.1)), Json.arr (rs.toArray.map (·.2)))

end EsExport

def main (args : List String) : IO UInt32 := do
  let some (path, bound) := (match args with
    | [p]    => some (p, 2)
    | [p, n] => some (p, n.toNat!)
    | _      => none : Option (String × Nat))
    | do IO.eprintln "usage: smrd-es <program.json> [<bound>]"; return 2
  let input ← IO.FS.readFile path
  match Json.parse input >>= EsExport.input with
  | .error err => IO.eprintln s!"smrd-es: {err}"; return 1
  | .ok (s, free, bounds) =>
      let n : Bounds := fun ℓ => (bounds.lookup ℓ).getD bound
      let es := EsExport.denoteFree n s free
      match Json.parse input >>= (·.getObjVal? "executions") >>= (·.getArr?) with
      | .error _ => IO.println (EsExport.esJson es).compress; return 0
      | .ok ex =>
          match EsExport.ppoJson es ex.toList with
          | .error err => IO.eprintln s!"smrd-es: {err}"; return 1
          | .ok (ppo, closed) =>
              IO.println ((EsExport.esJson es).setObjVal! "ppo" ppo |>.setObjVal! "closed" closed).compress
              return 0
