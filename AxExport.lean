import Lean.Data.Json
import Smrd.AxiomEval

/-!
# `smrd-ax`: the axioms of finite executions, decided

Reads executions given by their primitives (`AxiomEval.PrimsL`) as JSON and
prints, for each, the verdicts of the decided axioms. This is the Lean side of
the differential test against MoRDor's executions (`scripts/exec_diff.py`).

```
smrd-ax <executions.json>
```

## Input

`{"executions": [e, ...]}`, each `e` an object with the event lists `X`, `W`,
`R`, `F`, `RelW`, `RelF`, `AcqR`, `AcqF`, `el` (`†`) and the pair lists `po`
(`⊑` within `X ∪ X_F`), `rf`, `rmw`, `sl` (same location), `dep` (`DP ∪ ≼`)
and `co`; a missing field is empty.

## Output

`{"results": [r, ...]}`, each `r` an object of booleans:

* `cert`: the closures are certified (`PrimsL.certB`); the other verdicts are
  the axioms only if it holds;
* `nta`: No-Thin-Air (`noThinAir_decide`);
* `coOrderT`, `coOrder`: `co` is a coherence order over the writes of `X ∖ †`,
  of `X` (`coherenceOrderT_decide`, `coherenceOrder_decide`);
* `cohT`, `coh`, `cohV`, `cohP`: `CoherenceT`, RC11's `Coherence`,
  `CoherenceV` and `CoherenceP` under `co` (`coherenceT_decide`, …);
* `atom`: Atomicity under `co` (`atomicity_decide`).
-/

open Lean AxiomEval

namespace AxExport

def ids (j : Json) (k : String) : Except String (List EventId) :=
  match j.getObjVal? k with
  | .error _ => pure []
  | .ok a => do (← a.getArr?).toList.mapM fun v => v.getNat?

def pairs (j : Json) (k : String) : Except String PairL :=
  match j.getObjVal? k with
  | .error _ => pure []
  | .ok a => do
      (← a.getArr?).toList.mapM fun v => do
        let p ← v.getArr?
        if h : p.size = 2 then
          pure ((← p[0].getNat?), (← p[1].getNat?))
        else throw "a pair has two elements"

def primsL (j : Json) : Except String PrimsL := do
  pure {
    X := ← ids j "X", W := ← ids j "W", R := ← ids j "R", F := ← ids j "F",
    RelW := ← ids j "RelW", RelF := ← ids j "RelF", AcqR := ← ids j "AcqR",
    AcqF := ← ids j "AcqF", el := ← ids j "el",
    po := ← pairs j "po", rf := ← pairs j "rf", rmw := ← pairs j "rmw", sl := ← pairs j "sl",
    dep := ← pairs j "dep", co := ← pairs j "co" }

def verdicts (q : PrimsL) : Json :=
  Json.mkObj [
    ("cert", q.certB), ("nta", q.ntaB),
    ("coOrderT", q.coOrderB q.XT), ("coOrder", q.coOrderB q.X),
    ("cohT", q.cohB q.hbTL), ("coh", q.cohB q.hbL), ("cohV", q.cohB q.hbVL),
    ("cohP", q.cohB q.hbPL), ("atom", q.atomB)]

end AxExport

def main (args : List String) : IO UInt32 := do
  let [path] := args
    | do IO.eprintln "usage: smrd-ax <executions.json>"; return 2
  let input ← IO.FS.readFile path
  match Json.parse input >>= (·.getObjVal? "executions") >>= (·.getArr?) >>=
      (·.toList.mapM AxExport.primsL) with
  | .error err => IO.eprintln s!"smrd-ax: {err}"; return 1
  | .ok qs =>
      IO.println (Json.mkObj [("results", Json.arr (qs.map AxExport.verdicts).toArray)]).compress
      return 0
