import Smrd.Basic
import Smrd.ElabDec.Saturate
import Smrd.ElabDec.RelSplitMain

/-!
# The conditions on the library's examples

Conditions C1–C3 (`EventStructure.Bounded`), with MoRDor's Strengthening
predicates (`mordorQs`: equations between the values of two events) and no
multiplication (`M = []`), checked by `boundedB` on the concrete event
structures of the library: the litmus tests of the forwarding and elision
examples, and RCU's read-side retry loop (`RoutineHyps.rcu1`, MoRDor's
`rcu-1.lit`: an `FADD`, a load through the pointer it returns, a store of the
incremented value and a `CAS`, retried in a `while` loop) unravelled to loop
bounds `0`, `1` and `2`.

For each, the decision procedure applies (`decideJ_iff`): whether a
justification is equivalent to one of the Weakening-free closure is decided
relative to the oracle.

`div_example` shows a structure outside the fragment: `RoutineHyps.esDiv`
divides by a symbol.
-/

open Expr Smrd.ElabDec EventStructure

namespace Smrd.ElabDec.Examples

/-- The conditions, for MoRDor's Strengthening and no multiplication. -/
abbrev Meets (es : EventStructure) : Prop := es.Bounded es.mordorQs []

theorem meets_of {es : EventStructure} (h : es.boundedB es.mordorQs [] = true) : Meets es :=
  boundedB_sound h

theorem fwdAcrossAlias : Meets FwdAcrossAlias.esP := meets_of (by decide)
theorem fwdAcrossAcquire : Meets FwdAcrossAcquire.esA := meets_of (by decide)
theorem fwdAcrossJoin : Meets FwdAcrossJoin.esP := meets_of (by decide)
theorem fwdPastWindow : Meets FwdPastWindow.esP := meets_of (by decide)
theorem fwdChain : Meets FwdChain.esP := meets_of (by decide)
theorem liftCross : Meets LiftCross.esC := meets_of (by decide)
theorem rmwElision : Meets RMWElision.esL := meets_of (by decide)
theorem weAcrossRelease : Meets WEAcrossRelease.esR := meets_of (by decide)
theorem rmwCross : Meets RMWCross.esX := meets_of (by decide)
theorem coRR : Meets PpoNecessity.esCoRR := meets_of (by decide)
theorem coWR : Meets PpoNecessity.esCoWR := meets_of (by decide)
theorem mp : Meets PpoNecessity.esMP := meets_of (by decide)

set_option maxRecDepth 100000

unseal interp in
/-- RCU's read side, with its retry loop unravelled `0`, `1` and `2` times. -/
theorem rcu1_0 : Meets (denote (Bounds.uniform 0) RoutineHyps.rcu1) := meets_of (by decide)

unseal interp in
theorem rcu1_1 : Meets (denote (Bounds.uniform 1) RoutineHyps.rcu1) := meets_of (by decide)

unseal interp in
theorem rcu1_2 : Meets (denote (Bounds.uniform 2) RoutineHyps.rcu1) := meets_of (by decide)

/-- Division by a symbol is outside the fragment. -/
theorem div_example : RoutineHyps.esDiv.boundedB RoutineHyps.esDiv.mordorQs [] = false := by decide

/-- The decision procedure on RCU's read side unravelled once, relative to an
    oracle, with `Ω = ⊤`. -/
theorem rcu1_decidable (O : Oracle) (j : Justification) :
    let es := denote (Bounds.uniform 1) RoutineHyps.rcu1
    es.decideJ O Expr.tt es.mordorQs es.relSplit j = true ↔
      ∃ j', es.GenR Expr.tt.holds es.mordorQs false j' ∧ JEq j' j :=
  decideJ_iff rcu1_1 rfl j

end Smrd.ElabDec.Examples
