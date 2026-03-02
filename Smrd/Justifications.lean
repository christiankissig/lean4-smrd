import Smrd.Types
import Smrd.Forwardingcontext

/-! ## Justifications -/

/-- A justification of a write event w in an event structure.
    A justification j : (P, D) ⊢^δ w consists of:
    - a predicate P (boolean expression over the event structure's symbolic state)
    - a set D ⊆ E of event ids
    - a forwarding context δ = (f, we)
    - the write event w being justified -/
structure Justification : Type where
  /-- Pⱼ : the predicate -/
  P     : BoolExpr
  /-- Dⱼ : a subset of events (represented by their ids) -/
  D     : List Nat
  /-- δⱼ : the forwarding context -/
  delta : ForwardingContext
  /-- the write event being justified -/
  w     : Event
  deriving Repr

/-- Well-formedness: D must only reference event ids present in the event structure,
    w must be a write event, and δ's relations must stay within E × E. -/
def Justification.WellFormed (j : Justification) (es : EventStructure) : Prop :=
  /- w is a write event -/
  (∃ loc val ord, j.w.kind = EventKind.write loc val ord) ∧
  /- D ⊆ E -/
  (∀ id ∈ j.D, es.events.any (·.id == id)) ∧
  /- forwarding and elision relations are over E × E -/
  (∀ p ∈ j.delta.f,  es.events.any (·.id == p.1) ∧ es.events.any (·.id == p.2)) ∧
  (∀ p ∈ j.delta.we, es.events.any (·.id == p.1) ∧ es.events.any (·.id == p.2))
