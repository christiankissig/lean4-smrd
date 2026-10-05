import Smrd.Types

/-!
# Forwarding Contexts (Definition `def:fwd-ctx`)

A forwarding context `δ = (F, WE)` pairs a forwarding relation, whose edges are
introduced by Forwarding (Definition `def:elab-fwd`), with a write elision
relation, whose edges are introduced by Write Elision (`def:elab-we`). It
induces the predicate `ψ_δ`, equating the values of forwarded pairs, and the
remapping `remap_δ` of events to their canonical sources.
-/

/-- `δ = (F, WE)`, both finite. -/
structure FwdCtx where
  f  : List (EventId × EventId) := []
  we : List (EventId × EventId) := []
  deriving Repr, DecidableEq

namespace FwdCtx

/-- `(∅, ∅)` -/
def empty : FwdCtx := {}

/-- The pointwise union of two contexts, as in `δ_J = ⋃_{j ∈ J} δ_j`. -/
def union (δ₁ δ₂ : FwdCtx) : FwdCtx := ⟨δ₁.f ++ δ₂.f, δ₁.we ++ δ₂.we⟩

/-- An edge of `F ∪ WE`. -/
def edge (δ : FwdCtx) : Rel := fun a b => (a, b) ∈ δ.f ∨ (a, b) ∈ δ.we

/-- The well-formedness conditions of Definition `def:fwd-ctx`: `F ∪ WE` is
    acyclic, and every event has at most one `F ∪ WE`-predecessor. Forwarding
    and Write Elision (`Generated.fwd`, `Generated.we`) yield no justification
    whose context violates them, and the shared context of an execution
    satisfies them (`Execution.IsExecution`). -/
structure WF (δ : FwdCtx) : Prop where
  acyclic : Rel.Acyclic δ.edge
  uniq    : ∀ a b e, δ.edge a e → δ.edge b e → a = b

theorem WF.empty : WF FwdCtx.empty where
  acyclic a h := by
    have : ∀ x y, Relation.TransGen FwdCtx.empty.edge x y → False := by
      intro x y h
      induction h with
      | single h => rcases h with h | h <;> cases h
      | tail _ _ ih => exact ih
    exact this a a h
  uniq a b e h := by rcases h with h | h <;> cases h

/-- `remap_δ(e) = e'`, as a relation:

    `remap_δ(e) ≜ remap_δ(e₁)` where `(e₁, e) ∈ F ∪ WE`, and `e` otherwise.

    The paper's recursive function presupposes that `δ` is well-formed (`WF`):
    acyclicity makes the recursion terminate, and the unique predecessor makes
    it deterministic. The relational reading is defined without them; under
    the second it is functional (`Remap.functional`). -/
inductive Remap (δ : FwdCtx) : EventId → EventId → Prop
  | canon {e : EventId} : (∀ a, ¬ δ.edge a e) → Remap δ e e
  | step {a e e' : EventId} : δ.edge a e → Remap δ a e' → Remap δ e e'

/-- With at most one `F ∪ WE`-predecessor per event, `remap_δ` is a partial
    function. -/
theorem Remap.functional {δ : FwdCtx} (huniq : ∀ a b e, δ.edge a e → δ.edge b e → a = b)
    {e e₁ e₂ : EventId} (h₁ : δ.Remap e e₁) (h₂ : δ.Remap e e₂) : e₁ = e₂ := by
  induction h₁ generalizing e₂ with
  | canon hno =>
      cases h₂ with
      | canon _ => rfl
      | step hae _ => exact absurd hae (hno _)
  | step hae _ ih =>
      cases h₂ with
      | canon hno => exact absurd hae (hno _)
      | step hbe hb => exact ih (huniq _ _ _ hae hbe ▸ hb)

/-- `remap_δ(R) = {(remap_δ(a), remap_δ(b)) | (a, b) ∈ R}` -/
def remapRel (δ : FwdCtx) (R : Rel) : Rel :=
  fun a' b' => ∃ a b, R a b ∧ δ.Remap a a' ∧ δ.Remap b b'

/-- `ψ_δ ≜ ⋀_{(e₁, e₂) ∈ F} val(e₁) = val(e₂)`, over the events of `es`. -/
def psi (es : EventStructure) (δ : FwdCtx) : Pred := fun g =>
  ∀ p ∈ δ.f, ∀ e₁ e₂ v₁ v₂, es.ev p.1 = some e₁ → es.ev p.2 = some e₂ →
    e₁.val = some v₁ → e₂.val = some v₂ → (Expr.eq v₁ v₂).holds g

end FwdCtx
