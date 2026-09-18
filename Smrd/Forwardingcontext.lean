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

/-- `remap_δ(e) = e'`, as a relation:

    `remap_δ(e) ≜ remap_δ(e₁)` where `(e₁, e) ∈ F ∪ WE`, and `e` otherwise.

    The paper's recursive function presupposes that `F ∪ WE` is acyclic and
    that every event has at most one `F ∪ WE`-predecessor; the relational
    reading needs neither to be stated. -/
inductive Remap (δ : FwdCtx) : EventId → EventId → Prop
  | canon {e : EventId} : (∀ a, ¬ δ.edge a e) → Remap δ e e
  | step {a e e' : EventId} : δ.edge a e → Remap δ a e' → Remap δ e e'

/-- `remap_δ(R) = {(remap_δ(a), remap_δ(b)) | (a, b) ∈ R}` -/
def remapRel (δ : FwdCtx) (R : Rel) : Rel :=
  fun a' b' => ∃ a b, R a b ∧ δ.Remap a a' ∧ δ.Remap b b'

/-- `ψ_δ ≜ ⋀_{(e₁, e₂) ∈ F} val(e₁) = val(e₂)`, over the events of `es`. -/
def psi (es : EventStructure) (δ : FwdCtx) : Pred := fun g =>
  ∀ p ∈ δ.f, ∀ e₁ e₂ v₁ v₂, es.ev p.1 = some e₁ → es.ev p.2 = some e₂ →
    e₁.val = some v₁ → e₂.val = some v₂ → (Expr.eq v₁ v₂).holds g

end FwdCtx
