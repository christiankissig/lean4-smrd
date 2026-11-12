import Smrd.PpoKit
import Smrd.PpoMordor
import Smrd.PpoStability

/-!
# Reflexivity of closed relabel-equivalence

Closed relabel-equivalence (Definition `def:rel-eq`, `ClosedRelabEq`) relates
two events when they are relabel-equivalent and *every* immediate
`≼`-predecessor of the one is closed relabel-equivalent to *every* immediate
`≼`-predecessor of the other. Lifting (`Generated.lift`) uses it to compare
the histories of two writes; whether the comparison can stop where the two
histories share their events depends on whether an event is closed
relabel-equivalent to itself.

* `closedRelabEq_refl`: it is, under a relabelling that fixes the symbols of
  the events the recursion visits, provided no branching event is visited and
  the two predicates give every visited event the same immediate predecessor,
  or none on both sides (`PredDiag`). Relabel-equivalence of an event with
  itself (`relabEq_self`) needs only the first of these.
* `not_closedRelabEq_self`: it is not in general. A release write `z :=ʳᵉˡ 1`
  after two relaxed reads of `x` and `y` has both reads as immediate
  `≼`-predecessors, and the all-pairs clause asks the read of `x` to be
  relabel-equivalent to the read of `y`, which fails on their locations. This
  holds under every relabelling, with the predicate `⊤` and no forwarding.

So reflexivity fails exactly because the recursion pairs every predecessor
with every other, not because of relabelling or the predicates: with at most
one immediate predecessor per visited event, it holds.
-/

namespace RelabEqRefl

open EventStructure PpoKit

/-! ## Renaming that fixes an expression's symbols -/

/-- `Λ` leaves every symbol of `x` where it is. -/
def Fixes (Λ : Relabelling) (x : Expr) : Prop := ∀ β ∈ x.syms, Λ.app β = β

theorem rename_of_fixes {Λ : Relabelling} {x : Expr} (h : Fixes Λ x) : x.rename Λ = x := by
  induction x with
  | val v => rfl
  | sym β =>
      have := h β (by simp [Expr.syms])
      simp only [Expr.rename]
      exact congrArg Expr.sym this
  | bin op a b iha ihb | eq a b iha ihb | le a b iha ihb | and a b iha ihb
  | or a b iha ihb =>
      simp only [Expr.rename]
      rw [iha (fun β hβ => h β (by simp [Expr.syms, hβ])),
        ihb (fun β hβ => h β (by simp [Expr.syms, hβ]))]
  | not a iha =>
      simp only [Expr.rename]
      rw [iha (fun β hβ => h β (by simpa [Expr.syms] using hβ))]

/-- An expression whose symbols `Λ` fixes is relabel-equivalent to itself,
    under any two predicates: the expression is its own witness. -/
theorem relabEqExpr_self (es : EventStructure) (δ : FwdCtx) {Λ : Relabelling}
    (P₁ P₂ : Expr) {x : Expr} (h : Fixes Λ x) : es.relabEqExpr δ Λ P₁ x P₂ x := by
  refine ⟨x, ?_, AgreesUnder.refl _ _⟩
  rw [rename_of_fixes h]
  exact AgreesUnder.refl _ _

/-- The symbols of an event's location and value are fixed by `Λ`. -/
def FixesEv (Λ : Relabelling) (e : Event) : Prop :=
  (∀ l, e.loc = some l → Fixes Λ l) ∧ (∀ v, e.val = some v → Fixes Λ v)

/-- **An event that is no branching is relabel-equivalent to itself** under a
    relabelling fixing the symbols of its location and value, whatever the two
    predicates. -/
theorem relabEq_self (es : EventStructure) (δ : FwdCtx) {Λ : Relabelling} (P₁ P₂ : Expr)
    {e : Event} (hb : e.isBranch = false) (hΛ : FixesEv Λ e) :
    es.relabEq δ Λ P₁ e P₂ e := by
  obtain ⟨hl, hv⟩ := hΛ
  rcases e with ⟨id, k, lab, gs⟩
  cases k with
  | read o l α vol =>
      simp only [relabEq, Event.isRead, Event.isWrite, Event.isAlloc, Bool.and_self,
        Bool.true_or, if_true]
      exact ⟨⟨l, l, rfl, rfl, relabEqExpr_self es δ P₁ P₂ (hl l rfl)⟩,
        ⟨_, _, rfl, rfl, relabEqExpr_self es δ P₁ P₂ (hv _ rfl)⟩⟩
  | write o l v vol =>
      simp only [relabEq, Event.isRead, Event.isWrite, Event.isAlloc, Bool.and_self,
        Bool.true_or, Bool.or_true, if_true]
      exact ⟨⟨l, l, rfl, rfl, relabEqExpr_self es δ P₁ P₂ (hl l rfl)⟩,
        ⟨v, v, rfl, rfl, relabEqExpr_self es δ P₁ P₂ (hv v rfl)⟩⟩
  | alloc α s =>
      simp only [relabEq, Event.isRead, Event.isWrite, Event.isAlloc, Bool.and_self,
        Bool.or_true, if_true]
      exact ⟨⟨_, _, rfl, rfl, relabEqExpr_self es δ P₁ P₂ (hl _ rfl)⟩,
        ⟨s, s, rfl, rfl, relabEqExpr_self es δ P₁ P₂ (hv s rfl)⟩⟩
  | dealloc l =>
      simp only [relabEq, Event.isRead, Event.isWrite, Event.isAlloc, Event.isDealloc,
        Bool.and_self, Bool.or_self, if_true]
      exact ⟨l, l, rfl, rfl, relabEqExpr_self es δ P₁ P₂ (hl l rfl)⟩
  | fence o =>
      simp [relabEq, Event.isRead, Event.isWrite, Event.isAlloc, Event.isDealloc,
        Event.isFence]
  | branch c => simp [Event.isBranch] at hb

/-! ## Reflexivity of the closed relation -/

/-- The two predicates give the event `a` the same immediate predecessor, or
    none on both sides: every pair the all-pairs clause of `ClosedRelabEq`
    forms at `a` is a pair of one event with itself. -/
def PredDiag (es : EventStructure) (δ : FwdCtx) (P₁ P₂ : Expr) (a : EventId) : Prop :=
  ((∀ x, ¬ es.pred δ a P₁.holds x) ↔ (∀ x, ¬ es.pred δ a P₂.holds x)) ∧
  ∀ x₁ x₂, es.pred δ a P₁.holds x₁ → es.pred δ a P₂.holds x₂ → x₁ = x₂

/-- **Closed relabel-equivalence is reflexive** on the events of a set `G`
    closed under immediate `≼^{P₁}`-predecessors, provided that on `G`

    * no event is a branching, and `Λ` fixes the symbols of every location
      and value (`relabEq_self`);
    * the predecessors agree as in `PredDiag`;

    and the recursion is well-founded from the event (`Acc`), as it is on the
    finite, `≼`-acyclic event structures the semantics generates. -/
theorem closedRelabEq_refl (es : EventStructure) (δ : FwdCtx) (Λ : Relabelling)
    (P₁ P₂ : Expr) (G : EventId → Prop)
    (hclosed : ∀ a x, G a → es.pred δ a P₁.holds x → G x)
    (hev : ∀ a ev, G a → es.ev a = some ev → ev.isBranch = false ∧ FixesEv Λ ev)
    (hdiag : ∀ a, G a → PredDiag es δ P₁ P₂ a) :
    ∀ a, Acc (fun x a => es.pred δ a P₁.holds x) a → G a →
      ∀ ev, es.ev a = some ev → es.ClosedRelabEq δ Λ P₁ ev P₂ ev := by
  intro a hacc
  induction hacc with
  | intro a _ ih =>
    intro hG ev hea
    have hid : ev.id = a := (ev_inv hea).2
    obtain ⟨hb, hΛ⟩ := hev a ev hG hea
    obtain ⟨hiff, hd⟩ := hdiag a hG
    refine .mk (relabEq_self es δ P₁ P₂ hb hΛ) (hid ▸ hiff) ?_
    intro x₁ x₂ ev₁ ev₂ h₁ h₂ he₁ he₂
    rw [hid] at h₁ h₂
    have hx : x₁ = x₂ := hd x₁ x₂ h₁ h₂
    subst hx
    rw [he₁] at he₂
    cases he₂
    exact ih x₁ h₁ (hclosed a x₁ hG h₁) ev₁ he₁

/-! ## Counterexample: two immediate predecessors -/

/-- `r₁ := x; r₂ := y; z :=ʳᵉˡ 1`, one thread, all reads relaxed. -/
def e0 : Event := PpoStability.R 0 0 [0] [] [] .rlx "x"
def e1 : Event := PpoStability.R 1 0 [1] [] [] .rlx "y"
def e2 : Event := PpoStability.W 2 0 [2] [] [] .rel "z" 1

def esR : EventStructure := ⟨[e0, e1, e2], [(0, 1), (0, 2), (1, 2)], []⟩

theorem nodupR : (esR.events.map (·.id)).Nodup := by decide

theorem gR : GlobLocs esR := globLocs_of (by decide)

theorem noEdge_empty : ∀ a b, ¬ FwdCtx.empty.edge a b := by
  intro a b h; rcases h with h | h <;> cases h

theorem ev0 : esR.ev 0 = some e0 := PpoKit.ev_of_mem nodupR (e := e0) (by simp [esR])
theorem ev1 : esR.ev 1 = some e1 := PpoKit.ev_of_mem nodupR (e := e1) (by simp [esR])
theorem ev2 : esR.ev 2 = some e2 := PpoKit.ev_of_mem nodupR (e := e2) (by simp [esR])

/-- Both reads are `≼_sync`-before the release write, whatever the predicate. -/
theorem ppo_to_rel {P : Pred} {a : EventId} (ha : a = 0 ∨ a = 1) :
    esR.ppo P .empty a 2 := by
  have hpo : esR.poR a 2 := by
    rcases ha with rfl | rfl <;> show (_, _) ∈ esR.po <;> decide
  have hnf : ¬ (esR.cls Event.isFence a ∨ esR.cls Event.isBranch a) := by
    rintro (h | h) <;> have := cls_clsB.1 h <;> revert this <;>
      rcases ha with rfl | rfl <;> decide
  have hnf₂ : ¬ (esR.cls Event.isFence 2 ∨ esR.cls Event.isBranch 2) := by
    rintro (h | h) <;> have := cls_clsB.1 h <;> revert this <;> decide
  refine ⟨(FwdCtx.remapRel_of_noEdge noEdge_empty).2 (.inl (.inl ?_)), ?_⟩
  · refine ⟨.inl (.inl ⟨2, hpo, rfl, cls_clsB.2 (by decide)⟩), hnf, hnf₂⟩
  · rcases ha with rfl | rfl <;> decide

/-- No event lies `≼`-between a read and the release write. -/
theorem no_between {P : Pred} {a b : EventId} (h₁ : esR.ppo P .empty a b)
    (h₂ : esR.ppo P .empty b 2) : False := by
  have m₁ := ppo_mem rfl gR noEdge_empty h₁
  have m₂ := ppo_mem rfl gR noEdge_empty h₂
  have hirr : b ≠ 2 := h₂.2
  have key : ∀ p ∈ syncL esR ++ aliasL esR, ∀ q ∈ syncL esR ++ aliasL esR,
      p.2 = q.1 → q.2 = 2 → p.2 = 2 := by decide
  exact hirr (key (a, b) m₁ (b, 2) m₂ rfl rfl)

theorem pred_rel {P : Pred} {a : EventId} (ha : a = 0 ∨ a = 1) :
    esR.pred .empty 2 P a :=
  ⟨ppo_to_rel ha, fun ⟨_, h₁, h₂⟩ => no_between h₁ h₂⟩

/-- **The release write is not closed relabel-equivalent to itself**, under
    any relabelling, with the predicate `⊤` and the empty forwarding context. -/
theorem not_closedRelabEq_self (Λ : Relabelling) :
    ¬ esR.ClosedRelabEq .empty Λ Expr.tt e2 Expr.tt e2 := by
  intro h
  cases h with
  | mk _ _ hall =>
    have h01 := hall 0 1 e0 e1 (pred_rel (.inl rfl)) (pred_rel (.inr rfl)) ev0 ev1
    cases h01 with
    | mk hrel _ _ =>
      simp only [relabEq, e0, e1, PpoStability.R, Event.isRead, Event.isWrite,
        Event.isAlloc, Event.loc, Event.val, Bool.and_self, Bool.true_or, if_true] at hrel
      obtain ⟨⟨l₁, l₂, hl₁, hl₂, w, ha, hb⟩, -⟩ := hrel
      cases hl₁; cases hl₂
      let f : Valuation := fun _ => .num 0
      have hψ : FwdCtx.empty.psi esR f := fun p hp => by cases hp
      have hx := ha f ⟨hψ, by simp [Expr.rename, Expr.tt, Expr.holds, Expr.eval]⟩ _ rfl
      have hy := hb f ⟨hψ, by simp [Expr.tt, Expr.holds, Expr.eval]⟩ _ rfl
      rw [hx] at hy
      simp at hy

end RelabEqRefl
