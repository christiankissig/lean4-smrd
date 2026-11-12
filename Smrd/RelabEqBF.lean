import Smrd.RelabEqRefl

/-!
# Closed relabel-equivalence with predecessors matched back and forth

`ClosedRelabEq` (Definition `def:rel-eq`) asks *every* immediate
`≼`-predecessor of `e₁` to be closed relabel-equivalent to *every* immediate
`≼`-predecessor of `e₂`. Two unordered predecessors on one side then have to
be equivalent to each other. `ClosedRelabEqBF` asks instead that the
predecessors match back and forth: each predecessor of `e₁` is equivalent to
some predecessor of `e₂`, and each predecessor of `e₂` to some predecessor of
`e₁`.

* `closedRelabEqBF_of_closedRelabEq`: the back-and-forth relation contains
  the all-pairs one, wherever immediate predecessors are events.
* `closedRelabEqBF_refl`: it is reflexive on a `pred`-closed set of events
  whose symbols `Λ` fixes, none of them a branching, given that both
  predicates give each of them the same immediate predecessors (`PredEq`).
  `RelabEqRefl.closedRelabEq_refl` needed at most one predecessor per event
  (`PredDiag`).
* `closedRelabEqBF_esR`: the release write of
  `RelabEqRefl.not_closedRelabEq_self`, which is not closed
  relabel-equivalent to itself, is related to itself here.
* `strict`: the inclusion is strict, and the witness is a Lifting. In
  `r :acq= y; rc := c; if (rc = 1) { z := 1 } else { z := 1 }`, after
  `z := 0`, each `z := 1` has the two unordered immediate predecessors
  `z := 0` (same location) and the acquire read. Under the predicates of the
  two arms the writes are related back and forth (`bf_arms`) and, for every
  relabelling, not all-pairs (`not_closedRelabEq_arms`), as that would need
  the write `z := 0` to be equivalent to the read of `y`. So Lifting cannot
  merge the arms, and the control dependency on `rc` stays.
-/

namespace RelabEqBF

open EventStructure PpoKit RelabEqRefl

mutual

/-- `P₁ : e₁ ≅^Λ_δ* P₂ : e₂` with immediate predecessors matched back and
    forth. As for `ClosedRelabEq`, the recursion descends along `≼`, so the
    inductive reading is the intended one. The partners are stated through
    `MatchR` and `MatchL` because Lean does not accept the relation nested
    under `∃`; `matchR_iff` and `matchL_iff` give the existential form. -/
inductive ClosedRelabEqBF (es : EventStructure) (δ : FwdCtx) (Λ : Relabelling) :
    Expr → Event → Expr → Event → Prop
  | mk {P₁ P₂ : Expr} {e₁ e₂ : Event} :
      es.relabEq δ Λ P₁ e₁ P₂ e₂ →
      (∀ x₁ ev₁, es.pred δ e₁.id P₁.holds x₁ → es.ev x₁ = some ev₁ →
        MatchR es δ Λ P₁ ev₁ P₂ e₂) →
      (∀ x₂ ev₂, es.pred δ e₂.id P₂.holds x₂ → es.ev x₂ = some ev₂ →
        MatchL es δ Λ P₁ e₁ P₂ ev₂) →
      ClosedRelabEqBF es δ Λ P₁ e₁ P₂ e₂

/-- `MatchR … P₁ ev₁ P₂ e₂`: `ev₁` is related to some immediate predecessor
    of `e₂`. -/
inductive MatchR (es : EventStructure) (δ : FwdCtx) (Λ : Relabelling) :
    Expr → Event → Expr → Event → Prop
  | mk {P₁ P₂ : Expr} {ev₁ e₂ ev₂ : Event} {x₂ : EventId} :
      es.pred δ e₂.id P₂.holds x₂ → es.ev x₂ = some ev₂ →
      ClosedRelabEqBF es δ Λ P₁ ev₁ P₂ ev₂ → MatchR es δ Λ P₁ ev₁ P₂ e₂

/-- `MatchL … P₁ e₁ P₂ ev₂`: some immediate predecessor of `e₁` is related
    to `ev₂`. -/
inductive MatchL (es : EventStructure) (δ : FwdCtx) (Λ : Relabelling) :
    Expr → Event → Expr → Event → Prop
  | mk {P₁ P₂ : Expr} {e₁ ev₁ ev₂ : Event} {x₁ : EventId} :
      es.pred δ e₁.id P₁.holds x₁ → es.ev x₁ = some ev₁ →
      ClosedRelabEqBF es δ Λ P₁ ev₁ P₂ ev₂ → MatchL es δ Λ P₁ e₁ P₂ ev₂

end

theorem matchR_iff {es : EventStructure} {δ : FwdCtx} {Λ : Relabelling} {P₁ P₂ : Expr}
    {ev₁ e₂ : Event} :
    MatchR es δ Λ P₁ ev₁ P₂ e₂ ↔
      ∃ x₂ ev₂, es.pred δ e₂.id P₂.holds x₂ ∧ es.ev x₂ = some ev₂ ∧
        ClosedRelabEqBF es δ Λ P₁ ev₁ P₂ ev₂ :=
  ⟨fun ⟨h, he, hr⟩ => ⟨_, _, h, he, hr⟩, fun ⟨_, _, h, he, hr⟩ => .mk h he hr⟩

theorem matchL_iff {es : EventStructure} {δ : FwdCtx} {Λ : Relabelling} {P₁ P₂ : Expr}
    {e₁ ev₂ : Event} :
    MatchL es δ Λ P₁ e₁ P₂ ev₂ ↔
      ∃ x₁ ev₁, es.pred δ e₁.id P₁.holds x₁ ∧ es.ev x₁ = some ev₁ ∧
        ClosedRelabEqBF es δ Λ P₁ ev₁ P₂ ev₂ :=
  ⟨fun ⟨h, he, hr⟩ => ⟨_, _, h, he, hr⟩, fun ⟨_, _, h, he, hr⟩ => .mk h he hr⟩

/-! ## The all-pairs relation is contained in it -/

/-- **All pairs implies back and forth**, where every immediate predecessor
    is an event: the emptiness clause of `ClosedRelabEq` supplies a partner
    on the other side, and the all-pairs clause relates it. -/
theorem closedRelabEqBF_of_closedRelabEq {es : EventStructure} {δ : FwdCtx}
    {Λ : Relabelling}
    (hpe : ∀ (a : EventId) (P : Pred) (x : EventId), es.pred δ a P x → ∃ ev, es.ev x = some ev)
    {P₁ P₂ : Expr} {e₁ e₂ : Event} (h : es.ClosedRelabEq δ Λ P₁ e₁ P₂ e₂) :
    ClosedRelabEqBF es δ Λ P₁ e₁ P₂ e₂ := by
  induction h with
  | mk hrel hiff _ ih =>
    refine .mk hrel ?_ ?_
    · intro x₁ ev₁ h₁ he₁
      have : ∃ x₂, es.pred δ _ _ x₂ := Classical.byContradiction fun hn =>
        hiff.2 (fun x hx => hn ⟨x, hx⟩) x₁ h₁
      obtain ⟨x₂, h₂⟩ := this
      obtain ⟨ev₂, he₂⟩ := hpe _ _ x₂ h₂
      exact .mk h₂ he₂ (ih x₁ x₂ ev₁ ev₂ h₁ h₂ he₁ he₂)
    · intro x₂ ev₂ h₂ he₂
      have : ∃ x₁, es.pred δ _ _ x₁ := Classical.byContradiction fun hn =>
        hiff.1 (fun x hx => hn ⟨x, hx⟩) x₂ h₂
      obtain ⟨x₁, h₁⟩ := this
      obtain ⟨ev₁, he₁⟩ := hpe _ _ x₁ h₁
      exact .mk h₁ he₁ (ih x₁ x₂ ev₁ ev₂ h₁ h₂ he₁ he₂)

/-! ## Reflexivity -/

/-- Both predicates give the event `a` the same immediate predecessors. -/
def PredEq (es : EventStructure) (δ : FwdCtx) (P₁ P₂ : Expr) (a : EventId) : Prop :=
  ∀ x, es.pred δ a P₁.holds x ↔ es.pred δ a P₂.holds x

/-- **Back-and-forth closed relabel-equivalence is reflexive** on the events
    of a set `G` closed under immediate `≼^{P₁}`-predecessors, provided that
    on `G` no event is a branching, `Λ` fixes the symbols of every location
    and value, and the two predicates give every event the same immediate
    predecessors. Each predecessor is matched with itself. -/
theorem closedRelabEqBF_refl (es : EventStructure) (δ : FwdCtx) (Λ : Relabelling)
    (P₁ P₂ : Expr) (G : EventId → Prop)
    (hclosed : ∀ a x, G a → es.pred δ a P₁.holds x → G x)
    (hev : ∀ a ev, G a → es.ev a = some ev → ev.isBranch = false ∧ FixesEv Λ ev)
    (hpred : ∀ a, G a → PredEq es δ P₁ P₂ a) :
    ∀ a, Acc (fun x a => es.pred δ a P₁.holds x) a → G a →
      ∀ ev, es.ev a = some ev → ClosedRelabEqBF es δ Λ P₁ ev P₂ ev := by
  intro a hacc
  induction hacc with
  | intro a _ ih =>
    intro hG ev hea
    have hid : ev.id = a := (ev_inv hea).2
    obtain ⟨hb, hΛ⟩ := hev a ev hG hea
    refine .mk (relabEq_self es δ P₁ P₂ hb hΛ) ?_ ?_
    · intro x ev' h he
      rw [hid] at h
      exact .mk (hid ▸ (hpred a hG x).1 h) he (ih x h (hclosed a x hG h) ev' he)
    · intro x ev' h he
      rw [hid] at h
      have h₁ := (hpred a hG x).2 h
      exact .mk (hid ▸ h₁) he (ih x h₁ (hclosed a x hG h₁) ev' he)

/-- Under one predicate on both sides `PredEq` is trivial. -/
theorem closedRelabEqBF_refl_same (es : EventStructure) (δ : FwdCtx) (Λ : Relabelling)
    (P : Expr) (G : EventId → Prop)
    (hclosed : ∀ a x, G a → es.pred δ a P.holds x → G x)
    (hev : ∀ a ev, G a → es.ev a = some ev → ev.isBranch = false ∧ FixesEv Λ ev) :
    ∀ a, Acc (fun x a => es.pred δ a P.holds x) a → G a →
      ∀ ev, es.ev a = some ev → ClosedRelabEqBF es δ Λ P ev P ev :=
  closedRelabEqBF_refl es δ Λ P P G hclosed hev (fun _ _ _ => Iff.rfl)

/-- `pred` is well-founded when it decreases event ids. -/
theorem acc_of_lt {r : EventId → EventId → Prop} (h : ∀ x a, r x a → x < a) (a : EventId) :
    Acc r a :=
  Subrelation.accessible (fun {x a} hr => h x a hr) (Nat.lt_wfRel.wf.apply a)

/-- The empty relabelling. -/
def Λ₀ : Relabelling := fun _ => none

theorem fixesEv_Λ₀ (e : Event) : FixesEv Λ₀ e :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-! ## The release write of `RelabEqRefl` is now related to itself -/

theorem factR : ∀ p ∈ syncL esR ++ aliasL esR, p.1 < p.2 := by decide

theorem pred_lt_R {P : Pred} {a x : EventId} (h : esR.pred .empty a P x) : x < a :=
  factR (x, a) (ppo_mem rfl gR noEdge_empty h.1)

/-- `z :=ʳᵉˡ 1` after two relaxed reads is back-and-forth closed
    relabel-equivalent to itself, under the empty relabelling and `⊤`. -/
theorem closedRelabEqBF_esR : ClosedRelabEqBF esR .empty Λ₀ Expr.tt e2 Expr.tt e2 := by
  refine closedRelabEqBF_refl_same esR .empty Λ₀ Expr.tt (fun _ => True)
    (fun _ _ _ _ => trivial) ?_ 2 (acc_of_lt (fun _ _ h => pred_lt_R h) 2) trivial e2 ev2
  intro a ev _ he
  refine ⟨?_, fixesEv_Λ₀ ev⟩
  have hm := (ev_inv he).1
  simp only [esR, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl <;> rfl

/-! ## The strictness witness: Lifting over identical arms -/

/-- The branch condition `rc = 1`; `rc` is the symbol of the read of `c`. -/
def cond : Expr := .eq (.sym 2) (.val (.num 1))

/-- `z := 0; r :acq= y; rc := c; if (rc = 1) { z := 1 } else { z := 1 }` -/
def a0 : Event := PpoStability.W 0 0 [0] [] [] .rlx "z" 0
def a1 : Event := PpoStability.R 1 0 [1] [] [] .acq "y"
def a2 : Event := PpoStability.R 2 0 [2] [] [] .rlx "c"
def a3 : Event := ⟨3, .branch cond, ⟨0, [3], []⟩, []⟩
def a4 : Event := PpoStability.W 4 0 [3, 0] [] [⟨3, cond, true⟩] .rlx "z" 1
def a5 : Event := PpoStability.W 5 0 [3, 1] [] [⟨3, cond, false⟩] .rlx "z" 1

def esA : EventStructure :=
  ⟨[a0, a1, a2, a3, a4, a5],
    [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5),
     (2, 3), (2, 4), (2, 5), (3, 4), (3, 5)], []⟩

theorem nodupA : (esA.events.map (·.id)).Nodup := by decide

theorem gA : GlobLocs esA := globLocs_of (by decide)

theorem evA0 : esA.ev 0 = some a0 := PpoKit.ev_of_mem nodupA (e := a0) (by simp [esA])
theorem evA1 : esA.ev 1 = some a1 := PpoKit.ev_of_mem nodupA (e := a1) (by simp [esA])
theorem evA4 : esA.ev 4 = some a4 := PpoKit.ev_of_mem nodupA (e := a4) (by simp [esA])
theorem evA5 : esA.ev 5 = some a5 := PpoKit.ev_of_mem nodupA (e := a5) (by simp [esA])

/-- The `≼`-pairs, over-approximated: none ends in `z := 0` or the acquire
    read, and those ending in either `z := 1` start in one of them. -/
theorem factA : ∀ p ∈ syncL esA ++ aliasL esA, p.2 ≠ 0 ∧ p.2 ≠ 1 ∧
    (p.2 = 4 → p.1 = 0 ∨ p.1 = 1) ∧ (p.2 = 5 → p.1 = 0 ∨ p.1 = 1) := by decide

theorem memA {P : Pred} {a b : EventId} (h : esA.ppo P .empty a b) :
    (a, b) ∈ syncL esA ++ aliasL esA :=
  ppo_mem rfl gA noEdge_empty h

theorem no_ppo_01 {P : Pred} {a x : EventId} (ha : a = 0 ∨ a = 1) :
    ¬ esA.ppo P .empty x a := fun h => by
  have := factA _ (memA h)
  rcases ha with rfl | rfl
  · exact this.1 rfl
  · exact this.2.1 rfl

theorem no_pred_01 {P : Pred} {a x : EventId} (ha : a = 0 ∨ a = 1) :
    ¬ esA.pred .empty a P x := fun h => no_ppo_01 ha h.1

/-- The predicates of the two arms, `valres` of the two writes. -/
def P₄ : Expr := a4.valres
def P₅ : Expr := a5.valres

def f₁ : Valuation := fun _ => .num 1
def f₀ : Valuation := fun _ => .num 0

theorem sat₄ : Sat (Pred.and P₄.holds (Expr.eq (Expr.glob "z") (Expr.glob "z")).holds) :=
  ⟨f₁, by unfold Expr.holds; decide, by unfold Expr.holds; decide⟩

theorem sat₅ : Sat (Pred.and P₅.holds (Expr.eq (Expr.glob "z") (Expr.glob "z")).holds) :=
  ⟨f₀, by unfold Expr.holds; decide, by unfold Expr.holds; decide⟩

theorem nfb {a : EventId} (ha : a = 0 ∨ a = 1 ∨ a = 4 ∨ a = 5) :
    ¬ (esA.cls Event.isFence a ∨ esA.cls Event.isBranch a) := by
  rintro (h | h) <;> have := cls_clsB.1 h <;> revert this <;>
    rcases ha with rfl | rfl | rfl | rfl <;> decide

/-- `z := 0 ≼ z := 1`, in either arm, by location. -/
theorem ppo_init {P : Expr} {b : EventId} {eb : Event} (hb : b = 4 ∨ b = 5)
    (heb : esA.ev b = some eb) (hl : eb.loc = some (Expr.glob "z"))
    (hs : Sat (Pred.and P.holds (Expr.eq (Expr.glob "z") (Expr.glob "z")).holds)) :
    esA.ppo P.holds .empty 0 b := by
  have hpo : esA.poR 0 b := by rcases hb with rfl | rfl <;> show (_, _) ∈ esA.po <;> decide
  refine ⟨(FwdCtx.remapRel_of_noEdge noEdge_empty).2
    (.inr ⟨hpo, a0, eb, _, _, evA0, heb, rfl, hl, hs⟩), ?_⟩
  rcases hb with rfl | rfl <;> decide

/-- `r :acq= y ≼ z := 1`, in either arm, by the acquire. -/
theorem ppo_acq {P : Pred} {b : EventId} (hb : b = 4 ∨ b = 5) : esA.ppo P .empty 1 b := by
  have hpo : esA.poR 1 b := by rcases hb with rfl | rfl <;> show (_, _) ∈ esA.po <;> decide
  refine ⟨(FwdCtx.remapRel_of_noEdge noEdge_empty).2 (.inl (.inl ?_)), ?_⟩
  · refine ⟨.inr (.inl ⟨1, ⟨rfl, cls_clsB.2 (by decide)⟩, hpo⟩), nfb (by simp),
      nfb (by rcases hb with rfl | rfl <;> simp)⟩
  · rcases hb with rfl | rfl <;> decide

/-- The immediate predecessors of a `z := 1` are `z := 0` and the acquire
    read, under a predicate of its arm. -/
theorem pred_arm {P : Expr} {b : EventId} {eb : Event} (hb : b = 4 ∨ b = 5)
    (heb : esA.ev b = some eb) (hl : eb.loc = some (Expr.glob "z"))
    (hs : Sat (Pred.and P.holds (Expr.eq (Expr.glob "z") (Expr.glob "z")).holds))
    (x : EventId) : esA.pred .empty b P.holds x ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    have := factA _ (memA h.1)
    rcases hb with rfl | rfl
    · exact this.2.2.1 rfl
    · exact this.2.2.2 rfl
  · intro hx
    refine ⟨?_, fun ⟨c, h₁, h₂⟩ => ?_⟩
    · rcases hx with rfl | rfl
      · exact ppo_init hb heb hl hs
      · exact ppo_acq hb
    · have hc : c = 0 ∨ c = 1 := by
        have := factA _ (memA h₂)
        rcases hb with rfl | rfl
        · exact this.2.2.1 rfl
        · exact this.2.2.2 rfl
      exact no_ppo_01 hc h₁

theorem pred4 (x : EventId) : esA.pred .empty 4 P₄.holds x ↔ x = 0 ∨ x = 1 :=
  pred_arm (.inl rfl) evA4 rfl sat₄ x

theorem pred5 (x : EventId) : esA.pred .empty 5 P₅.holds x ↔ x = 0 ∨ x = 1 :=
  pred_arm (.inr rfl) evA5 rfl sat₅ x

/-! ### All pairs: the arms are not related -/

/-- **The two writes `z := 1` are not closed relabel-equivalent** under the
    predicates of their arms, for any relabelling: the all-pairs clause pairs
    the write `z := 0` with the acquire read of `y`. -/
theorem not_closedRelabEq_arms (Λ : Relabelling) :
    ¬ esA.ClosedRelabEq .empty Λ P₄ a4 P₅ a5 := by
  intro h
  cases h with
  | mk _ _ hall =>
    have h01 := hall 0 1 a0 a1 ((pred4 0).2 (.inl rfl)) ((pred5 1).2 (.inr rfl)) evA0 evA1
    cases h01 with
    | mk hrel _ _ =>
      simp [relabEq, a0, a1, PpoStability.R, PpoStability.W, Event.isRead, Event.isWrite,
        Event.isAlloc, Event.isDealloc, Event.isFence] at hrel

/-! ### Back and forth: the arms are related -/

/-- The writes themselves: same location, same value. -/
theorem relabEq_45 : esA.relabEq .empty Λ₀ P₄ a4 P₅ a5 := by
  have hv : esA.relabEqExpr .empty Λ₀ P₄ (.val (.num 1)) P₅ (.val (.num 1)) :=
    ⟨.val (.num 1), fun _ _ _ h => h, fun _ _ _ h => h⟩
  have hl : esA.relabEqExpr .empty Λ₀ P₄ (Expr.glob "z") P₅ (Expr.glob "z") :=
    ⟨Expr.glob "z", fun _ _ _ h => h, fun _ _ _ h => h⟩
  simp only [relabEq, a4, a5, PpoStability.W, Event.isRead, Event.isWrite, Event.isAlloc,
    Event.loc, Event.val]
  simp only [Bool.and_self, Bool.or_true]
  exact ⟨⟨_, _, rfl, rfl, hl⟩, ⟨_, _, rfl, rfl, hv⟩⟩

/-- `z := 0` and the acquire read, which have no predecessors, are each
    related to themselves. -/
theorem bf_leaf {e : Event} (hid : e.id = 0 ∨ e.id = 1) (hb : e.isBranch = false) :
    ClosedRelabEqBF esA .empty Λ₀ P₄ e P₅ e :=
  .mk (relabEq_self esA .empty P₄ P₅ hb (fixesEv_Λ₀ e))
    (fun _ _ h _ => (no_pred_01 hid h).elim) (fun _ _ h _ => (no_pred_01 hid h).elim)

theorem bf0 : ClosedRelabEqBF esA .empty Λ₀ P₄ a0 P₅ a0 := bf_leaf (e := a0) (.inl rfl) rfl
theorem bf1 : ClosedRelabEqBF esA .empty Λ₀ P₄ a1 P₅ a1 := bf_leaf (e := a1) (.inr rfl) rfl

/-- The predecessor `x` of either arm, with its event, is `z := 0` or the
    acquire read, related to itself. -/
theorem match_self {x : EventId} {ev : Event} (hx : x = 0 ∨ x = 1) (he : esA.ev x = some ev) :
    ClosedRelabEqBF esA .empty Λ₀ P₄ ev P₅ ev := by
  rcases hx with rfl | rfl
  · rw [evA0] at he; cases he; exact bf0
  · rw [evA1] at he; cases he; exact bf1

/-- **The two writes `z := 1` are back-and-forth closed relabel-equivalent**
    under the predicates of their arms: each predecessor matches itself. -/
theorem bf_arms : ClosedRelabEqBF esA .empty Λ₀ P₄ a4 P₅ a5 := by
  refine .mk relabEq_45 ?_ ?_
  · intro x ev h he
    have hx := (pred4 x).1 h
    exact .mk ((pred5 x).2 hx) he (match_self hx he)
  · intro x ev h he
    have hx := (pred5 x).1 h
    exact .mk ((pred4 x).2 hx) he (match_self hx he)

/-- **The back-and-forth relation is strictly larger**: it relates the two
    arms, which the all-pairs relation relates under no relabelling. -/
theorem strict :
    ClosedRelabEqBF esA .empty Λ₀ P₄ a4 P₅ a5 ∧
    ∀ Λ, ¬ esA.ClosedRelabEq .empty Λ P₄ a4 P₅ a5 :=
  ⟨bf_arms, not_closedRelabEq_arms⟩

end RelabEqBF
