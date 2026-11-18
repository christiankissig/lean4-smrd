import Smrd.RelabEqBF

/-!
# Same-location predecessors of writes Lifting merges

When back-and-forth closed relabel-equivalence (`ClosedRelabEqBF`) relates
two writes `w₁` and `w₂` that Lifting merges, does their same-location
context match? The intended property: the immediate `≼`-predecessors of
`w₁` that may alias it (`≼_alias`, `AliasPred`) correspond one to one, at
related locations, to those of `w₂` (`AliasOneToOne`), so that the merged
write has the same coherence and `po|loc` constraints whichever arm it came
from.

The argument for it: two immediate predecessors of `w₁` matched to the same
event on the other side have equal locations under the predicate, so
`≼_alias` orders them, and they are not both immediate. It assumes that two
`⊑`-predecessors of `w₁` are `⊑`-comparable. They need not be: after the
join of a parallel block both threads are `⊑`-before the code that follows,
and incomparable.

* `ClosedRelabEqBF.partnerR`, `ClosedRelabEqBF.partnerL` (**true**): each
  immediate predecessor with a location, on either side, has an immediate
  predecessor on the other side that it is closed relabel-equivalent to, at
  a relabel-equivalent location (`relabEqExpr`). The matching is total in
  both directions; it need not be one to one.
* `not_aliasOneToOne` (**the one-to-one form is false**), in
  `rc := c; if (rc = 1) { (x := 1 ∥ x := 1); x := 2 } else { x := 1; x := 2 }`:
  the two writes `x := 2` are related back and forth (`bf_46`), Lifting
  merges them (`gen_lift`), the `then` write has two immediate `≼_alias`
  predecessors, the two threads' `x := 1`, and the `else` write one
  (`aliasPred4`, `aliasPred6`). Both `then` predecessors are matched to the
  single `else` one (`two_to_one`).

The counterexample needs code after the join of a parallel block. Where the
immediate predecessors of `w₁` are `⊑`-comparable, the argument above
applies only when the witnesses of relabel equivalence are compared under
one predicate: `relabEqExpr` compares a location of `w₁`'s side with its
witness under `⟦P₁⟧_Λ` and the witness with the other side's location under
`P₂`, so two predecessors matched to one event have locations equal to two
witnesses, which agree under `P₂` but need not under `⟦P₁⟧_Λ`. The
one-to-one form for `⊑`-comparable predecessors is left open.
-/

namespace RelabEqAlias

open EventStructure PpoKit RelabEqRefl RelabEqBF

/-! ## The property -/

/-- `x` is an immediate `≼^P_δ`-predecessor of `w` that may alias it. -/
def AliasPred (es : EventStructure) (δ : FwdCtx) (P : Pred) (w x : EventId) : Prop :=
  es.pred δ w P x ∧ es.mayAlias P x w

/-- **One-to-one correspondence of the immediate alias predecessors**: a
    bijection `m` between the immediate predecessors of `w₁` that may alias
    it and those of `w₂`, relating closed relabel-equivalent events. -/
def AliasOneToOne (es : EventStructure) (δ : FwdCtx) (Λ : Relabelling) (P₁ : Expr) (w₁ : Event)
    (P₂ : Expr) (w₂ : Event) : Prop :=
  ∃ m : EventId → EventId,
    (∀ x, AliasPred es δ P₁.holds w₁.id x →
      AliasPred es δ P₂.holds w₂.id (m x) ∧
      ∃ a b, es.ev x = some a ∧ es.ev (m x) = some b ∧ es.ClosedRelabEqBF δ Λ P₁ a P₂ b) ∧
    (∀ x y, AliasPred es δ P₁.holds w₁.id x → AliasPred es δ P₁.holds w₁.id y → m x = m y →
      x = y) ∧
    (∀ z, AliasPred es δ P₂.holds w₂.id z → ∃ x, AliasPred es δ P₁.holds w₁.id x ∧ m x = z)

/-! ## The matching is total, at related locations -/

/-- Relabel-equivalent events with a location on one side have
    relabel-equivalent locations. -/
theorem relabEq_loc {es : EventStructure} {δ : FwdCtx} {Λ : Relabelling} {P₁ P₂ : Expr}
    {a b : Event} {l₁ : Expr} (h : es.relabEq δ Λ P₁ a P₂ b) (hl : a.loc = some l₁) :
    ∃ l₂, b.loc = some l₂ ∧ es.relabEqExpr δ Λ P₁ l₁ P₂ l₂ := by
  have hloc : ∀ (o₁ o₂ : Option Expr),
      (∃ x y, o₁ = some x ∧ o₂ = some y ∧ es.relabEqExpr δ Λ P₁ x P₂ y) → o₁ = some l₁ →
      ∃ l₂, o₂ = some l₂ ∧ es.relabEqExpr δ Λ P₁ l₁ P₂ l₂ := by
    rintro _ _ ⟨x, y, rfl, rfl, hr⟩ h
    cases h; exact ⟨y, rfl, hr⟩
  unfold relabEq at h
  simp only at h
  split at h
  · exact hloc _ _ h.1 hl
  · split at h
    · exact hloc _ _ h hl
    · split at h
      · rename_i hf
        have : a.isFence = true := by
          revert hf; cases a.isFence <;> simp
        exfalso
        unfold Event.isFence at this; unfold Event.loc at hl
        split at this <;> simp_all
      · exact h.elim

/-- **Each immediate predecessor of `e₁` with a location has a partner**: an
    immediate predecessor of `e₂` it is closed relabel-equivalent to, at a
    relabel-equivalent location. -/
theorem ClosedRelabEqBF.partnerR {es : EventStructure} {δ : FwdCtx} {Λ : Relabelling}
    {P₁ P₂ : Expr} {e₁ e₂ a : Event} {x₁ : EventId} {l₁ : Expr}
    (h : es.ClosedRelabEqBF δ Λ P₁ e₁ P₂ e₂) (hx : es.pred δ e₁.id P₁.holds x₁)
    (he : es.ev x₁ = some a) (hl : a.loc = some l₁) :
    ∃ x₂ b l₂, es.pred δ e₂.id P₂.holds x₂ ∧ es.ev x₂ = some b ∧ b.loc = some l₂ ∧
      es.relabEqExpr δ Λ P₁ l₁ P₂ l₂ ∧ es.ClosedRelabEqBF δ Λ P₁ a P₂ b := by
  cases h with
  | mk _ hR _ =>
    obtain ⟨x₂, b, h₂, he₂, hc⟩ := bfMatchR_iff.1 (hR x₁ a hx he)
    have hc' := hc
    cases hc' with
    | mk hr _ _ =>
      obtain ⟨l₂, hl₂, hrl⟩ := relabEq_loc hr hl
      exact ⟨x₂, b, l₂, h₂, he₂, hl₂, hrl, hc⟩

/-- **Each immediate predecessor of `e₂` with a location has a partner**:
    an immediate predecessor of `e₁` closed relabel-equivalent to it, at a
    relabel-equivalent location. -/
theorem ClosedRelabEqBF.partnerL {es : EventStructure} {δ : FwdCtx} {Λ : Relabelling}
    {P₁ P₂ : Expr} {e₁ e₂ b : Event} {x₂ : EventId} {l₂ : Expr}
    (h : es.ClosedRelabEqBF δ Λ P₁ e₁ P₂ e₂) (hx : es.pred δ e₂.id P₂.holds x₂)
    (he : es.ev x₂ = some b) (hl : b.loc = some l₂) :
    ∃ x₁ a l₁, es.pred δ e₁.id P₁.holds x₁ ∧ es.ev x₁ = some a ∧ a.loc = some l₁ ∧
      es.relabEqExpr δ Λ P₁ l₁ P₂ l₂ ∧ es.ClosedRelabEqBF δ Λ P₁ a P₂ b := by
  cases h with
  | mk _ _ hL =>
    obtain ⟨x₁, a, h₁, he₁, hc⟩ := bfMatchL_iff.1 (hL x₂ b hx he)
    have hc' := hc
    cases hc' with
    | mk hr _ _ =>
      -- the location of `a`: `relabEq` relates only events of one kind
      have : ∃ l₁, a.loc = some l₁ ∧ es.relabEqExpr δ Λ P₁ l₁ P₂ l₂ := by
        unfold relabEq at hr
        simp only at hr
        have hloc : ∀ (o₁ o₂ : Option Expr),
            (∃ x y, o₁ = some x ∧ o₂ = some y ∧ es.relabEqExpr δ Λ P₁ x P₂ y) → o₂ = some l₂ →
            ∃ l₁, o₁ = some l₁ ∧ es.relabEqExpr δ Λ P₁ l₁ P₂ l₂ := by
          rintro _ _ ⟨x, y, rfl, rfl, hr⟩ h
          cases h; exact ⟨x, rfl, hr⟩
        split at hr
        · exact hloc _ _ hr.1 hl
        · split at hr
          · exact hloc _ _ hr hl
          · split at hr
            · rename_i hf
              have : b.isFence = true := by
                revert hf; cases b.isFence <;> simp
              exfalso
              unfold Event.isFence at this; unfold Event.loc at hl
              split at this <;> simp_all
            · exact hr.elim
      obtain ⟨l₁, hl₁, hrl⟩ := this
      exact ⟨x₁, a, l₁, h₁, he₁, hl₁, hrl, hc⟩

/-! ## The one-to-one form fails after a join -/

/-- The branch condition `rc = 1`; `rc` is the symbol of the read of `c`. -/
def cond : Expr := .eq (.sym 0) (.val (.num 1))

def gT : Guard := ⟨1, cond, true⟩
def gF : Guard := ⟨1, cond, false⟩

/-- `rc := c; if (rc = 1) { (x := 1 ∥ x := 1); x := 2 } else { x := 1; x := 2 }` -/
def b0 : Event := PpoStability.R 0 0 [0] [] [] .rlx "c"
def b1 : Event := ⟨1, .branch cond, ⟨0, [1], []⟩, []⟩
def b2 : Event := PpoStability.W 2 1 [1, 0, 0] [] [gT] .rlx "x" 1
def b3 : Event := PpoStability.W 3 2 [1, 0, 1] [] [gT] .rlx "x" 1
def b4 : Event := PpoStability.W 4 0 [1, 0, 2] [] [gT] .rlx "x" 2
def b5 : Event := PpoStability.W 5 0 [1, 1, 0] [] [gF] .rlx "x" 1
def b6 : Event := PpoStability.W 6 0 [1, 1, 1] [] [gF] .rlx "x" 2

def esP : EventStructure :=
  ⟨[b0, b1, b2, b3, b4, b5, b6],
    [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6),
     (2, 4), (3, 4), (5, 6)], []⟩

theorem nodupP : (esP.events.map (·.id)).Nodup := by decide

theorem gP : GlobLocs esP := globLocs_of (by decide)

theorem evP {e : Event} (he : e ∈ esP.events) : esP.ev e.id = some e := PpoKit.ev_of_mem nodupP he

theorem ev2 : esP.ev 2 = some b2 := evP (e := b2) (by simp [esP])
theorem ev3 : esP.ev 3 = some b3 := evP (e := b3) (by simp [esP])
theorem ev4 : esP.ev 4 = some b4 := evP (e := b4) (by simp [esP])
theorem ev5 : esP.ev 5 = some b5 := evP (e := b5) (by simp [esP])
theorem ev6 : esP.ev 6 = some b6 := evP (e := b6) (by simp [esP])

/-- The `≼`-pairs, over-approximated: the writes of `x` along `⊑`. -/
theorem factP : ∀ p ∈ syncL esP ++ aliasL esP, p = (2, 4) ∨ p = (3, 4) ∨ p = (5, 6) := by
  decide

theorem memP {P : Pred} {a b : EventId} (h : esP.ppo P .empty a b) :
    (a, b) = (2, 4) ∨ (a, b) = (3, 4) ∨ (a, b) = (5, 6) :=
  factP _ (ppo_mem rfl gP noEdge_empty h)

/-- `x := 1 ≼ x := 2` along `⊑`, by location. -/
theorem ppo_x {P : Expr} {a b : EventId} {ea eb : Event} (hpo : esP.poR a b) (hab : a ≠ b)
    (hea : esP.ev a = some ea) (heb : esP.ev b = some eb)
    (hla : ea.loc = some (Expr.glob "x")) (hlb : eb.loc = some (Expr.glob "x"))
    (hs : Sat (Pred.and P.holds (Expr.eq (Expr.glob "x") (Expr.glob "x")).holds)) :
    esP.ppo P.holds .empty a b :=
  ⟨(FwdCtx.remapRel_of_noEdge noEdge_empty).2
    (.inr ⟨hpo, ea, eb, _, _, hea, heb, hla, hlb, hs⟩), hab⟩

/-- The predicates of the two arms. -/
def P₄ : Expr := b4.valres
def P₆ : Expr := b6.valres

theorem sat₄ : Sat (Pred.and P₄.holds (Expr.eq (Expr.glob "x") (Expr.glob "x")).holds) :=
  ⟨f₁, by unfold Expr.holds; decide, by unfold Expr.holds; decide⟩

theorem sat₆ : Sat (Pred.and P₆.holds (Expr.eq (Expr.glob "x") (Expr.glob "x")).holds) :=
  ⟨f₀, by unfold Expr.holds; decide, by unfold Expr.holds; decide⟩

theorem no_ppo_into {P : Pred} {a x : EventId} (ha : a ≠ 4 ∧ a ≠ 6) :
    ¬ esP.ppo P .empty x a := fun h => by
  rcases memP h with h | h | h <;> cases h <;> simp at ha

theorem no_pred_into {P : Pred} {a x : EventId} (ha : a ≠ 4 ∧ a ≠ 6) :
    ¬ esP.pred .empty a P x := fun h => no_ppo_into ha h.1

/-- The immediate predecessors of the `then` write are the two threads' writes. -/
theorem pred4 (x : EventId) : esP.pred .empty 4 P₄.holds x ↔ x = 2 ∨ x = 3 := by
  constructor
  · intro h
    rcases memP h.1 with h | h | h <;> cases h <;> simp
  · intro hx
    refine ⟨?_, fun ⟨c, h₁, h₂⟩ => ?_⟩
    · rcases hx with rfl | rfl
      · exact ppo_x (by show (2, 4) ∈ esP.po; decide) (by decide) ev2 ev4 rfl rfl sat₄
      · exact ppo_x (by show (3, 4) ∈ esP.po; decide) (by decide) ev3 ev4 rfl rfl sat₄
    · exact h₂.2 (by rcases memP h₁ with h | h | h <;> cases h <;> simp at hx ⊢)

/-- The immediate predecessor of the `else` write is the `else` arm's write. -/
theorem pred6 (x : EventId) : esP.pred .empty 6 P₆.holds x ↔ x = 5 := by
  constructor
  · intro h
    rcases memP h.1 with h | h | h <;> cases h <;> simp
  · rintro rfl
    refine ⟨ppo_x (by show (5, 6) ∈ esP.po; decide) (by decide) ev5 ev6 rfl rfl sat₆,
      fun ⟨c, h₁, h₂⟩ => ?_⟩
    exact h₂.2 (by rcases memP h₁ with h | h | h <;> cases h; rfl)

theorem mayAlias_x {P : Expr} {a b : EventId} {ea eb : Event}
    (hea : esP.ev a = some ea) (heb : esP.ev b = some eb)
    (hla : ea.loc = some (Expr.glob "x")) (hlb : eb.loc = some (Expr.glob "x"))
    (hs : Sat (Pred.and P.holds (Expr.eq (Expr.glob "x") (Expr.glob "x")).holds)) :
    esP.mayAlias P.holds a b :=
  ⟨ea, eb, _, _, hea, heb, hla, hlb, hs⟩

/-- **The `then` write has two immediate alias predecessors.** -/
theorem aliasPred4 (x : EventId) : AliasPred esP .empty P₄.holds 4 x ↔ x = 2 ∨ x = 3 := by
  refine ⟨fun h => (pred4 x).1 h.1, fun hx => ⟨(pred4 x).2 hx, ?_⟩⟩
  rcases hx with rfl | rfl
  · exact mayAlias_x ev2 ev4 rfl rfl sat₄
  · exact mayAlias_x ev3 ev4 rfl rfl sat₄

/-- **The `else` write has one.** -/
theorem aliasPred6 (x : EventId) : AliasPred esP .empty P₆.holds 6 x ↔ x = 5 :=
  ⟨fun h => (pred6 x).1 h.1, fun hx => ⟨(pred6 x).2 hx, by
    subst hx; exact mayAlias_x ev5 ev6 rfl rfl sat₆⟩⟩

theorem relabEq_W {P₁ P₂ : Expr} (i i' t t' : Nat) (pc pc' : List Nat) (gs gs' : List Guard)
    (n : Nat) :
    esP.relabEq .empty Λ₀ P₁ (PpoStability.W i t pc [] gs .rlx "x" n) P₂
      (PpoStability.W i' t' pc' [] gs' .rlx "x" n) := by
  simp only [relabEq, PpoStability.W, Event.isRead, Event.isWrite, Event.isAlloc, Event.loc,
    Event.val, Bool.and_self, Bool.or_true]
  exact ⟨⟨_, _, rfl, rfl, Expr.glob "x", fun _ _ _ h => h, fun _ _ _ h => h⟩,
    ⟨_, _, rfl, rfl, .val (.num n), fun _ _ _ h => h, fun _ _ _ h => h⟩⟩

/-- A thread's `x := 1` is related to the `else` arm's: neither has a
    predecessor. -/
theorem bf_leaf {a : Event} (ha : a = b2 ∨ a = b3) : esP.ClosedRelabEqBF .empty Λ₀ P₄ a P₆ b5 := by
  have hid : a.id ≠ 4 ∧ a.id ≠ 6 := by rcases ha with rfl | rfl <;> decide
  refine .mk ?_ (fun _ _ h _ => (no_pred_into hid h).elim)
    (fun _ _ h _ => (no_pred_into (a := 5) (by decide) h).elim)
  rcases ha with rfl | rfl
  · exact relabEq_W 2 5 1 0 _ _ _ _ 1
  · exact relabEq_W 3 5 2 0 _ _ _ _ 1

/-- **The two writes `x := 2` are related back and forth.** -/
theorem bf_46 : esP.ClosedRelabEqBF .empty Λ₀ P₄ b4 P₆ b6 := by
  refine .mk (relabEq_W 4 6 0 0 _ _ _ _ 2) ?_ ?_
  · intro x ev h he
    have hx := (pred4 x).1 h
    refine .mk ((pred6 5).2 rfl) ev5 (bf_leaf ?_)
    rcases hx with rfl | rfl
    · rw [ev2] at he; cases he; exact .inl rfl
    · rw [ev3] at he; cases he; exact .inr rfl
  · intro x ev h he
    have hx := (pred6 x).1 h; subst hx
    rw [ev5] at he; cases he
    exact .mk ((pred4 2).2 (.inl rfl)) ev2 (bf_leaf (.inl rfl))

/-- **Both immediate alias predecessors of the `then` write are matched to the
    single one of the `else` write.** -/
theorem two_to_one :
    AliasPred esP .empty P₄.holds 4 2 ∧ AliasPred esP .empty P₄.holds 4 3 ∧
    esP.ClosedRelabEqBF .empty Λ₀ P₄ b2 P₆ b5 ∧ esP.ClosedRelabEqBF .empty Λ₀ P₄ b3 P₆ b5 ∧
    ∀ x, AliasPred esP .empty P₆.holds 6 x ↔ x = 5 :=
  ⟨(aliasPred4 2).2 (.inl rfl), (aliasPred4 3).2 (.inr rfl), bf_leaf (.inl rfl),
    bf_leaf (.inr rfl), aliasPred6⟩

/-- **The immediate alias predecessors do not correspond one to one**, under
    any relabelling. -/
theorem not_aliasOneToOne (Λ : Relabelling) : ¬ AliasOneToOne esP .empty Λ P₄ b4 P₆ b6 := by
  rintro ⟨m, hm, hinj, -⟩
  have h2 := (aliasPred6 (m 2)).1 (hm 2 ((aliasPred4 2).2 (.inl rfl))).1
  have h3 := (aliasPred6 (m 3)).1 (hm 3 ((aliasPred4 3).2 (.inr rfl))).1
  have := hinj 2 3 ((aliasPred4 2).2 (.inl rfl)) ((aliasPred4 3).2 (.inr rfl)) (h2.trans h3.symm)
  cases this

/-! ### Lifting merges the two writes -/

def j₄ : Justification := ⟨b4.valres, [], .empty, b4⟩
def j₆ : Justification := ⟨b6.valres, [], .empty, b6⟩
/-- `(⊤ ∧ (rc = 1 ∨ ¬ rc = 1), ∅) ⊢ x := 2` in the `else` arm. -/
def jL : Justification := { j₆ with P := Expr.liftPred (j₄.P.rename Λ₀) j₆.P }

theorem pre₄ : esP.Generated (fun _ => True) j₄ :=
  .pre (w := b4) (by simp [esP]) rfl ⟨f₁, by unfold Expr.holds; decide⟩

theorem pre₆ : esP.Generated (fun _ => True) j₆ :=
  .pre (w := b6) (by simp [esP]) rfl ⟨f₀, by unfold Expr.holds; decide⟩

theorem lift_conds : esP.LiftConds (fun _ => True) Λ₀ j₄ j₆ := by
  refine ⟨rfl, ?_, bf_46, ?_, ?_, ?_, ?_, ?_, ?_, ⟨f₀, ?_, trivial⟩⟩
  · intro a b c ha; simp [Λ₀] at ha
  · intro e; show e ∈ ([] : List EventId) ↔ ∃ α ∈ ([] : List EventId), Λ₀.app α = e; simp
  · intro α h; nomatch h
  · intro h; have := cls_clsB.1 h; revert this; decide
  · intro h; have := cls_clsB.1 h; revert this; decide
  · intro α h; nomatch h
  · intro α h
    have key : ∀ α ∈ (j₄.P.rename Λ₀).syms, (α, 6) ∈ esP.po := by decide
    exact key α h
  · unfold Expr.holds; decide

theorem liftBranch : esP.LiftBranch Λ₀ j₄.w.id j₆.w.id :=
  ⟨gT, gF, ⟨b4, ev4, by decide⟩, ⟨b6, ev6, by decide⟩, rfl, rfl, by decide,
    fun _ _ h => by simp [Λ₀] at h⟩

theorem injOn : Λ₀.InjOn (j₄.P.syms ++ j₄.D) := by unfold Relabelling.InjOn; decide

/-- **Lifting merges the two writes `x := 2`**, whose immediate alias
    predecessors do not correspond one to one (`not_aliasOneToOne`). -/
theorem gen_lift : esP.Generated (fun _ => True) jL :=
  .lift' pre₄ pre₆ lift_conds liftBranch injOn

end RelabEqAlias
