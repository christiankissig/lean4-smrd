import Smrd.Types
import Smrd.Forwardingcontext

/-!
# Preserved Program Order (Definition `def:ppo`)

`≼^P_δ ≜ remap_δ(≼_sync ∪ ≼_rmw ∪ ≼_alias) ∖ Δ_E`, relative to a predicate `P`
and a forwarding context `δ`, and the immediate-predecessor relation
`pred_δ(e, P)`. `≼_rmw` and `≼` are irreflexive by construction (`ppoRMW_irrefl`,
`ppo_irrefl`): the read of an RMW `≼_sync`-before its own write gives `(e_r, e_r)`
in `≼_rmw` before `Δ_E` is removed, and a read forwarded from a write
`≼_alias`-before it is remapped onto that write.

The predicate is semantic, so that the restricted predicates `⌈P⌉ᵢ` of
Appendix B.2 (`EpisodicLoops.Restriction`, in `lean4-episodic-loops`) can be passed for `P`. The lemmas at the end
record how `≼` depends on `P`: only through the satisfiability of alias
equations and the entailment of read-modify-write conditions.
-/

namespace EventStructure

variable (es : EventStructure)

/-- `≼_sync`, the statically declared memory order:

    `(⊑;Δ_{W_rel,sc} ∪ ⊑;Δ_{F_rel,sc};⊑_{∖R} ∪ Δ_{R_acq,sc};⊑ ∪ ⊑_{∖W};Δ_{F_acq,sc};⊑)_{∖F∪B}` -/
def ppoSync : Rel :=
  let po := es.poR
  let t₁ := po.comp (diag (es.cls Event.isRelW))
  let t₂ := (po.comp (diag (es.cls Event.isRelF))).comp (po.excl (es.cls Event.isRead))
  let t₃ := (diag (es.cls Event.isAcqR)).comp po
  let t₄ := ((po.excl (es.cls Event.isWrite)).comp (diag (es.cls Event.isAcqF))).comp po
  ((t₁.union t₂).union (t₃.union t₄)).excl
    (fun e => es.cls Event.isFence e ∨ es.cls Event.isBranch e)

/-- `{(e_w, e_r) | (e_r, c, e_w) ∈ ⊑ʳᵐʷ ∧ c ≡_P ⊤}` -/
def rmwPairs (P : Pred) : Rel := fun w r =>
  ∃ ent ∈ es.rmw, ent.w = w ∧ ent.r = r ∧ EquivUnder P ent.cond Expr.tt

/-- `≼_rmw ≜ (≼_sync ; rmwPairs ∪ rmwPairs ; ≼_sync) ∖ Δ_E` -/
def ppoRMW (P : Pred) : Rel :=
  ((es.ppoSync.comp (es.rmwPairs P)).union ((es.rmwPairs P).comp es.ppoSync)).offDiag

/-- The alias query `∃ f. ⟦P ∧ loc(e₁) = loc(e₂)⟧_f ≡ ⊤` for two events. -/
def mayAlias (P : Pred) (a b : EventId) : Prop :=
  ∃ e₁ e₂ l₁ l₂, es.ev a = some e₁ ∧ es.ev b = some e₂ ∧
    e₁.loc = some l₁ ∧ e₂.loc = some l₂ ∧ Sat (Pred.and P (Expr.eq l₁ l₂).holds)

/-- `≼_alias ≜ {(e₁, e₂) ∈ ⊑ | ∃ f. ⟦P ∧ loc(e₁) = loc(e₂)⟧_f ≡ ⊤}` -/
def ppoAlias (P : Pred) : Rel := fun a b => es.poR a b ∧ es.mayAlias P a b

/-- The union `≼_sync ∪ ≼_rmw ∪ ≼_alias` before remapping. -/
def ppoBase (P : Pred) : Rel :=
  (es.ppoSync.union (es.ppoRMW P)).union (es.ppoAlias P)

/-- `≼^P_δ ≜ remap_δ(≼_sync ∪ ≼_rmw ∪ ≼_alias) ∖ Δ_E` -/
def ppo (P : Pred) (δ : FwdCtx) : Rel := (δ.remapRel (es.ppoBase P)).offDiag

theorem ppoRMW_irrefl (P : Pred) (a : EventId) : ¬ es.ppoRMW P a a :=
  fun h => h.2 rfl

theorem ppo_irrefl (P : Pred) (δ : FwdCtx) (a : EventId) : ¬ es.ppo P δ a a :=
  fun h => h.2 rfl

/-- `pred_δ(e, P)`: the immediate `≼^P_δ`-predecessors of `e`,
    `{e' | e' ≼ e ∧ ¬∃ e''. e' ≼ e'' ≼ e}`. -/
def pred (δ : FwdCtx) (e : EventId) (P : Pred) : EvSet := fun e' =>
  es.ppo P δ e' e ∧ ¬ ∃ e'', es.ppo P δ e' e'' ∧ es.ppo P δ e'' e

/-- The form of `pred` before `≼` was made irreflexive, with the endpoints
    excluded explicitly, is equivalent to the paper's. -/
theorem pred_iff (δ : FwdCtx) (e : EventId) (P : Pred) (e' : EventId) :
    es.pred δ e P e' ↔ es.ppo P δ e' e ∧ e ≠ e' ∧
      ∀ e'', es.ppo P δ e' e'' → es.ppo P δ e'' e → e' = e'' ∨ e'' = e := by
  constructor
  · rintro ⟨h, hn⟩
    exact ⟨h, fun heq => h.2 heq.symm, fun e'' h₁ h₂ => absurd ⟨e'', h₁, h₂⟩ hn⟩
  · rintro ⟨h, -, hall⟩
    refine ⟨h, fun ⟨e'', h₁, h₂⟩ => ?_⟩
    rcases hall e'' h₁ h₂ with rfl | rfl
    · exact h₁.2 rfl
    · exact h₂.2 rfl

/-! ## Dependence on the predicate -/

/-! `≼_sync` takes no predicate, which is the first part of Claim
`restrict-ppo:other` of Lemma `l:restrict-ppo`. -/

/-- A weaker predicate admits more aliasing. -/
theorem ppoAlias_mono {P Q : Pred} (h : Entails P Q) :
    Rel.Subset (es.ppoAlias P) (es.ppoAlias Q) := by
  rintro a b ⟨hpo, e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, hP, heq⟩
  exact ⟨hpo, e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, h f hP, heq⟩

theorem rmwPairs_anti {P Q : Pred} (h : Entails P Q) :
    Rel.Subset (es.rmwPairs Q) (es.rmwPairs P) := by
  rintro w r ⟨ent, hmem, hw, hr, hc⟩
  exact ⟨ent, hmem, hw, hr, fun f hP => hc f (h f hP)⟩

/-- A weaker predicate entails fewer read-modify-write conditions. -/
theorem ppoRMW_anti {P Q : Pred} (h : Entails P Q) :
    Rel.Subset (es.ppoRMW Q) (es.ppoRMW P) := by
  rintro a c ⟨⟨b, hs, hr⟩ | ⟨b, hr, hs⟩, hne⟩
  · exact ⟨Or.inl ⟨b, hs, es.rmwPairs_anti h _ _ hr⟩, hne⟩
  · exact ⟨Or.inr ⟨b, es.rmwPairs_anti h _ _ hr, hs⟩, hne⟩

/-- `≼` depends on the predicate only through the alias queries and the
    entailment of read-modify-write conditions. -/
theorem ppoBase_congr {P Q : Pred}
    (halias : ∀ a b, es.mayAlias P a b ↔ es.mayAlias Q a b)
    (hrmw : ∀ ent ∈ es.rmw,
      EquivUnder P ent.cond Expr.tt ↔ EquivUnder Q ent.cond Expr.tt) :
    ∀ a b, es.ppoBase P a b ↔ es.ppoBase Q a b := by
  have hpairs : ∀ w r, es.rmwPairs P w r ↔ es.rmwPairs Q w r := by
    intro w r
    constructor
    · rintro ⟨ent, hm, hw, hr, hc⟩; exact ⟨ent, hm, hw, hr, (hrmw ent hm).1 hc⟩
    · rintro ⟨ent, hm, hw, hr, hc⟩; exact ⟨ent, hm, hw, hr, (hrmw ent hm).2 hc⟩
  intro a b
  simp only [ppoBase, ppoRMW, ppoAlias, Rel.union, Rel.comp, Rel.offDiag, hpairs, halias]

theorem ppo_congr {P Q : Pred} (δ : FwdCtx)
    (h : ∀ a b, es.ppoBase P a b ↔ es.ppoBase Q a b) :
    ∀ a b, es.ppo P δ a b ↔ es.ppo Q δ a b := by
  intro a b
  simp only [ppo, Rel.offDiag, FwdCtx.remapRel, h]

/-- `pred` depends on the predicate only through `≼`. -/
theorem pred_congr {P Q : Pred} (δ : FwdCtx) (e : EventId)
    (h : ∀ a b, es.ppo P δ a b ↔ es.ppo Q δ a b) :
    ∀ e', es.pred δ e P e' ↔ es.pred δ e Q e' := by
  intro e'
  simp only [pred, h]

end EventStructure
