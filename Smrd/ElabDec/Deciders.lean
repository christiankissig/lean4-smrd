import Smrd.ElabDec.Remap

/-!
# Deciding the side conditions of the elaborations

Relative to an `Oracle` for bounded arithmetic, the side conditions of the
elaborations are decided on finite event structures:

* `≼_sync` by bounded search over the events of `⊑` and `⊑ʳᵐʷ`
  (`ppoSync_iff`), the alias queries and RMW conditions of `≼` by the oracle
  (`ppoBaseB_iff`), `≼^P_δ` with `remap_δ` computed (`ppoB_iff`), and
  `pred_δ` by searching the finitely many events `≼` can relate (`predB_iff`);
* the part of Forwarding and Write Elision that depends on the justification,
  `fwdBase` (`fwdBaseB_iff`); the rest of `fwdRel`/`weRel` depends on the two
  events alone and is supplied by a `RelSplit`, so that the development does
  not depend on how those restrictions are spelled (`relSplit`, for the
  restrictions of this library);
* closed relabel-equivalence with the second premise's expressions as
  witnesses (`ClosedRelabEqC`, the restriction of `def:rel-eq` that `GenR`'s
  Lifting uses) as a least fixed point over pairs of events, computed by
  Kleene iteration (`crB_iff`).

The conditions on the structure are bundled as `Bounded es Qs M` (Conditions
C1 and C3 of `Smrd.ElabDec`, and C2's `Qs` bounded).

## Relabel equivalence on expressions

`relabEqExpr` asks for a witness `x` that agrees with `⟦x₁⟧_Λ` under
`ψ_δ ∧ ⟦P₁⟧_Λ` and with `x₂` under `ψ_δ ∧ P₂`, denoting a value wherever
they do. It is not trivial (`relabEqExpr_not_trivial`). Read through
`def:sem-equiv` alone, as it once was here and in the paper, it held of any
two expressions, since an ill-typed witness such as `⊤ + ⊤` denotes no value.

Whether some witness exists is not decided here: it may combine `⟦x₁⟧_Λ` and
`x₂` by cases on the premises, as far as the syntax of expressions allows.
`GenR` restricts Lifting to the witness `x₂` (`relabEqExprC`), which the
oracle decides (`relabExprB_iff`), and so the closure decided by
`Smrd.ElabDec.Saturate` is that restriction.
-/

open Expr Smrd.ElabDec

namespace EventStructure

variable (es : EventStructure)

instance decCls (p : Event → Bool) (id : EventId) : Decidable (es.cls p id) :=
  decidable_of_iff ((es.ev id).any p = true) (by unfold cls; cases es.ev id <;> simp)

instance decPoR (a b : EventId) : Decidable (es.poR a b) :=
  inferInstanceAs (Decidable ((a, b) ∈ es.po))

/-- The events `⊑` and `⊑ʳᵐʷ` mention. -/
def dom : List EventId :=
  es.po.map Prod.fst ++ es.po.map Prod.snd ++ es.rmw.map RMWEntry.r ++ es.rmw.map RMWEntry.w

variable {es}

theorem poR_dom {a b : EventId} (h : es.poR a b) : a ∈ es.dom ∧ b ∈ es.dom := by
  constructor <;> simp only [dom, List.mem_append, List.mem_map]
  · exact Or.inl (Or.inl (Or.inl ⟨(a, b), h, rfl⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨(a, b), h, rfl⟩))

variable (es)

/-- `≼_sync` with its intermediate events bounded. -/
def syncP (a b : EventId) : Prop :=
  ((es.poR a b ∧ es.cls Event.isRelW b) ∨
    (∃ c ∈ es.dom, es.poR a c ∧ es.cls Event.isRelF c ∧ es.poR c b ∧ ¬ es.cls Event.isRead c ∧
      ¬ es.cls Event.isRead b) ∨
    (es.cls Event.isAcqR a ∧ es.poR a b) ∨
    (∃ c ∈ es.dom, es.poR a c ∧ ¬ es.cls Event.isWrite a ∧ ¬ es.cls Event.isWrite c ∧
      es.cls Event.isAcqF c ∧ es.poR c b)) ∧
  ¬ (es.cls Event.isFence a ∨ es.cls Event.isBranch a) ∧
  ¬ (es.cls Event.isFence b ∨ es.cls Event.isBranch b)

instance (a b : EventId) : Decidable (es.syncP a b) := by unfold syncP; infer_instance

variable {es}

theorem ppoSync_iff {a b : EventId} : es.ppoSync a b ↔ es.syncP a b := by
  simp only [ppoSync, Rel.excl, Rel.union, Rel.comp, diag, syncP]
  constructor
  · rintro ⟨h, hna, hnb⟩
    refine ⟨?_, hna, hnb⟩
    rcases h with (⟨m, hpo, rfl, hr⟩ | ⟨m, ⟨c, hpo, rfl, hf⟩, hpo2, hnr, hnr2⟩) |
        (⟨m, ⟨rfl, hq⟩, hpo⟩ | ⟨m, ⟨c, ⟨hpo, hn1, hn2⟩, rfl, hq⟩, hpo2⟩)
    · exact Or.inl ⟨hpo, hr⟩
    · exact Or.inr (Or.inl ⟨c, (poR_dom hpo).2, hpo, hf, hpo2, hnr, hnr2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hq, hpo⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨c, (poR_dom hpo).2, hpo, hn1, hn2, hq, hpo2⟩))
  · rintro ⟨h, hna, hnb⟩
    refine ⟨?_, hna, hnb⟩
    rcases h with ⟨hpo, hr⟩ | ⟨c, -, hpo, hf, hpo2, hnr, hnr2⟩ | ⟨hq, hpo⟩ |
        ⟨c, -, hpo, hn1, hn2, hq, hpo2⟩
    · exact Or.inl (Or.inl ⟨b, hpo, rfl, hr⟩)
    · exact Or.inl (Or.inr ⟨c, ⟨c, hpo, rfl, hf⟩, hpo2, hnr, hnr2⟩)
    · exact Or.inr (Or.inl ⟨a, ⟨rfl, hq⟩, hpo⟩)
    · exact Or.inr (Or.inr ⟨c, ⟨c, ⟨hpo, hn1, hn2⟩, rfl, hq⟩, hpo2⟩)

theorem syncP_dom {a b : EventId} (h : es.syncP a b) : a ∈ es.dom ∧ b ∈ es.dom := by
  obtain ⟨h, -, -⟩ := h
  rcases h with ⟨hpo, -⟩ | ⟨c, -, hpo, -, hpo2, -⟩ | ⟨-, hpo⟩ | ⟨c, -, hpo, -, -, -, hpo2⟩
  · exact poR_dom hpo
  · exact ⟨(poR_dom hpo).1, (poR_dom hpo2).2⟩
  · exact poR_dom hpo
  · exact ⟨(poR_dom hpo).1, (poR_dom hpo2).2⟩

theorem rmwPairs_dom {P : Pred} {w r : EventId} (h : es.rmwPairs P w r) :
    w ∈ es.dom ∧ r ∈ es.dom := by
  obtain ⟨ent, hm, rfl, rfl, -⟩ := h
  constructor <;> simp only [dom, List.mem_append, List.mem_map]
  · exact Or.inr ⟨ent, hm, rfl⟩
  · exact Or.inl (Or.inr ⟨ent, hm, rfl⟩)

theorem ppoBase_dom {P : Pred} {a b : EventId} (h : es.ppoBase P a b) : a ∈ es.dom ∧ b ∈ es.dom := by
  rcases h with (h | ⟨⟨c, h1, h2⟩ | ⟨c, h1, h2⟩, -⟩) | ⟨hpo, -⟩
  · exact syncP_dom (ppoSync_iff.1 h)
  · exact ⟨(syncP_dom (ppoSync_iff.1 h1)).1, (rmwPairs_dom h2).2⟩
  · exact ⟨(rmwPairs_dom h1).1, (syncP_dom (ppoSync_iff.1 h2)).2⟩
  · exact poR_dom hpo

/-! ## The conditions on the structure -/

variable (es)

/-- Conditions C1 and C3, with the Strengthening predicates `Qs` bounded:
    locations, values (written values and allocation sizes) are terms;
    guards and RMW conditions bounded predicates; the numerals that multiply or
    divide come from `M`, and no relaxed write writes one of them, so that
    store-store forwarding keeps predicates in the fragment. -/
structure Bounded (Qs : List Expr) (M : List Nat) : Prop where
  locs : ∀ e ∈ es.events, ∀ l, e.loc = some l → isTerm M l = true
  vals : ∀ e ∈ es.events, ∀ v, e.val = some v → isTerm M v = true
  guards : ∀ e ∈ es.events, ∀ g ∈ e.guards, isBPred M g.cond = true
  rmw : ∀ ent ∈ es.rmw, isBPred M ent.cond = true
  qs : ∀ Q ∈ Qs, isBPred M Q = true
  numFwd : ∀ e ∈ es.events, e.isRlxW = true → ∀ c ∈ M, e.val ≠ some (.val (.num c))

variable {es}

variable (es) in
/-- `Bounded`, checked. -/
def boundedB (Qs : List Expr) (M : List Nat) : Bool :=
  es.events.all (fun e => e.loc.all (isTerm M) && e.val.all (isTerm M) &&
    e.guards.all (fun g => isBPred M g.cond) &&
    (!e.isRlxW || M.all (fun c => e.val != some (.val (.num c))))) &&
  es.rmw.all (fun ent => isBPred M ent.cond) && Qs.all (isBPred M)

theorem boundedB_sound {Qs : List Expr} {M : List Nat} (h : es.boundedB Qs M = true) :
    es.Bounded Qs M := by
  simp only [boundedB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨he, hr⟩, hq⟩ := h
  refine ⟨fun e hm l hl => ?_, fun e hm v hv => ?_, fun e hm g hg => (he e hm).1.2 g hg,
    hr, hq, fun e hm hw c hc => ?_⟩
  · have := (he e hm).1.1.1; rw [hl] at this; simpa using this
  · have := (he e hm).1.1.2; rw [hv] at this; simpa using this
  · rcases (he e hm).2 with h | h
    · rw [hw] at h; cases h
    · exact h c hc

theorem Bounded.valsAtomic {Qs : List Expr} {M : List Nat} (h : es.Bounded Qs M) : es.ValsAtomic :=
  fun e he v hv => isTerm_not_conn (h.vals e he v hv)

theorem Bounded.valres {Qs : List Expr} {M : List Nat} (h : es.Bounded Qs M) {e : Event}
    (he : e ∈ es.events) : isBPred M e.valres = true := by
  apply isBPred_conj
  intro g hg
  obtain ⟨gd, hgd, rfl⟩ := List.mem_map.1 hg
  unfold Guard.expr; split
  · exact h.guards e he gd hgd
  · simp only [isBPred]; exact h.guards e he gd hgd

theorem Bounded.valresOf {Qs : List Expr} {M : List Nat} (h : es.Bounded Qs M) (e : EventId) :
    isBPred M (es.valresOf e) = true := by
  unfold EventStructure.valresOf
  cases hev : es.ev e with
  | none => rfl
  | some ev => exact h.valres (mem_events_of_ev hev)

theorem isBPred_of_conjuncts {M : List Nat} :
    ∀ (P : Expr), (∀ c ∈ P.conjuncts, isBPred M c = true) → isBPred M P = true
  | .and a b, h => by
      simp only [conjuncts, List.mem_append] at h
      simp only [isBPred, Bool.and_eq_true]
      exact ⟨isBPred_of_conjuncts a (fun c hc => h c (Or.inl hc)),
        isBPred_of_conjuncts b (fun c hc => h c (Or.inr hc))⟩
  | .not _, h | .or _ _, h | .val _, h | .sym _, h | .bin _ _ _, h | .eq _ _, h | .le _ _, h =>
      h _ (List.mem_singleton_self _)

/-- The value Forwarding replaces is no numeral of `M` (Condition C3). -/
theorem fwd_val_not_num {Qs : List Expr} {M : List Nat} (hb : es.Bounded Qs M) {j : Justification}
    {e₁ e₂ : EventId} {ev₂ : Event} {v₂ : Expr}
    (hf : es.fwdRel j e₁ e₂) (h₂ : es.ev e₂ = some ev₂) (hv₂ : ev₂.val = some v₂) :
    ∀ c ∈ M, v₂ ≠ .val (.num c) := by
  have m₂ := mem_events_of_ev h₂
  intro c hc heq
  subst heq
  -- the forwarded event writes a numeral: it is a relaxed write, excluded by C3
  have hcls := hf.1.2
  have hrd : ¬ ev₂.isRead = true := fun hr => by
    unfold Event.isRead at hr; unfold Event.val at hv₂
    split at hr <;> simp_all
  have hcl : ∀ p : Event → Bool, es.cls p e₂ → p ev₂ = true := fun p ⟨e, he, hp⟩ => by
    rw [h₂] at he; cases he; exact hp
  rcases hcls with ⟨-, hr⟩ | ⟨-, hw⟩ | ⟨-, hr⟩
  · exact hrd (by have := hcl _ hr; unfold Event.isRlxR at this; unfold Event.isRead
                  split at this <;> simp_all)
  · exact hb.numFwd ev₂ m₂ (hcl _ hw) c hc hv₂
  · exact hrd (hcl _ hr)

/-- Forwarding keeps a predicate bounded (Conditions C1 and C3). -/
theorem isBPred_fwd_replace {Qs : List Expr} {M : List Nat} (hb : es.Bounded Qs M) {j : Justification}
    (hP : isBPred M j.P = true) {e₁ e₂ : EventId} {ev₁ ev₂ : Event} {v₁ v₂ : Expr}
    (hf : es.fwdRel j e₁ e₂) (h₁ : es.ev e₁ = some ev₁) (h₂ : es.ev e₂ = some ev₂)
    (hv₁ : ev₁.val = some v₁) (hv₂ : ev₂.val = some v₂) : isBPred M (j.P.replace v₂ v₁) = true :=
  isBPred_replace (hb.vals ev₂ (mem_events_of_ev h₂) v₂ hv₂)
    (hb.vals ev₁ (mem_events_of_ev h₁) v₁ hv₁) (fwd_val_not_num hb hf h₂ hv₂) _ hP

theorem isBPred_strPred {Qs : List Expr} {M : List Nat} (hb : es.Bounded Qs M) {P Q : Expr}
    (hP : isBPred M P = true) (hQ : Q ∈ Qs) (S : List EventId) :
    isBPred M (es.strPred P Q S) = true := by
  simp only [strPred, isBPred, Bool.and_eq_true]
  exact ⟨hP, hb.qs Q hQ, isBPred_conj (fun e he => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 he; exact hb.valresOf x)⟩

/-- Every predicate of the closure is a bounded predicate. -/
theorem GenR.bpred {Ω : Pred} {Qs : List Expr} {wk : Bool} {M : List Nat} (hb : es.Bounded Qs M)
    {j : Justification} (h : es.GenR Ω Qs wk j) : isBPred M j.P = true := by
  induction h with
  | pre hw hj _ => rw [(preJust_D hj).2.2.1]; exact hb.valres hw
  | va _ _ _ _ ih => exact ih
  | str Q S hQ _ _ _ _ _ ih => exact isBPred_strPred hb ih hQ S
  | fwd _ _ hf h₁ h₂ hv₁ hv₂ _ _ ih => exact isBPred_fwd_replace hb ih hf h₁ h₂ hv₁ hv₂
  | we _ _ _ _ ih => exact ih
  | lift Λ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
      exact isBPred_liftPred (by rw [isBPred_rename]; exact ih₁) ih₂
  | weak _ _ hc _ _ ih =>
      apply isBPred_of_conjuncts
      intro c hc'
      exact isBPred_conjuncts _ ih c ((hc c).2 (by simp [conjuncts, hc']))

/-- The location and value of an event are terms of bounded arithmetic. -/
def TermEv (M : List Nat) (e : Event) : Prop :=
  (∀ l, e.loc = some l → isTerm M l = true) ∧ (∀ v, e.val = some v → isTerm M v = true)

theorem Bounded.termEv {Qs : List Expr} {M : List Nat} (hb : es.Bounded Qs M) {e : Event}
    (he : e ∈ es.events) : TermEv M e :=
  ⟨hb.locs e he, hb.vals e he⟩

/-- The justified write of the closure has a term as location and value. -/
theorem GenR.wterm {Ω : Pred} {Qs : List Expr} {wk : Bool} {M : List Nat} (hb : es.Bounded Qs M)
    {j : Justification} (h : es.GenR Ω Qs wk j) : TermEv M j.w := by
  induction h with
  | @pre w j hw hj _ => rw [(preJust_D hj).1]; exact hb.termEv hw
  | @va j₁ o x e b α v _ hk _ _ ih =>
      have hx := ih.1 x (by simp [Event.loc, hk])
      have he := ih.2 e (by simp [Event.val, hk])
      refine ⟨fun l hl => ?_, fun u hu => ?_⟩
      · simp only [Event.loc, Option.some.injEq] at hl; rw [← hl]; exact isTerm_subst_val α v x hx
      · simp only [Event.val, Option.some.injEq] at hu; rw [← hu]; exact isTerm_subst_val α v e he
  | str _ _ _ _ _ _ _ _ ih => exact ih
  | @fwd j₁ o x e b e₁ e₂ ev₁ ev₂ v₁ v₂ _ hk hf h₁ h₂ hv₁ hv₂ _ _ ih =>
      have hx := ih.1 x (by simp [Event.loc, hk])
      have he := ih.2 e (by simp [Event.val, hk])
      have hq := hb.vals ev₁ (mem_events_of_ev h₁) v₁ hv₁
      have hn := fwd_val_not_num hb hf h₂ hv₂
      refine ⟨fun l hl => ?_, fun u hu => ?_⟩
      · simp only [Event.loc, Option.some.injEq] at hl; rw [← hl]; exact isTerm_replace hq hn x hx
      · simp only [Event.val, Option.some.injEq] at hu; rw [← hu]; exact isTerm_replace hq hn e he
  | we _ _ _ _ ih => exact ih
  | lift _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₂ => exact ih₂
  | weak _ _ _ _ _ ih => exact ih

/-! ## `≼` and `pred` -/

variable (es) (O : Oracle)

def mayAliasB (P : Expr) (a b : EventId) : Bool :=
  match es.ev a, es.ev b with
  | some e₁, some e₂ =>
      match e₁.loc, e₂.loc with
      | some l₁, some l₂ => O.satAnd P (.eq l₁ l₂)
      | _, _ => false
  | _, _ => false

def rmwPairsB (P : Expr) (w r : EventId) : Bool :=
  es.rmw.any fun ent => ent.w == w && ent.r == r && O.equivB P ent.cond Expr.tt

def syncB (a b : EventId) : Bool := decide (es.syncP a b)

def ppoBaseB (P : Expr) (a b : EventId) : Bool :=
  es.syncB a b ||
    (a != b && ((es.dom.any fun c => es.syncB a c && es.rmwPairsB O P c b) ||
      (es.dom.any fun c => es.rmwPairsB O P a c && es.syncB c b))) ||
    (decide (es.poR a b) && es.mayAliasB O P a b)

/-- `≼^P_δ`, computed. -/
def ppoB (P : Expr) (δ : FwdCtx) (a b : EventId) : Bool :=
  a != b && es.dom.any fun a₀ => es.dom.any fun b₀ =>
    es.ppoBaseB O P a₀ b₀ && δ.remapB a₀ == a && δ.remapB b₀ == b

/-- The events `≼^P_δ` can relate. -/
def candL (δ : FwdCtx) : List EventId := es.dom ++ δ.edges.map Prod.fst

/-- `pred_δ(e, P)`, computed. -/
def predB (P : Expr) (δ : FwdCtx) (e e' : EventId) : Bool :=
  es.ppoB O P δ e' e && !((es.candL δ).any fun e'' => es.ppoB O P δ e' e'' && es.ppoB O P δ e'' e)

def predL (P : Expr) (δ : FwdCtx) (e : EventId) : List EventId :=
  (es.candL δ).filter (es.predB O P δ e)

/-- The part of Forwarding's and Write Elision's conditions that depends on the
    justification, computed. -/
def fwdBaseB (j : Justification) (e₁ e₂ : EventId) : Bool :=
  es.predB O j.P j.δ e₂ e₁ && decide (es.poR e₁ e₂) &&
    match es.ev e₁, es.ev e₂ with
    | some ev₁, some ev₂ =>
        match ev₁.loc, ev₂.loc with
        | some l₁, some l₂ => O.equivB (.and j.P (es.psiE j.δ)) l₁ l₂
        | _, _ => false
    | _, _ => false

variable {es O}

theorem isBPred_eq_bpred {M : List Nat} {a b : Expr} (ha : isBPred M a = true)
    (hb : isBPred M b = true) : isBPred M (.eq a b) = true := by simp [isBPred, ha, hb]

theorem isBPred_eq_term {M : List Nat} {a b : Expr} (ha : isTerm M a = true)
    (hb : isTerm M b = true) : isBPred M (.eq a b) = true := by simp [isBPred, ha, hb]

theorem isBPred_tt {M : List Nat} : isBPred M Expr.tt = true := rfl

section spec

variable {Qs : List Expr} {M : List Nat} (hb : es.Bounded Qs M) {P : Expr}
  (hP : isBPred M P = true)
include hb hP

theorem mayAliasB_iff {a b : EventId} : es.mayAliasB O P a b = true ↔ es.mayAlias P.holds a b := by
  unfold mayAliasB mayAlias
  constructor
  · intro h
    split at h
    · rename_i e₁ e₂ h₁ h₂
      split at h
      · rename_i l₁ l₂ hl₁ hl₂
        exact ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, (O.satAnd_iff hP (isBPred_eq_term
          (hb.locs e₁ (mem_events_of_ev h₁) l₁ hl₁) (hb.locs e₂ (mem_events_of_ev h₂) l₂ hl₂))).1 h⟩
      · cases h
    · cases h
  · rintro ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, hs⟩
    simp only [h₁, h₂, hl₁, hl₂]
    exact (O.satAnd_iff hP (isBPred_eq_term
      (hb.locs e₁ (mem_events_of_ev h₁) l₁ hl₁) (hb.locs e₂ (mem_events_of_ev h₂) l₂ hl₂))).2 hs

theorem rmwPairsB_iff {w r : EventId} : es.rmwPairsB O P w r = true ↔ es.rmwPairs P.holds w r := by
  unfold rmwPairsB rmwPairs
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨ent, hm, ⟨hw, hr⟩, he⟩
    exact ⟨ent, hm, hw, hr, (O.equivB_iff hP (isBPred_eq_bpred (hb.rmw ent hm) isBPred_tt)).1 he⟩
  · rintro ⟨ent, hm, hw, hr, he⟩
    exact ⟨ent, hm, ⟨hw, hr⟩, (O.equivB_iff hP (isBPred_eq_bpred (hb.rmw ent hm) isBPred_tt)).2 he⟩

theorem ppoBaseB_iff {a b : EventId} : es.ppoBaseB O P a b = true ↔ es.ppoBase P.holds a b := by
  unfold ppoBaseB ppoBase ppoRMW ppoAlias
  simp only [syncB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    bne_iff_ne, ne_eq, Rel.union, Rel.comp, Rel.offDiag, rmwPairsB_iff hb hP, mayAliasB_iff hb hP,
    ← ppoSync_iff]
  constructor
  · rintro ((h | ⟨hne, ⟨c, -, h1, h2⟩ | ⟨c, -, h1, h2⟩⟩) | ⟨h1, h2⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨Or.inl ⟨c, h1, h2⟩, hne⟩)
    · exact Or.inl (Or.inr ⟨Or.inr ⟨c, h1, h2⟩, hne⟩)
    · exact Or.inr ⟨h1, h2⟩
  · rintro ((h | ⟨⟨c, h1, h2⟩ | ⟨c, h1, h2⟩, hne⟩) | ⟨h1, h2⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨hne, Or.inl ⟨c, (syncP_dom (ppoSync_iff.1 h1)).2, h1, h2⟩⟩)
    · exact Or.inl (Or.inr ⟨hne, Or.inr ⟨c, (rmwPairs_dom h1).2, h1, h2⟩⟩)
    · exact Or.inr ⟨h1, h2⟩

theorem ppoB_iff {δ : FwdCtx} (hwf : δ.WF) {a b : EventId} :
    es.ppoB O P δ a b = true ↔ es.ppo P.holds δ a b := by
  unfold ppoB ppo
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, beq_iff_eq,
    ppoBaseB_iff hb hP, Rel.offDiag, FwdCtx.remapRel, FwdCtx.remap_iff hwf]
  constructor
  · rintro ⟨hne, a₀, -, b₀, -, ⟨h, ha⟩, hb'⟩; exact ⟨⟨a₀, b₀, h, ha, hb'⟩, hne⟩
  · rintro ⟨⟨a₀, b₀, h, ha, hb'⟩, hne⟩
    exact ⟨hne, a₀, (ppoBase_dom h).1, b₀, (ppoBase_dom h).2, ⟨h, ha⟩, hb'⟩

end spec

theorem ppo_cand {P : Pred} {δ : FwdCtx} {a b : EventId} (h : es.ppo P δ a b) :
    a ∈ es.candL δ ∧ b ∈ es.candL δ := by
  obtain ⟨⟨a₀, b₀, hbase, ha, hb⟩, -⟩ := h
  have hd := ppoBase_dom hbase
  constructor
  · rcases ha.cases with rfl | h
    · exact List.mem_append_left _ hd.1
    · exact List.mem_append_right _ h
  · rcases hb.cases with rfl | h
    · exact List.mem_append_left _ hd.2
    · exact List.mem_append_right _ h

section spec2

variable {Qs : List Expr} {M : List Nat} (hb : es.Bounded Qs M) {P : Expr}
  (hP : isBPred M P = true) {δ : FwdCtx} (hwf : δ.WF)
include hb hP hwf

theorem predB_iff {e e' : EventId} : es.predB O P δ e e' = true ↔ es.pred δ e P.holds e' := by
  unfold predB pred
  rw [Bool.and_eq_true, ppoB_iff hb hP hwf, Bool.not_eq_true', List.any_eq_false]
  apply and_congr_right'
  constructor
  · rintro hn ⟨e'', h1, h2⟩
    have := hn e'' (ppo_cand h1).2
    rw [(ppoB_iff hb hP hwf).2 h1, (ppoB_iff hb hP hwf).2 h2] at this
    exact this rfl
  · intro hn e'' _ h
    rw [Bool.and_eq_true, ppoB_iff hb hP hwf, ppoB_iff hb hP hwf] at h
    exact hn ⟨e'', h⟩

theorem mem_predL {e x : EventId} : x ∈ es.predL O P δ e ↔ es.pred δ e P.holds x := by
  unfold predL
  rw [List.mem_filter, predB_iff hb hP hwf]
  exact ⟨fun h => h.2, fun h => ⟨(ppo_cand h.1).1, h⟩⟩

end spec2

theorem pred_and_psi (j : Justification) :
    Pred.and j.P.holds (j.δ.psi es) = (Expr.and j.P (es.psiE j.δ)).holds := by
  funext f; apply propext
  rw [holds_and, Pred.and, psi_iff]

theorem fwdBaseB_iff {Qs : List Expr} {M : List Nat} (hb : es.Bounded Qs M) {j : Justification}
    (hP : isBPred M j.P = true) (hwf : j.δ.WF) {e₁ e₂ : EventId} :
    es.fwdBaseB O j e₁ e₂ = true ↔ es.fwdBase j e₁ e₂ := by
  unfold fwdBaseB fwdBase
  simp only [Bool.and_eq_true, decide_eq_true_eq, predB_iff hb hP hwf, pred_and_psi]
  rw [and_assoc]
  apply and_congr_right'
  apply and_congr_right'
  have hq : ∀ ev₁ ev₂ l₁ l₂, es.ev e₁ = some ev₁ → es.ev e₂ = some ev₂ → ev₁.loc = some l₁ →
      ev₂.loc = some l₂ → (O.equivB (.and j.P (es.psiE j.δ)) l₁ l₂ = true ↔
        EquivUnder (Expr.and j.P (es.psiE j.δ)).holds l₁ l₂) := fun ev₁ ev₂ l₁ l₂ h₁ h₂ hl₁ hl₂ =>
    O.equivB_iff (M := M) (by simp [isBPred, hP, isBPred_psiE es hb.vals])
      (isBPred_eq_term (hb.locs ev₁ (mem_events_of_ev h₁) l₁ hl₁)
        (hb.locs ev₂ (mem_events_of_ev h₂) l₂ hl₂))
  constructor
  · intro h
    split at h
    · rename_i ev₁ ev₂ h₁ h₂
      split at h
      · rename_i l₁ l₂ hl₁ hl₂
        exact ⟨ev₁, ev₂, l₁, l₂, h₁, h₂, hl₁, hl₂, (hq _ _ _ _ h₁ h₂ hl₁ hl₂).1 h⟩
      · cases h
    · cases h
  · rintro ⟨ev₁, ev₂, l₁, l₂, h₁, h₂, hl₁, hl₂, hs⟩
    simp only [h₁, h₂, hl₁, hl₂]
    exact (hq _ _ _ _ h₁ h₂ hl₁ hl₂).2 hs

/-! ## Forwarding and Write Elision -/

variable (es)

/-- `fwdRel` and `weRel` split into `fwdBase` and conditions on the two events
    alone, given as decisions. -/
structure RelSplit where
  fwdR : EventId → EventId → Bool
  weR : EventId → EventId → Bool
  fwd_iff : ∀ j a b, es.fwdRel j a b ↔ es.fwdBase j a b ∧ fwdR a b = true
  we_iff : ∀ j a b, es.weRel j a b ↔ es.fwdBase j a b ∧ weR a b = true

variable {es}

theorem fwdBase_congr {j j' : Justification} (hP : j.P.holds = j'.P.holds) (hδ : j.δ = j'.δ)
    {a b : EventId} : es.fwdBase j a b ↔ es.fwdBase j' a b := by
  unfold fwdBase; rw [hP, hδ]

/-! ## Closed relabel equivalence -/

/-- Relabel equivalence on expressions is not trivial: under the empty
    forwarding context and the empty relabelling, `⊤ : 1` and `⊤ : 2` are not
    relabel equivalent, whatever the structure. -/
theorem relabEqExpr_not_trivial :
    ¬ es.relabEqExpr .empty (fun _ => none) Expr.tt (.val (.num 1)) Expr.tt (.val (.num 2)) := by
  rintro ⟨x, h₁, h₂⟩
  let f : Valuation := fun _ => .num 0
  have hψ : FwdCtx.empty.psi es f := by
    intro p hp; simp [FwdCtx.empty] at hp
  have ht : ∀ Λ : Relabelling, (Expr.tt.rename Λ).holds f := fun _ => rfl
  have a := h₁ f ⟨hψ, ht _⟩ (.num 1) rfl
  have b := h₂ f ⟨hψ, ht (fun _ => none)⟩ (.num 2) rfl
  rw [a] at b; cases b

theorem eval_rename (Λ : Relabelling) (f : Valuation) :
    ∀ e : Expr, (e.rename Λ).eval f = e.eval (fun α => f (Λ.app α))
  | .val _ => rfl
  | .sym _ => rfl
  | .bin _ a b | .eq a b | .le a b | .and a b | .or a b => by
      simp only [Expr.rename, Expr.eval, eval_rename Λ f a, eval_rename Λ f b]
  | .not a => by simp only [Expr.rename, Expr.eval, eval_rename Λ f a]

theorem holds_rename_congr (Λ : Relabelling) {P P' : Expr} (h : P.holds = P'.holds) :
    (P.rename Λ).holds = (P'.rename Λ).holds := by
  funext f
  show ((P.rename Λ).eval f = _) = ((P'.rename Λ).eval f = _)
  rw [eval_rename, eval_rename]
  exact congrFun h _

variable (es O)

/-- `relabEqExprC`, decided. -/
def relabExprB (δ : FwdCtx) (Λ : Relabelling) (P₁ x₁ x₂ : Expr) : Bool :=
  x₁.rename Λ == x₂ ||
    (x₂.isTotal && O.equivB (.and (es.psiE δ) (P₁.rename Λ)) (x₁.rename Λ) x₂)

/-- `relabEqC`, decided. -/
def relabEvB (δ : FwdCtx) (Λ : Relabelling) (P₁ : Expr) (e₁ e₂ : Event) : Bool :=
  let ex : Option Expr → Option Expr → Bool := fun o₁ o₂ =>
    match o₁, o₂ with
    | some a, some b => es.relabExprB O δ Λ P₁ a b
    | _, _ => false
  if (e₁.isRead && e₂.isRead) || (e₁.isWrite && e₂.isWrite) || (e₁.isAlloc && e₂.isAlloc) then
    ex e₁.loc e₂.loc && ex e₁.val e₂.val
  else if e₁.isDealloc && e₂.isDealloc then ex e₁.loc e₂.loc
  else if e₁.isFence && e₂.isFence then true
  else false

variable {es O}

theorem relabExprB_iff {Qs : List Expr} {M : List Nat} (hb : es.Bounded Qs M) {δ : FwdCtx}
    {Λ : Relabelling} {P₁ x₁ x₂ : Expr} (hP₁ : isBPred M P₁ = true) (hx₁ : isTerm M x₁ = true)
    (hx₂ : isTerm M x₂ = true) :
    es.relabExprB O δ Λ P₁ x₁ x₂ = true ↔ es.relabEqExprC δ Λ P₁ x₁ x₂ := by
  have hq : O.equivB (.and (es.psiE δ) (P₁.rename Λ)) (x₁.rename Λ) x₂ = true ↔
      EquivUnder (Pred.and (δ.psi es) (P₁.rename Λ).holds) (x₁.rename Λ) x₂ := by
    rw [O.equivB_iff (M := M) (by simp [isBPred, isBPred_psiE es hb.vals, isBPred_rename, hP₁])
      (by simp [isBPred, isTerm_rename, hx₁, hx₂])]
    have : (Expr.and (es.psiE δ) (P₁.rename Λ)).holds = Pred.and (δ.psi es) (P₁.rename Λ).holds := by
      funext f; apply propext; rw [holds_and, Pred.and, psi_iff]
    rw [this]
  unfold relabExprB relabEqExprC
  rw [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, hq]

theorem relabEvB_iff {Qs : List Expr} {M : List Nat} (hb : es.Bounded Qs M) {δ : FwdCtx}
    {Λ : Relabelling} {P₁ : Expr} {e₁ e₂ : Event} (hP₁ : isBPred M P₁ = true)
    (h₁ : TermEv M e₁) (h₂ : TermEv M e₂) :
    es.relabEvB O δ Λ P₁ e₁ e₂ = true ↔ es.relabEqC δ Λ P₁ e₁ e₂ := by
  have hE : ∀ (o₁ o₂ : Option Expr), (∀ a, o₁ = some a → isTerm M a = true) →
      (∀ b, o₂ = some b → isTerm M b = true) →
      ((match o₁, o₂ with
        | some a, some b => es.relabExprB O δ Λ P₁ a b
        | _, _ => false) = true ↔
        ∃ a b, o₁ = some a ∧ o₂ = some b ∧ es.relabEqExprC δ Λ P₁ a b) := by
    intro o₁ o₂ t₁ t₂
    cases o₁ with
    | none => simp
    | some a =>
      cases o₂ with
      | none => simp
      | some b =>
        simp only [Option.some.injEq, exists_and_left, exists_eq_left']
        exact relabExprB_iff hb hP₁ (t₁ a rfl) (t₂ b rfl)
  unfold relabEvB relabEqC
  simp only
  split
  · rw [Bool.and_eq_true, hE _ _ h₁.1 h₂.1, hE _ _ h₁.2 h₂.2]
  · split
    · exact hE _ _ h₁.1 h₂.1
    · split <;> simp

theorem ClosedRelabEqC.congr {δ : FwdCtx} {Λ : Relabelling} {P₁ P₂ P₁' P₂' : Expr}
    (h₁ : P₁.holds = P₁'.holds) (h₂ : P₂.holds = P₂'.holds) {e₁ e₂ : Event}
    (h : es.ClosedRelabEqC δ Λ P₁ e₁ P₂ e₂) : es.ClosedRelabEqC δ Λ P₁' e₁ P₂' e₂ := by
  have hr : ∀ a b, es.relabEqC δ Λ P₁ a b → es.relabEqC δ Λ P₁' a b := by
    intro a b hab
    have hx : ∀ x y, es.relabEqExprC δ Λ P₁ x y → es.relabEqExprC δ Λ P₁' x y := by
      intro x y hxy
      unfold relabEqExprC at hxy ⊢
      rw [← holds_rename_congr Λ h₁]; exact hxy
    have hE : ∀ (o₁ o₂ : Option Expr),
        (∃ x y, o₁ = some x ∧ o₂ = some y ∧ es.relabEqExprC δ Λ P₁ x y) →
        ∃ x y, o₁ = some x ∧ o₂ = some y ∧ es.relabEqExprC δ Λ P₁' x y :=
      fun _ _ ⟨x, y, hx₁, hy, hxy⟩ => ⟨x, y, hx₁, hy, hx x y hxy⟩
    unfold relabEqC at hab ⊢
    simp only at hab ⊢
    split
    · rw [if_pos (by assumption)] at hab; exact ⟨hE _ _ hab.1, hE _ _ hab.2⟩
    · rw [if_neg (by assumption)] at hab
      split
      · rw [if_pos (by assumption)] at hab; exact hE _ _ hab
      · rw [if_neg (by assumption)] at hab; exact hab
  induction h with
  | mk hab hiff _ ih =>
      refine .mk (hr _ _ hab) ?_ ?_
      · rw [← h₁, ← h₂]; exact hiff
      · intro x₁ x₂ ev₁ ev₂ hx₁ hx₂ he₁ he₂
        rw [← h₁] at hx₁; rw [← h₂] at hx₂
        first
          | exact ih x₁ x₂ ev₁ ev₂ hx₁ hx₂ he₁ he₂
          | exact ih x₁ x₂ ev₁ ev₂ hx₁ hx₂ he₁ he₂ h₂
          | exact ih x₁ x₂ ev₁ ev₂ hx₁ hx₂ he₁ he₂ h₁ h₂

/-! ### Kleene iteration over a finite universe -/

/-- `F^k(⊥)`. -/
def kIter {α : Type} (F : (α → Bool) → α → Bool) : Nat → α → Bool
  | 0 => fun _ => false
  | k + 1 => F (kIter F k)

theorem filter_length_mono {α : Type} {p q : α → Bool} :
    ∀ (U : List α), (∀ x ∈ U, p x = true → q x = true) → (U.filter p).length ≤ (U.filter q).length
  | [], _ => Nat.le_refl _
  | a :: U, h => by
      have ih := filter_length_mono U (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [List.filter_cons]
      by_cases hp : p a = true
      · rw [if_pos hp, if_pos (h a (List.mem_cons_self ..) hp)]; simp; omega
      · rw [if_neg hp]; split <;> simp <;> omega

theorem filter_length_lt {α : Type} {p q : α → Bool} :
    ∀ (U : List α), (∀ x ∈ U, p x = true → q x = true) → ∀ x₀ ∈ U, q x₀ = true → p x₀ = false →
      (U.filter p).length < (U.filter q).length
  | [], _, _, h, _, _ => by cases h
  | a :: U, h, x₀, hx, hq, hp => by
      have hmono := filter_length_mono U (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp only [List.filter_cons]
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [if_neg (by simp [hp]), if_pos hq]; simp; omega
      · have ih := filter_length_lt U (fun x hx => h x (List.mem_cons_of_mem _ hx)) x₀ hx hq hp
        by_cases hpa : p a = true
        · rw [if_pos hpa, if_pos (h a (List.mem_cons_self ..) hpa)]; simp; omega
        · rw [if_neg hpa]; split <;> simp <;> omega

theorem kIter_fix {α : Type} (U : List α) (F : (α → Bool) → α → Bool)
    (hmono : ∀ S T : α → Bool, (∀ x ∈ U, S x = true → T x = true) →
      ∀ x ∈ U, F S x = true → F T x = true)
    (hloc : ∀ S T : α → Bool, (∀ x ∈ U, S x = T x) → ∀ x ∈ U, F S x = F T x) :
    ∀ x ∈ U, F (kIter F U.length) x = kIter F U.length x := by
  have up : ∀ k, ∀ x ∈ U, kIter F k x = true → kIter F (k + 1) x = true := by
    intro k
    induction k with
    | zero => intro x _ h; cases h
    | succ k ih => intro x hx h; exact hmono _ _ ih x hx h
  -- a stage that does not grow is a fixed point from then on
  have stay : ∀ k, (∀ x ∈ U, kIter F (k + 1) x = kIter F k x) →
      ∀ m, ∀ x ∈ U, kIter F (k + m) x = kIter F k x := by
    intro k hk m
    induction m with
    | zero => intro x _; rfl
    | succ m ih =>
        intro x hx
        show F (kIter F (k + m)) x = _
        rw [hloc _ (kIter F k) ih x hx]; exact hk x hx
  -- some stage up to `|U|` does not grow
  have hex : ∃ k ≤ U.length, ∀ x ∈ U, kIter F (k + 1) x = kIter F k x := by
    refine Classical.byContradiction fun hne => ?_
    have grow : ∀ k ≤ U.length + 1, k ≤ (U.filter (kIter F k)).length := by
      intro k
      induction k with
      | zero => intro _; exact Nat.zero_le _
      | succ k ih =>
          intro hk
          have ih := ih (by omega)
          have : ¬ ∀ x ∈ U, kIter F (k + 1) x = kIter F k x := fun h => hne ⟨k, by omega, h⟩
          have ⟨x, hx, hd⟩ : ∃ x ∈ U, kIter F (k + 1) x ≠ kIter F k x :=
            Classical.byContradiction fun h' => this fun x hx =>
              Classical.byContradiction fun hd => h' ⟨x, hx, hd⟩
          have hk1 : kIter F (k + 1) x = true ∧ kIter F k x = false := by
            have := up k x hx
            cases h1 : kIter F (k + 1) x <;> cases h2 : kIter F k x <;> simp_all
          have := filter_length_lt U (up k) x hx hk1.1 hk1.2
          omega
    have := grow (U.length + 1) (Nat.le_refl _)
    have := List.length_filter_le (kIter F (U.length + 1)) U
    omega
  obtain ⟨k, hk, hfix⟩ := hex
  intro x hx
  have e1 := stay k hfix (U.length - k) x hx
  have e2 := stay k hfix (U.length - k + 1) x hx
  rw [Nat.add_sub_cancel' hk] at e1
  rw [show k + (U.length - k + 1) = U.length + 1 by omega] at e2
  show kIter F (U.length + 1) x = _
  rw [e2, e1]

/-! ### Closed relabel equivalence, decided -/

variable (es O)

/-- One unfolding of closed relabel equivalence, with the pairs of
    predecessors looked up in `S`. -/
def crStep (P₁ P₂ : Expr) (δ : FwdCtx) (Λ : Relabelling) (S : EventId × EventId → Bool)
    (e₁ e₂ : Event) : Bool :=
  es.relabEvB O δ Λ P₁ e₁ e₂ &&
    ((es.predL O P₁ δ e₁.id).isEmpty == (es.predL O P₂ δ e₂.id).isEmpty) &&
    (es.predL O P₁ δ e₁.id).all fun y₁ => (es.predL O P₂ δ e₂.id).all fun y₂ =>
      match es.ev y₁, es.ev y₂ with
      | some _, some _ => S (y₁, y₂)
      | _, _ => true

def crF (P₁ P₂ : Expr) (δ : FwdCtx) (Λ : Relabelling) (S : EventId × EventId → Bool)
    (p : EventId × EventId) : Bool :=
  match es.ev p.1, es.ev p.2 with
  | some a, some b => es.crStep O P₁ P₂ δ Λ S a b
  | _, _ => false

/-- Closed relabel equivalence (`ClosedRelabEqC`) of two events, decided. -/
def crB (P₁ P₂ : Expr) (δ : FwdCtx) (Λ : Relabelling) (e₁ e₂ : Event) : Bool :=
  es.crStep O P₁ P₂ δ Λ (kIter (es.crF O P₁ P₂ δ Λ) (prodL (es.candL δ) (es.candL δ)).length) e₁ e₂

variable {es O}

theorem all_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.all_cons, h a (List.mem_cons_self ..),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem crStep_congr {P₁ P₂ : Expr} {δ : FwdCtx} {Λ : Relabelling} {S T : EventId × EventId → Bool}
    (hST : ∀ y₁ ∈ es.candL δ, ∀ y₂ ∈ es.candL δ, S (y₁, y₂) = T (y₁, y₂)) (a b : Event) :
    es.crStep O P₁ P₂ δ Λ S a b = es.crStep O P₁ P₂ δ Λ T a b := by
  unfold crStep
  rw [all_congr_mem (fun y₁ hy₁ => all_congr_mem (fun y₂ hy₂ => ?_))]
  cases es.ev y₁ <;> cases es.ev y₂ <;> try rfl
  exact hST y₁ (List.mem_filter.1 hy₁).1 y₂ (List.mem_filter.1 hy₂).1

theorem crStep_mono {P₁ P₂ : Expr} {δ : FwdCtx} {Λ : Relabelling} {S T : EventId × EventId → Bool}
    (hST : ∀ y₁ ∈ es.candL δ, ∀ y₂ ∈ es.candL δ, S (y₁, y₂) = true → T (y₁, y₂) = true)
    {a b : Event} (h : es.crStep O P₁ P₂ δ Λ S a b = true) :
    es.crStep O P₁ P₂ δ Λ T a b = true := by
  unfold crStep at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨h.1, fun y₁ hy₁ y₂ hy₂ => ?_⟩
  have := h.2 y₁ hy₁ y₂ hy₂
  revert this
  cases es.ev y₁ <;> cases es.ev y₂ <;> try (intro; rfl)
  exact hST y₁ (List.mem_filter.1 hy₁).1 y₂ (List.mem_filter.1 hy₂).1

section spec3

variable {Qs : List Expr} {M : List Nat} (hb : es.Bounded Qs M) {P₁ P₂ : Expr}
  (hP₁ : isBPred M P₁ = true) (hP₂ : isBPred M P₂ = true) {δ : FwdCtx} (hwf : δ.WF)
  (Λ : Relabelling)
include hb hP₁ hP₂ hwf

theorem crStep_sound {S : EventId × EventId → Bool}
    (hS : ∀ y₁ y₂ a b, es.ev y₁ = some a → es.ev y₂ = some b → S (y₁, y₂) = true →
      es.ClosedRelabEqC δ Λ P₁ a P₂ b)
    {e₁ e₂ : Event} (ht₁ : TermEv M e₁) (ht₂ : TermEv M e₂)
    (h : es.crStep O P₁ P₂ δ Λ S e₁ e₂ = true) : es.ClosedRelabEqC δ Λ P₁ e₁ P₂ e₂ := by
  unfold crStep at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨hs, he⟩, hall⟩ := h
  refine .mk ((relabEvB_iff hb hP₁ ht₁ ht₂).1 hs) ?_ ?_
  · have h1 : (∀ x, ¬ es.pred δ e₁.id P₁.holds x) ↔ (es.predL O P₁ δ e₁.id).isEmpty = true := by
      rw [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
      exact forall_congr' fun x => not_congr (mem_predL hb hP₁ hwf).symm
    have h2 : (∀ x, ¬ es.pred δ e₂.id P₂.holds x) ↔ (es.predL O P₂ δ e₂.id).isEmpty = true := by
      rw [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
      exact forall_congr' fun x => not_congr (mem_predL hb hP₂ hwf).symm
    rw [h1, h2, he]
  · intro x₁ x₂ ev₁ ev₂ hx₁ hx₂ he₁ he₂
    have := hall x₁ ((mem_predL hb hP₁ hwf).2 hx₁) x₂ ((mem_predL hb hP₂ hwf).2 hx₂)
    rw [he₁, he₂] at this
    exact hS x₁ x₂ ev₁ ev₂ he₁ he₂ this

theorem kIter_cr_sound : ∀ k y₁ y₂ a b, es.ev y₁ = some a → es.ev y₂ = some b →
    kIter (es.crF O P₁ P₂ δ Λ) k (y₁, y₂) = true → es.ClosedRelabEqC δ Λ P₁ a P₂ b
  | 0, _, _, _, _, _, _, h => by cases h
  | k + 1, y₁, y₂, a, b, ha, hb', h => by
      simp only [kIter, crF, ha, hb'] at h
      exact crStep_sound hb hP₁ hP₂ hwf Λ (kIter_cr_sound k)
        (hb.termEv (mem_events_of_ev ha)) (hb.termEv (mem_events_of_ev hb')) h

theorem crB_iff {e₁ e₂ : Event} (ht₁ : TermEv M e₁) (ht₂ : TermEv M e₂) :
    es.crB O P₁ P₂ δ Λ e₁ e₂ = true ↔ es.ClosedRelabEqC δ Λ P₁ e₁ P₂ e₂ := by
  let U := prodL (es.candL δ) (es.candL δ)
  have hpredU : ∀ (P : Expr), isBPred M P = true → ∀ e y, y ∈ es.predL O P δ e → y ∈ es.candL δ :=
    fun P hP e y hy => (List.mem_filter.1 hy).1
  have hloc : ∀ S T : EventId × EventId → Bool, (∀ x ∈ U, S x = T x) →
      ∀ x ∈ U, es.crF O P₁ P₂ δ Λ S x = es.crF O P₁ P₂ δ Λ T x := by
    intro S T hST x _
    unfold crF
    cases es.ev x.1 <;> cases es.ev x.2 <;> try rfl
    exact crStep_congr (fun y₁ h₁ y₂ h₂ => hST _ (mem_prodL h₁ h₂)) _ _
  have hmono : ∀ S T : EventId × EventId → Bool, (∀ x ∈ U, S x = true → T x = true) →
      ∀ x ∈ U, es.crF O P₁ P₂ δ Λ S x = true → es.crF O P₁ P₂ δ Λ T x = true := by
    intro S T hST x _ h
    unfold crF at h ⊢
    revert h
    cases es.ev x.1 <;> cases es.ev x.2 <;> try (intro h; exact h)
    exact crStep_mono (fun y₁ h₁ y₂ h₂ => hST _ (mem_prodL h₁ h₂))
  have hfix := kIter_fix U _ hmono hloc
  constructor
  · intro h
    exact crStep_sound hb hP₁ hP₂ hwf Λ (kIter_cr_sound hb hP₁ hP₂ hwf Λ _) ht₁ ht₂ h
  · intro h
    have hemp : ∀ (P : Expr), isBPred M P = true → ∀ e,
        (∀ x, ¬ es.pred δ e P.holds x) ↔ (es.predL O P δ e).isEmpty = true := fun P hP e => by
      rw [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
      exact forall_congr' fun x => not_congr (mem_predL hb hP hwf).symm
    suffices key : ∀ Q₁ a₁ Q₂ a₂, es.ClosedRelabEqC δ Λ Q₁ a₁ Q₂ a₂ → P₁ = Q₁ → P₂ = Q₂ →
        TermEv M a₁ → TermEv M a₂ →
        es.crStep O P₁ P₂ δ Λ (kIter (es.crF O P₁ P₂ δ Λ) U.length) a₁ a₂ = true from
      key _ _ _ _ h rfl rfl ht₁ ht₂
    intro Q₁ a₁ Q₂ a₂ hc
    induction hc with
    | mk hr hiff _ ih =>
        intro e1 e2 t₁ t₂
        subst e1 e2
        unfold crStep
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
        refine ⟨⟨(relabEvB_iff hb hP₁ t₁ t₂).2 hr, ?_⟩, fun y₁ hy₁ y₂ hy₂ => ?_⟩
        · cases h1 : (es.predL O _ δ _).isEmpty <;> cases h2 : (es.predL O _ δ _).isEmpty <;>
            simp_all [← hemp _ hP₁, ← hemp _ hP₂]
        · cases he₁ : es.ev y₁ with
          | none => simp
          | some ev₁ =>
            cases he₂ : es.ev y₂ with
            | none => simp
            | some ev₂ =>
              simp only
              have hc := ih y₁ y₂ ev₁ ev₂ ((mem_predL hb hP₁ hwf).1 hy₁) ((mem_predL hb hP₂ hwf).1 hy₂)
                he₁ he₂ rfl rfl (hb.termEv (mem_events_of_ev he₁)) (hb.termEv (mem_events_of_ev he₂))
              have hU : (y₁, y₂) ∈ U := mem_prodL (hpredU _ hP₁ _ _ hy₁) (hpredU _ hP₂ _ _ hy₂)
              rw [← hfix _ hU]
              simp only [crF, he₁, he₂]; exact hc

end spec3

end EventStructure
