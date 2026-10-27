import Smrd.PpoStability
import Smrd.CoherenceT

/-!
# Dependencies run along `⊑` (`DP ⊆ ⊑`)

With Strengthening restricted to origins `⊑`-before the justified write
(`Generated.str`, sMRD §4.7's prose), every symbol of a generated
justification's predicate, dependencies and expressions has its origin
`⊑`-before the justified event (`Generated.past`), and so `DP ⊆ ⊑`
(`Execution.dp_po`). The hypotheses `DP ⊆ ⊑` of `noThinAir_iff_win`,
`noThinAir_iff_trunc`, `dep_po_T`, … are derived from it.

## What the invariant needs

* `SymWF`: the event structure introduces symbols at their origin and
  `⊑`-before their uses: every symbol of an event's value restriction and
  expressions has its origin `⊑`-before the event, and a read introduces its
  own id. The semantics `⟨P⟩_n` builds structures of this shape
  (`SymWFDenote.denote_symWF`).
* `FwdWin`: the forwarded write `e₂` of a store-store forwarding is `⊑`-before
  or equal to the justified write (MoRDor's forwarding window, DEPARTURES E4).
  Store-store forwarding replaces the *expression* `val(e₂)`, which can occur
  in `P` without `e₂` being an origin of `P`, so without the window it brings
  in `val(e₁)`'s origins from beyond the write. Store forwarding and load
  forwarding need nothing: they replace the symbol of a read `e₂`, which, if it
  occurs, is an origin and so `⊑`-before the write.
* `LiftPast`: Lifting keeps `⟦P₁⟧_Λ`'s symbols `⊑`-before `w₂`. Closed
  relabel-equivalence constrains `Λ` on `D₁` only (`D₂ = Λ(D₁)`); a symbol of
  `P₁` outside `D₁` keeps an origin `⊑`-before `w₁`, which need not be
  `⊑`-before `w₂` (the other arm of a branch, or `w₁` in another thread or
  `⊑`-after `w₂`).

Value Assignment, Strengthening, Write Elision and Weakening preserve the
invariant without further hypotheses.
-/

namespace Expr

theorem mem_syms_replace {p q : Expr} {α : Sym} :
    ∀ {E : Expr}, α ∈ (E.replace p q).syms → α ∈ E.syms ∨ α ∈ q.syms := by
  intro E
  induction E with
  | val w =>
      intro h; unfold replace at h; split at h
      · exact .inr h
      · simp [syms] at h
  | sym β =>
      intro h; unfold replace at h; split at h
      · exact .inr h
      · exact .inl h
  | bin op a b iha ihb | eq a b iha ihb | le a b iha ihb | and a b iha ihb | or a b iha ihb =>
      intro h; unfold replace at h; split at h
      · exact .inr h
      · simp only [syms, List.mem_append] at h ⊢
        rcases h with h | h
        · rcases iha h with h | h
          · exact .inl (.inl h)
          · exact .inr h
        · rcases ihb h with h | h
          · exact .inl (.inr h)
          · exact .inr h
  | not a iha =>
      intro h; unfold replace at h; split at h
      · exact .inr h
      · simp only [syms] at h ⊢
        exact iha h

theorem replace_sym_of_not_mem {β : Sym} {q : Expr} :
    ∀ {E : Expr}, β ∉ E.syms → E.replace (.sym β) q = E := by
  intro E
  induction E with
  | val w =>
      intro _; unfold replace; split
      · rename_i heq; cases heq
      · rfl
  | sym γ =>
      intro h; unfold replace; split
      · rename_i heq; cases heq; exact absurd (List.mem_singleton_self β) h
      · rfl
  | bin op a b iha ihb =>
      intro h; unfold replace; split
      · rename_i heq; cases heq
      · simp only [syms, List.mem_append, not_or] at h
        simp only [iha h.1, ihb h.2]
  | eq a b iha ihb =>
      intro h; unfold replace; split
      · rename_i heq; cases heq
      · simp only [syms, List.mem_append, not_or] at h
        simp only [iha h.1, ihb h.2]
  | le a b iha ihb =>
      intro h; unfold replace; split
      · rename_i heq; cases heq
      · simp only [syms, List.mem_append, not_or] at h
        simp only [iha h.1, ihb h.2]
  | and a b iha ihb =>
      intro h; unfold replace; split
      · rename_i heq; cases heq
      · simp only [syms, List.mem_append, not_or] at h
        simp only [iha h.1, ihb h.2]
  | or a b iha ihb =>
      intro h; unfold replace; split
      · rename_i heq; cases heq
      · simp only [syms, List.mem_append, not_or] at h
        simp only [iha h.1, ihb h.2]
  | not a iha =>
      intro h; unfold replace; split
      · rename_i heq; cases heq
      · simp only [syms] at h
        simp only [iha h]

theorem mem_syms_subst_val {β : Sym} {v : Val} {α : Sym} :
    ∀ {E : Expr}, α ∈ (E.subst β (.val v)).syms → α ∈ E.syms := by
  intro E
  induction E with
  | val w => intro h; simp [subst, syms] at h
  | sym γ =>
      intro h; simp only [subst] at h
      split at h
      · simp [syms] at h
      · exact h
  | bin op a b iha ihb | eq a b iha ihb | le a b iha ihb | and a b iha ihb | or a b iha ihb =>
      intro h; simp only [subst, syms, List.mem_append] at h ⊢
      rcases h with h | h
      · exact .inl (iha h)
      · exact .inr (ihb h)
  | not a iha => intro h; simp only [subst, syms] at h ⊢; exact iha h

end Expr

namespace Event

/-- The symbols of an event's expressions: the location and value of a write,
    the location of a read or deallocation, the size of an allocation. Not the
    symbol a read or allocation introduces. -/
def exprSyms (e : Event) : List Sym :=
  match e.kind with
  | .write _ x v _ => x.syms ++ v.syms
  | .read _ l _ _ => l.syms
  | .alloc _ s => s.syms
  | .dealloc l => l.syms
  | _ => []

/-- The symbols an event depends on: those of its value restriction and of its
    expressions. -/
def depSyms (e : Event) : List Sym := e.valres.syms ++ e.exprSyms

end Event

namespace EventStructure

variable (es : EventStructure)

/-- Symbols are introduced `⊑`-before their uses: every symbol an event
    depends on has its origin `⊑`-before it, and a read introduces the symbol
    of its own id (`origin α = α`). -/
structure SymWF : Prop where
  past : ∀ e ∈ es.events, ∀ α ∈ e.depSyms, es.poR α e.id
  read_sym : ∀ e ∈ es.events, ∀ o l α v, e.kind = .read o l α v → α = e.id

/-- Every symbol of `j`'s predicate, dependencies and expressions has its
    origin `⊑`-before the justified event. -/
def Past (j : Justification) : Prop :=
  ∀ α, (α ∈ j.P.syms ∨ α ∈ j.D ∨ α ∈ j.w.exprSyms) → es.poR α j.w.id

/-- The forwarded write of each store-store forwarding of `j` lies in `j`'s
    window, `e₂ ⊑ w ∨ e₂ = w` (MoRDor, DEPARTURES E4). -/
def FwdWin (j : Justification) : Prop :=
  ∀ p ∈ j.δ.f, es.cls Event.isWrite p.2 → es.poR p.2 j.w.id ∨ p.2 = j.w.id

/-- Lifting keeps the relabelled premise's symbols `⊑`-before `w₂`. -/
def LiftPast (Ω : Pred) : Prop :=
  ∀ (j₁ j₂ : Justification) (Λ : Relabelling), es.Generated Ω j₁ → es.Generated Ω j₂ →
    j₁.δ = j₂.δ → Λ.Injective → es.ClosedRelabEq j₁.δ Λ j₁.P j₁.w j₂.P j₂.w →
    (∀ e, e ∈ j₂.D ↔ ∃ α ∈ j₁.D, Λ.app α = e) →
    ∀ α ∈ (j₁.P.rename Λ).syms, es.poR α j₂.w.id

variable {es}

theorem ev_some {a : EventId} {e : Event} (h : es.ev a = some e) : e ∈ es.events ∧ e.id = a := by
  unfold ev at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- The symbols of the value `val(e₁)` of a forwarding source are `⊑`-before
    the forwarded event. -/
theorem val_src_po (hwf : es.SymWF) (hpo : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    {e₁ e₂ : EventId} {ev₁ : Event} {v₁ : Expr} (h₁ : es.ev e₁ = some ev₁)
    (hv₁ : ev₁.val = some v₁) (hcls : es.cls Event.isWrite e₁ ∨ es.cls Event.isRead e₁)
    (h12 : es.poR e₁ e₂) : ∀ α ∈ v₁.syms, es.poR α e₂ := by
  intro α hα
  obtain ⟨hm, hid⟩ := ev_some h₁
  have hk : ∀ e', es.ev e₁ = some e' → e' = ev₁ := fun e' h => by rw [h₁] at h; cases h; rfl
  rcases hcls with ⟨e', he', hw⟩ | ⟨e', he', hr⟩
  · rw [hk e' he'] at hw
    unfold Event.isWrite at hw
    split at hw
    · rename_i o x v b heq
      simp only [Event.val, heq, Option.some.injEq] at hv₁
      subst hv₁
      refine hpo _ _ _ ?_ h12
      rw [← hid]
      exact hwf.past ev₁ hm α (by simp [Event.depSyms, Event.exprSyms, heq, hα])
    · cases hw
  · rw [hk e' he'] at hr
    unfold Event.isRead at hr
    split at hr
    · rename_i o l β b heq
      simp only [Event.val, heq, Option.some.injEq] at hv₁
      subst hv₁
      simp only [Expr.syms, List.mem_singleton] at hα
      rw [hα, hwf.read_sym ev₁ hm o l β b heq, hid]
      exact h12
    · cases hr

/-- **Every origin of a generated justification is `⊑`-before its event**,
    given `SymWF`, the forwarding window and `LiftPast`. -/
theorem Generated.past {Ω : Pred} (hwf : es.SymWF)
    (hpo : ∀ a b c, es.poR a b → es.poR b c → es.poR a c) (hL : es.LiftPast Ω)
    {j : Justification} (h : es.Generated Ω j) : es.FwdWin j → es.Past j := by
  induction h with
  | @pre w j hw hj _ =>
      intro _ α hα
      unfold preJust at hj
      split at hj <;> cases hj
      all_goals
        rename_i heq
        apply hwf.past w hw α
        simp only [Event.depSyms, Event.exprSyms, List.mem_append] at hα ⊢
        rcases hα with h | h | h <;> simp_all
  | @va j₁ o x e b α' v _ hk _ _ ih =>
      intro hW α hα
      have hW₁ : es.FwdWin j₁ := hW
      apply ih hW₁ α
      simp only [Event.exprSyms, hk, List.mem_append] at hα ⊢
      rcases hα with h | (h | h) | (h | h)
      · exact .inl h
      · exact .inr (.inr (.inl (Expr.mem_syms_subst_val h)))
      · exact .inr (.inr (.inr (Expr.mem_syms_subst_val h)))
      · exact .inr (.inr (.inl (Expr.mem_syms_subst_val h)))
      · exact .inr (.inr (.inr (Expr.mem_syms_subst_val h)))
  | @str j₁ Q S _ hS _ hord _ ih =>
      intro hW α hα
      have ih := ih hW
      rcases hα with h | h
      · by_cases hP : α ∈ j₁.P.syms
        · exact ih α (.inl hP)
        · exact (hord α ((hS α).2 ⟨h, hP⟩)).1
      · exact ih α (.inr h)
  | @fwd j₁ o x e b e₁ e₂ ev₁ ev₂ v₁ v₂ _ hk hf h₁ h₂ hv₁ hv₂ _ _ ih =>
      intro hW α hα
      have hW₁ : es.FwdWin j₁ := fun p hp => hW p (List.mem_append_left _ hp)
      have ih := ih hW₁
      have hwin := hW (e₁, e₂) (List.mem_append_right _ (List.mem_singleton_self _))
      obtain ⟨⟨-, h12, -⟩, hcls, -, -⟩ := hf
      have hsrc : es.cls Event.isWrite e₁ ∨ es.cls Event.isRead e₁ := by
        rcases hcls with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact .inl h
        · exact .inl h
        · exact .inr h
      have hv := val_src_po hwf hpo h₁ hv₁ hsrc h12
      -- replacing `v₂` by `v₁` in an expression whose origins precede `w`
      have key : ∀ E : Expr, (∀ β ∈ E.syms, es.poR β j₁.w.id) →
          ∀ β ∈ (E.replace v₂ v₁).syms, es.poR β j₁.w.id := by
        intro E hE β hβ
        have via : es.poR e₂ j₁.w.id ∨ e₂ = j₁.w.id → es.poR β j₁.w.id := by
          intro h2
          rcases Expr.mem_syms_replace hβ with hβ | hβ
          · exact hE β hβ
          · rcases h2 with h2 | h2
            · exact hpo _ _ _ (hv β hβ) h2
            · rw [← h2]; exact hv β hβ
        by_cases hr : es.cls Event.isWrite e₂
        · exact via (hwin hr)
        · -- `e₂` is a read: `v₂` is the symbol `e₂`
          have hr₂ : es.cls Event.isRead e₂ := by
            rcases hcls with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
            · obtain ⟨e', he', h⟩ := h
              refine ⟨e', he', ?_⟩
              unfold Event.isRlxR at h; unfold Event.isRead
              split at h <;> simp_all
            · obtain ⟨e', he', h⟩ := h
              refine absurd ⟨e', he', ?_⟩ hr
              unfold Event.isRlxW at h; unfold Event.isWrite
              split at h <;> simp_all
            · exact h
          obtain ⟨e', he', hrd⟩ := hr₂
          rw [h₂] at he'; cases he'
          obtain ⟨hm₂, hid₂⟩ := ev_some h₂
          unfold Event.isRead at hrd
          split at hrd
          · rename_i o' l' γ b' heq
            simp only [Event.val, heq, Option.some.injEq] at hv₂
            subst hv₂
            have hγ : γ = e₂ := by rw [hwf.read_sym ev₂ hm₂ o' l' γ b' heq, hid₂]
            by_cases hm : γ ∈ E.syms
            · exact via (.inl (hγ ▸ hE γ hm))
            · rw [Expr.replace_sym_of_not_mem hm] at hβ
              exact hE β hβ
          · cases hrd
      have hP := key j₁.P (fun β h => ih β (.inl h))
      have hx := key x (fun β h => ih β (.inr (.inr (by simp [Event.exprSyms, hk, h]))))
      have he := key e (fun β h => ih β (.inr (.inr (by simp [Event.exprSyms, hk, h]))))
      simp only [Event.exprSyms, List.mem_append] at hα
      rcases hα with h | (h | h) | (h | h)
      · exact hP α h
      · exact he α h
      · exact hx α h
      · exact hx α h
      · exact he α h
  | @we j₁ e₁ e₂ _ _ _ _ ih =>
      intro hW
      exact ih hW
  | @lift j₁ j₂ Λ g₁ g₂ hδ hΛ hrel hD _ _ _ _ _ _ ih₂ =>
      intro hW α hα
      have ih := ih₂ hW
      rcases hα with h | h
      · rcases List.mem_append.1 ((Expr.mem_syms_liftPred_iff _ _ α).1 h) with h | h
        · exact hL j₁ j₂ Λ g₁ g₂ hδ hΛ hrel hD α h
        · exact ih α (.inl h)
      · exact ih α (.inr h)
  | @weak j₁ P' Pw _ hc _ _ ih =>
      intro hW α hα
      have ih := ih hW
      rcases hα with h | h
      · refine ih α (.inl ((hc.mem_syms_iff α).2 ?_))
        simp only [Expr.syms, List.mem_append]
        exact .inl h
      · exact ih α (.inr h)

end EventStructure

namespace Execution

open EventStructure

variable {es : EventStructure} {x : Execution}

/-- **`DP ⊆ ⊑`**: every dependency runs `⊑`-forward, given `SymWF`, the
    forwarding window and `LiftPast`. -/
theorem dp_po {Ω : Pred} (hx : x.IsExecution es Ω) (hwf : es.SymWF)
    (hpo : ∀ a b c, es.poR a b → es.poR b c → es.poR a c) (hL : es.LiftPast Ω)
    (hW : ∀ j ∈ x.J, es.FwdWin j) : ∀ a b, x.DP a b → es.poR a b := by
  rintro a b ⟨-, -, j, hj, rfl, hab⟩
  exact (hx.generated j hj).past hwf hpo hL (hW j hj) a
    (by rcases hab with h | h; exact .inl h; exact .inr (.inl h))

/-- Without forwarding the window holds vacuously. -/
theorem fwdWin_of_noFwd (hF : ∀ p ∈ x.δ.f, False) : ∀ j ∈ x.J, es.FwdWin j :=
  fun _ hj p hp _ => (hF p (mem_δ_f hj hp)).elim

/-- Without `F ∪ WE` edges the window holds vacuously. -/
theorem fwdWin_of_noEdge (hδ : ∀ a b, ¬ x.δ.edge a b) : ∀ j ∈ x.J, es.FwdWin j :=
  fun _ hj p hp _ => (hδ p.1 p.2 (.inl (mem_δ_f hj hp))).elim

end Execution

/-! ## The `DP ⊆ ⊑` hypotheses, derived

Without forwarding the window is vacuous, so `DP ⊆ ⊑` reduces to `SymWF` and
`LiftPast`. -/

namespace Execution

open EventStructure

variable {es : EventStructure} {x : Execution}

theorem dp_po_noFwd {Ω : Pred} (hx : x.IsExecution es Ω) (hwf : es.SymWF)
    (hpo : ∀ a b c, es.poR a b → es.poR b c → es.poR a c) (hL : es.LiftPast Ω)
    (hF : ∀ p ∈ x.δ.f, False) : ∀ a b, x.DP a b → es.poR a b :=
  dp_po hx hwf hpo hL (fwdWin_of_noFwd hF)

/-- `noThinAir_iff_win_we` with `DP ⊆ ⊑` derived. -/
theorem noThinAir_iff_win_we_past {Ω : Pred} (hx : x.IsExecution es Ω) (hphi : x.phi es)
    (hW : WEForward es x)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hN : NoCross es x) (hT : RMWTightR es x)
    (hwf : es.SymWF) (hL : es.LiftPast Ω) :
    x.NoThinAir es ↔ Rel.Acyclic ((depWin es x).union x.rf) :=
  noThinAir_iff_win_we hx hphi hW hpo_trans hirr hF hN hT
    (dp_po_noFwd hx hwf hpo_trans hL hW.1)

/-- `noThinAir_iff_trunc` with `DP ⊆ ⊑` derived. -/
theorem noThinAir_iff_trunc_past {Ω : Pred}
    (hx : x.IsExecution es Ω) (hphi : x.phi es)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a)
    (hnf : ∀ e ∈ es.events, e.isFence = false) (hr : es.rmw = [])
    (hδ : ∀ a b, ¬ x.δ.edge a b) (hm : LocModel es x)
    (hwf : es.SymWF) (hL : es.LiftPast Ω) :
    x.NoThinAir es ↔ Rel.Acyclic (((x.ppoTrunc es).union x.DP).union x.rf) :=
  PpoStability.noThinAir_iff_trunc hx hphi hpo_trans hirr hnf hr hδ hm
    (dp_po hx hwf hpo_trans hL (fwdWin_of_noEdge hδ))

/-- `dep_po_T` with `DP ⊆ ⊑` derived. -/
theorem dep_po_T_past {Ω : Pred} (hx : x.IsExecution es Ω) (hW : WEForward es x)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hLc : NoCrossLoc es x) (hT : RMWTightR es x)
    (hwf : es.SymWF) (hL : es.LiftPast Ω) {a b : EventId} (h : x.dep es a b) :
    x.poX es a b :=
  dep_po_T hx hW hpo_trans hirr hF hLc hT (dp_po_noFwd hx hwf hpo_trans hL hW.1) h

end Execution
