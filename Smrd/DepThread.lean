import Smrd.DPPast
import Smrd.FwdEntails

/-!
# Dependencies are thread-internal

The model does not assume that `dep = DP ∪ ≼` refines program order. It is
*thread-internal*: every pair of `DP ∪ ≼` relates `⊑`-comparable (or equal)
events, `ThreadInternal`.

## The notion of thread

"Same thread" is read as `PoCmp`: `a = b ∨ a ⊑ b ∨ b ⊑ a`. Among the events of
an execution, which are conflict-free, two events are incomparable exactly
when they lie in different threads of a parallel composition (events on two
outcomes of a branching conflict and are never both in `X`). After a join, the
continuation is comparable with both threads, as is the code before a fork:
the order already says what "the same thread" means, and the library's
restrictions on forwarding and elision (`fwdNoJoin`, `weNoJoin`, `Anchored`)
are stated in it. Two other notions are available and are not used:

* thread ids (`Event.thread`): `⟨P₁ ∥ P₂⟩` gives `P₁` the parent's id, so the
  initialising prefix and the first thread share one id while the second
  thread does not. Ids neither separate the prefix from the threads nor say
  anything the generation rules can see;
* segments: not part of the library on `main`.

## Results

* `GeneratedStr`: `Generated` with sMRD's published Strengthening (Def. 4.11):
  the new origins are `⊑`-comparable with the justified write, `e ⊑ w ∨ w ⊑ e`,
  instead of `⊑`-before it (`Generated.str`, condition `cond:str-before`).
  Every other rule, Lifting's `⊑`-restriction included, is the library's.
  `Generated.toStr`: the restricted rule is an instance.
* `GeneratedStr.joinPast`: every symbol of a justification generated so has its
  origin *joinable* with the write (a common `⊑`-upper bound), given `SymWF`
  and the store-store forwarding window (`FwdWin`), with no hypothesis on the
  shape of `⊑`. So `DP ⊆ Joinable` (`Execution.dp_joinable`), and where `⊑` is a
  forest (`PoForest`, no code after a join) `DP` is thread-internal
  (`Execution.dp_thread`). Strengthening's restriction to origins before the
  write is not needed for this; a restriction to the same thread is.
* `Execution.ppo_po_E`: `≼ ⊆ ⊑` under `FwdEntailsImg`, without any hypothesis
  on `DP`: Strengthening's order condition plays no role for `≼`.
* `Execution.dep_thread_str`: `DP ∪ ≼` thread-internal for justifications of
  `GeneratedStr`, under `PoForest`, the window, and `≼ ⊆ ⊑`;
  `Execution.dep_thread_E`, `dep_thread_denote`: thread-internal for the executions
  of the library (where in fact `DP ∪ ≼ ⊆ ⊑`).

## Where the hypotheses are needed

* `PoForest`: with code after a join, published Strengthening and Forwarding
  together move a symbol across threads. In `(w ∥ r := x); y := r; s := y`
  with `w` in the first thread, strengthening `w` with the read `s := y` of the
  continuation (`w ⊑ s`), then store-forwarding `s` from `y := r`, replaces
  `s`'s symbol by `r`'s, from the second thread. `fwdNoJoin` admits it: every
  event `⊑`-below `s` is comparable with `y := r`. Under the restricted rule
  the origin `s` lies `⊑`-before `w` and the forwarded value's symbols with it
  (`Generated.past`). Not mechanised.
* `FwdWin`: store-store forwarding replaces the *expression* `val(e₂)`, which
  can occur in `P` without `e₂` being related to `w` at all; without the window
  it brings in origins of another thread.
* `≼`: the closure of `≼` composes steps, and comparability is not transitive:
  a step `⊑`-backwards from one thread into the code before a fork, followed by
  a step forwards into a sibling thread, crosses threads. Backward steps come
  from remapping (`Smrd.FwdAcrossAlias`), and `FwdEntailsImg` excludes them.
  Without a segment restriction on Forwarding (a forwarding from the
  initialising prefix into a thread is admitted by `fwdNoJoin`) the library has
  no weaker hypothesis that keeps `≼` thread-internal.
-/

namespace EventStructure

variable (es : EventStructure)

/-- `j ∈ 𝕁` under sMRD's published Strengthening (Def. 4.11, the paper's
    `def:elab-str`): the new origins `S` are `⊑`-comparable with the justified
    write, `e ⊑ w ∨ w ⊑ e`, and not `≼`-after it. Every other rule is that of
    `Generated`. -/
inductive GeneratedStr (Ω : Pred) : Justification → Prop
  | pre {w : Event} {j : Justification} :
      w ∈ es.events → preJust w = some j → Sat w.valres.holds →
      GeneratedStr Ω j
  | va {j₁ : Justification} {o : MemOrd} {x e : Expr} {b : Bool} {α : Sym} {v : Val} :
      GeneratedStr Ω j₁ →
      j₁.w.kind = .write o x e b →
      EquivUnder j₁.P.holds (.sym α) (.val v) →
      Sat (Pred.and j₁.P.holds Ω) →
      GeneratedStr Ω
        { P := j₁.P
          D := (x.subst α (.val v)).syms ++ (e.subst α (.val v)).syms
          δ := j₁.δ
          w := { j₁.w with kind := .write o (x.subst α (.val v)) (e.subst α (.val v)) b } }
  /-- Strengthening as published: the new origins on either side of the
      write. -/
  | str {j₁ : Justification} (Q : Expr) (S : List EventId) :
      GeneratedStr Ω j₁ →
      (∀ e, e ∈ S ↔ e ∈ (strPred es j₁.P Q S).syms ∧ e ∉ j₁.P.syms) →
      (∀ e ∈ S, j₁.δ.Remap e e) →
      (∀ e ∈ S, (es.poR e j₁.w.id ∨ es.poR j₁.w.id e) ∧ ¬ es.ppo j₁.P.holds j₁.δ j₁.w.id e) →
      Sat (Pred.and (strPred es j₁.P Q S).holds Ω) →
      GeneratedStr Ω { j₁ with P := strPred es j₁.P Q S }
  | fwd {j₁ : Justification} {o : MemOrd} {x e : Expr} {b : Bool} {e₁ e₂ : EventId}
      {ev₁ ev₂ : Event} {v₁ v₂ : Expr} :
      GeneratedStr Ω j₁ →
      j₁.w.kind = .write o x e b →
      es.fwdRel j₁ e₁ e₂ →
      es.ev e₁ = some ev₁ → es.ev e₂ = some ev₂ →
      ev₁.val = some v₁ → ev₂.val = some v₂ →
      FwdCtx.WF { j₁.δ with f := j₁.δ.f ++ [(e₁, e₂)] } →
      Sat (Pred.and (j₁.P.replace v₂ v₁).holds Ω) →
      GeneratedStr Ω
        { P := j₁.P.replace v₂ v₁
          D := (e.replace v₂ v₁).syms ++ (x.replace v₂ v₁).syms
          δ := { j₁.δ with f := j₁.δ.f ++ [(e₁, e₂)] }
          w := { j₁.w with kind := .write o (x.replace v₂ v₁) (e.replace v₂ v₁) b } }
  | we {j₁ : Justification} {e₁ e₂ : EventId} :
      GeneratedStr Ω j₁ →
      es.weRel j₁ e₁ e₂ →
      FwdCtx.WF { j₁.δ with we := j₁.δ.we ++ [(e₂, e₁)] } →
      Sat (Pred.and j₁.P.holds Ω) →
      GeneratedStr Ω { j₁ with δ := { j₁.δ with we := j₁.δ.we ++ [(e₂, e₁)] } }
  | lift {j₁ j₂ : Justification} (Λ : Relabelling) :
      GeneratedStr Ω j₁ → GeneratedStr Ω j₂ →
      j₁.δ = j₂.δ →
      Λ.Injective →
      es.LiftBranch Λ j₁.w.id j₂.w.id →
      Λ.InjOn (j₁.P.syms ++ j₁.D) →
      es.ClosedRelabEq j₁.δ Λ j₁.P j₁.w j₂.P j₂.w →
      (∀ e, e ∈ j₂.D ↔ ∃ α ∈ j₁.D, Λ.app α = e) →
      (∀ α ∈ j₁.D, ∃ ev₁ ev₂, es.ev α = some ev₁ ∧ es.ev (Λ.app α) = some ev₂ ∧
        es.ClosedRelabEq j₁.δ Λ j₁.P ev₁ j₂.P ev₂) →
      ¬ es.cls Event.isVol j₁.w.id → ¬ es.cls Event.isVol j₂.w.id →
      (∀ α ∈ j₁.D ++ j₂.D, ¬ es.cls Event.isVol α) →
      (∀ α ∈ (j₁.P.rename Λ).syms, es.poR α j₂.w.id) →
      Sat (Pred.and (Expr.liftPred (j₁.P.rename Λ) j₂.P).holds Ω) →
      GeneratedStr Ω { j₂ with P := Expr.liftPred (j₁.P.rename Λ) j₂.P }
  | weak {j₁ : Justification} {P' Pw : Expr} :
      GeneratedStr Ω j₁ →
      j₁.P.ConjEq (.and P' Pw) →
      Entails Ω Pw.holds →
      Sat (Pred.and P'.holds Ω) →
      GeneratedStr Ω { j₁ with P := P' }

variable {es}

/-- **The restricted rule is an instance of the published one.** -/
theorem Generated.toStr {Ω : Pred} {j : Justification} (h : es.Generated Ω j) :
    es.GeneratedStr Ω j := by
  induction h with
  | pre hw hj hs => exact .pre hw hj hs
  | va _ hk hv hs ih => exact .va ih hk hv hs
  | str Q S _ hS hR hord hs ih =>
      exact .str Q S ih hS hR (fun e he => ⟨.inl (hord e he).1, (hord e he).2⟩) hs
  | fwd _ hk hf h₁ h₂ hv₁ hv₂ hwf hs ih => exact .fwd ih hk hf h₁ h₂ hv₁ hv₂ hwf hs
  | we _ hwe hwf hs ih => exact .we ih hwe hwf hs
  | lift Λ _ _ hδ hi hb hio hc hD hDc hv₁ hv₂ hvD hL hs ih₁ ih₂ =>
      exact .lift Λ ih₁ ih₂ hδ hi hb hio hc hD hDc hv₁ hv₂ hvD hL hs
  | weak _ hc he hs ih => exact .weak ih hc he hs

/-- Every symbol of `j`'s predicate, dependencies and expressions has its
    origin joinable with the justified event: some event lies at or
    `⊑`-above both. -/
def JoinPast (j : Justification) : Prop :=
  ∀ α, (α ∈ j.P.syms ∨ α ∈ j.D ∨ α ∈ j.w.exprSyms) → es.Joinable α j.w.id

theorem joinable_of_po_left (hpo : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    {a b c : EventId} (hab : es.poR a b) (h : es.Joinable b c) : es.Joinable a c := by
  obtain ⟨d, hb, hc⟩ := h
  refine ⟨d, .inr ?_, hc⟩
  rcases hb with rfl | hb
  · exact hab
  · exact hpo _ _ _ hab hb

theorem joinable_of_po (h : es.poR a b) : es.Joinable a b := ⟨b, .inr h, .inl rfl⟩

theorem joinable_of_po' (h : es.poR b a) : es.Joinable a b := ⟨a, .inl rfl, .inr h⟩

/-- **Every origin of a justification of `GeneratedStr` is joinable with its
    event**, given `SymWF` and the forwarding window. No hypothesis on the
    shape of `⊑`. -/
theorem GeneratedStr.joinPast {Ω : Pred} (hwf : es.SymWF)
    (hpo : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    {j : Justification} (h : es.GeneratedStr Ω j) : es.FwdWin j → es.JoinPast j := by
  induction h with
  | @pre w j hw hj _ =>
      intro _ α hα
      unfold preJust at hj
      split at hj <;> cases hj
      all_goals
        rename_i heq
        apply joinable_of_po
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
        · rcases (hord α ((hS α).2 ⟨h, hP⟩)).1 with h | h
          · exact joinable_of_po h
          · exact joinable_of_po' h
      · exact ih α (.inr h)
  | @fwd j₁ o x e b e₁ e₂ ev₁ ev₂ v₁ v₂ _ hk hf h₁ h₂ hv₁ hv₂ _ _ ih =>
      intro hW α hα
      have hW₁ : es.FwdWin j₁ := fun p hp => hW p (List.mem_append_left _ hp)
      have ih := ih hW₁
      have hwin := hW (e₁, e₂) (List.mem_append_right _ (List.mem_singleton_self _))
      obtain ⟨⟨⟨-, h12, -⟩, hcls, -⟩, -, -⟩ := hf
      have hsrc : es.cls Event.isWrite e₁ ∨ es.cls Event.isRead e₁ := by
        rcases hcls with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact .inl h
        · exact .inl h
        · exact .inr h
      have hv := val_src_po hwf hpo h₁ hv₁ hsrc h12
      have key : ∀ E : Expr, (∀ β ∈ E.syms, es.Joinable β j₁.w.id) →
          ∀ β ∈ (E.replace v₂ v₁).syms, es.Joinable β j₁.w.id := by
        intro E hE β hβ
        have via : es.Joinable e₂ j₁.w.id → es.Joinable β j₁.w.id := by
          intro h2
          rcases Expr.mem_syms_replace hβ with hβ | hβ
          · exact hE β hβ
          · exact joinable_of_po_left hpo (hv β hβ) h2
        by_cases hr : es.cls Event.isWrite e₂
        · exact via (by
            rcases hwin hr with h | h
            · exact joinable_of_po h
            · exact ⟨j₁.w.id, .inl h, .inl rfl⟩)
        · have hr₂ : es.cls Event.isRead e₂ := by
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
            · exact via (hγ ▸ hE γ hm)
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
  | @lift j₁ j₂ Λ _ _ _ _ _ _ _ _ _ _ _ _ hL _ _ ih₂ =>
      intro hW α hα
      have ih := ih₂ hW
      rcases hα with h | h
      · rcases List.mem_append.1 ((Expr.mem_syms_liftPred_iff _ _ α).1 h) with h | h
        · exact joinable_of_po (hL α h)
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

/-- A relation is **thread-internal** if it relates `⊑`-comparable events
    only, or an event to itself. -/
def ThreadInternal (es : EventStructure) (R : Rel) : Prop := ∀ a b, R a b → es.PoCmp a b

/-- `⊑`-forward relations are thread-internal. -/
theorem threadInternal_of_po {R : Rel} (h : ∀ a b, R a b → es.poR a b) : ThreadInternal es R :=
  fun a b hab => .inr (.inl (h a b hab))

/-- **`DP` relates joinable events**, for justifications generated under the
    published Strengthening, given `SymWF` and the store-store forwarding
    window. -/
theorem dp_joinable {Ω : Pred} (hJ : ∀ j ∈ x.J, es.GeneratedStr Ω j) (hwf : es.SymWF)
    (hpo : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hW : ∀ j ∈ x.J, es.FwdWin j) : ∀ a b, x.DP a b → es.Joinable a b := by
  rintro a b ⟨-, -, j, hj, rfl, hab⟩
  exact (hJ j hj).joinPast hwf hpo (hW j hj) a
    (by rcases hab with h | h; exact .inl h; exact .inr (.inl h))

/-- **`DP` is thread-internal** where `⊑` is a forest, under the published
    Strengthening: Strengthening's restriction to origins before the write
    (`cond:str-before`) is not needed, only its restriction to the write's
    thread. -/
theorem dp_thread {Ω : Pred} (hJ : ∀ j ∈ x.J, es.GeneratedStr Ω j) (hwf : es.SymWF)
    (hpo : ∀ a b c, es.poR a b → es.poR b c → es.poR a c) (hF : PoForest es)
    (hW : ∀ j ∈ x.J, es.FwdWin j) : ThreadInternal es x.DP := fun a b h => by
  obtain ⟨d, ha, hb⟩ := dp_joinable hJ hwf hpo hW a b h
  exact hF a b d ha hb

/-- `dp_thread` for the executions of the library. -/
theorem dp_thread_of_execution {Ω : Pred} (hx : x.IsExecution es Ω) (hwf : es.SymWF)
    (hpo : ∀ a b c, es.poR a b → es.poR b c → es.poR a c) (hF : PoForest es)
    (hW : ∀ j ∈ x.J, es.FwdWin j) : ThreadInternal es x.DP :=
  dp_thread (fun j hj => (hx.generated j hj).toStr) hwf hpo hF hW

/-- **`≼ ⊆ ⊑` under `FwdEntailsImg`**, with no hypothesis on `DP`. -/
theorem ppo_po_E {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hT : RMWTightR es x)
    (hsat : Sat (x.P es)) (hev : LocsEval es) (hE : FwdEntailsImg es x) (hR : NoRevRMW es x)
    {a b : EventId} (h : x.ppo es a b) : es.poR a b :=
  ppo_po hpo_trans (fun _ _ h => ppoStep_po_E hx hpo_trans hirr hT hsat hev hE hR h) h

/-- **`DP ∪ ≼` is thread-internal under the published Strengthening**: where
    `⊑` is a forest, given `SymWF`, the forwarding window, and `≼ ⊆ ⊑`. -/
theorem dep_thread_str {Ω : Pred} (hJ : ∀ j ∈ x.J, es.GeneratedStr Ω j) (hwf : es.SymWF)
    (hpo : ∀ a b c, es.poR a b → es.poR b c → es.poR a c) (hF : PoForest es)
    (hW : ∀ j ∈ x.J, es.FwdWin j) (hppo : ∀ a b, x.ppo es a b → es.poR a b) :
    ThreadInternal es (x.dep es) := by
  rintro a b (h | h)
  · exact .inr (.inl (hppo a b h))
  · exact dp_thread hJ hwf hpo hF hW a b h

/-- **`DP ∪ ≼` is thread-internal for the executions of the library**, under
    the hypotheses of `dep_po_E` with `DP ⊆ ⊑` derived (`Execution.dp_po`):
    there `DP ∪ ≼ ⊆ ⊑`. -/
theorem dep_thread_E {Ω : Pred} (hx : x.IsExecution es Ω) (hwf : es.SymWF)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hT : RMWTightR es x) (hFW : ∀ j ∈ x.J, es.FwdWin j)
    (hsat : Sat (x.P es)) (hev : LocsEval es) (hE : FwdEntailsImg es x) (hR : NoRevRMW es x) :
    ThreadInternal es (x.dep es) :=
  threadInternal_of_po fun _ _ h =>
    (dep_po_E hx hpo_trans hirr hT (dp_po hx hwf hpo_trans hFW) hsat hev hE hR h).2.2

end Execution
