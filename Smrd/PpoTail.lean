import Smrd.CoherenceRC11

/-!
# MoRDor's untruncated `≼`: program order, coherence conditions, No-Thin-Air

`Execution.ppo` is MoRDor's frozen `ppo`, whose synchronisation and location
parts are not cut to the justification windows (`Smrd.Executions`). This
module records what follows.

* `ppoStep_po`, `ppo_po`: without forwarding or write elision (`δ` has no
  edge) and with every RMW's read and write adjacent in `X ∪ X_F`
  (`RMWTight`), `≼ ⊆ ⊑`. Write elision alone breaks it: an initialising write
  elided by a thread's write remaps the initialising write's pairs onto that
  thread, across threads (`Smrd.PpoNecessity`, `ppo_cross_thread`).
* `poloc_dep`, `rel_dep`, `acq_dep`, `coherence_of_coherenceV_untrunc`:
  conditions (i) `⊑|loc ⊆ DP ∪ ≼` and (ii) `⊑;[W_rel] ⊆ DP ∪ ≼`,
  `[R_acq];⊑ ⊆ DP ∪ ≼` of `coherence_of_coherenceV` hold for fence-free
  executions without forwarding or elision; (i) needs a model of the combined
  predicate under which the locations of `X` evaluate (`LocModel`).
* `acyclic_iff_of_tail`, `noThinAir_iff_win`: where every step of `≼` lies in
  `⊑` and `DP ⊆ ⊑`, No-Thin-Air is the same over `≼` and over its cut to the
  justification windows (`ppoWin`): a pair the cut drops ends after the
  thread's last justified write, and no `DP ∪ ≼ ∪ rf` edge leaves that tail
  except `⊑`-forward within it.
-/

namespace Execution

variable {es : EventStructure} {x : Execution}

/-! ## The shared context -/

theorem mem_δ_f {j : Justification} (hj : j ∈ x.J) {p : EventId × EventId} (hp : p ∈ j.δ.f) :
    p ∈ x.δ.f := by
  obtain ⟨X, J, rf⟩ := x
  simp only [δ] at *
  induction J with
  | nil => cases hj
  | cons j' J ih =>
      rcases List.mem_cons.1 hj with rfl | hj
      · simp [FwdCtx.union, hp]
      · have := ih hj
        simp only [FwdCtx.union] at this ⊢
        exact List.mem_append_right _ this

/-- `ψ_δ` of the shared context entails each justification's `ψ_{δ_j}`. -/
theorem psi_of_mem {j : Justification} (hj : j ∈ x.J) {f : Valuation} (h : x.δ.psi es f) :
    j.δ.psi es f :=
  fun p hp => h p (mem_δ_f hj hp)

/-- MoRDor's combined predicate entails the frozen `P`. -/
theorem P_of_Pm {f : Valuation} (h : x.Pm es f) : x.P es f :=
  fun j hj => ⟨h.1 j hj, psi_of_mem hj h.2.1⟩

/-! ## `≼` within `⊑` -/

/-- The read and the write of each RMW are adjacent among the events of
    `X ∪ X_F`: only the branch of a `CAS` lies between them in `denote`. -/
def RMWTight (es : EventStructure) (x : Execution) : Prop :=
  (∀ ent ∈ es.rmw, ∀ a, x.XwF es a → es.poR a ent.w → a = ent.r ∨ es.poR a ent.r) ∧
  (∀ ent ∈ es.rmw, ∀ b, x.XwF es b → es.poR ent.r b → b = ent.w ∨ es.poR ent.w b)

theorem ppoM_po (hnoδ : ∀ a b, ¬ x.δ.edge a b) (hT : RMWTight es x) {Pa Pr : Pred}
    {a b : EventId} (ha : x.XwF es a) (hb : x.XwF es b) (h : es.ppoM Pa Pr x.δ a b) :
    es.poR a b := by
  obtain ⟨hr, hne⟩ := h
  have hab := (FwdCtx.remapRel_of_noEdge hnoδ).1 hr
  rcases hab with (hs | (⟨w, hs, ent, hm, hw, hr', -⟩ | ⟨r, ⟨ent, hm, hw, hr', -⟩, hs⟩)) | hal
  · exact hs.1
  · subst hw hr'
    rcases hT.1 ent hm a ha hs.1 with rfl | h
    · exact absurd rfl hne
    · exact h
  · subst hw hr'
    rcases hT.2 ent hm b hb hs.1 with rfl | h
    · exact absurd rfl hne
    · exact h
  · exact hal.1

/-- **Without forwarding or elision, each step of `≼` lies in `⊑`.** -/
theorem ppoStep_po (hnoδ : ∀ a b, ¬ x.δ.edge a b) (hT : RMWTight es x) {a b : EventId}
    (h : x.ppoStep es a b) : es.poR a b := by
  obtain ⟨ha, hb, ⟨j, -, hp, -⟩ | hs | ⟨hp, -⟩⟩ := h
  · exact ppoM_po hnoδ hT ha hb hp
  · exact ppoM_po hnoδ hT ha hb (es.ppoSyncRM_sub_ppoM (x.Pm es) (x.Pm es) x.δ _ _ hs)
  · exact ppoM_po hnoδ hT ha hb hp

theorem transGen_po (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    {R : Rel} (hR : ∀ a b, R a b → es.poR a b) {a b : EventId}
    (h : Relation.TransGen R a b) : es.poR a b := by
  induction h with
  | single h => exact hR _ _ h
  | tail _ h ih => exact hpo_trans _ _ _ ih (hR _ _ h)

/-- `≼ ⊆ ⊑` where every step of it is. -/
theorem ppo_po (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hstep : ∀ a b, x.ppoStep es a b → es.poR a b) {a b : EventId} (h : x.ppo es a b) :
    es.poR a b :=
  transGen_po hpo_trans hstep h.2.2

/-! ## Conditions (i) and (ii) -/

/-- A model of MoRDor's combined predicate under which every location of `X`
    evaluates. -/
def LocModel (es : EventStructure) (x : Execution) : Prop :=
  ∃ f, x.Pm es f ∧ ∀ a e l, x.X a → es.ev a = some e → e.loc = some l → (l.eval f).isSome

theorem X_of_XwF (hnf : x.FenceFree es) {a : EventId} (h : x.XwF es a) : x.X a := by
  rcases h with h | h
  · exact h
  · exact absurd h.2.1 (hnf a (.inr h))

theorem ppo_of_step {a b : EventId} (ha : x.X a) (hb : x.X b) (h : x.ppoStep es a b) :
    x.ppo es a b := ⟨ha, hb, .single h⟩

/-- **Condition (i)**, `⊑|loc ⊆ DP ∪ ≼`, for MoRDor's `≼`. -/
theorem poloc_dep (hnf : x.FenceFree es) (hirr : ∀ a, ¬ es.poR a a)
    (hnoδ : ∀ a b, ¬ x.δ.edge a b) (hm : LocModel es x)
    {a b : EventId} (h : x.poloc es a b) : x.dep es a b := by
  obtain ⟨⟨hXa, hXb, hpo⟩, ea, eb, la, lb, hea, heb, hla, hlb, heq⟩ := h
  have ha := X_of_XwF hnf hXa
  have hb := X_of_XwF hnf hXb
  obtain ⟨f, hP, hdef⟩ := hm
  obtain ⟨va, hva⟩ := Option.isSome_iff_exists.1 (hdef a ea la ha hea hla)
  obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.1 (hdef b eb lb hb heb hlb)
  have hv : va = vb := heq f (P_of_Pm hP) va vb hva hvb
  subst hv
  have hal : es.mayAlias (x.Pm es) a b :=
    ⟨ea, eb, la, lb, hea, heb, hla, hlb, f, hP, by
      simp [Expr.holds, Expr.eval, hva, hvb]⟩
  refine .inl (ppo_of_step ha hb ⟨hXa, hXb, .inr (.inr ⟨⟨?_, fun h => hirr a (h ▸ hpo)⟩, hal⟩)⟩)
  exact (FwdCtx.remapRel_of_noEdge hnoδ).2 (.inr ⟨hpo, .inr hal⟩)

/-- **Condition (ii), release half**, `⊑;[W_rel] ⊆ DP ∪ ≼`. -/
theorem rel_dep (hnf : x.FenceFree es) (hirr : ∀ a, ¬ es.poR a a)
    (hnoδ : ∀ a b, ¬ x.δ.edge a b)
    {a w : EventId} (h : x.poX es a w) (hw : es.cls Event.isRelW w) : x.dep es a w := by
  obtain ⟨hXa, hXw, hpo⟩ := h
  have hrel : es.cls Event.isRelM w := by
    obtain ⟨e, he, h⟩ := hw; exact ⟨e, he, by simp [Event.isRelM, h]⟩
  exact .inl (ppo_of_step (X_of_XwF hnf hXa) (X_of_XwF hnf hXw)
    ⟨hXa, hXw, .inr (.inl ⟨(FwdCtx.remapRel_of_noEdge hnoδ).2 ⟨hpo, .inr hrel⟩,
      fun h => hirr a (h ▸ hpo)⟩)⟩)

/-- **Condition (ii), acquire half**, `[R_acq];⊑ ⊆ DP ∪ ≼`. -/
theorem acq_dep (hnf : x.FenceFree es) (hirr : ∀ a, ¬ es.poR a a)
    (hnoδ : ∀ a b, ¬ x.δ.edge a b)
    {r b : EventId} (hr : es.cls Event.isAcqR r) (h : x.poX es r b) : x.dep es r b := by
  obtain ⟨hXr, hXb, hpo⟩ := h
  have hacq : es.cls Event.isAcqM r := by
    obtain ⟨e, he, h⟩ := hr; exact ⟨e, he, by simp [Event.isAcqM, h]⟩
  exact .inl (ppo_of_step (X_of_XwF hnf hXr) (X_of_XwF hnf hXb)
    ⟨hXr, hXb, .inr (.inl ⟨(FwdCtx.remapRel_of_noEdge hnoδ).2 ⟨hpo, .inl hacq⟩,
      fun h => hirr r (h ▸ hpo)⟩)⟩)

/-- **RC11 coherence from `HB_v`-coherence** for MoRDor's `≼`, for executions
    without fences, forwarding or elision, and with a location model. -/
theorem coherence_of_coherenceV_untrunc {co : Rel}
    (hnf : x.FenceFree es)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a)
    (hLtrans : ∀ a b c, x.sameLoc es a b → x.sameLoc es b c → x.sameLoc es a c)
    (hrfL : ∀ a b, x.rf a b → x.sameLoc es a b)
    (hcoL : ∀ a b, co a b → x.sameLoc es a b)
    (hnoδ : ∀ a b, ¬ x.δ.edge a b) (hm : LocModel es x)
    (h : x.CoherenceV es co) : x.Coherence es co :=
  coherence_of_coherenceV hnf hpo_trans hirr hLtrans hrfL hcoL
    (fun _ _ h => poloc_dep hnf hirr hnoδ hm h)
    (fun _ _ h hw => rel_dep hnf hirr hnoδ h hw)
    (fun _ _ hr h => acq_dep hnf hirr hnoδ hr h) h

/-- The converse, RC11 coherence to `HB_v`-coherence, where `DP ∪ ≼ ⊆ ⊑`:
    without forwarding or elision, with `RMWTight` and `DP ⊆ ⊑`. -/
theorem coherenceV_of_coherence_untrunc {co : Rel}
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hnoδ : ∀ a b, ¬ x.δ.edge a b) (hT : RMWTight es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b)
    (h : x.Coherence es co) : x.CoherenceV es co :=
  x.coherenceV_of_coherence es (fun a b hd => by
    rcases hd with hp | hd
    · exact ⟨.inl hp.1, .inl hp.2.1,
        ppo_po hpo_trans (fun _ _ h => ppoStep_po hnoδ hT h) hp⟩
    · exact ⟨.inl hd.1, .inl hd.2.1, hDP a b hd⟩) h

/-! ## No-Thin-Air -/

/-- An abstract form of the tail argument: `R` and `O ⊆ R` are acyclic together
    if every `R`-edge not in `O` ends in a set `T` that `R` leaves only
    `⊑`-forward into `T`, and `⊑` is a strict order. -/
theorem acyclic_iff_of_tail {R O : Rel} (T : EvSet)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a)
    (hOR : ∀ a b, O a b → R a b)
    (hedge : ∀ a b, R a b → O a b ∨ T b)
    (hstep : ∀ a b, T a → R a b → T b ∧ es.poR a b) :
    Rel.Acyclic R ↔ Rel.Acyclic O := by
  constructor
  · intro h a ha
    exact h a (transGen_mono hOR ha)
  · intro h c hc
    have path : ∀ a b, T a → Relation.TransGen R a b → T b ∧ es.poR a b := by
      intro a b ha hab
      induction hab with
      | single h => exact hstep _ _ ha h
      | tail _ h ih =>
          obtain ⟨hT, hpo⟩ := ih
          obtain ⟨hT', hpo'⟩ := hstep _ _ hT h
          exact ⟨hT', hpo_trans _ _ _ hpo hpo'⟩
    have key : ∀ a b, Relation.TransGen R a b → Relation.TransGen O a b ∨
        ∃ m, T m ∧ (m = b ∨ Relation.TransGen R m b) ∧ Relation.TransGen R a m := by
      intro a b hab
      induction hab with
      | single hs =>
          rcases hedge _ _ hs with ho | hT
          · exact .inl (.single ho)
          · exact .inr ⟨_, hT, .inl rfl, .single hs⟩
      | tail hp hs ih =>
          rcases ih with ho | ⟨m, hT, hmb, ham⟩
          · rcases hedge _ _ hs with ho' | hT
            · exact .inl (.tail ho ho')
            · exact .inr ⟨_, hT, .inl rfl, .tail hp hs⟩
          · refine .inr ⟨m, hT, .inr ?_, ham⟩
            rcases hmb with rfl | hmb
            · exact .single hs
            · exact .tail hmb hs
    rcases key c c hc with ho | ⟨m, hT, hmc, hcm⟩
    · exact h c ho
    · have hmm : Relation.TransGen R m m := by
        rcases hmc with rfl | hmc
        · exact hcm
        · exact transGen_trans hmc hcm
      exact hirr m (path m m hT hmm).2

/-- The tail of a thread: events not `⊑`-before or equal to a justified write. -/
def Tail (x : Execution) (es : EventStructure) (b : EventId) : Prop :=
  ¬ ∃ j ∈ x.J, Win es j b

theorem win_of_po (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    {j : Justification} {a b : EventId} (hab : es.poR a b) (hb : Win es j b) : Win es j a := by
  rcases hb with rfl | hb
  · exact .inr hab
  · exact .inr (hpo_trans _ _ _ hab hb)

theorem tail_of_po (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    {a b : EventId} (hab : es.poR a b) (ha : x.Tail es a) : x.Tail es b :=
  fun ⟨j, hj, hb⟩ => ha ⟨j, hj, win_of_po hpo_trans hab hb⟩

/-- The `ppo` cut to the windows is contained in it. -/
theorem ppoWin_sub {a b : EventId} (h : x.ppoWin es a b) : x.ppo es a b := by
  refine ⟨h.1, h.2.1, transGen_mono (fun c d hs => ?_) h.2.2⟩
  obtain ⟨hc, hd, hj | ⟨hp, -⟩⟩ := hs
  · exact ⟨hc, hd, .inl hj⟩
  · exact ⟨hc, hd, .inr hp⟩

/-- A pair of `≼` is in its cut to the windows unless it ends in the tail. -/
theorem ppo_win_or_tail (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hstep : ∀ a b, x.ppoStep es a b → es.poR a b) {a b : EventId} (h : x.ppo es a b) :
    x.ppoWin es a b ∨ x.Tail es b := by
  obtain ⟨ha, hb, h⟩ := h
  have one : ∀ c d, x.ppoStep es c d → x.ppoWinStep es c d ∨ x.Tail es d := by
    intro c d hs
    obtain ⟨hc, hd, hj | hp⟩ := hs
    · exact .inl ⟨hc, hd, .inl hj⟩
    · by_cases hT : x.Tail es d
      · exact .inr hT
      · obtain ⟨j, hj, hdj⟩ := Classical.not_not.1 hT
        have hcd := hstep c d ⟨hc, hd, .inr hp⟩
        exact .inl ⟨hc, hd, .inr ⟨hp, j, hj, win_of_po hpo_trans hcd hdj, hdj⟩⟩
  have gen : ∀ c d, Relation.TransGen (x.ppoStep es) c d →
      Relation.TransGen (x.ppoWinStep es) c d ∨ x.Tail es d := by
    intro c d hcd
    induction hcd with
    | single hs =>
        rcases one _ _ hs with h | h
        · exact .inl (.single h)
        · exact .inr h
    | tail _ hs ih =>
        rcases ih with h' | hT
        · rcases one _ _ hs with h'' | hT
          · exact .inl (.tail h' h'')
          · exact .inr hT
        · exact .inr (tail_of_po hpo_trans (hstep _ _ hs) hT)
  rcases gen a b h with h | h
  · exact .inl ⟨ha, hb, h⟩
  · exact .inr h

/-- The dependency order with `≼` cut to the windows. -/
def depWin (es : EventStructure) (x : Execution) : Rel := (x.ppoWin es).union x.DP

/-- **No-Thin-Air is the same over MoRDor's `≼` and its cut to the
    justification windows**, where every step of `≼` lies in `⊑`
    (`ppoStep_po`: no forwarding or elision; condition (1)) and `DP` does
    (`DP` origins `⊑`-before their write, condition (2)). The combined
    predicate (condition (3)) is built into `≼`. -/
theorem noThinAir_iff_win {Ω : Pred} (hx : x.IsExecution es Ω) (hphi : x.phi es)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a)
    (hstep : ∀ a b, x.ppoStep es a b → es.poR a b) (hDP : ∀ a b, x.DP a b → es.poR a b) :
    x.NoThinAir es ↔ Rel.Acyclic ((depWin es x).union x.rf) := by
  refine acyclic_iff_of_tail (x.Tail es) hpo_trans hirr ?_ ?_ ?_
  · rintro a b ((hw | hd) | hrf)
    · exact .inl (.inl (ppoWin_sub hw))
    · exact .inl (.inr hd)
    · exact .inr hrf
  · rintro a b ((hp | hd) | hrf)
    · rcases ppo_win_or_tail hpo_trans hstep hp with hw | hT
      · exact .inl (.inl (.inl hw))
      · exact .inr hT
    · exact .inl (.inl (.inr hd))
    · exact .inl (.inr hrf)
  · intro a b ha h
    have fwd : es.poR a b → x.Tail es b ∧ es.poR a b :=
      fun hpo => ⟨tail_of_po hpo_trans hpo ha, hpo⟩
    rcases h with (hp | hd) | hrf
    · exact fwd (ppo_po hpo_trans hstep hp)
    · exact fwd (hDP a b hd)
    · obtain ⟨hW, -, hXa, -⟩ := hx.rf_wr a b hrf
      have hnel : ¬ x.elided a := hphi.1 a (.inl ⟨b, hrf⟩)
      have hE : es.cls Event.isEffect a := by
        obtain ⟨e, he, hw⟩ := hW
        exact ⟨e, he, by simp [Event.isEffect, hw]⟩
      obtain ⟨j, hj, hjw, -⟩ := hx.justified a hXa hE hnel
      exact absurd ⟨j, hj, .inl hjw.symm⟩ ha

end Execution
