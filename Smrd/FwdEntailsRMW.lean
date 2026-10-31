import Smrd.FwdEntails

/-!
# The RMW part of `NoRevLoc`

`dep_po_E` and `noRevLoc_of_fwdEntailsAll` (`Smrd.FwdEntails`) keep a
hypothesis `NoRevRMW`: no `⊑`-ordered pair with an RMW access is reversed by
`remap_δ`. This module settles it.

* `NoRevRMW` does not follow from the restrictions (`Smrd.RMWCross`):
  `y := 0; x := 1; FADD_rlx(y, 1); x := 2` with `x := 1` elided into `x := 2`
  across the FADD is a consistent execution with every restriction and
  `FwdEntailsAll`, where `NoRevRMW` and `NoRevLoc` fail. So
  `noRevLoc_of_fwdEntailsAll` has no version without an RMW hypothesis.
* `NoCrossRMW` (no `F ∪ WE` edge crosses an RMW access) is the extra
  condition that rules it out: it implies `NoRevRMW`
  (`noRevRMW_of_noCrossRMW`), hence `NoRevLoc` under `FwdEntailsAll`
  (`noRevLoc_of_fwdEntailsAll_noCrossRMW`).
* `DP ∪ ≼ ⊆ ⊑` does not need `NoRevRMW`: `≼` asks it only of the pairs of
  `ppo_rmw` (MoRDor's `ppo_sync ; rmw ∪ rmw ; ppo_sync`), and for these it
  follows from the restrictions, `pred` and the generating predicates, given
  that the read of an RMW `⊑`-precedes its write at the same location
  (`RMWWF`). `dep_po_R` is `dep_po_E` with `NoRevRMW` replaced by `RMWWF`.

## The `ppo_rmw` pairs

A pair `(a, e_r)` with `a` in `ppo_sync` before `e_w`: an acquire `a` is not
moved forward (`remap_acq_back`); for a release `e_w`, `a`'s chain enters the
up-set of `e_r` by a Write Elision edge `p -WE→ q` across `e_r`. `q` is not
`⊑`-between `e_r` and `e_w` (`RMWTightR`); if `e_w ⊑ q`, the elision crosses
the release `e_w` (`weNoRel`); if `q = e_w`, then `p` is elided into the
RMW's own write across its read, which is at `e_w`'s location, so `≼`-between
`p` and `e_w` in the generating justification, against `pred` (`no_cross`).

A pair `(e_w, b)` with `e_r` in `ppo_sync` before `b`: a release `b` is not
moved backward (`remap_rel_fwd`); for an acquire `e_r`, a Forwarding edge
across `e_r` is excluded by `fwdNoAcq`, so `b`'s chain stays in the up-set of
`e_r`, and ends at `e_r` itself or `⊑`-after `e_w` (`RMWTightR`). Ending at
`e_r`, its last edge forwards some `t ⊒ e_w` from `e_r`, across `e_w`, which is
at `e_r`'s location: against `pred` again.

`x := 1; FADD_rel(x, 1)` is the case `q = e_w`: `pred` refuses to elide
`x := 1` into the FADD's write (`RMWCross.not_weRel_fadd`).
-/

namespace Execution

open EventStructure

variable {es : EventStructure} {x : Execution}

/-- The read of each RMW `⊑`-precedes its write, and they are at one location
    outright. The interpreter generates both from one access. -/
def RMWWF (es : EventStructure) : Prop :=
  ∀ ent ∈ es.rmw, es.poR ent.r ent.w ∧ es.mustAlias ent.r ent.w

/-- An RMW access has no `F ∪ WE`-predecessor. -/
theorem rmw_canon {Ω : Pred} (hx : x.IsExecution es Ω) {e : EventId} (hr : es.RMWAcc e) :
    ∀ a, ¬ x.δ.edge a e :=
  fun a ha => rmw_not_elided hx ((x.elided_iff e).2 ⟨a, ha⟩) hr

/-- The last edge of a chain that moves its event. -/
theorem remap_last {δ : FwdCtx} {e e' : EventId} (h : δ.Remap e e') (hne : e ≠ e') :
    ∃ t, δ.edge e' t ∧ δ.Remap t e' := by
  induction h with
  | canon _ => exact absurd rfl hne
  | @step q e e' he hr ih =>
      by_cases hq : q = e'
      · subst hq; exact ⟨e, he, .step he hr⟩
      · exact ih hq

/-- **The first `ppo_rmw` pair is not reversed**: `(a, e_r)` with
    `a ≼_sync e_w`. -/
theorem rmwR_not_back {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hT : RMWTightR es x)
    (hev : LocsEval es) (hW : RMWWF es) {ent : RMWEntry} (hm : ent ∈ es.rmw)
    {a a' b' : EventId} {f : Valuation} (hs : es.ppoSyncM a ent.w) (hab : es.poR a ent.r)
    (ra : x.δ.Remap a a') (rb : x.δ.Remap ent.r b') (ha' : x.XwF es a') (hne : a' ≠ b')
    (H : ∀ s t, x.δ.edge s t → x.δ.Remap t a' →
      ∃ j₀ u v, EdgeGen es x j₀ s t u v ∧ PredOf es j₀ f) :
    ¬ es.poR b' a' := by
  intro hba
  have hu := hx.fwdWF.uniq
  have hfun := fun {e e₁ e₂ : EventId} => @FwdCtx.Remap.functional x.δ hu e e₁ e₂
  have accR : es.RMWAcc ent.r := ⟨ent, hm, .inl rfl⟩
  obtain rfl : ent.r = b' := remap_rmwAcc hx rb accR
  obtain ⟨hrw, hmust⟩ := hW ent hm
  rcases hs.2 with hacq | hrel
  · rcases remap_acq_back hx hpo_trans ra hacq with rfl | h
    · exact hirr _ (hpo_trans _ _ _ hab hba)
    · exact hirr _ (hpo_trans _ _ _ hab (hpo_trans _ _ _ hba h))
  · have hnot : ¬ (ent.r = a ∨ es.poR ent.r a) := by
      rintro (h | h)
      · rw [h] at hab; exact hirr _ hab
      · exact hirr _ (hpo_trans _ _ _ hab h)
    rcases remap_enter_up' hx hpo_trans ra (es.joinCmp_of_poCmp (.inr (.inr hab))) hnot (.inr hba)
      with hrr | ⟨q, p, hw, hpr, hrq, hpa⟩
    · exact hne (hfun hrr (.canon (rmw_canon hx accR)))
    · have hqp : x.δ.edge q p := .inr hw
      have hqa : x.δ.Remap q a' := remap_inv_step hu hqp hpa
      rcases hT.2 ent hm q a' hqa ha' hrq with rfl | hwq
      · -- `p` elided into the RMW's own write, across its read
        obtain ⟨j₀, u, v, hg, hf₀⟩ := H _ _ hqp hpa
        have hpq : es.poR p ent.w := we_po hx _ hw
        obtain ⟨rfl, rfl⟩ : u = p ∧ v = ent.w := by
          rcases hg.1 with ⟨-, rfl, rfl, hr⟩ | ⟨-, rfl, rfl, -⟩
          · exact absurd (hpo_trans _ _ _ hr.1.1.2.1 hpq) (hirr _)
          · exact ⟨rfl, rfl⟩
        obtain ⟨val, h₁, h₂⟩ := locVal_of_mustAlias hev hmust f
        refine no_cross hev hg.base hf₀ hpr hrw h₁ h₂ (c₀ := ent.r)
          (.canon fun e he => rmw_canon hx accR e (hg.sub _ _ he)) ?_ ?_
        · intro h; rw [h] at hpr; exact hirr _ hpr
        · intro h; rw [h] at hrw; exact hirr _ hrw
      · -- the elision crosses the release `e_w`
        obtain ⟨j₀, ⟨-, hnr, -⟩, -⟩ := we_edge hx hw
        exact hnr.2 ent.w (hpo_trans _ _ _ hpr hrw) hwq
          (cls_mono es (fun _ h => Event.publishes_of_isRelM h) hrel)

/-- **The second `ppo_rmw` pair is not reversed**: `(e_w, b)` with
    `e_r ≼_sync b`. -/
theorem rmwW_not_back {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hT : RMWTightR es x)
    (hev : LocsEval es) (hW : RMWWF es) {ent : RMWEntry} (hm : ent ∈ es.rmw)
    {b a' b' : EventId} {f : Valuation} (hs : es.ppoSyncM ent.r b) (hwb : es.poR ent.w b)
    (ra : x.δ.Remap ent.w a') (rb : x.δ.Remap b b') (hb' : x.XwF es b') (hne : a' ≠ b')
    (H : ∀ s t, x.δ.edge s t → x.δ.Remap t b' →
      ∃ j₀ u v, EdgeGen es x j₀ s t u v ∧ PredOf es j₀ f) :
    ¬ es.poR b' a' := by
  intro hba
  have hu := hx.fwdWF.uniq
  have accR : es.RMWAcc ent.r := ⟨ent, hm, .inl rfl⟩
  have accW : es.RMWAcc ent.w := ⟨ent, hm, .inr rfl⟩
  obtain rfl : ent.w = a' := remap_rmwAcc hx ra accW
  obtain ⟨hrw, hmust⟩ := hW ent hm
  rcases hs.2 with hacq | hrel
  · -- `b`'s chain ends at `e_r`: its last edge forwards from `e_r` across `e_w`
    have atR : b' = ent.r → False := by
      rintro rfl
      have hbr : b ≠ ent.r := fun h => by rw [h] at hs; exact hirr _ hs.1
      obtain ⟨t, het, hrt⟩ := remap_last rb hbr
      rcases edge_cases hx het with ⟨hf, hrt'⟩ | ⟨hw, -⟩
      · rcases hT.2 ent hm t ent.r hrt hb' hrt' with rfl | hwt
        · exact rmw_canon hx accW _ het
        · obtain ⟨j₀, u, v, hg, hf₀⟩ := H _ _ het hrt
          obtain ⟨rfl, rfl⟩ : u = ent.r ∧ v = t := by
            rcases hg.1 with ⟨-, rfl, rfl, -⟩ | ⟨-, rfl, rfl, hr⟩
            · exact ⟨rfl, rfl⟩
            · exact absurd (hpo_trans _ _ _ hr.1.1.2.1 hrt') (hirr _)
          obtain ⟨val, h₁, h₂⟩ := locVal_of_mustAlias hev hmust f
          have ht : locVal es f v = some val := by rw [← (hg.loc hev hf₀).1]; exact h₁
          refine no_cross hev hg.base hf₀ hrw hwt h₂ ht (c₀ := ent.w)
            (.canon fun e he => rmw_canon hx accW e (hg.sub _ _ he)) ?_ ?_
          · intro h; rw [h] at hrw; exact hirr _ hrw
          · intro h; rw [h] at hwt; exact hirr _ hwt
      · obtain ⟨j₀, ⟨⟨-, -, hwr, -⟩, -⟩, -⟩ := we_edge hx hw
        exact cls_excl es (fun e h₁ h₂ => by
          rw [Event.not_write_of_isAcqM h₁] at h₂; cases h₂) hacq hwr
    rcases remap_stay_up' hx hpo_trans rb (c := ent.r) (.inr hs.1) with
      (heq | hrb') | hrr | ⟨q, p, hf, hqr, hrp, -⟩
    · exact atR heq.symm
    · rcases hT.2 ent hm b' b' (.canon (canon_of_remap rb)) hb' hrb' with h | h
      · exact hne h.symm
      · exact hirr _ (hpo_trans _ _ _ h hba)
    · exact atR (remap_rmwAcc hx hrr accR).symm
    · obtain ⟨j₀, -, hna, -⟩ := fwd_edge hx hf
      exact (hna.2.2 ent.r hqr hrp).1 (cls_mono es (fun _ h => acquires_of_isAcqM h) hacq)
  · rcases remap_rel_fwd hx hpo_trans rb hrel with rfl | h
    · exact hirr _ (hpo_trans _ _ _ hwb hba)
    · exact hirr _ (hpo_trans _ _ _ hwb (hpo_trans _ _ _ h hba))

/-- `ppoM_po_E` without `NoRevRMW`: the `ppo_rmw` pairs are not reversed
    under `RMWWF`, given a valuation that satisfies the generating predicates
    of the edges on the chains into `a'` and `b'`. -/
theorem ppoM_po_R {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hT : RMWTightR es x)
    (hev : LocsEval es) (hW : RMWWF es)
    {Pa Pr : Pred} {a' b' : EventId} {f : Valuation}
    (H : ∀ s t, x.δ.edge s t → (x.δ.Remap t a' ∨ x.δ.Remap t b') →
      ∃ j₀ u v, EdgeGen es x j₀ s t u v ∧ PredOf es j₀ f)
    (hAl : ∀ a b, es.poR a b → (es.mustAlias a b ∨ es.mayAlias Pa a b) →
      x.δ.Remap a a' → x.δ.Remap b b' → a' ≠ b' → ¬ es.poR b' a')
    (ha' : x.XwF es a') (hb' : x.XwF es b')
    (hA : x.Anchored es a' b') (h : es.ppoM Pa Pr x.δ a' b') : es.poR a' b' := by
  obtain ⟨⟨a, b, hab, ra, rb⟩, hne⟩ := h
  have hfun := fun {e e₁ e₂ : EventId} => @FwdCtx.Remap.functional x.δ hx.fwdWF.uniq e e₁ e₂
  have hbase : es.poR a b := by
    rcases hab with (hs | (⟨w, hs, ent, hm, hw, hr', -⟩ | ⟨r, ⟨ent, hm, hw, hr', -⟩, hs⟩)) | hal
    · exact hs.1
    · subst hw hr'
      rcases hT.1 ent hm a a' ra ha' hs.1 with rfl | h
      · exact absurd (hfun ra rb) hne
      · exact h
    · subst hw hr'
      rcases hT.2 ent hm b b' rb hb' hs.1 with rfl | h
      · exact absurd (hfun ra rb) hne
      · exact h
    · exact hal.1
  rcases remap_poCmp hx (.inr (.inl hbase)) ra rb (joinable_of_anchored hA) with h | h | h
  · exact absurd h hne
  · exact h
  · refine absurd h ?_
    rcases hab with (hs | (⟨w, hs, ent, hm, hw, hr', -⟩ | ⟨r, ⟨ent, hm, hw, hr', -⟩, hs⟩)) | hal
    · exact sync_not_back hx hpo_trans hirr hs ra rb hne
    · subst hw hr'
      exact rmwR_not_back hx hpo_trans hirr hT hev hW hm hs hbase ra rb ha' hne
        fun s t he ht => H s t he (.inl ht)
    · subst hw hr'
      exact rmwW_not_back hx hpo_trans hirr hT hev hW hm hs hbase ra rb hb' hne
        fun s t he ht => H s t he (.inr ht)
    · exact hAl a b hbase hal.2 ra rb hne

/-- **Each step of `≼` lies in `⊑` under `FwdEntailsImg` and `RMWWF`.** -/
theorem ppoStep_po_R {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hT : RMWTightR es x)
    (hsat : Sat (x.P es)) (hev : LocsEval es) (hE : FwdEntailsImg es x) (hW : RMWWF es)
    {a b : EventId} (h : x.ppoStep es a b) : es.poR a b := by
  obtain ⟨ha, hb, ⟨j, hj, hp, hwa, hwb⟩ | ⟨hs | ⟨hp, hal'⟩, hA⟩⟩ := h
  · -- the generating predicates of the edges into the window of `j`, under `P_j ∧ ψ_δ`
    have Hj : ∀ f, x.PJ es j f → ∀ s t, x.δ.edge s t → (x.δ.Remap t a ∨ x.δ.Remap t b) →
        ∃ j₀ u v, EdgeGen es x j₀ s t u v ∧ PredOf es j₀ f := fun f hf s t he ht => by
      obtain ⟨j₀, u, v, hg, hJ, -⟩ := hE s t he
      refine ⟨j₀, u, v, hg, hJ j hj ?_ f hf⟩
      rcases ht with ht | ht
      · exact ⟨_, ht, hwa⟩
      · exact ⟨_, ht, hwb⟩
    obtain ⟨f₀, hf₀⟩ := hsat
    refine ppoM_po_R hx hpo_trans hirr hT hev hW (Hj f₀ (PJ_of_P hf₀ hj)) ?_ ha hb
      (anchored_of_inWin hx.inX ⟨j, hj, hwa, hwb⟩) hp
    intro a₀ b₀ hab hal ra rb hne
    obtain ⟨f, hf, val, h₁, h₂⟩ : ∃ f, x.PJ es j f ∧ ∃ v, locVal es f a₀ = some v ∧
        locVal es f b₀ = some v := by
      rcases hal with hm | hm
      · exact ⟨f₀, PJ_of_P hf₀ hj, locVal_of_mustAlias hev hm f₀⟩
      · exact of_mayAlias hm
    exact noRev_of_edges hx hpo_trans hirr hev hab ra rb hne h₁ h₂ (Hj f hf)
  · exact ppoSyncRM_po_T hx hpo_trans hirr hA hs
  · -- the generating predicates of every edge, under `p_combined`
    have Hm : ∀ f, x.Pm es f → ∀ s t, x.δ.edge s t → (x.δ.Remap t a ∨ x.δ.Remap t b) →
        ∃ j₀ u v, EdgeGen es x j₀ s t u v ∧ PredOf es j₀ f := fun f hf s t he _ => by
      obtain ⟨j₀, u, v, hg, -, hm⟩ := hE s t he
      exact ⟨j₀, u, v, hg, hm f hf⟩
    obtain ⟨f₀, hf₀, -⟩ := of_mayAlias hal'
    refine ppoM_po_R hx hpo_trans hirr hT hev hW (Hm f₀ hf₀) ?_ ha hb hA hp
    intro a₀ b₀ hab hal ra rb hne
    obtain ⟨f, hf, val, h₁, h₂⟩ : ∃ f, x.Pm es f ∧ ∃ v, locVal es f a₀ = some v ∧
        locVal es f b₀ = some v := by
      rcases hal with hm | hm
      · exact ⟨f₀, hf₀, locVal_of_mustAlias hev hm f₀⟩
      · exact of_mayAlias hm
    exact noRev_of_edges hx hpo_trans hirr hev hab ra rb hne h₁ h₂ (Hm f hf)

/-- **`DP ∪ ≼ ⊆ ⊑` under `FwdEntailsImg`, without `NoRevRMW`**: `dep_po_E`
    with `NoRevRMW` replaced by `RMWWF`. -/
theorem dep_po_R {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hT : RMWTightR es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b) (hsat : Sat (x.P es)) (hev : LocsEval es)
    (hE : FwdEntailsImg es x) (hW : RMWWF es) {a b : EventId} (h : x.dep es a b) :
    x.poX es a b := by
  rcases h with hp | hd
  · exact ⟨.inl hp.1, .inl hp.2.1,
      ppo_po hpo_trans (fun _ _ h => ppoStep_po_R hx hpo_trans hirr hT hsat hev hE hW h) hp⟩
  · exact ⟨.inl hd.1, .inl hd.2.1, hDP a b hd⟩

/-- `dep_po_R` from a consistent execution: `φ` gives the model of `P`. -/
theorem dep_po_R_of_phi {Ω : Pred} (hx : x.IsExecution es Ω) (hphi : x.phi es)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hT : RMWTightR es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b) (hev : LocsEval es)
    (hE : FwdEntailsImg es x) (hW : RMWWF es) {a b : EventId} (h : x.dep es a b) :
    x.poX es a b :=
  dep_po_R hx hpo_trans hirr hT hDP (by obtain ⟨-, -, f, hf, -⟩ := hphi; exact ⟨f, hf⟩)
    hev hE hW h

/-! ## `NoRevRMW` itself -/

/-- **No `F ∪ WE` edge crosses an RMW access**: no RMW access lies strictly
    `⊑`-between the two ends of an edge. Stronger than the restrictions:
    MoRDor elides `x := 1` into `x := 2` across `FADD_rlx(y, 1)`
    (`Smrd.RMWCross`). -/
def NoCrossRMW (es : EventStructure) (x : Execution) : Prop :=
  ∀ s t c, x.δ.edge s t → ((es.poR s c ∧ es.poR c t) ∨ (es.poR t c ∧ es.poR c s)) →
    ¬ es.RMWAcc c

theorem noCrossRMW_of_nil (h : es.rmw = []) : NoCrossRMW es x :=
  fun _ _ c _ _ => es.not_rmwAcc_of_nil h c

/-- **`NoCrossRMW` implies `NoRevRMW`**: an RMW access is its own image, so a
    reversal moves the other event across it, by a Forwarding edge (from after
    to before) or a Write Elision edge (from before to after). -/
theorem noRevRMW_of_noCrossRMW {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hN : NoCrossRMW es x) : NoRevRMW es x := by
  intro a b a' b' hab ra rb hr hba
  rcases hr with hr | hr
  · obtain rfl : a = a' := remap_rmwAcc hx ra hr
    rcases remap_stay_up' hx hpo_trans rb (c := a) (.inr hab) with
      (heq | hab') | hra | ⟨q, p, hf, hqa, hap, -⟩
    · rw [heq] at hba; exact hirr _ hba
    · exact hirr _ (hpo_trans _ _ _ hab' hba)
    · rw [remap_rmwAcc hx hra hr] at hba; exact hirr _ hba
    · exact hN q p a (.inl hf) (.inl ⟨hqa, hap⟩) hr
  · obtain rfl : b = b' := remap_rmwAcc hx rb hr
    have hnot : ¬ (b = a ∨ es.poR b a) := by
      rintro (h | h)
      · rw [h] at hab; exact hirr _ hab
      · exact hirr _ (hpo_trans _ _ _ hab h)
    rcases remap_enter_up' hx hpo_trans ra (es.joinCmp_of_poCmp (.inr (.inr hab))) hnot (.inr hba)
      with hrb | ⟨q, p, hw, hpb, hbq, -⟩
    · rw [← remap_rmwAcc hx hrb hr] at hba; exact hirr _ hba
    · exact hN q p b (.inr hw) (.inr ⟨hpb, hbq⟩) hr

/-- **`FwdEntailsAll` and `NoCrossRMW` imply `NoRevLoc`.** `FwdEntailsAll`
    alone does not (`RMWCross.fwdEntailsAll_not_noRevLoc`). -/
theorem noRevLoc_of_fwdEntailsAll_noCrossRMW {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hsat : Sat (x.P es)) (hev : LocsEval es)
    (hE : FwdEntailsAll es x) (hN : NoCrossRMW es x) : NoRevLoc es x :=
  noRevLoc_of_fwdEntailsAll hx hpo_trans hirr hsat hev hE
    (noRevRMW_of_noCrossRMW hx hpo_trans hirr hN)

end Execution
