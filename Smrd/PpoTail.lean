import Smrd.CoherenceRC11

/-!
# MoRDor's untruncated `≼`: program order, coherence conditions, No-Thin-Air

`Execution.ppo` is MoRDor's frozen `ppo`, whose synchronisation and location
parts are not cut to the justification windows (`Smrd.Executions`). This
module records what follows.

* `ppoStep_po`, `ppo_po`: without forwarding or write elision (`δ` has no
  edge) and with every RMW's read and write adjacent in `X ∪ X_F`
  (`RMWTight`), `≼ ⊆ ⊑`.
* `ppoStep_cmp`: whatever `δ`, every step of `≼` relates `⊑`-comparable
  events, as the uncut parts are cut to `Anchored` pairs and `⊑` is a forest
  (`PoForest`): no pair of `≼` crosses threads.
* `ppoStep_po_we`, `dep_po_we`: **without forwarding, write elision allowed**,
  `DP ∪ ≼ ⊆ ⊑`, where no elision crosses an event (`NoCross`: an event
  `⊑`-between an elided write and the write it is elided into is elided into
  it too), and RMWs are tight through `remap_δ` (`RMWTightR`). Without
  `NoCross` a backward pair within the thread remains (an elision across a
  release write); Write Elision's release restriction excludes that one, and
  `Smrd.CoherenceT` weakens `NoCross` to `NoCrossLoc`. The initialising write of `x := 0; (x := 1 ∥ x := 2)` elided
  into `x := 1` is no longer a counterexample (`Smrd.PpoNecessity`,
  `ppo_cross_thread`).
* `coherenceV_of_coherence_we` (RC11 to `HB_v`, under the hypotheses of
  `dep_po_we`), `coherence_of_coherenceV_canon` (`HB_v` to RC11, forwarding
  and elision allowed where no event of the path is elided; it fails at an
  elided write, `Smrd.PpoNecessity.coww_elided`), `coherenceV_iff_coherence_we`.
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
  obtain ⟨ha, hb, ⟨j, -, hp, -⟩ | ⟨hs | ⟨hp, -⟩, -⟩⟩ := h
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

/-! ## `≼` within `⊑` under write elision

The cut to `Anchored` pairs makes every step of `≼` relate `⊑`-comparable
events, where `⊑` is a forest (`PoForest`: the `⊑`-down-set of an event is a
chain). `denote` builds a forest only without code after a parallel block:
`(P₁ ∥ P₂); κ` joins, and with Forwarding into `κ` a step of `≼` can relate
the two threads (`Smrd.FwdAcrossJoin`). The results here assume `PoForest`;
`Smrd.CoherenceT` drops it for executions, whose elaborations carry the join
restrictions (`remap_poCmp`). Without forwarding, `remap_δ` moves an event only
`⊑`-forward, to the write it is elided into (`WEForward`), so a remapped pair
`(a', b')` of a base pair `a ⊑ b` points backward only if the elision of `a`
crosses `b`: `a ⊑ b ⊑ remap_δ(a)` with `b` not elided into the same write.
`NoCross` excludes this, and `ppoStep_po_we` concludes `≼ ⊆ ⊑`.

Without `NoCross` the backward pairs are real, within one thread: in
`x := 1; y :rel= 1; x := 2` with `x := 1` elided into `x := 2` (its immediate
`≼`-predecessor at `x`, as `y :rel= 1` is not `≼`-before `x := 2`), the pair
`(x := 1, y :rel= 1)` of `ppo_sync` is remapped to `(x := 2, y :rel= 1)`.
-/

/-- A pair in one justification window is anchored at its justified write. -/
theorem anchored_of_inWin (hinX : ∀ j ∈ x.J, x.X j.w.id) {a b : EventId}
    (h : x.InWin es a b) : x.Anchored es a b := by
  obtain ⟨j, hj, ha, hb⟩ := h
  exact ⟨j.w.id, .inl (hinX j hj), ha, hb⟩

/-- `⊑` is a forest: the events at or below one event are pairwise
    comparable. -/
def PoForest (es : EventStructure) : Prop :=
  ∀ a b e, (a = e ∨ es.poR a e) → (b = e ∨ es.poR b e) → a = b ∨ es.poR a b ∨ es.poR b a

/-- Where `⊑` is a forest, joinable events are comparable. -/
theorem joinCmp_of_poForest (hF : PoForest es) (c e : EventId) : es.JoinCmp c e := by
  rintro ⟨d, hc, he⟩
  exact hF c e d hc he

/-- **The join restrictions are vacuous where `⊑` is a forest.** -/
theorem fwdNoJoin_of_poForest (hF : PoForest es) (e₁ e₂ : EventId) : es.fwdNoJoin e₁ e₂ :=
  fun c _ => joinCmp_of_poForest hF c e₁

theorem weNoJoin_of_poForest (hF : PoForest es) (e₁ e₂ : EventId) : es.weNoJoin e₁ e₂ :=
  fun c _ => joinCmp_of_poForest hF c e₂

/-- No forwarding, and every write elision `(e₂, e₁) ∈ WE` (`e₁` elided into
    `e₂`) is `⊑`-forward, `e₁ ⊑ e₂`. The second half holds of every execution,
    as Write Elision asks `e₁ ⊑ e₂` (`EventStructure.fwdBase`,
    `Execution.weForward_of_noFwd`). -/
def WEForward (es : EventStructure) (x : Execution) : Prop :=
  (∀ p ∈ x.δ.f, False) ∧ ∀ p ∈ x.δ.we, es.poR p.2 p.1

/-- No elision crosses an event: an event `⊑`-between an event and its image
    under `remap_δ` has the same image (it is elided into the same write). -/
def NoCross (es : EventStructure) (x : Execution) : Prop :=
  ∀ a a' c, x.δ.Remap a a' → es.poR a c → es.poR c a' → x.δ.Remap c a'

/-- `RMWTight` through `remap_δ`: an event `⊑`-before the write of an RMW
    whose image is on the path is its read or `⊑`-before it, and an event
    `⊑`-after the read whose image is on the path is its write or `⊑`-after
    it. -/
def RMWTightR (es : EventStructure) (x : Execution) : Prop :=
  (∀ ent ∈ es.rmw, ∀ a a', x.δ.Remap a a' → x.XwF es a' → es.poR a ent.w →
    a = ent.r ∨ es.poR a ent.r) ∧
  (∀ ent ∈ es.rmw, ∀ b b', x.δ.Remap b b' → x.XwF es b' → es.poR ent.r b →
    b = ent.w ∨ es.poR ent.w b)

/-- `RMWTight` is `RMWTightR` where `δ` has no edge. -/
theorem rmwTightR_of_noEdge (hnoδ : ∀ a b, ¬ x.δ.edge a b) (hT : RMWTight es x) :
    RMWTightR es x :=
  ⟨fun ent hm a a' hr ha' hpo => by
      rw [FwdCtx.Remap.eq_of_noEdge hnoδ hr] at ha'; exact hT.1 ent hm a ha' hpo,
   fun ent hm b b' hr hb' hpo => by
      rw [FwdCtx.Remap.eq_of_noEdge hnoδ hr] at hb'; exact hT.2 ent hm b hb' hpo⟩

/-- Where `δ` has no edge, no elision crosses an event. -/
theorem noCross_of_noEdge (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hnoδ : ∀ a b, ¬ x.δ.edge a b) : NoCross es x := by
  intro a a' c hr h₁ h₂
  rw [FwdCtx.Remap.eq_of_noEdge hnoδ hr] at h₂
  exact absurd (hpo_trans _ _ _ h₁ h₂) (hirr a)

theorem anchored_cmp (hF : PoForest es) {a b : EventId} (h : x.Anchored es a b) :
    a = b ∨ es.poR a b ∨ es.poR b a := by
  obtain ⟨e, -, ha, hb⟩ := h
  exact hF a b e ha hb

/-- Without forwarding, `remap_δ` moves events only `⊑`-forward. -/
theorem remap_fwd (hW : WEForward es x)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    {a a' : EventId} (h : x.δ.Remap a a') : a = a' ∨ es.poR a a' := by
  induction h with
  | canon _ => exact .inl rfl
  | @step c e e' he _ ih =>
      have hce : es.poR e c := by
        rcases he with hf | hw
        · exact (hW.1 _ hf).elim
        · exact hW.2 _ hw
      rcases ih with rfl | ih
      · exact .inr hce
      · exact .inr (hpo_trans _ _ _ hce ih)

/-- **A step of `ppoM`, anchored and on the path, lies in `⊑`** without
    forwarding, where no elision crosses an event. -/
theorem ppoM_po_we (hW : WEForward es x) (hu : ∀ a b e, x.δ.edge a e → x.δ.edge b e → a = b)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hN : NoCross es x) (hT : RMWTightR es x)
    {Pa Pr : Pred} {a' b' : EventId} (ha' : x.XwF es a') (hb' : x.XwF es b')
    (hA : x.Anchored es a' b') (h : es.ppoM Pa Pr x.δ a' b') : es.poR a' b' := by
  obtain ⟨⟨a, b, hab, ra, rb⟩, hne⟩ := h
  have hfun := fun {e e₁ e₂ : EventId} => @FwdCtx.Remap.functional x.δ hu e e₁ e₂
  -- the base pair is `⊑`-forward
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
  rcases anchored_cmp hF hA with h | h | h
  · exact absurd h hne
  · exact h
  · -- backward: the elision of `a` crosses `b`
    have hba' : es.poR b a' := by
      rcases remap_fwd hW hpo_trans rb with rfl | hbb
      · exact h
      · exact hpo_trans _ _ _ hbb h
    exact absurd (hfun rb (hN a a' b ra hbase hba')) (fun h => hne h.symm)

/-- **Without forwarding, each step of `≼` lies in `⊑`**, where no elision
    crosses an event (`NoCross`), `⊑` is a forest and RMWs are tight. -/
theorem ppoStep_po_we (hinX : ∀ j ∈ x.J, x.X j.w.id) (hW : WEForward es x)
    (hu : ∀ a b e, x.δ.edge a e → x.δ.edge b e → a = b)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hN : NoCross es x) (hT : RMWTightR es x)
    {a b : EventId} (h : x.ppoStep es a b) : es.poR a b := by
  obtain ⟨ha, hb, ⟨j, hj, hp, hwa, hwb⟩ | ⟨hs | ⟨hp, -⟩, hA⟩⟩ := h
  · exact ppoM_po_we hW hu hpo_trans hirr hF hN hT ha hb
      (anchored_of_inWin hinX ⟨j, hj, hwa, hwb⟩) hp
  · exact ppoM_po_we hW hu hpo_trans hirr hF hN hT ha hb hA
      (es.ppoSyncRM_sub_ppoM (x.Pm es) (x.Pm es) x.δ _ _ hs)
  · exact ppoM_po_we hW hu hpo_trans hirr hF hN hT ha hb hA hp

/-- Every step of `≼` relates `⊑`-comparable events, whatever `δ`. -/
theorem ppoStep_cmp (hinX : ∀ j ∈ x.J, x.X j.w.id) (hF : PoForest es) {a b : EventId}
    (h : x.ppoStep es a b) : es.poR a b ∨ es.poR b a := by
  have hne : a ≠ b := by
    obtain ⟨-, -, ⟨j, -, hp, -⟩ | ⟨hs | ⟨hp, -⟩, -⟩⟩ := h
    · exact hp.2
    · exact hs.2
    · exact hp.2
  have hA : x.Anchored es a b := by
    obtain ⟨-, -, ⟨j, hj, -, hwa, hwb⟩ | ⟨-, hA⟩⟩ := h
    · exact anchored_of_inWin hinX ⟨j, hj, hwa, hwb⟩
    · exact hA
  rcases anchored_cmp hF hA with h | h
  · exact absurd h hne
  · exact h

/-! ## Conditions (i) and (ii) -/

/-- A model of MoRDor's combined predicate and of `φ_rf` under which every
    location of `X` evaluates. -/
def LocModel (es : EventStructure) (x : Execution) : Prop :=
  ∃ f, x.Pm es f ∧ x.phiRf es f ∧
    ∀ a e l, x.X a → es.ev a = some e → e.loc = some l → (l.eval f).isSome

theorem X_of_XwF (hnf : x.FenceFree es) {a : EventId} (h : x.XwF es a) : x.X a := by
  rcases h with h | h
  · exact h
  · exact absurd h.2.1 (hnf a (.inr h))

theorem anchored_of_po {a b : EventId} (hb : x.XwF es b) (h : es.poR a b) :
    x.Anchored es a b := ⟨b, hb, .inr h, .inl rfl⟩

theorem ppo_of_step {a b : EventId} (ha : x.X a) (hb : x.X b) (h : x.ppoStep es a b) :
    x.ppo es a b := ⟨ha, hb, .single h⟩

/-- **Condition (i)**, `⊑|loc ⊆ DP ∪ ≼`, for MoRDor's `≼`. -/
theorem poloc_dep (hnf : x.FenceFree es) (hirr : ∀ a, ¬ es.poR a a)
    (hnoδ : ∀ a b, ¬ x.δ.edge a b) (hm : LocModel es x)
    {a b : EventId} (h : x.poloc es a b) : x.dep es a b := by
  obtain ⟨⟨hXa, hXb, hpo⟩, ea, eb, la, lb, hea, heb, hla, hlb, heq⟩ := h
  have ha := X_of_XwF hnf hXa
  have hb := X_of_XwF hnf hXb
  obtain ⟨f, hP, hrf, hdef⟩ := hm
  obtain ⟨va, hva⟩ := Option.isSome_iff_exists.1 (hdef a ea la ha hea hla)
  obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.1 (hdef b eb lb hb heb hlb)
  have hv : va = vb := Option.some.inj (hva ▸ hvb ▸ heq f (P_of_Pm hP) hrf)
  subst hv
  have hal : es.mayAlias (x.Pm es) a b :=
    ⟨ea, eb, la, lb, hea, heb, hla, hlb, f, hP, by
      simp [Expr.holds, Expr.eval, hva, hvb]⟩
  refine .inl (ppo_of_step ha hb ⟨hXa, hXb, .inr ⟨.inr ⟨⟨?_, fun h => hirr a (h ▸ hpo)⟩, hal⟩,
    anchored_of_po hXb hpo⟩⟩)
  exact (FwdCtx.remapRel_of_noEdge hnoδ).2 (.inr ⟨hpo, .inr hal⟩)

/-- **Condition (ii), release half**, `⊑;[W_rel] ⊆ DP ∪ ≼`. -/
theorem rel_dep (hnf : x.FenceFree es) (hirr : ∀ a, ¬ es.poR a a)
    (hnoδ : ∀ a b, ¬ x.δ.edge a b)
    {a w : EventId} (h : x.poX es a w) (hw : es.cls Event.isRelW w) : x.dep es a w := by
  obtain ⟨hXa, hXw, hpo⟩ := h
  have hrel : es.cls Event.isRelM w := by
    obtain ⟨e, he, h⟩ := hw; exact ⟨e, he, by simp [Event.isRelM, h]⟩
  exact .inl (ppo_of_step (X_of_XwF hnf hXa) (X_of_XwF hnf hXw)
    ⟨hXa, hXw, .inr ⟨.inl ⟨(FwdCtx.remapRel_of_noEdge hnoδ).2 ⟨hpo, .inr hrel⟩,
      fun h => hirr a (h ▸ hpo)⟩, anchored_of_po hXw hpo⟩⟩)

/-- **Condition (ii), acquire half**, `[R_acq];⊑ ⊆ DP ∪ ≼`. -/
theorem acq_dep (hnf : x.FenceFree es) (hirr : ∀ a, ¬ es.poR a a)
    (hnoδ : ∀ a b, ¬ x.δ.edge a b)
    {r b : EventId} (hr : es.cls Event.isAcqR r) (h : x.poX es r b) : x.dep es r b := by
  obtain ⟨hXr, hXb, hpo⟩ := h
  have hacq : es.cls Event.isAcqM r := by
    obtain ⟨e, he, h⟩ := hr; exact ⟨e, he, by simp [Event.isAcqM, h]⟩
  exact .inl (ppo_of_step (X_of_XwF hnf hXr) (X_of_XwF hnf hXb)
    ⟨hXr, hXb, .inr ⟨.inl ⟨(FwdCtx.remapRel_of_noEdge hnoδ).2 ⟨hpo, .inl hacq⟩,
      fun h => hirr r (h ▸ hpo)⟩, anchored_of_po hXb hpo⟩⟩)

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

/-! ## Both directions under write elision

RC11 to `HB_v` needs `DP ∪ ≼ ⊆ ⊑`, which holds without forwarding where no
elision crosses an event (`ppoStep_po_we`): `coherenceV_of_coherence_we`.

`HB_v` to RC11 needs conditions (i) and (ii), which hold between events that
are not elided (`†`), whatever `δ` (`poloc_dep_canon`, `rel_dep_canon`,
`acq_dep_canon`): such an event is its own image, and the base pair is
anchored at its later end. An elided write has no image of its own and lies
in no pair of `≼`, nor of `DP` (`φ`), so the conditions fail at it, and with
them the direction (`Smrd.PpoNecessity.coww_elided`: `x := 1; x := 2` with
`x := 1` elided and `CO` `2 < 1` is `HB_v`-coherent and not RC11-coherent).
`coherence_of_coherenceV_canon` asks that no event of the path is elided. -/

theorem remap_self_of_not_elided {a : EventId} (h : ¬ x.elided a) : x.δ.Remap a a :=
  .canon fun c hc => h ((x.elided_iff a).2 ⟨c, hc⟩)

/-- **Condition (i) between two events that are not elided**, whatever `δ`. -/
theorem poloc_dep_ne (hnf : x.FenceFree es) (hirr : ∀ a, ¬ es.poR a a) (hm : LocModel es x)
    {a b : EventId} (hna : ¬ x.elided a) (hnb : ¬ x.elided b) (h : x.poloc es a b) :
    x.dep es a b := by
  obtain ⟨⟨hXa, hXb, hpo⟩, ea, eb, la, lb, hea, heb, hla, hlb, heq⟩ := h
  have ha := X_of_XwF hnf hXa
  have hb := X_of_XwF hnf hXb
  obtain ⟨f, hP, hrf, hdef⟩ := hm
  obtain ⟨va, hva⟩ := Option.isSome_iff_exists.1 (hdef a ea la ha hea hla)
  obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.1 (hdef b eb lb hb heb hlb)
  have hv : va = vb := Option.some.inj (hva ▸ hvb ▸ heq f (P_of_Pm hP) hrf)
  subst hv
  have hal : es.mayAlias (x.Pm es) a b :=
    ⟨ea, eb, la, lb, hea, heb, hla, hlb, f, hP, by
      simp [Expr.holds, Expr.eval, hva, hvb]⟩
  exact .inl (ppo_of_step ha hb ⟨hXa, hXb, .inr ⟨.inr ⟨⟨⟨a, b, .inr ⟨hpo, .inr hal⟩,
    remap_self_of_not_elided hna, remap_self_of_not_elided hnb⟩,
    fun h => hirr a (h ▸ hpo)⟩, hal⟩, anchored_of_po hXb hpo⟩⟩)

/-- **Condition (i) between events that are not elided**, whatever `δ`. -/
theorem poloc_dep_canon (hnf : x.FenceFree es) (hirr : ∀ a, ¬ es.poR a a)
    (hcan : ∀ a, x.XwF es a → ¬ x.elided a) (hm : LocModel es x)
    {a b : EventId} (h : x.poloc es a b) : x.dep es a b :=
  poloc_dep_ne hnf hirr hm (hcan a h.1.1) (hcan b h.1.2.1) h

/-- **Condition (ii), release half, between two events that are not elided.** -/
theorem rel_dep_ne (hnf : x.FenceFree es) (hirr : ∀ a, ¬ es.poR a a)
    {a w : EventId} (hna : ¬ x.elided a) (hnw : ¬ x.elided w) (h : x.poX es a w)
    (hw : es.cls Event.isRelW w) : x.dep es a w := by
  obtain ⟨hXa, hXw, hpo⟩ := h
  have hrel : es.cls Event.isRelM w := by
    obtain ⟨e, he, h⟩ := hw; exact ⟨e, he, by simp [Event.isRelM, h]⟩
  exact .inl (ppo_of_step (X_of_XwF hnf hXa) (X_of_XwF hnf hXw)
    ⟨hXa, hXw, .inr ⟨.inl ⟨⟨a, w, ⟨hpo, .inr hrel⟩, remap_self_of_not_elided hna,
      remap_self_of_not_elided hnw⟩, fun h => hirr a (h ▸ hpo)⟩,
      anchored_of_po hXw hpo⟩⟩)

/-- **Condition (ii), release half, between events that are not elided.** -/
theorem rel_dep_canon (hnf : x.FenceFree es) (hirr : ∀ a, ¬ es.poR a a)
    (hcan : ∀ a, x.XwF es a → ¬ x.elided a)
    {a w : EventId} (h : x.poX es a w) (hw : es.cls Event.isRelW w) : x.dep es a w :=
  rel_dep_ne hnf hirr (hcan a h.1) (hcan w h.2.1) h hw

/-- **Condition (ii), acquire half, between two events that are not elided.** -/
theorem acq_dep_ne (hnf : x.FenceFree es) (hirr : ∀ a, ¬ es.poR a a)
    {r b : EventId} (hnr : ¬ x.elided r) (hnb : ¬ x.elided b)
    (hr : es.cls Event.isAcqR r) (h : x.poX es r b) : x.dep es r b := by
  obtain ⟨hXr, hXb, hpo⟩ := h
  have hacq : es.cls Event.isAcqM r := by
    obtain ⟨e, he, h⟩ := hr; exact ⟨e, he, by simp [Event.isAcqM, h]⟩
  exact .inl (ppo_of_step (X_of_XwF hnf hXr) (X_of_XwF hnf hXb)
    ⟨hXr, hXb, .inr ⟨.inl ⟨⟨r, b, ⟨hpo, .inl hacq⟩, remap_self_of_not_elided hnr,
      remap_self_of_not_elided hnb⟩, fun h => hirr r (h ▸ hpo)⟩,
      anchored_of_po hXb hpo⟩⟩)

/-- **Condition (ii), acquire half, between events that are not elided.** -/
theorem acq_dep_canon (hnf : x.FenceFree es) (hirr : ∀ a, ¬ es.poR a a)
    (hcan : ∀ a, x.XwF es a → ¬ x.elided a)
    {r b : EventId} (hr : es.cls Event.isAcqR r) (h : x.poX es r b) : x.dep es r b :=
  acq_dep_ne hnf hirr (hcan r h.1) (hcan b h.2.1) hr h

/-- **RC11 coherence from `HB_v`-coherence** where no event of the path is
    elided (forwarding and elision edges into events off the path allowed). -/
theorem coherence_of_coherenceV_canon {co : Rel}
    (hnf : x.FenceFree es)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a)
    (hLtrans : ∀ a b c, x.sameLoc es a b → x.sameLoc es b c → x.sameLoc es a c)
    (hrfL : ∀ a b, x.rf a b → x.sameLoc es a b)
    (hcoL : ∀ a b, co a b → x.sameLoc es a b)
    (hcan : ∀ a, x.XwF es a → ¬ x.elided a) (hm : LocModel es x)
    (h : x.CoherenceV es co) : x.Coherence es co :=
  coherence_of_coherenceV hnf hpo_trans hirr hLtrans hrfL hcoL
    (fun _ _ h => poloc_dep_canon hnf hirr hcan hm h)
    (fun _ _ h hw => rel_dep_canon hnf hirr hcan h hw)
    (fun _ _ hr h => acq_dep_canon hnf hirr hcan hr h) h

/-- **`DP ∪ ≼ ⊆ ⊑` without forwarding**, where no elision crosses an event. -/
theorem dep_po_we (hinX : ∀ j ∈ x.J, x.X j.w.id) (hW : WEForward es x)
    (hu : ∀ a b e, x.δ.edge a e → x.δ.edge b e → a = b)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hN : NoCross es x) (hT : RMWTightR es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b) {a b : EventId} (h : x.dep es a b) :
    x.poX es a b := by
  rcases h with hp | hd
  · exact ⟨.inl hp.1, .inl hp.2.1,
      ppo_po hpo_trans (fun _ _ h => ppoStep_po_we hinX hW hu hpo_trans hirr hF hN hT h) hp⟩
  · exact ⟨.inl hd.1, .inl hd.2.1, hDP a b hd⟩

/-- **RC11 coherence to `HB_v`-coherence without forwarding**, write elision
    allowed where it crosses no event. -/
theorem coherenceV_of_coherence_we {co : Rel} (hinX : ∀ j ∈ x.J, x.X j.w.id)
    (hW : WEForward es x) (hu : ∀ a b e, x.δ.edge a e → x.δ.edge b e → a = b)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hN : NoCross es x) (hT : RMWTightR es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b)
    (h : x.Coherence es co) : x.CoherenceV es co :=
  x.coherenceV_of_coherence es
    (fun _ _ hd => dep_po_we hinX hW hu hpo_trans hirr hF hN hT hDP hd) h

/-- `HB_v`-coherence and RC11 coherence coincide where no event of the path is
    elided and no forwarding or crossing elision is off it. -/
theorem coherenceV_iff_coherence_we {co : Rel} (hnf : x.FenceFree es)
    (hinX : ∀ j ∈ x.J, x.X j.w.id)
    (hW : WEForward es x) (hu : ∀ a b e, x.δ.edge a e → x.δ.edge b e → a = b)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hN : NoCross es x) (hT : RMWTightR es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b)
    (hLtrans : ∀ a b c, x.sameLoc es a b → x.sameLoc es b c → x.sameLoc es a c)
    (hrfL : ∀ a b, x.rf a b → x.sameLoc es a b)
    (hcoL : ∀ a b, co a b → x.sameLoc es a b)
    (hcan : ∀ a, x.XwF es a → ¬ x.elided a) (hm : LocModel es x) :
    x.CoherenceV es co ↔ x.Coherence es co :=
  ⟨coherence_of_coherenceV_canon hnf hpo_trans hirr hLtrans hrfL hcoL hcan hm,
   coherenceV_of_coherence_we hinX hW hu hpo_trans hirr hF hN hT hDP⟩

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
theorem ppoWin_sub (hinX : ∀ j ∈ x.J, x.X j.w.id) {a b : EventId} (h : x.ppoWin es a b) :
    x.ppo es a b := by
  refine ⟨h.1, h.2.1, transGen_mono (fun c d hs => ?_) h.2.2⟩
  obtain ⟨hc, hd, hj | ⟨hp, hw⟩⟩ := hs
  · exact ⟨hc, hd, .inl hj⟩
  · exact ⟨hc, hd, .inr ⟨hp, anchored_of_inWin hinX hw⟩⟩

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
        exact .inl ⟨hc, hd, .inr ⟨hp.1, j, hj, win_of_po hpo_trans hcd hdj, hdj⟩⟩
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

/-- `DP` leaves the head only where `DP ⊆ ⊑`: the origin of a dependency is
    `⊑`-before a justified write, so not in the tail. -/
theorem dp_not_tail (hDP : ∀ a b, x.DP a b → es.poR a b) :
    ∀ a b, x.DP a b → ¬ x.Tail es a := by
  rintro a b hd ht
  have hab := hDP a b hd
  obtain ⟨-, -, j, hj, hjb, -⟩ := hd
  exact ht ⟨j, hj, .inr (hjb ▸ hab)⟩

/-- **No-Thin-Air is the same over MoRDor's `≼` and its cut to the
    justification windows**, where every step of `≼` lies in `⊑`
    (`ppoStep_po`: no forwarding or elision; condition (1)) and no origin of
    `DP` lies in the tail (condition (2), implied by `DP ⊆ ⊑`, `dp_not_tail`,
    which `Smrd.DPPast` derives). The combined
    predicate (condition (3)) is built into `≼`. -/
theorem noThinAir_iff_win {Ω : Pred} (hx : x.IsExecution es Ω) (hphi : x.phi es)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a)
    (hstep : ∀ a b, x.ppoStep es a b → es.poR a b) (hDP : ∀ a b, x.DP a b → ¬ x.Tail es a) :
    x.NoThinAir es ↔ Rel.Acyclic ((depWin es x).union x.rf) := by
  refine acyclic_iff_of_tail (x.Tail es) hpo_trans hirr ?_ ?_ ?_
  · rintro a b ((hw | hd) | hrf)
    · exact .inl (.inl (ppoWin_sub hx.inX hw))
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
    · exact absurd ha (hDP a b hd)
    · obtain ⟨hW, -, hXa, -⟩ := hx.rf_wr a b hrf
      have hnel : ¬ x.elided a := hphi.1 a (.inl ⟨b, hrf⟩)
      have hE : es.cls Event.isEffect a := by
        obtain ⟨e, he, hw⟩ := hW
        exact ⟨e, he, by simp [Event.isEffect, hw]⟩
      obtain ⟨j, hj, hjw, -⟩ := hx.justified a hXa hE hnel
      exact absurd ⟨j, hj, .inl hjw.symm⟩ ha

/-- No-Thin-Air over `≼` and over its cut to the windows coincide **without
    forwarding**, write elision allowed where it crosses no event. -/
theorem noThinAir_iff_win_we {Ω : Pred} (hx : x.IsExecution es Ω) (hphi : x.phi es)
    (hW : WEForward es x)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hN : NoCross es x) (hT : RMWTightR es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b) :
    x.NoThinAir es ↔ Rel.Acyclic ((depWin es x).union x.rf) :=
  noThinAir_iff_win hx hphi hpo_trans hirr
    (fun _ _ h => ppoStep_po_we hx.inX hW hx.fwdWF.uniq hpo_trans hirr hF hN hT h)
    (dp_not_tail hDP)

end Execution
