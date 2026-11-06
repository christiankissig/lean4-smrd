import Smrd.FenceMP
import Smrd.CoherenceT

/-!
# Store buffering under RC11's SC axiom

Store buffering, `x := 0; y := 0; (x := 1; r1 := y ∥ y := 1; r2 := x)` with
`r1 = r2 = 0`: both reads take the initialising writes. RC11's coherence and
atomicity axioms admit the outcome whatever the memory orders; only its SC
axiom (`Execution.PSC`, `acyclic(psc_base ∪ psc_F)`) can forbid it.

* **`sc` accesses** (`x :=_sc 1; r1 :=_sc y ∥ y :=_sc 1; r2 :=_sc x`,
  `sbSC_summary`): the execution satisfies `φ`, No-Thin-Air, Coherence and
  Atomicity under a coherence order, so the outcome was allowed before `PSC`.
  Coherence forces `x := 0` and `y := 0` `CO`-first, and
  `x := 1 →sb r1 →fr y := 1 →sb r2 →fr x := 1` is a `psc_base` cycle through
  `sc` accesses: `Coherent` and `CoherentT` fail.
* **relaxed accesses, `sc` fences between** (`sbF_summary`): likewise, with the
  cycle `F₁ →psc F₂ →psc F₁` of `psc_base` with fence ends,
  `F₁ ⊑ r1 →fr y := 1 ⊑ F₂` and `F₂ ⊑ r2 →fr x := 1 ⊑ F₁`.
* **relaxed accesses, no fences** (`sbRlx_summary`): the program has no `sc`
  event, `PSC` holds (`psc_of_noSC`), and the execution is consistent
  (`ConsistentT`, and RC11's `Consistent`).
-/

namespace PSCExamples

open EventStructure PpoKit PpoStability PpoNecessity Execution FenceMP

/-! ## Simple executions without synchronisation -/

/-- No `SW` where every write read from is, with every event `⊑`-before it,
    neither releasing write nor releasing fence, and `⊑` is transitive. -/
theorem sw_none {es : EventStructure} {rf : List (EventId × EventId)} (hr : es.rmw = [])
    (hsrc : ∀ p ∈ rf, ∀ a ∈ es.ids, (a = p.1 ∨ (a, p.1) ∈ es.po ∨
        ∃ q ∈ es.po, q.1 = a ∧ (q.2, p.1) ∈ es.po) →
      (clsB es Event.isRelW a || clsB es Event.isRelF a) = false)
    {a b : EventId} : ¬ (simple es rf).sw es a b := by
  rintro ⟨hrel, w, w', r, hw, ⟨-, w₀, h₀, -, hseq⟩, hrf, -⟩
  have hw' : w' = w₀ := by
    rcases hseq with h | h
    · exact h
    · exfalso
      have last : ∀ c d, Relation.TransGen ((simple es rf).rfRmw es) c d → False := by
        intro c d h
        cases h with
        | single s => obtain ⟨_, _, -, -, ent, hm, -⟩ := s; rw [hr] at hm; cases hm
        | tail _ s => obtain ⟨_, _, -, -, ent, hm, -⟩ := s; rw [hr] at hm; cases hm
      exact last _ _ h
  subst hw'
  have ha : a ∈ es.ids := by
    rcases hrel with h | h <;> exact clsB_id (cls_clsB.1 h)
  have key := hsrc (w', r) hrf a ha (by
    rcases hw with rfl | ⟨-, hpo⟩
    · rcases h₀ with rfl | hpl
      · exact .inl rfl
      · exact .inr (.inl hpl.1.2.2)
    · rcases h₀ with rfl | hpl
      · exact .inr (.inl hpo.2.2)
      · exact .inr (.inr ⟨(a, w), hpo.2.2, rfl, hpl.1.2.2⟩))
  rcases hrel with h | h <;> simp [cls_clsB.1 h] at key

/-- RC11's `HB` within `⊑` where there is no `SW`. -/
theorem hb_po {es : EventStructure} {rf : List (EventId × EventId)} (hpo : Closed es.po)
    (hsw : ∀ a b, ¬ (simple es rf).sw es a b) {a b : EventId}
    (h : (simple es rf).hb es a b) : (a, b) ∈ es.po :=
  transGen_mem (fun _ _ s => by
    rcases s with s | s
    · exact s.2.2
    · exact (hsw _ _ s).elim) hpo h

/-- RC11's coherence axiom where there is no `SW`, from a closed bound `E` on
    `ECO` that reverses no pair of `⊑`. -/
theorem coherence_of {es : EventStructure} {rf co E : List (EventId × EventId)}
    (hpo : Closed es.po) (hsw : ∀ a b, ¬ (simple es rf).sw es a b)
    (hE : ∀ p ∈ rf ++ co ++ frL rf co, p ∈ E) (hEc : Closed E)
    (hok : ∀ p ∈ es.po, p.1 ≠ p.2 ∧ (p.2, p.1) ∉ E) :
    (simple es rf).Coherence es (relL co) := by
  refine coherenceVOver_of (D := (simple es rf).poX es) (H := es.po) (E := E)
    (fun a b h => hb_po hpo hsw h) (fun a b h => ?_) hok
  refine eco_mem (fun c d h => hE _ ?_) (fun c d h => hE _ ?_) (fun c d h => hE _ ?_) hEc h
  · exact List.mem_append.2 (.inl (List.mem_append.2 (.inl h)))
  · exact List.mem_append.2 (.inl (List.mem_append.2 (.inr h)))
  · exact List.mem_append.2 (.inr (fr_mem h))

theorem atomicity_of {es : EventStructure} {rf : List (EventId × EventId)} (hr : es.rmw = [])
    (co : Rel) : (simple es rf).Atomicity es co := by
  rintro r w ⟨-, -, ent, hm, -⟩
  rw [hr] at hm; cases hm

/-- No-Thin-Air where `DP` is empty, `rf ⊆ ⊑`, and `⊑` is closed and
    irreflexive. -/
theorem nta_of {es : EventStructure} {rf : List (EventId × EventId)} (S : Simple es)
    (hg : GlobLocs es) (hd : ∀ j ∈ preJs es, j.P.syms = [] ∧ j.D = [])
    (hpo : Closed es.po) (hirr : ∀ p ∈ es.po, p.1 ≠ p.2)
    (hsub : ∀ p ∈ syncML es ++ aliasL es, p ∈ es.po) (hrf : ∀ p ∈ rf, p ∈ es.po) :
    (simple es rf).NoThinAir es := by
  intro a h
  have hm : (a, a) ∈ es.po := by
    refine transGen_mem (fun c d s => ?_) hpo h
    rcases s with (hp | hdp) | hr
    · exact transGen_mem (fun _ _ st =>
        hsub _ (ppoStep_mem S.normw hg (noEdge_simple es rf) st)) hpo hp.2.2
    · exact absurd hdp (dp_none hd)
    · exact hrf _ hr
  exact hirr _ hm rfl

/-- `psc_base` between two `sc` events of `D` along an `scb` edge. -/
theorem pscBase_sc {es : EventStructure} {x : Execution} {D : EvSet} {sb hb co : Rel}
    {a b : EventId} (ha : D a) (hsa : es.cls Event.isSC a) (hb' : D b)
    (hsb : es.cls Event.isSC b) (h : x.scbOf es sb hb co a b) :
    x.pscBaseOf es D sb hb co a b :=
  ⟨a, b, .inl ⟨rfl, ha, hsa⟩, h, .inl ⟨rfl, hb', hsb⟩⟩

/-! ## Store buffering with `sc` accesses -/

/-- `x := 0; y := 0; (x :=_sc 1; r1 :=_sc y ∥ y :=_sc 1; r2 :=_sc x)` -/
def sbSC : Stmt := .seq (st .rlx "x" 0) (.seq (st .rlx "y" 0)
  (.par (.seq (st .sc "x" 1) (ld .sc "r1" "y"))
        (.seq (st .sc "y" 1) (ld .sc "r2" "x"))))

def esSC : EventStructure :=
  ⟨[W 0 0 [0] .rlx "x" 0, W 1 0 [1, 0] .rlx "y" 0, W 2 0 [1, 1, 0, 0] .sc "x" 1,
    R 3 0 [1, 1, 0, 1] .sc "y", W 4 1 [1, 1, 1, 0] .sc "y" 1, R 5 1 [1, 1, 1, 1] .sc "x"],
   [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (4, 5)], []⟩

unseal interp in
theorem denote_sbSC : denote (fun _ => 0) sbSC = esSC := rfl

theorem S_SC : Simple esSC := ⟨by decide, by decide, rfl⟩
theorem g_SC : GlobLocs esSC := globLocs_of (by decide)

/-- `r1 = r2 = 0`: both reads take the initialising writes. -/
def rfSB : List (EventId × EventId) := [(1, 3), (0, 5)]
def coSB : List (EventId × EventId) := [(0, 2), (1, 4)]
def xSC : Execution := simple esSC rfSB

theorem exec_SC : xSC.IsExecution esSC (fun _ => True) ∧ xSC.phi esSC :=
  ⟨isExecution_simple S_SC (by decide),
   phi_simple S_SC (by decide) (by decide) (by decide) (fun _ => .num 0) (by decide)⟩

theorem sw_SC (a b : EventId) : ¬ xSC.sw esSC a b := sw_none rfl (by decide)

theorem X_SC : ∀ e ∈ esSC.events, xSC.X e.id :=
  fun e he => X_simple S_SC he (by revert e; decide) (by revert e; decide)

/-- **Coherence and Atomicity admit `r1 = r2 = 0`**, with No-Thin-Air and `φ`. -/
theorem sbSC_old :
    xSC.CoherenceOrder esSC (relL coSB) ∧ xSC.Coherence esSC (relL coSB) ∧
    xSC.Atomicity esSC (relL coSB) ∧ xSC.NoThinAir esSC :=
  ⟨coherenceOrder_simple S_SC g_SC exec_SC.2 (by decide) (by decide) (by decide) (by decide),
   coherence_of (E := [(1, 3), (0, 5), (0, 2), (1, 4), (3, 4), (5, 2)]) (by decide) sw_SC
     (by decide) (by decide) (by decide),
   atomicity_of rfl _,
   nta_of S_SC g_SC (by decide) (by decide) (by decide) (by decide) (by decide)⟩

/-- **The SC axiom forbids `r1 = r2 = 0`**, under every coherence order that
    satisfies Coherence. -/
theorem sbSC_not_psc {co : Rel} (hco : xSC.CoherenceOrder esSC co)
    (hcoh : xSC.Coherence esSC co) : ¬ xSC.PSC esSC co := by
  have X0 := X_SC (W 0 0 [0] .rlx "x" 0) (by simp [esSC])
  have X1 := X_SC (W 1 0 [1, 0] .rlx "y" 0) (by simp [esSC])
  have X2 := X_SC (W 2 0 [1, 1, 0, 0] .sc "x" 1) (by simp [esSC])
  have X3 := X_SC (R 3 0 [1, 1, 0, 1] .sc "y") (by simp [esSC])
  have X4 := X_SC (W 4 1 [1, 1, 1, 0] .sc "y" 1) (by simp [esSC])
  have X5 := X_SC (R 5 1 [1, 1, 1, 1] .sc "x") (by simp [esSC])
  have c02 : co 0 2 := by
    rcases hco.total 0 2 X0 X2 ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩ (by decide)
      (sameLoc_of rfl rfl rfl rfl) with h | h
    · exact h
    · exact (hcoh 0 ⟨2, .single (.inl (poX_of X0 X2 (show (0, 2) ∈ esSC.po by decide))),
        .inr (.single (.inl (.inr h)))⟩).elim
  have c14 : co 1 4 := by
    rcases hco.total 1 4 X1 X4 ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩ (by decide)
      (sameLoc_of rfl rfl rfl rfl) with h | h
    · exact h
    · exact (hcoh 1 ⟨4, .single (.inl (poX_of X1 X4 (show (1, 4) ∈ esSC.po by decide))),
        .inr (.single (.inl (.inr h)))⟩).elim
  -- `x := 1 →sb r1 →fr y := 1 →sb r2 →fr x := 1`
  have s1 : xSC.pscBaseOf esSC (xSC.XwF esSC) (xSC.poX esSC) (xSC.hb esSC) co 2 3 :=
    pscBase_sc (.inl X2) ⟨_, rfl, rfl⟩ (.inl X3) ⟨_, rfl, rfl⟩
    (.inl (poX_of X2 X3 (show (2, 3) ∈ esSC.po by decide)))
  have s2 : xSC.pscBaseOf esSC (xSC.XwF esSC) (xSC.poX esSC) (xSC.hb esSC) co 3 4 :=
    pscBase_sc (.inl X3) ⟨_, rfl, rfl⟩ (.inl X4) ⟨_, rfl, rfl⟩
    (.inr (.inr (.inr (.inr ⟨1, show (1, 3) ∈ rfSB by decide, c14⟩))))
  have s3 : xSC.pscBaseOf esSC (xSC.XwF esSC) (xSC.poX esSC) (xSC.hb esSC) co 4 5 :=
    pscBase_sc (.inl X4) ⟨_, rfl, rfl⟩ (.inl X5) ⟨_, rfl, rfl⟩
    (.inl (poX_of X4 X5 (show (4, 5) ∈ esSC.po by decide)))
  have s4 : xSC.pscBaseOf esSC (xSC.XwF esSC) (xSC.poX esSC) (xSC.hb esSC) co 5 2 :=
    pscBase_sc (.inl X5) ⟨_, rfl, rfl⟩ (.inl X2) ⟨_, rfl, rfl⟩
    (.inr (.inr (.inr (.inr ⟨0, show (0, 5) ∈ rfSB by decide, c02⟩))))
  intro h
  exact h 2 (.tail (.tail (.tail (.single (.inl s1)) (.inl s2)) (.inl s3)) (.inl s4))

/-- **Store buffering over `sc` accesses**: an execution with `r1 = r2 = 0`
    that satisfies `φ`, No-Thin-Air, Coherence and Atomicity under a coherence
    order, and is neither `Coherent` nor `CoherentT`: the SC axiom forbids it. -/
theorem sbSC_summary :
    xSC.IsExecution esSC (fun _ => True) ∧ xSC.phi esSC ∧ xSC.NoThinAir esSC ∧
    (∃ co, xSC.CoherenceOrder esSC co ∧ xSC.Coherence esSC co ∧ xSC.Atomicity esSC co) ∧
    ¬ xSC.Coherent esSC ∧ ¬ xSC.CoherentT esSC := by
  have hnc : ¬ xSC.Coherent esSC := by
    rintro ⟨co, ho, hc, -, hp⟩
    exact sbSC_not_psc ho hc hp
  exact ⟨exec_SC.1, exec_SC.2, sbSC_old.2.2.2, ⟨_, sbSC_old.1, sbSC_old.2.1, sbSC_old.2.2.1⟩,
    hnc, fun h => hnc ((coherentT_iff_coherent (not_elided_simple esSC rfSB)).1 h)⟩

/-! ## Store buffering with relaxed accesses and `sc` fences -/

theorem XF_of {es : EventStructure} {rf : List (EventId × EventId)} (S : Simple es) {e : Event}
    (he : e ∈ es.events) (hf : e.isFence = true) : (simple es rf).XF es e.id :=
  ⟨⟨e, he, rfl⟩, ⟨e, PpoKit.ev_of_mem S.nodup he, hf⟩, fun _ _ ⟨_, _, ha, hb, hn⟩ =>
    hn ⟨fun _ => .num 0, S.holds (ev_inv ha).1 _, S.holds (ev_inv hb).1 _⟩⟩

/-- `x := 0; y := 0; (x := 1; fence(sc); r1 := y ∥ y := 1; fence(sc); r2 := x)` -/
def sbF : Stmt := .seq (st .rlx "x" 0) (.seq (st .rlx "y" 0)
  (.par (.seq (st .rlx "x" 1) (.seq (.fence .sc) (ld .rlx "r1" "y")))
        (.seq (st .rlx "y" 1) (.seq (.fence .sc) (ld .rlx "r2" "x")))))

def esF : EventStructure :=
  ⟨[W 0 0 [0] .rlx "x" 0, W 1 0 [1, 0] .rlx "y" 0, W 2 0 [1, 1, 0, 0] .rlx "x" 1,
    Fe 3 0 [1, 1, 0, 1, 0] .sc, R 4 0 [1, 1, 0, 1, 1] .rlx "y",
    W 5 1 [1, 1, 1, 0] .rlx "y" 1, Fe 6 1 [1, 1, 1, 1, 0] .sc, R 7 1 [1, 1, 1, 1, 1] .rlx "x"],
   [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 2), (1, 3), (1, 4), (1, 5),
    (1, 6), (1, 7), (2, 3), (2, 4), (3, 4), (5, 6), (5, 7), (6, 7)], []⟩

unseal interp in
theorem denote_sbF : denote (fun _ => 0) sbF = esF := rfl

theorem S_F : Simple esF := ⟨by decide, by decide, rfl⟩
theorem g_F : GlobLocs esF := globLocs_of (by decide)

/-- `r1 = r2 = 0`. -/
def rfF : List (EventId × EventId) := [(1, 4), (0, 7)]
def coF : List (EventId × EventId) := [(0, 2), (1, 5)]
def xF : Execution := simple esF rfF

theorem exec_F : xF.IsExecution esF (fun _ => True) ∧ xF.phi esF :=
  ⟨isExecution_simple S_F (by decide),
   phi_simple S_F (by decide) (by decide) (by decide) (fun _ => .num 0) (by decide)⟩

theorem sw_F (a b : EventId) : ¬ xF.sw esF a b := sw_none rfl (by decide)

/-- **Coherence and Atomicity admit `r1 = r2 = 0`**, with No-Thin-Air and `φ`. -/
theorem sbF_old :
    xF.CoherenceOrder esF (relL coF) ∧ xF.Coherence esF (relL coF) ∧
    xF.Atomicity esF (relL coF) ∧ xF.NoThinAir esF :=
  ⟨coherenceOrder_simple S_F g_F exec_F.2 (by decide) (by decide) (by decide) (by decide),
   coherence_of (E := [(1, 4), (0, 7), (0, 2), (1, 5), (4, 5), (7, 2)]) (by decide) sw_F
     (by decide) (by decide) (by decide),
   atomicity_of rfl _,
   nta_of S_F g_F (by decide) (by decide) (by decide) (by decide) (by decide)⟩

/-- **The SC axiom forbids `r1 = r2 = 0`** through the `sc` fences, under every
    coherence order that satisfies Coherence. -/
theorem sbF_not_psc {co : Rel} (hco : xF.CoherenceOrder esF co)
    (hcoh : xF.Coherence esF co) : ¬ xF.PSC esF co := by
  have X : ∀ e ∈ esF.events, e.isFence = false → xF.X e.id :=
    fun e he hf => X_simple S_F he (by revert e; decide) hf
  have X0 := X (W 0 0 [0] .rlx "x" 0) (by simp [esF]) rfl
  have X1 := X (W 1 0 [1, 0] .rlx "y" 0) (by simp [esF]) rfl
  have X2 := X (W 2 0 [1, 1, 0, 0] .rlx "x" 1) (by simp [esF]) rfl
  have X4 := X (R 4 0 [1, 1, 0, 1, 1] .rlx "y") (by simp [esF]) rfl
  have X5 := X (W 5 1 [1, 1, 1, 0] .rlx "y" 1) (by simp [esF]) rfl
  have X7 := X (R 7 1 [1, 1, 1, 1, 1] .rlx "x") (by simp [esF]) rfl
  have F3 : xF.XF esF 3 := XF_of (e := Fe 3 0 [1, 1, 0, 1, 0] .sc) S_F (by simp [esF]) rfl
  have F6 : xF.XF esF 6 := XF_of (e := Fe 6 1 [1, 1, 1, 1, 0] .sc) S_F (by simp [esF]) rfl
  have c02 : co 0 2 := by
    rcases hco.total 0 2 X0 X2 ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩ (by decide)
      (sameLoc_of rfl rfl rfl rfl) with h | h
    · exact h
    · exact (hcoh 0 ⟨2, .single (.inl (poX_of X0 X2 (show (0, 2) ∈ esF.po by decide))),
        .inr (.single (.inl (.inr h)))⟩).elim
  have c15 : co 1 5 := by
    rcases hco.total 1 5 X1 X5 ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩ (by decide)
      (sameLoc_of rfl rfl rfl rfl) with h | h
    · exact h
    · exact (hcoh 1 ⟨5, .single (.inl (poX_of X1 X5 (show (1, 5) ∈ esF.po by decide))),
        .inr (.single (.inl (.inr h)))⟩).elim
  have hb34 : xF.hb esF 3 4 := .single (.inl ⟨.inr F3, .inl X4, show (3, 4) ∈ esF.po by decide⟩)
  have hb56 : xF.hb esF 5 6 := .single (.inl ⟨.inl X5, .inr F6, show (5, 6) ∈ esF.po by decide⟩)
  have hb67 : xF.hb esF 6 7 := .single (.inl ⟨.inr F6, .inl X7, show (6, 7) ∈ esF.po by decide⟩)
  have hb23 : xF.hb esF 2 3 := .single (.inl ⟨.inl X2, .inr F3, show (2, 3) ∈ esF.po by decide⟩)
  -- `F₁ ⊑ r1 →fr y := 1 ⊑ F₂` and `F₂ ⊑ r2 →fr x := 1 ⊑ F₁`
  have p1 : xF.pscBaseOf esF (xF.XwF esF) (xF.poX esF) (xF.hb esF) co 3 6 :=
    ⟨4, 5, .inr ⟨.inr F3, ⟨_, rfl, rfl⟩, .inr hb34⟩,
      .inr (.inr (.inr (.inr ⟨1, show (1, 4) ∈ rfF by decide, c15⟩))),
      .inr ⟨.inr F6, ⟨_, rfl, rfl⟩, .inr hb56⟩⟩
  have p2 : xF.pscBaseOf esF (xF.XwF esF) (xF.poX esF) (xF.hb esF) co 6 3 :=
    ⟨7, 2, .inr ⟨.inr F6, ⟨_, rfl, rfl⟩, .inr hb67⟩,
      .inr (.inr (.inr (.inr ⟨0, show (0, 7) ∈ rfF by decide, c02⟩))),
      .inr ⟨.inr F3, ⟨_, rfl, rfl⟩, .inr hb23⟩⟩
  intro h
  exact h 3 (.tail (.single (.inl p1)) (.inl p2))

/-- **Store buffering through `sc` fences**: allowed by `φ`, No-Thin-Air,
    Coherence and Atomicity, forbidden by the SC axiom. -/
theorem sbF_summary :
    xF.IsExecution esF (fun _ => True) ∧ xF.phi esF ∧ xF.NoThinAir esF ∧
    (∃ co, xF.CoherenceOrder esF co ∧ xF.Coherence esF co ∧ xF.Atomicity esF co) ∧
    ¬ xF.Coherent esF ∧ ¬ xF.CoherentT esF := by
  have hnc : ¬ xF.Coherent esF := by
    rintro ⟨co, ho, hc, -, hp⟩
    exact sbF_not_psc ho hc hp
  exact ⟨exec_F.1, exec_F.2, sbF_old.2.2.2, ⟨_, sbF_old.1, sbF_old.2.1, sbF_old.2.2.1⟩,
    hnc, fun h => hnc ((coherentT_iff_coherent (not_elided_simple esF rfF)).1 h)⟩

/-! ## Store buffering with relaxed accesses -/

/-- `x := 0; y := 0; (x := 1; r1 := y ∥ y := 1; r2 := x)` -/
def sbRlx : Stmt := .seq (st .rlx "x" 0) (.seq (st .rlx "y" 0)
  (.par (.seq (st .rlx "x" 1) (ld .rlx "r1" "y"))
        (.seq (st .rlx "y" 1) (ld .rlx "r2" "x"))))

def esRlx : EventStructure :=
  ⟨[W 0 0 [0] .rlx "x" 0, W 1 0 [1, 0] .rlx "y" 0, W 2 0 [1, 1, 0, 0] .rlx "x" 1,
    R 3 0 [1, 1, 0, 1] .rlx "y", W 4 1 [1, 1, 1, 0] .rlx "y" 1, R 5 1 [1, 1, 1, 1] .rlx "x"],
   [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (4, 5)], []⟩

unseal interp in
theorem denote_sbRlx : denote (fun _ => 0) sbRlx = esRlx := rfl

theorem S_Rlx : Simple esRlx := ⟨by decide, by decide, rfl⟩
theorem g_Rlx : GlobLocs esRlx := globLocs_of (by decide)

def xRlx : Execution := simple esRlx rfSB

theorem exec_Rlx : xRlx.IsExecution esRlx (fun _ => True) ∧ xRlx.phi esRlx :=
  ⟨isExecution_simple S_Rlx (by decide),
   phi_simple S_Rlx (by decide) (by decide) (by decide) (fun _ => .num 0) (by decide)⟩

/-- The program has no `sc` event. -/
theorem scFree_Rlx : esRlx.SCFree := esRlx.scFree_of_all (by decide)

theorem coherent_Rlx : xRlx.Coherent esRlx :=
  ⟨relL coSB,
   coherenceOrder_simple S_Rlx g_Rlx exec_Rlx.2 (by decide) (by decide) (by decide) (by decide),
   coherence_of (E := [(1, 3), (0, 5), (0, 2), (1, 4), (3, 4), (5, 2)]) (by decide)
     (fun _ _ => sw_none rfl (by decide)) (by decide) (by decide) (by decide),
   atomicity_of rfl _,
   xRlx.psc_of_noSC esRlx (xRlx.scFree_of_es esRlx scFree_Rlx) _⟩

/-- **Relaxed store buffering is still allowed**: the execution with
    `r1 = r2 = 0` is consistent, for sMRD (`ConsistentT`) and for RC11
    (`Consistent`). -/
theorem sbRlx_summary :
    xRlx.ConsistentT esRlx (fun _ => True) ∧ xRlx.Consistent esRlx (fun _ => True) := by
  have nta : xRlx.NoThinAir esRlx :=
    nta_of S_Rlx g_Rlx (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨⟨exec_Rlx.1, exec_Rlx.2, nta,
      (coherentT_iff_coherent (not_elided_simple esRlx rfSB)).2 coherent_Rlx⟩,
    ⟨exec_Rlx.1, exec_Rlx.2, nta, coherent_Rlx⟩⟩

end PSCExamples
