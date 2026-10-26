import Smrd.PpoNecessity
import Smrd.CoherenceT

/-!
# Write elision across a release (MoRDor #207)

`x := 0; flag := 0; (x :=rlx 1; flag :=rel 1; x :=rlx 2 ∥ r1 :=acq flag; r2 :=rlx x)`,
MoRDor's `litmus-tests/own/WE-across-release.lit`. RC11 forbids
`r1 = 1 ∧ r2 = 0`: `x := 1 ⊑ flag := 1 →sw r1 ⊑ r2`, and `r2` reading the
initial write puts it `FR`-before `x := 1`.

* `rc11_forbids`: RC11 (which does not elide) forbids it, under every
  coherence order.
* `blind_admitted`: with Write Elision blind to the memory order
  (`weRelBlind`, the paper's), `x := 1` is elided into `x := 2`, and the
  execution satisfies every condition of an execution but the release
  restriction, `φ`, No-Thin-Air, and `CoherentT`, the coherence axiom over
  `X ∖ †`, with `r1 = 1 ∧ r2 = 0`. MoRDor's sMRD forbade it only through the
  remapped backward pair `(x := 2, flag)` of `ppo_sync`; `HB_T` has no such pair.
* `not_generated`, `blind_not_execution`: under the release restriction the
  elision is not generated, and the execution above is no execution.
* `forbidden_T`: with the restriction, no execution without forwarding admits
  the outcome under `CoherenceT`.

`coww_elided_T` restates `Smrd.PpoNecessity.coww_elided` for `CoherenceT`: the
coherence order there orders the elided write and is none of `X ∖ †`; under
every coherence order of `X ∖ †`, `CoherenceT` and `HB_v`-coherence hold.
-/

namespace WEAcrossRelease

open EventStructure PpoKit PpoNecessity Execution

/-- `x := 0; flag := 0; (x :=rlx 1; flag :=rel 1; x :=rlx 2 ∥ r1 :=acq flag; r2 :=rlx x)` -/
def prog : Stmt :=
  .seq (PpoStability.st .rlx "x" 0) (.seq (PpoStability.st .rlx "flag" 0)
    (.par (.seq (PpoStability.st .rlx "x" 1)
        (.seq (PpoStability.st .rel "flag" 1) (PpoStability.st .rlx "x" 2)))
      (.seq (PpoStability.ld .acq "r1" "flag") (PpoStability.ld .rlx "r2" "x"))))

def esR : EventStructure :=
  ⟨[W 0 0 [0] .rlx "x" 0, W 1 0 [1, 0] .rlx "flag" 0, W 2 0 [1, 1, 0, 0] .rlx "x" 1,
    W 3 0 [1, 1, 0, 1, 0] .rel "flag" 1, W 4 0 [1, 1, 0, 1, 1] .rlx "x" 2,
    R 5 1 [1, 1, 1, 0] .acq "flag", R 6 1 [1, 1, 1, 1] .rlx "x"],
   [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6),
    (2, 3), (2, 4), (3, 4), (5, 6)], []⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esR := rfl

theorem SR : Simple esR := ⟨by decide, by decide, rfl⟩
theorem gR : GlobLocs esR := globLocs_of (by decide)
theorem poTrans_R : ∀ a b c, esR.poR a b → esR.poR b c → esR.poR a c := poTrans_of (by decide)
theorem poIrr_R : ∀ a, ¬ esR.poR a a := poIrr_of (by decide)

/-- `r1` reads `flag := 1`, `r2` the initial `x := 0`. -/
def rfR : List (EventId × EventId) := [(3, 5), (0, 6)]

theorem po_of {a b : EventId} (h : (a, b) ∈ esR.po) : esR.poR a b := h

/-- `SW` from `flag := 1` to `r1` wherever `r1` reads it. -/
theorem sw35 {x : Execution} (h : x.rf 3 5) : x.sw esR 3 5 :=
  ⟨.inl ⟨_, rfl, rfl⟩, 3, 3, 5, .inl rfl,
    ⟨⟨_, rfl, rfl⟩, 3, .inl rfl, ⟨_, rfl, rfl⟩, .inl rfl⟩,
    h, ⟨_, rfl, rfl⟩, .inl rfl, .inl ⟨_, rfl, rfl⟩⟩

/-! ## RC11 forbids the outcome -/

def xR : Execution := simple esR rfR

/-- **RC11 forbids `r1 = 1 ∧ r2 = 0`** on the program's own events, under every
    coherence order. -/
theorem rc11_forbids :
    xR.IsExecution esR (fun _ => True) ∧ xR.phi esR ∧
    ∀ co, xR.CoherenceOrder esR co → ¬ xR.Coherence esR co := by
  refine ⟨isExecution_simple SR (by decide),
    phi_simple SR (by decide) (by decide) (by decide)
      (fun α => if α = 5 then .num 1 else .num 0) (by decide), fun co hco hcoh => ?_⟩
  have X : ∀ e ∈ esR.events, xR.X e.id :=
    fun e he => X_simple SR he (by revert e; decide) (by revert e; decide)
  have X0 := X (W 0 0 [0] .rlx "x" 0) (by simp [esR])
  have X2 := X (W 2 0 [1, 1, 0, 0] .rlx "x" 1) (by simp [esR])
  have X3 := X (W 3 0 [1, 1, 0, 1, 0] .rel "flag" 1) (by simp [esR])
  have X5 := X (R 5 1 [1, 1, 1, 0] .acq "flag") (by simp [esR])
  have X6 := X (R 6 1 [1, 1, 1, 1] .rlx "x") (by simp [esR])
  rcases hco.total 0 2 X0 X2 ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩ (by decide)
    (sameLoc_of rfl rfl rfl rfl) with h | h
  · have hb : xR.hb esR 2 6 :=
      .tail (.tail (.single (.inl (poX_of X2 X3 (po_of (by decide))))) (.inr
        (sw35 (show (3, 5) ∈ rfR by decide))))
        (.inl (poX_of X5 X6 (po_of (by decide))))
    exact hcoh 2 ⟨6, hb, .inr (.single (.inr ⟨0, show (0, 6) ∈ rfR by decide, h⟩))⟩
  · exact hcoh 0 ⟨2, .single (.inl (poX_of X0 X2 (po_of (by decide)))),
      .inr (.single (.inl (.inr h)))⟩

/-! ## Under the release restriction the elision is not generated -/

/-- `x := 1` may not be elided into `x := 2`: `flag :rel= 1` lies between. -/
theorem not_weNoRel : ¬ esR.weNoRel 2 4 :=
  fun h => h.2 3 (po_of (by decide)) (po_of (by decide)) ⟨_, rfl, rfl⟩

/-- **No generated justification elides `x := 1` into `x := 2`.** -/
theorem not_generated {Ω : Pred} {j : Justification} (h : esR.Generated Ω j) :
    (4, 2) ∉ j.δ.we := by
  intro hp
  obtain ⟨j₀, ⟨-, hnr⟩, -⟩ := Generated.we_mem esR h _ hp
  exact not_weNoRel hnr

/-- The locations of two globals with different names are equal under no
    satisfiable predicate. -/
theorem not_equiv_glob {P : Pred} (hs : Sat P) {y z : Var} (hne : y ≠ z) :
    ¬ EquivUnder P (Expr.glob y) (Expr.glob z) := by
  intro h
  obtain ⟨f, hf⟩ := hs
  have := h f hf _ _ rfl rfl
  simp at this
  exact hne this

/-- **With the release restriction, no execution admits `r1 = 1 ∧ r2 = 0`
    under `CoherenceT`**, for executions without forwarding (elisions point
    `⊑`-forward in every execution, `we_po`). -/
theorem forbidden_T {Ω : Pred} {x : Execution} (hx : x.IsExecution esR Ω) (hphi : x.phi esR)
    (hnoF : ∀ p ∈ x.δ.f, False) (h35 : x.rf 3 5) (h06 : x.rf 0 6) : ¬ x.CoherentT esR := by
  have hW := weForward_of_noFwd hx hnoF
  rintro ⟨co, hco, hcoh, -⟩
  have X : ∀ e ∈ esR.events, x.X e.id := fun e he =>
    all_in_X hx SR (cand_of_mem SR.nodup he (by revert e; decide) (by revert e; decide))
  have X0 := X (W 0 0 [0] .rlx "x" 0) (by simp [esR])
  have X2 := X (W 2 0 [1, 1, 0, 0] .rlx "x" 1) (by simp [esR])
  have X3 := X (W 3 0 [1, 1, 0, 1, 0] .rel "flag" 1) (by simp [esR])
  have X5 := X (R 5 1 [1, 1, 1, 0] .acq "flag") (by simp [esR])
  have X6 := X (R 6 1 [1, 1, 1, 1] .rlx "x") (by simp [esR])
  have n0 : ¬ x.elided 0 := hphi.1 0 (.inl ⟨6, h06⟩)
  have n3 : ¬ x.elided 3 := hphi.1 3 (.inl ⟨5, h35⟩)
  have n5 : ¬ x.elided 5 := not_elided_of_not_write hx hW
    (fun _ h => Event.not_write_of_isRead h) ⟨_, rfl, rfl⟩
  have n6 : ¬ x.elided 6 := not_elided_of_not_write hx hW
    (fun _ h => Event.not_write_of_isRead h) ⟨_, rfl, rfl⟩
  -- `x := 1` is not elided: forward of it lie only `flag := 1` and `x := 2`
  have n2 : ¬ x.elided 2 := by
    intro hel
    obtain ⟨e₂, he⟩ := elided_we hW hel
    obtain ⟨j₀, ⟨⟨⟨-, -, ev₁, ev₂, l₁, l₂, h₁, h₂, hl₁, hl₂, heq⟩, -⟩, hnr⟩, hs, hf⟩ :=
      we_edge hx he
    have hpo : esR.poR 2 e₂ := hW.2 _ he
    have : e₂ = 3 ∨ e₂ = 4 := by
      have key : ∀ p ∈ esR.po, p.1 = 2 → p.2 = 3 ∨ p.2 = 4 := by decide
      exact key _ hpo rfl
    rcases this with rfl | rfl
    · cases h₁; cases h₂; cases hl₁; cases hl₂
      refine not_equiv_glob (y := "x") (z := "flag") ?_ (by decide) heq
      obtain ⟨f, hP⟩ := hs
      exact ⟨f, hP, fun q hq => (hW.1 q (hf q hq)).elim⟩
    · exact not_weNoRel hnr
  have hco02 := hco.total 0 2 ⟨X0, n0⟩ ⟨X2, n2⟩ ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩ (by decide)
    (sameLoc_of rfl rfl rfl rfl)
  have poT : ∀ a b, x.X a → x.X b → ¬ x.elided a → ¬ x.elided b → (a, b) ∈ esR.po →
      x.poXT esR a b := fun a b ha hb na nb h => ⟨poX_of ha hb h, na, nb⟩
  rcases hco02 with h | h
  · have hb : x.hbT esR 2 6 :=
      .tail (.tail (.single (.inl (poT 2 3 X2 X3 n2 n3 (by decide))))
        (.inr ⟨sw35 h35, n3, n5⟩)) (.inl (poT 5 6 X5 X6 n5 n6 (by decide)))
    exact hcoh 2 ⟨6, hb, .inr (.single (.inr ⟨0, h06, h⟩))⟩
  · exact hcoh 0 ⟨2, .single (.inl (poT 0 2 X0 X2 n0 n2 (by decide))),
      .inr (.single (.inl (.inr h)))⟩

/-! ## Without the restriction: elided, and admitted by `CoherenceT` -/

/-- `≼` bounded by the remapped templates, where `remap_δ` is a function `f`. -/
theorem ppoM_mem_f {es : EventStructure} (hr : es.rmw = []) (hg : GlobLocs es) {Pa Pr : Pred}
    {δ : FwdCtx} {f : EventId → EventId} (hf : ∀ a a', δ.Remap a a' → a' = f a) {a b : EventId}
    (h : es.ppoM Pa Pr δ a b) :
    (a, b) ∈ (syncML es ++ aliasL es).map (fun p => (f p.1, f p.2)) := by
  obtain ⟨⟨a₀, b₀, hab, ra, rb⟩, -⟩ := h
  have base : (a₀, b₀) ∈ syncML es ++ aliasL es := by
    rcases hab with (hs | (⟨x, -, hx⟩ | ⟨x, hx, -⟩)) | ⟨hpo, hm | hal⟩
    · exact List.mem_append.2 (.inl (ppoSyncM_mem hs))
    · exact absurd hx (not_rmwPairs hr)
    · exact absurd hx (not_rmwPairs hr)
    · exact List.mem_append.2 (.inr (mustAlias_mem hg hpo hm))
    · exact List.mem_append.2 (.inr (mayAlias_mem hg hpo hal))
  exact List.mem_map.2 ⟨_, base, by rw [hf _ _ ra, hf _ _ rb]⟩

theorem ppoStep_ppoM {es : EventStructure} {x : Execution} {a b : EventId}
    (h : x.ppoStep es a b) : ∃ Pa Pr, es.ppoM Pa Pr x.δ a b := by
  obtain ⟨-, -, ⟨j, -, hp, -⟩ | ⟨hs | ⟨hp, -⟩, -⟩⟩ := h
  · exact ⟨_, _, hp⟩
  · exact ⟨x.Pm es, x.Pm es, es.ppoSyncRM_sub_ppoM (x.Pm es) (x.Pm es) x.δ _ _ hs⟩
  · exact ⟨_, _, hp⟩

def e0 : Event := W 0 0 [0] .rlx "x" 0
def e1 : Event := W 1 0 [1, 0] .rlx "flag" 0
def e3 : Event := W 3 0 [1, 1, 0, 1, 0] .rel "flag" 1
def e4 : Event := W 4 0 [1, 1, 0, 1, 1] .rlx "x" 2

/-- `x := 2`'s pre-justification. -/
def jB : Justification := pj e4
/-- `x := 2`'s justification with `x := 1` elided: `WE = {(4, 2)}`. -/
def jWE : Justification := { jB with δ := { jB.δ with we := jB.δ.we ++ [(4, 2)] } }
def JB : List Justification := [pj e0, pj e1, pj e3, jWE]
/-- The execution eliding `x := 1` into `x := 2`, with `r1 = 1 ∧ r2 = 0`. -/
def xB : Execution := ⟨esR.Candidate, JB, fun w r => (w, r) ∈ rfR⟩
def coB : List (EventId × EventId) := [(0, 4), (1, 3)]

theorem δB : xB.δ = ⟨[], [(4, 2)]⟩ := rfl

theorem edge_B {a b : EventId} (h : xB.δ.edge a b) : a = 4 ∧ b = 2 := by
  rw [δB] at h
  rcases h with h | h
  · cases h
  · simp at h; exact h

theorem elided_B {a : EventId} : xB.elided a ↔ a = 2 := by
  constructor
  · intro h; obtain ⟨b, hb⟩ := (xB.elided_iff a).1 h; exact (edge_B hb).2
  · rintro rfl; exact ⟨(4, 2), .inr (by rw [δB]; simp), rfl⟩

/-- `remap_δ` moves `x := 1` to `x := 2` and fixes the rest. -/
def fB (a : EventId) : EventId := if a = 2 then 4 else a

theorem remap_B {a a' : EventId} (h : xB.δ.Remap a a') : a' = fB a := by
  induction h with
  | @canon e hno =>
      unfold fB
      split
      · subst_vars; exact absurd (show xB.δ.edge 4 2 from .inr (by rw [δB]; simp)) (hno 4)
      · rfl
  | step he hr ih =>
      obtain ⟨rfl, rfl⟩ := edge_B he
      cases hr with
      | canon _ => rfl
      | step he' _ => exact absurd (edge_B he').2 (by decide)

theorem X_B {a : EventId} : xB.X a ↔ a ∈ esR.ids := by
  constructor
  · exact ids_of_cand
  · intro h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    exact cand_of_mem SR.nodup he (by revert e; decide) (by revert e; decide)

theorem pre_B {w : Event} (hw : w ∈ esR.events) (hk : preJust w = some (pj w)) :
    esR.Generated (fun _ => True) (pj w) :=
  .pre hw hk ⟨fun _ => .num 0, SR.holds hw _⟩

/-- Write Elision blind to the memory order elides `x := 1` into `x := 2`:
    `x := 1` is the immediate `≼`-predecessor of `x := 2` at its location. -/
theorem blind_we : esR.weRelBlind jB 2 4 := by
  have hδ0 : ∀ a b, ¬ jB.δ.edge a b := by
    intro a b h; rcases h with h | h <;> cases h
  have hppo : ∀ a b, esR.ppo jB.P.holds jB.δ a b → (a, b) ∈ syncL esR ++ aliasL esR :=
    fun a b h => ppo_mem rfl gR hδ0 h
  refine ⟨⟨⟨⟨(FwdCtx.remapRel_of_noEdge hδ0).2 (.inr
      ⟨po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl, fun _ => .num 0,
        SR.holds (e := e4) (by simp [esR, e4]) _,
        by simp [Expr.holds, Expr.eval, Expr.glob]⟩), by decide⟩, ?_⟩,
      po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl, fun _ _ _ _ h₁ h₂ => by rw [h₁] at h₂; cases h₂; rfl⟩,
    ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, fun ⟨e, he, hp⟩ => by cases he; simp [W, Event.isVol] at hp⟩
  rintro ⟨e'', h₁, h₂⟩
  have m₁ := hppo _ _ h₁
  have m₂ := hppo _ _ h₂
  have key : ∀ p ∈ syncL esR ++ aliasL esR, ∀ q ∈ syncL esR ++ aliasL esR,
      p.1 = 2 → q.2 = 4 → p.2 = q.1 → False := by decide
  exact key _ m₁ _ m₂ rfl rfl rfl

theorem wf_we : FwdCtx.WF { jB.δ with we := jB.δ.we ++ [(4, 2)] } := by
  refine ⟨fun a ha => ?_, fun a b e ha hb => ?_⟩
  · have : ∀ c d, Relation.TransGen
        ({ jB.δ with we := jB.δ.we ++ [(4, 2)] } : FwdCtx).edge c d → c = 4 ∧ d = 2 := by
      intro c d h
      induction h with
      | single h => rcases h with h | h <;> simp [jB, pj, FwdCtx.empty] at h; exact h
      | tail _ h ih =>
          rcases h with h | h <;> simp [jB, pj, FwdCtx.empty] at h
          obtain ⟨-, rfl⟩ := ih; cases h.1
    have := this a a ha
    rw [this.1] at this; cases this.2
  · rcases ha with h | h <;> simp [jB, pj, FwdCtx.empty] at h
    rcases hb with h' | h' <;> simp [jB, pj, FwdCtx.empty] at h'
    rw [h.1, h'.1]

theorem mem_JB {j : Justification} (hj : j ∈ JB) :
    j = pj e0 ∨ j = pj e1 ∨ j = pj e3 ∨ j = jWE := by
  simpa [JB] using hj

/-- Every justification of `xB` holds everywhere, and none forwards. -/
theorem J_B {j : Justification} (hj : j ∈ JB) : (∀ f, j.P.holds f) ∧ j.δ.f = [] ∧
    j.P.syms = [] ∧ j.D = [] := by
  rcases mem_JB hj with rfl | rfl | rfl | rfl <;>
    exact ⟨fun _ => by simp [jWE, jB, pj, e0, e1, e3, e4, W, Event.valres, Expr.conj,
      Expr.holds, Expr.eval, Expr.tt], by simp [jWE, jB, pj, FwdCtx.empty],
      by simp [jWE, jB, pj, e0, e1, e3, e4, W, Event.valres, Expr.conj, Expr.syms, Expr.tt],
      rfl⟩

theorem P_B (f : Valuation) : xB.P esR f := fun j hj =>
  ⟨(J_B hj).1 f, fun p hp => by rw [(J_B hj).2.1] at hp; cases hp⟩

theorem no_dp_B {a b : EventId} : ¬ xB.DP a b := by
  rintro ⟨-, -, j, hj, -, h⟩
  rw [(J_B hj).2.2.1, (J_B hj).2.2.2] at h
  rcases h with h | h <;> cases h

theorem rfOK_B : RfOK esR rfR := by decide

/-- **Were the elision generated, `xB` would be an execution**: every other
    condition of `IsExecution` holds. -/
theorem isExecution_B (hg : esR.Generated (fun _ => True) jWE) :
    xB.IsExecution esR (fun _ => True) where
  maximal := ⟨fun _ h => h, fun a b _ _ ⟨ea, eb, ha, hb, hn⟩ =>
      hn ⟨fun _ => .num 0, SR.holds (ev_inv ha).1 _, SR.holds (ev_inv hb).1 _⟩,
    fun _ hc hn => absurd hc hn⟩
  generated j hj := by
    rcases mem_JB hj with rfl | rfl | rfl | rfl
    · exact pre_B (by simp [esR, e0]) rfl
    · exact pre_B (by simp [esR, e1]) rfl
    · exact pre_B (by simp [esR, e3]) rfl
    · exact hg
  inX j hj := by
    rcases mem_JB hj with rfl | rfl | rfl | rfl <;> exact X_B.2 (by decide)
  consistent := ⟨fun _ => .num 0, fun j hj => (J_B hj).1 _,
    fun a e _ he => SR.holds (ev_inv he).1 _⟩
  fwdWF := by
    rw [δB]
    refine ⟨fun a ha => ?_, fun a b e ha hb => ?_⟩
    · have : ∀ c d, Relation.TransGen (FwdCtx.edge ⟨[], [(4, 2)]⟩) c d → c = 4 ∧ d = 2 := by
        intro c d h
        induction h with
        | single h => rcases h with h | h <;> simp at h; exact h
        | tail _ h ih =>
            rcases h with h | h <;> simp at h
            obtain ⟨-, rfl⟩ := ih; cases h.1
      have := this a a ha
      rw [this.1] at this; cases this.2
    · rcases ha with h | h <;> simp at h
      rcases hb with h' | h' <;> simp at h'
      rw [h.1, h'.1]
  rf_wr w r h := by
    obtain ⟨h₁, h₂⟩ := rfOK_B.1 _ h
    have hw := cls_clsB.2 h₁
    have hr := cls_clsB.2 h₂
    exact ⟨hw, hr, cand_of_cls SR.nodup (fun e he => wr_nb e (.inl he)) hw,
      cand_of_cls SR.nodup (fun e he => wr_nb e (.inr he)) hr⟩
  rf_func w w' r h h' := rfOK_B.2 _ h _ h' rfl
  justified w hw he hn := by
    have hids : ∀ w ∈ esR.ids, clsB esR Event.isEffect w = true → w ≠ 2 →
        w = 0 ∨ w = 1 ∨ w = 3 ∨ w = 4 := by decide
    have hw' := hids w (X_B.1 hw) (cls_clsB.1 he) (fun h => hn (elided_B.2 h))
    have uniq : ∀ j j', j ∈ JB → j' ∈ JB → j.w.id = j'.w.id → j' = j := by
      intro j j' hj hj' h
      rcases mem_JB hj with rfl | rfl | rfl | rfl <;>
        rcases mem_JB hj' with rfl | rfl | rfl | rfl <;>
        first | rfl | (simp [jWE, jB, pj, e0, e1, e3, e4, W] at h)
    rcases hw' with rfl | rfl | rfl | rfl
    · exact ⟨pj e0, by simp [xB, JB], rfl, fun j' hj' h => uniq _ _ (by simp [JB]) hj' h.symm⟩
    · exact ⟨pj e1, by simp [xB, JB], rfl, fun j' hj' h => uniq _ _ (by simp [JB]) hj' h.symm⟩
    · exact ⟨pj e3, by simp [xB, JB], rfl, fun j' hj' h => uniq _ _ (by simp [JB]) hj' h.symm⟩
    · exact ⟨jWE, by simp [xB, JB], rfl, fun j' hj' h => uniq _ _ (by simp [JB]) hj' h.symm⟩

/-- Under the release restriction `xB` is no execution. -/
theorem blind_not_execution {Ω : Pred} : ¬ xB.IsExecution esR Ω := by
  intro hx
  exact not_generated (hx.generated jWE (by simp [xB, JB])) (by simp [jWE, jB, pj, FwdCtx.empty])

/-- The outcome: `r1` reads `1`, `r2` reads `0`. -/
def fOut : Valuation := fun α => if α = 5 then .num 1 else .num 0

theorem phi_B : xB.phi esR := by
  refine ⟨fun e h hel => ?_, fun r => ⟨?_, ?_⟩, fOut, P_B fOut, ⟨?_, ?_, ?_⟩⟩
  · rw [elided_B] at hel; subst hel
    rcases h with ⟨r, hr⟩ | ⟨b, hb⟩
    · have : ∀ p ∈ rfR, p.1 ≠ 2 := by decide
      exact this _ hr rfl
    · exact no_dp_B hb
  · rintro ⟨w, hw⟩
    obtain ⟨-, h₂⟩ := rfOK_B.1 _ hw
    exact ⟨X_B.2 (clsB_id h₂), cls_clsB.2 h₂⟩
  · rintro ⟨hX, hr⟩
    have key : ∀ r ∈ esR.ids, clsB esR Event.isRead r = true → ∃ p ∈ rfR, p.2 = r := by decide
    obtain ⟨p, hp, rfl⟩ := key r (X_B.1 hX) (cls_clsB.1 hr)
    exact ⟨p.1, hp⟩
  · intro w r ew er h hw hr
    have key : ∀ p ∈ rfR, ∀ ew ∈ esR.events, ∀ er ∈ esR.events, ew.id = p.1 → er.id = p.2 →
        ew.loc.map (·.eval fOut) = er.loc.map (·.eval fOut) ∧
        ew.val.map (·.eval fOut) = er.val.map (·.eval fOut) := by decide
    have := key (w, r) h ew (ev_inv hw).1 er (ev_inv hr).1 (ev_inv hw).2 (ev_inv hr).2
    refine ⟨fun lw lr h₁ h₂ => ?_, fun vw vr h₁ h₂ => ?_⟩
    · have := this.1; rw [h₁, h₂] at this; exact Option.some.inj this
    · have := this.2; rw [h₁, h₂] at this; exact Option.some.inj this
  · intro a e α sz _ he hk
    obtain ⟨hm, -⟩ := ev_inv he
    simp only [esR, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hk
  · intro a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂ _ _ _ he₁ _ hk₁
    obtain ⟨hm, -⟩ := ev_inv he₁
    simp only [esR, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hk₁

/-- A rank `≼ ∪ rf` increases along: the backward pair `(x := 2, flag := 1)`
    is in `≼`, and `DP ∪ ≼ ∪ rf` is still acyclic. -/
def rkB (a : EventId) : Nat :=
  match a with
  | 0 => 0 | 1 => 0 | 2 => 0 | 4 => 1 | 3 => 2 | 5 => 3 | _ => 4

theorem ntaB : xB.NoThinAir esR := by
  have hstep : ∀ a b, xB.ppoStep esR a b → rkB a < rkB b := by
    intro a b h
    have hne : a ≠ b := by
      obtain ⟨-, -, ⟨j, -, hp, -⟩ | ⟨hs | ⟨hp, -⟩, -⟩⟩ := h
      · exact hp.2
      · exact hs.2
      · exact hp.2
    obtain ⟨Pa, Pr, hp⟩ := ppoStep_ppoM h
    have hm := ppoM_mem_f rfl gR (fun a a' h => remap_B h) hp
    have key : ∀ p ∈ (syncML esR ++ aliasL esR).map (fun p => (fB p.1, fB p.2)),
        p.1 ≠ p.2 → rkB p.1 < rkB p.2 := by decide
    exact key _ hm hne
  have mono : ∀ {R : Rel}, (∀ a b, R a b → rkB a < rkB b) →
      ∀ a b, Relation.TransGen R a b → rkB a < rkB b := by
    intro R hR a b h
    induction h with
    | single h => exact hR _ _ h
    | tail _ h ih => exact Nat.lt_trans ih (hR _ _ h)
  have hedge : ∀ a b, ((xB.dep esR).union xB.rf) a b → rkB a < rkB b := by
    rintro a b ((⟨-, -, hp⟩ | hd) | hrf)
    · exact mono hstep a b hp
    · exact absurd hd no_dp_B
    · have key : ∀ p ∈ rfR, rkB p.1 < rkB p.2 := by decide
      exact key _ hrf
  intro a h
  exact Nat.lt_irrefl _ (mono hedge a a h)

theorem locOf_B {a b : EventId} (h : xB.sameLoc esR a b) : locOf esR a = locOf esR b := by
  obtain ⟨ea, eb, la, lb, ha, hb, hla, hlb, heq⟩ := h
  obtain ⟨x, rfl⟩ := gR ea (ev_inv ha).1 _ hla
  obtain ⟨y, rfl⟩ := gR eb (ev_inv hb).1 _ hlb
  have := heq (fun _ => .num 0) (P_B _) _ _ rfl rfl
  cases this
  simp [locOf, ha, hb, hla, hlb]

theorem coherenceOrderT_B : xB.CoherenceOrderT esR (relL coB) where
  writes a b h := by
    have hw : ∀ p ∈ coB, clsB esR Event.isWrite p.1 = true ∧ clsB esR Event.isWrite p.2 = true ∧
        p.1 ∈ esR.ids ∧ p.2 ∈ esR.ids ∧ p.1 ≠ 2 ∧ p.2 ≠ 2 := by decide
    obtain ⟨h1, h2, i1, i2, n1, n2⟩ := hw _ h
    exact ⟨⟨X_B.2 i1, fun h => n1 (elided_B.1 h)⟩, ⟨X_B.2 i2, fun h => n2 (elided_B.1 h)⟩,
      cls_clsB.2 h1, cls_clsB.2 h2⟩
  irrefl a h := by
    have : ∀ p ∈ coB, p.1 ≠ p.2 := by decide
    exact this _ h rfl
  trans a b c h₁ h₂ := by
    have : Closed coB := by decide
    exact this _ h₁ _ h₂ rfl
  total a b ha hb hwa hwb hne hsl := by
    have key : ∀ a ∈ esR.ids.filter (· != 2), ∀ b ∈ esR.ids.filter (· != 2),
        clsB esR Event.isWrite a = true →
        clsB esR Event.isWrite b = true → a ≠ b → locOf esR a = locOf esR b →
        (a, b) ∈ coB ∨ (b, a) ∈ coB := by decide
    exact key a (List.mem_filter.2 ⟨X_B.1 ha.1, by simpa using fun h => ha.2 (elided_B.2 h)⟩)
      b (List.mem_filter.2 ⟨X_B.1 hb.1, by simpa using fun h => hb.2 (elided_B.2 h)⟩)
      (cls_clsB.1 hwa) (cls_clsB.1 hwb) hne (locOf_B hsl)

/-- A bound on `HB_T`: `⊑` and `flag := 1 →sw r1`, closed. -/
def HB : List (EventId × EventId) := esR.po ++ [(3, 5), (2, 5), (3, 6), (2, 6)]
/-- A bound on `ECO`. -/
def EB : List (EventId × EventId) := [(3, 5), (0, 6), (0, 4), (1, 3), (6, 4), (1, 5)]

theorem coherenceT_B : xB.CoherenceT esR (relL coB) := by
  have hH : ∀ a b, xB.hbT esR a b → (a, b) ∈ HB := by
    intro a b h
    refine transGen_mem (fun c d s => ?_) (by decide) h
    rcases s with ⟨⟨-, -, hpo⟩, -⟩ | ⟨hs, -⟩
    · exact List.mem_append_left _ hpo
    · have hsw : ∀ p ∈ swL esR, p ∈ HB := by decide
      exact hsw _ (sw_mem hs)
  have hE : ∀ a b, xB.eco (relL coB) a b → (a, b) ∈ EB :=
    fun a b h => eco_mem (fun a b h => by
        have : ∀ p ∈ rfR, p ∈ EB := by decide
        exact this _ h)
      (fun a b h => by
        have : ∀ p ∈ coB, p ∈ EB := by decide
        exact this _ h)
      (fun a b h => by
        have : ∀ p ∈ frL rfR coB, p ∈ EB := by decide
        obtain ⟨w, hrf, hco⟩ := h
        exact this _ (List.mem_flatMap.2 ⟨(w, a), hrf, List.mem_map.2 ⟨(w, b),
          List.mem_filter.2 ⟨hco, by simp⟩, rfl⟩⟩))
      (by decide) h
  have hok : ∀ p ∈ HB, p.1 ≠ p.2 ∧ (p.2, p.1) ∉ EB := by decide
  rintro a ⟨b, hab, rfl | hba⟩
  · exact (hok _ (hH _ _ hab)).1 rfl
  · exact (hok _ (hH _ _ hab)).2 (hE _ _ hba)

theorem coherentT_B : xB.CoherentT esR :=
  ⟨relL coB, coherenceOrderT_B, coherenceT_B, fun r w h => by
    obtain ⟨-, -, ent, hm, -⟩ := h; cases hm⟩

/-- **Without the release restriction, `CoherenceT` admits `r1 = 1 ∧ r2 = 0`.**
    Write Elision blind to the memory order (`weRelBlind`) elides `x := 1` into
    `x := 2` (`jWE` from the pre-justification `jB` of `x := 2`); the release
    restriction refutes it (`¬ weNoRel 2 4`); everything else an execution
    asks holds (`isExecution_B`), and so do `φ`, No-Thin-Air and `CoherentT`,
    with `r1` reading `flag := 1` and `r2` the initial `x := 0`. -/
theorem blind_admitted :
    (esR.Generated (fun _ => True) jB ∧ esR.weRelBlind jB 2 4 ∧
      FwdCtx.WF { jB.δ with we := jB.δ.we ++ [(4, 2)] } ∧ Sat (Pred.and jB.P.holds fun _ => True)) ∧
    ¬ esR.weNoRel 2 4 ∧
    (esR.Generated (fun _ => True) jWE → xB.IsExecution esR (fun _ => True)) ∧
    xB.phi esR ∧ xB.NoThinAir esR ∧ xB.CoherentT esR ∧ xB.rf 3 5 ∧ xB.rf 0 6 :=
  ⟨⟨pre_B (by simp [esR, e4]) rfl, blind_we, wf_we,
    ⟨fun _ => .num 0, (J_B (j := jWE) (by simp [JB])).1 _, trivial⟩⟩,
   not_weNoRel, isExecution_B, phi_B, ntaB, coherentT_B,
   show (3, 5) ∈ rfR by decide, show (0, 6) ∈ rfR by decide⟩

/-! ## `coww_elided` over the transformed execution -/

/-- **`coww_elided` for `CoherenceT`**: in `x := 1; x := 2` with `x := 1`
    elided, the coherence order `2 < 1` of `coww_elided` orders the elided
    write and is no coherence order of `X ∖ †`; under every coherence order of
    `X ∖ †` (the empty one: one write is left), both `CoherenceT` and
    `HB_v`-coherence hold. -/
theorem coww_elided_T :
    ¬ xC.CoherenceOrderT esC (relL coC) ∧
    ∀ co, xC.CoherenceOrderT esC co → xC.CoherenceT esC co ∧ xC.CoherenceV esC co := by
  refine ⟨fun h => ?_, fun co hco => ⟨?_, ?_⟩⟩
  · exact (h.writes 1 0 (show (1, 0) ∈ coC by decide)).2.1.2 (elided_C.2 rfl)
  · have hnone : ∀ a b, ¬ co a b := by
      intro a b h
      obtain ⟨⟨ha, na⟩, ⟨hb, nb⟩, -, -⟩ := hco.writes a b h
      have ha1 : a = 1 := by
        rcases X_C.1 ha with rfl | rfl
        · exact absurd (elided_C.2 rfl) na
        · rfl
      have hb1 : b = 1 := by
        rcases X_C.1 hb with rfl | rfl
        · exact absurd (elided_C.2 rfl) nb
        · rfl
      subst ha1 hb1
      exact hco.irrefl _ h
    have hstep : ∀ c d, ((xC.poXT esC).union (xC.swT esC)) c d → False := by
      rintro c d (⟨⟨-, -, hpo⟩, nc, nd⟩ | ⟨hs, -⟩)
      · have : ∀ p ∈ esC.po, p.1 = 0 := by decide
        exact nc (elided_C.2 (this _ hpo))
      · have := sw_mem hs
        have : swL esC = [] := by decide
        simp_all
    rintro a ⟨b, hab, -⟩
    cases hab with
    | single h => exact hstep _ _ h
    | tail _ h => exact hstep _ _ h
  · rintro a ⟨b, hab, -⟩
    have hsw : ∀ c d, xC.sw esC c d → False := by
      intro c d h
      have := sw_mem h
      have : swL esC = [] := by decide
      simp_all
    have step : ∀ c d, ((xC.dep esC).union (xC.sw esC)) c d → False := by
      rintro c d (h | h)
      · exact no_dep_C h
      · exact hsw _ _ h
    cases hab with
    | single h => exact step _ _ h
    | tail _ h => exact step _ _ h

end WEAcrossRelease
