import Smrd.PpoNecessity

/-!
# Message passing through fences: `HB_v` misses fence synchronisation

Message passing with the release and the acquire on fences,

    x := 0; y := 0; (x := 1; fence(rel); y :=_rlx 1 ∥ r1 :=_rlx y; fence(acq); r2 :=_rlx x)

with `r1 = 1` (the read of `y` takes `y := 1`) and `r2 = 0` (the read of `x`
takes the initialising `x := 0`). RC11 forbids it: `x := 1 ⊑ fence(rel)`,
`fence(rel) SW fence(acq)` through `y := 1` and the read of `y`, and
`fence(acq) ⊑ r2`, so `x := 1` happens before `r2`, which reads a write
coherence-before `x := 1` (`mpf_rc11`).

* **`HB_v`-coherence holds** (`mpf_coherenceV`). `HB_v ≜ (DP ∪ ≼ ∪ SW)⁺`
  has no path from `x := 1` to `r2`: `≼` relates events of `X` only, so no
  edge of it enters `fence(rel)` or leaves `fence(acq)`, and the `SW` edge
  between the fences is a dead end. So `coherence_of_coherenceV` fails without
  `FenceFree`: the generalisation of it to fences over `HB_v` is false.
* **`≼` does not cross the fences** (`mpf_not_ppo`): MoRDor's `ppo_sync`
  relates `x := 1` to `fence(rel)` and `fence(acq)` to `r2`, but neither
  fence both acquires and releases, so the closure does not reach `y := 1`
  from `x := 1`, nor `r2` from `r1`. Definition `def:ppo`'s fence summands
  `⊑;Δ_{F_rel,sc};⊑_{∖R}` and `⊑_{∖W};Δ_{F_acq,sc};⊑` would order both
  pairs; MoRDor's templates, and so `Execution.ppo`, have none
  (`Smrd.PpoMordor`). An operational semantics that performs events in an
  order respecting `DP ∪ ≼` may therefore perform `y := 1` before `x := 1`,
  and `r2` before `r1`.
* **`HB_F`-coherence fails** (`mpf_not_coherenceF`), as RC11's does: over
  `≼_F` (`Execution.ppoF`, MoRDor's closure before its restriction to `X`)
  the path `x := 1 ≼_F fence(rel) SW fence(acq) ≼_F r2` is in `HB_F`, and
  `HB_F`-coherence coincides with RC11's coherence axiom with fences
  (`Execution.coherenceF_iff_coherence`).
-/

namespace FenceMP

open EventStructure PpoKit PpoStability PpoNecessity Execution

/-- `x := 0; y := 0; (x := 1; fence(rel); y := 1 ∥ r1 := y; fence(acq); r2 := x)` -/
def mpf : Stmt := .seq (st .rlx "x" 0) (.seq (st .rlx "y" 0)
  (.par (.seq (st .rlx "x" 1) (.seq (.fence .rel) (st .rlx "y" 1)))
        (.seq (ld .rlx "r1" "y") (.seq (.fence .acq) (ld .rlx "r2" "x")))))

/-- A fence event. -/
def Fe (i t : Nat) (pc : List Nat) (o : MemOrd) : Event := ⟨i, .fence o, ⟨t, pc, []⟩, []⟩

def esMPF : EventStructure :=
  ⟨[W 0 0 [0] .rlx "x" 0, W 1 0 [1, 0] .rlx "y" 0, W 2 0 [1, 1, 0, 0] .rlx "x" 1,
    Fe 3 0 [1, 1, 0, 1, 0] .rel, W 4 0 [1, 1, 0, 1, 1] .rlx "y" 1,
    R 5 1 [1, 1, 1, 0] .rlx "y", Fe 6 1 [1, 1, 1, 1, 0] .acq, R 7 1 [1, 1, 1, 1, 1] .rlx "x"],
   [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 2), (1, 3), (1, 4), (1, 5),
    (1, 6), (1, 7), (2, 3), (2, 4), (3, 4), (5, 6), (5, 7), (6, 7)], []⟩

unseal interp in
theorem denote_mpf : denote (fun _ => 0) mpf = esMPF := rfl

theorem SMPF : Simple esMPF := ⟨by decide, by decide, rfl⟩
theorem gMPF : GlobLocs esMPF := globLocs_of (by decide)

/-- `r1` reads `y := 1`, `r2` the initial `x := 0`. -/
def rfMPF : List (EventId × EventId) := [(4, 5), (0, 7)]
def coMPF : List (EventId × EventId) := [(0, 2), (1, 4)]
def xMPF : Execution := simple esMPF rfMPF

theorem mpf_exec : xMPF.IsExecution esMPF (fun _ => True) ∧ xMPF.phi esMPF :=
  ⟨isExecution_simple SMPF (by decide),
   phi_simple SMPF (by decide) (by decide) (by decide)
     (fun α => if α = 5 then .num 1 else .num 0) (by decide)⟩

theorem X_mpf : ∀ e ∈ esMPF.events, e.isFence = false → xMPF.X e.id :=
  fun e he hf => X_simple SMPF he (by revert e; decide) hf

/-- The fences lie on the path, in `X_F`. -/
theorem XF_mpf {e : Event} (he : e ∈ esMPF.events) (hf : e.isFence = true) :
    xMPF.XF esMPF e.id :=
  ⟨⟨e, he, rfl⟩, ⟨e, PpoKit.ev_of_mem SMPF.nodup he, hf⟩, fun _ _ ⟨ea, eb, ha, hb, hn⟩ =>
    hn ⟨fun _ => .num 0, SMPF.holds (ev_inv ha).1 _, SMPF.holds (ev_inv hb).1 _⟩⟩

theorem X0 : xMPF.X 0 := X_mpf (W 0 0 [0] .rlx "x" 0) (by simp [esMPF]) rfl
theorem X2 : xMPF.X 2 := X_mpf (W 2 0 [1, 1, 0, 0] .rlx "x" 1) (by simp [esMPF]) rfl
theorem X4 : xMPF.X 4 := X_mpf (W 4 0 [1, 1, 0, 1, 1] .rlx "y" 1) (by simp [esMPF]) rfl
theorem X5 : xMPF.X 5 := X_mpf (R 5 1 [1, 1, 1, 0] .rlx "y") (by simp [esMPF]) rfl
theorem X7 : xMPF.X 7 := X_mpf (R 7 1 [1, 1, 1, 1, 1] .rlx "x") (by simp [esMPF]) rfl
theorem F3 : xMPF.XF esMPF 3 := XF_mpf (e := Fe 3 0 [1, 1, 0, 1, 0] .rel) (by simp [esMPF]) rfl
theorem F6 : xMPF.XF esMPF 6 := XF_mpf (e := Fe 6 1 [1, 1, 1, 1, 0] .acq) (by simp [esMPF]) rfl

/-- `fence(rel) SW fence(acq)`, through `y := 1` and `r1`. -/
theorem sw36 : xMPF.sw esMPF 3 6 :=
  ⟨.inr ⟨_, rfl, rfl⟩, 4, 4, 5, .inr ⟨⟨_, rfl, rfl⟩, .inr F3, .inl X4, show (3, 4) ∈ esMPF.po by decide⟩,
    ⟨⟨_, rfl, rfl⟩, 4, .inl rfl, ⟨_, rfl, rfl⟩, .inl rfl⟩,
    show (4, 5) ∈ rfMPF by decide, ⟨_, rfl, rfl⟩,
    .inr ⟨⟨.inl X5, .inr F6, show (5, 6) ∈ esMPF.po by decide⟩, ⟨_, rfl, rfl⟩⟩, .inr ⟨_, rfl, rfl⟩⟩

/-- **RC11 forbids it** under every coherence order. -/
theorem mpf_rc11 {co : Rel} (hco : xMPF.CoherenceOrder esMPF co) : ¬ xMPF.Coherence esMPF co := by
  intro hcoh
  rcases hco.total 0 2 X0 X2 ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩ (by decide)
    (sameLoc_of rfl rfl rfl rfl) with h | h
  · have hb : xMPF.hb esMPF 2 7 :=
      .tail (.tail (.single (.inl ⟨.inl X2, .inr F3, show (2, 3) ∈ esMPF.po by decide⟩)) (.inr sw36))
        (.inl ⟨.inr F6, .inl X7, show (6, 7) ∈ esMPF.po by decide⟩)
    exact hcoh 2 ⟨7, hb, .inr (.single (.inr ⟨0, show (0, 7) ∈ rfMPF by decide, h⟩))⟩
  · exact hcoh 0 ⟨2, .single (.inl (poX_of X0 X2 (show (0, 2) ∈ esMPF.po by decide))),
      .inr (.single (.inl (.inr h)))⟩

/-- The steps of MoRDor's `≼`, closed: `ppo_sync` into `fence(rel)` and out of
    `fence(acq)`, and `ppo_loc`. -/
def stepsL : List (EventId × EventId) :=
  [(0, 3), (1, 3), (2, 3), (6, 7), (0, 2), (0, 7), (1, 4), (1, 5)]

theorem ppoF_mem {a b : EventId} (h : xMPF.ppoF esMPF a b) : (a, b) ∈ stepsL :=
  transGen_mem (fun c d hs => by
    have := ppoStep_mem SMPF.normw gMPF (noEdge_simple esMPF rfMPF) hs
    revert this; generalize (c, d) = p; revert p; decide) (by decide) h

theorem not_fence_of_X {a : EventId} (h : xMPF.X a) : clsB esMPF Event.isFence a = false := by
  cases hb : clsB esMPF Event.isFence a
  · rfl
  · exact absurd (cls_clsB.2 hb) h.2.2

/-- **`≼` does not cross the fences**: `x := 1` is not `≼`-before `y := 1`, nor
    `r1` before `r2`. -/
theorem mpf_not_ppo : ¬ xMPF.ppo esMPF 2 4 ∧ ¬ xMPF.ppo esMPF 5 7 :=
  ⟨fun h => absurd (ppoF_mem (ppoF_of_ppo h)) (by decide),
   fun h => absurd (ppoF_mem (ppoF_of_ppo h)) (by decide)⟩

/-- **`HB_v`-coherence holds.** -/
theorem mpf_coherenceV : xMPF.CoherenceV esMPF (relL coMPF) := by
  have hdp : ∀ a b, ¬ xMPF.DP a b := fun _ _ => dp_none (es := esMPF) (rf := rfMPF) (by decide)
  refine coherenceVOver_of (H := [(0, 2), (0, 7), (1, 4), (1, 5), (3, 6)])
    (E := [(4, 5), (0, 7), (0, 2), (1, 4), (7, 2), (1, 5)]) ?_ ?_ (by decide)
  · intro a b h
    refine transGen_mem (fun c d hs => ?_) (by decide) h
    rcases hs with (hp | hd) | hs
    · have hm := ppoF_mem (ppoF_of_ppo hp)
      have hc := not_fence_of_X hp.1
      have hd := not_fence_of_X hp.2.1
      have key : ∀ p ∈ stepsL, clsB esMPF Event.isFence p.1 = false →
          clsB esMPF Event.isFence p.2 = false → p ∈ [(0, 2), (0, 7), (1, 4), (1, 5), (3, 6)] := by
        decide
      exact key (c, d) hm hc hd
    · exact absurd hd (hdp _ _)
    · have := sw_mem hs
      revert this; generalize (c, d) = p; revert p; decide
  · intro a b h
    refine eco_mem (fun c d h => ?_) (fun c d h => ?_) (fun c d h => ?_) (by decide) h
    · revert h; show (c, d) ∈ rfMPF → _; generalize (c, d) = p; revert p; decide
    · revert h; show (c, d) ∈ coMPF → _; generalize (c, d) = p; revert p; decide
    · have := fr_mem (es := esMPF) h
      revert this; generalize (c, d) = p; revert p; decide

/-- **`HB_F`-coherence fails**, for the coherence order of the outcome. -/
theorem mpf_not_coherenceF : ¬ xMPF.CoherenceF esMPF (relL coMPF) := by
  intro h
  have p23 : xMPF.ppoF esMPF 2 3 :=
    .single ⟨.inl X2, .inr F3, .inr ⟨.inl ⟨(FwdCtx.remapRel_of_noEdge
      (noEdge_simple esMPF rfMPF)).2 ⟨show (2, 3) ∈ esMPF.po by decide, .inr ⟨_, rfl, rfl⟩⟩,
      by decide⟩, ⟨3, .inr F3, .inr (show (2, 3) ∈ esMPF.po by decide), .inl rfl⟩⟩⟩
  have p67 : xMPF.ppoF esMPF 6 7 :=
    .single ⟨.inr F6, .inl X7, .inr ⟨.inl ⟨(FwdCtx.remapRel_of_noEdge
      (noEdge_simple esMPF rfMPF)).2 ⟨show (6, 7) ∈ esMPF.po by decide, .inl ⟨_, rfl, rfl⟩⟩,
      by decide⟩, ⟨7, .inl X7, .inr (show (6, 7) ∈ esMPF.po by decide), .inl rfl⟩⟩⟩
  exact h 2 ⟨7, .tail (.tail (.single (.inl (.inl p23))) (.inr sw36)) (.inl (.inl p67)),
    .inr (.single (.inr ⟨0, show (0, 7) ∈ rfMPF by decide, show (0, 2) ∈ coMPF by decide⟩))⟩

/-- **Message passing through fences**: an execution with `φ` that RC11 forbids
    under every coherence order, `HB_v`-coherent and not `HB_F`-coherent, with
    `≼` crossing neither fence. -/
theorem summary :
    xMPF.IsExecution esMPF (fun _ => True) ∧ xMPF.phi esMPF ∧
    xMPF.CoherenceOrder esMPF (relL coMPF) ∧
    (∀ co, xMPF.CoherenceOrder esMPF co → ¬ xMPF.Coherence esMPF co) ∧
    xMPF.CoherenceV esMPF (relL coMPF) ∧ ¬ xMPF.CoherenceF esMPF (relL coMPF) ∧
    ¬ xMPF.ppo esMPF 2 4 ∧ ¬ xMPF.ppo esMPF 5 7 :=
  ⟨mpf_exec.1, mpf_exec.2, coherenceOrder_simple SMPF gMPF mpf_exec.2 (by decide) (by decide)
    (by decide) (by decide), fun _ h => mpf_rc11 h, mpf_coherenceV, mpf_not_coherenceF,
    mpf_not_ppo.1, mpf_not_ppo.2⟩

end FenceMP
