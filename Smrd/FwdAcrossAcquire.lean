import Smrd.WEAcrossRelease

/-!
# Forwarding across an acquire, with coherence over `X ∖ †`

`x := 0; flag := 0; (x :=rlx 1; r0 :=acq flag; x :=rlx 1 ∥ x :=rlx 2; flag :=rel 1)`,
MoRDor's `litmus-tests/own/RSE-across-acquire.lit`. RC11 forbids `r0 = 1` with
`x` ending at `2`: `x := 2 ⊑ flag := 1 →sw r0 ⊑ x := 1` (the second), so
`x := 2` is coherence-before the second `x := 1` (`rc11_forbids`).

Forwarding (store-store, redundant-store elimination) forwards the first
`x := 1` into the second and drops the second, across the acquire; nothing
restricts it. Write Elision's release restriction does not reach it, and
`CoherenceT`, over `X ∖ †`, admits the outcome (`fwd_admitted`): `x := 2` is
coherence-last, `φ` and No-Thin-Air hold, and the execution is one of sMRD's.
`HB_v`-coherence forbids it (`fwd_not_coherenceV`), through the remapped
backward pair `(r0, x := 1)` (the first) of `ppo_sync`, as MoRDor's sMRD does.

So with coherence over `X ∖ †`, Forwarding needs the dual of Write Elision's
release restriction: no acquiring read or fence (or `sc` access) `⊑`-between
the forwarding and the forwarded event. Without it the remapped backward pair
stays necessary.
-/

namespace FwdAcrossAcquire

open EventStructure PpoKit PpoNecessity Execution WEAcrossRelease

theorem Expr.replace_same (e p : Expr) : e.replace p p = e := by
  induction e with
  | val v => unfold Expr.replace; split <;> simp_all
  | sym a => unfold Expr.replace; split <;> simp_all
  | bin op a b iha ihb => unfold Expr.replace; split <;> simp_all
  | eq a b iha ihb => unfold Expr.replace; split <;> simp_all
  | le a b iha ihb => unfold Expr.replace; split <;> simp_all
  | not a iha => unfold Expr.replace; split <;> simp_all
  | and a b iha ihb => unfold Expr.replace; split <;> simp_all
  | or a b iha ihb => unfold Expr.replace; split <;> simp_all

/-- `x := 0; flag := 0; (x :=rlx 1; r0 :=acq flag; x :=rlx 1 ∥ x :=rlx 2; flag :=rel 1)` -/
def prog : Stmt :=
  .seq (PpoStability.st .rlx "x" 0) (.seq (PpoStability.st .rlx "flag" 0)
    (.par (.seq (PpoStability.st .rlx "x" 1)
        (.seq (PpoStability.ld .acq "r0" "flag") (PpoStability.st .rlx "x" 1)))
      (.seq (PpoStability.st .rlx "x" 2) (PpoStability.st .rel "flag" 1))))

def e0 : Event := W 0 0 [0] .rlx "x" 0
def e1 : Event := W 1 0 [1, 0] .rlx "flag" 0
def e2 : Event := W 2 0 [1, 1, 0, 0] .rlx "x" 1
def e4 : Event := W 4 0 [1, 1, 0, 1, 1] .rlx "x" 1
def e5 : Event := W 5 1 [1, 1, 1, 0] .rlx "x" 2
def e6 : Event := W 6 1 [1, 1, 1, 1] .rel "flag" 1

def esA : EventStructure :=
  ⟨[e0, e1, e2, R 3 0 [1, 1, 0, 1, 0] .acq "flag", e4, e5, e6],
   [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6),
    (2, 3), (2, 4), (3, 4), (5, 6)], []⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esA := rfl

theorem SA : Simple esA := ⟨by decide, by decide, rfl⟩
theorem gA : GlobLocs esA := globLocs_of (by decide)

theorem po_of {a b : EventId} (h : (a, b) ∈ esA.po) : esA.poR a b := h

/-- `r0` reads `flag := 1`. -/
def rfA : List (EventId × EventId) := [(6, 3)]

theorem sw63 {x : Execution} (h : x.rf 6 3) : x.sw esA 6 3 :=
  ⟨.inl ⟨_, rfl, rfl⟩, 6, 6, 3, .inl rfl,
    ⟨⟨_, rfl, rfl⟩, 6, .inl rfl, ⟨_, rfl, rfl⟩, .inl rfl⟩,
    h, ⟨_, rfl, rfl⟩, .inl rfl, .inl ⟨_, rfl, rfl⟩⟩

/-! ## RC11 forbids it -/

def xR : Execution := simple esA rfA

/-- **RC11 forbids `r0 = 1` with `x` ending at `2`**: every coherence order
    puts `x := 2` before the second `x := 1`. -/
theorem rc11_forbids :
    xR.IsExecution esA (fun _ => True) ∧ xR.phi esA ∧
    ∀ co, xR.CoherenceOrder esA co → xR.Coherence esA co → co 5 4 := by
  refine ⟨isExecution_simple SA (by decide),
    phi_simple SA (by decide) (by decide) (by decide)
      (fun α => if α = 3 then .num 1 else .num 0) (by decide), fun co hco hcoh => ?_⟩
  have X : ∀ e ∈ esA.events, xR.X e.id :=
    fun e he => X_simple SA he (by revert e; decide) (by revert e; decide)
  have X3 := X (R 3 0 [1, 1, 0, 1, 0] .acq "flag") (by simp [esA])
  have X4 := X e4 (by simp [esA])
  have X5 := X e5 (by simp [esA])
  have X6 := X e6 (by simp [esA])
  rcases hco.total 5 4 X5 X4 ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩ (by decide)
    (sameLoc_of rfl rfl rfl rfl) with h | h
  · exact h
  · have hb : xR.hb esA 5 4 :=
      .tail (.tail (.single (.inl (poX_of X5 X6 (po_of (by decide))))) (.inr
        (sw63 (show (6, 3) ∈ rfA by decide))))
        (.inl (poX_of X3 X4 (po_of (by decide))))
    exact absurd ⟨4, hb, .inr (.single (.inl (.inr h)))⟩ (hcoh 5)

/-! ## Forwarding the first `x := 1` into the second -/

def jB : Justification := pj e2

/-- The pre-justification of the first `x := 1` with the second forwarded
    from it, `F = {(2, 4)}`; `g = [1 ↦ 1]` changes nothing. -/
def jF : Justification :=
  { P := jB.P.replace (Expr.num 1) (Expr.num 1)
    D := ((Expr.num 1).replace (Expr.num 1) (Expr.num 1)).syms ++
      ((Expr.glob "x").replace (Expr.num 1) (Expr.num 1)).syms
    δ := { jB.δ with f := jB.δ.f ++ [(2, 4)] }
    w := { jB.w with
      kind := EventKind.write .rlx ((Expr.glob "x").replace (Expr.num 1) (Expr.num 1))
        ((Expr.num 1).replace (Expr.num 1) (Expr.num 1)) false } }

theorem jF_eq : jF = { jB with δ := ⟨[(2, 4)], []⟩ } := by
  simp only [jF, Expr.replace_same]
  rfl

def JF : List Justification := [pj e0, pj e1, jF, pj e5, pj e6]
def xF : Execution := ⟨esA.Candidate, JF, fun w r => (w, r) ∈ rfA⟩
/-- `x`: `0 < 1 < 2` (the first `x := 1`), `x := 2` last; `flag`: `0 < 1`. -/
def coF : List (EventId × EventId) := [(0, 2), (2, 5), (0, 5), (1, 6)]

theorem δF : xF.δ = ⟨[(2, 4)], []⟩ := by
  simp only [xF, JF, Execution.δ, List.foldr, jF_eq]
  rfl

theorem edge_F {a b : EventId} (h : xF.δ.edge a b) : a = 2 ∧ b = 4 := by
  rw [δF] at h
  rcases h with h | h
  · simp at h; exact h
  · cases h

theorem elided_F {a : EventId} : xF.elided a ↔ a = 4 := by
  constructor
  · intro h; obtain ⟨b, hb⟩ := (xF.elided_iff a).1 h; exact (edge_F hb).2
  · rintro rfl; exact ⟨(2, 4), .inl (by rw [δF]; simp), rfl⟩

def fF (a : EventId) : EventId := if a = 4 then 2 else a

theorem remap_F {a a' : EventId} (h : xF.δ.Remap a a') : a' = fF a := by
  induction h with
  | @canon e hno =>
      unfold fF
      split
      · subst_vars; exact absurd (show xF.δ.edge 2 4 from .inl (by rw [δF]; simp)) (hno 2)
      · rfl
  | step he hr ih =>
      obtain ⟨rfl, rfl⟩ := edge_F he
      cases hr with
      | canon _ => rfl
      | step he' _ => exact absurd (edge_F he').2 (by decide)

theorem X_F {a : EventId} : xF.X a ↔ a ∈ esA.ids := by
  constructor
  · exact ids_of_cand
  · intro h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    exact cand_of_mem SA.nodup he (by revert e; decide) (by revert e; decide)

theorem pre_A {w : Event} (hw : w ∈ esA.events) (hk : preJust w = some (pj w)) :
    esA.Generated (fun _ => True) (pj w) :=
  .pre hw hk ⟨fun _ => .num 0, SA.holds hw _⟩

/-- Store-store forwarding of the first `x := 1` into the second: the first
    is the immediate `≼`-predecessor of the second at its location, as the
    acquire `r0` orders only events after it. -/
theorem fwd_24 : esA.fwdRel jB 2 4 := by
  have hδ0 : ∀ a b, ¬ jB.δ.edge a b := by
    intro a b h; rcases h with h | h <;> cases h
  have hppo : ∀ a b, esA.ppo jB.P.holds jB.δ a b → (a, b) ∈ syncL esA ++ aliasL esA :=
    fun a b h => ppo_mem rfl gA hδ0 h
  refine ⟨⟨⟨⟨(FwdCtx.remapRel_of_noEdge hδ0).2 (.inr
      ⟨po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl, fun _ => .num 0,
        SA.holds (e := e2) (by simp [esA, e2]) _,
        by simp [Expr.holds, Expr.eval, Expr.glob]⟩), by decide⟩, ?_⟩,
      po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl, fun _ _ _ _ h₁ h₂ => by rw [h₁] at h₂; cases h₂; rfl⟩,
    .inr (.inl ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩),
    fun ⟨e, he, hp⟩ => by cases he; simp [e4, W, Event.isVol] at hp⟩
  rintro ⟨e'', h₁, h₂⟩
  have m₁ := hppo _ _ h₁
  have m₂ := hppo _ _ h₂
  have key : ∀ p ∈ syncL esA ++ aliasL esA, ∀ q ∈ syncL esA ++ aliasL esA,
      p.1 = 2 → q.2 = 4 → p.2 = q.1 → False := by decide
  exact key _ m₁ _ m₂ rfl rfl rfl

theorem gen_jF : esA.Generated (fun _ => True) jF := by
  refine .fwd (o := .rlx) (x := Expr.glob "x") (e := Expr.num 1) (b := false)
    (ev₁ := e2) (ev₂ := e4) (pre_A (by simp [esA, e2]) rfl) rfl fwd_24 rfl rfl rfl rfl ?_ ?_
  · refine ⟨fun a ha => ?_, fun a b e ha hb => ?_⟩
    · have : ∀ c d, Relation.TransGen
          ({ jB.δ with f := jB.δ.f ++ [(2, 4)] } : FwdCtx).edge c d → c = 2 ∧ d = 4 := by
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
  · refine ⟨fun _ => .num 0, ?_, trivial⟩
    rw [Expr.replace_same]
    simp [jB, pj, e2, W, Event.valres, Expr.conj, Expr.holds, Expr.eval, Expr.tt]

theorem mem_JF {j : Justification} (hj : j ∈ JF) :
    j = pj e0 ∨ j = pj e1 ∨ j = jF ∨ j = pj e5 ∨ j = pj e6 := by
  simpa [JF] using hj

theorem J_F {j : Justification} (hj : j ∈ JF) : (∀ f, j.P.holds f) ∧ j.P.syms = [] ∧ j.D = [] := by
  rcases mem_JF hj with rfl | rfl | rfl | rfl | rfl <;> (try rw [jF_eq]) <;>
    exact ⟨fun _ => by simp [jB, pj, e0, e1, e2, e5, e6, W, Event.valres, Expr.conj,
      Expr.holds, Expr.eval, Expr.tt],
      by simp [jB, pj, e0, e1, e2, e5, e6, W, Event.valres, Expr.conj, Expr.syms, Expr.tt],
      rfl⟩

/-- `ψ_δ`: the forwarded and the forwarding write write the same value. -/
theorem psi_F (f : Valuation) : xF.δ.psi esA f := by
  rw [δF]
  intro p hp e₁ e₂ v₁ v₂ h₁ h₂ hv₁ hv₂
  simp only [List.mem_singleton] at hp
  subst hp
  have h₁' : esA.ev 2 = some e2 := rfl
  have h₂' : esA.ev 4 = some e4 := rfl
  rw [h₁'] at h₁; rw [h₂'] at h₂; cases h₁; cases h₂
  cases hv₁; cases hv₂
  simp [Expr.holds, Expr.eval, Expr.num]

theorem P_F (f : Valuation) : xF.P esA f := fun j hj => by
  refine ⟨(J_F hj).1 f, fun p hp => ?_⟩
  rcases mem_JF hj with rfl | rfl | rfl | rfl | rfl
  · simp [pj, FwdCtx.empty] at hp
  · simp [pj, FwdCtx.empty] at hp
  · exact psi_F f p (by rw [δF]; rw [jF_eq] at hp; exact hp)
  · simp [pj, FwdCtx.empty] at hp
  · simp [pj, FwdCtx.empty] at hp

theorem no_dp_F {a b : EventId} : ¬ xF.DP a b := by
  rintro ⟨-, -, j, hj, -, h⟩
  rw [(J_F hj).2.1, (J_F hj).2.2] at h
  rcases h with h | h <;> cases h

theorem rfOK_F : RfOK esA rfA := by decide

/-- **The execution forwarding across the acquire is one of sMRD's.** -/
theorem isExecution_F : xF.IsExecution esA (fun _ => True) where
  maximal := ⟨fun _ h => h, fun a b _ _ ⟨ea, eb, ha, hb, hn⟩ =>
      hn ⟨fun _ => .num 0, SA.holds (ev_inv ha).1 _, SA.holds (ev_inv hb).1 _⟩,
    fun _ hc hn => absurd hc hn⟩
  generated j hj := by
    rcases mem_JF hj with rfl | rfl | rfl | rfl | rfl
    · exact pre_A (by simp [esA, e0]) rfl
    · exact pre_A (by simp [esA, e1]) rfl
    · exact gen_jF
    · exact pre_A (by simp [esA, e5]) rfl
    · exact pre_A (by simp [esA, e6]) rfl
  inX j hj := by
    rcases mem_JF hj with rfl | rfl | rfl | rfl | rfl <;> (try rw [jF_eq]) <;> exact X_F.2 (by decide)
  consistent := ⟨fun _ => .num 0, fun j hj => (J_F hj).1 _,
    fun a e _ he => SA.holds (ev_inv he).1 _⟩
  fwdWF := by
    rw [δF]
    refine ⟨fun a ha => ?_, fun a b e ha hb => ?_⟩
    · have : ∀ c d, Relation.TransGen (FwdCtx.edge ⟨[(2, 4)], []⟩) c d → c = 2 ∧ d = 4 := by
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
    obtain ⟨h₁, h₂⟩ := rfOK_F.1 _ h
    have hw := cls_clsB.2 h₁
    have hr := cls_clsB.2 h₂
    exact ⟨hw, hr, cand_of_cls SA.nodup (fun e he => wr_nb e (.inl he)) hw,
      cand_of_cls SA.nodup (fun e he => wr_nb e (.inr he)) hr⟩
  rf_func w w' r h h' := rfOK_F.2 _ h _ h' rfl
  justified w hw he hn := by
    have hids : ∀ w ∈ esA.ids, clsB esA Event.isEffect w = true → w ≠ 4 →
        w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 5 ∨ w = 6 := by decide
    have hw' := hids w (X_F.1 hw) (cls_clsB.1 he) (fun h => hn (elided_F.2 h))
    have uniq : ∀ j j', j ∈ JF → j' ∈ JF → j.w.id = j'.w.id → j' = j := by
      intro j j' hj hj' h
      rcases mem_JF hj with rfl | rfl | rfl | rfl | rfl <;>
        rcases mem_JF hj' with rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | (rw [jF_eq] at h; simp [jB, pj, e0, e1, e2, e5, e6, W] at h) |
          (simp [pj, e0, e1, e5, e6, W] at h)
    rcases hw' with rfl | rfl | rfl | rfl | rfl
    · exact ⟨pj e0, by simp [xF, JF], rfl, fun j' hj' h => uniq _ _ (by simp [JF]) hj' h.symm⟩
    · exact ⟨pj e1, by simp [xF, JF], rfl, fun j' hj' h => uniq _ _ (by simp [JF]) hj' h.symm⟩
    · exact ⟨jF, by simp [xF, JF], by rw [jF_eq]; rfl,
        fun j' hj' h => uniq _ _ (by simp [JF]) hj' (by rw [h, jF_eq]; rfl)⟩
    · exact ⟨pj e5, by simp [xF, JF], rfl, fun j' hj' h => uniq _ _ (by simp [JF]) hj' h.symm⟩
    · exact ⟨pj e6, by simp [xF, JF], rfl, fun j' hj' h => uniq _ _ (by simp [JF]) hj' h.symm⟩

/-- The outcome: `r0` reads `1`. -/
def fOut : Valuation := fun α => if α = 3 then .num 1 else .num 0

theorem phi_F : xF.phi esA := by
  refine ⟨fun e h hel => ?_, fun r => ⟨?_, ?_⟩, fOut, P_F fOut, ⟨?_, ?_, ?_⟩⟩
  · rw [elided_F] at hel; subst hel
    rcases h with ⟨r, hr⟩ | ⟨b, hb⟩
    · have : ∀ p ∈ rfA, p.1 ≠ 4 := by decide
      exact this _ hr rfl
    · exact no_dp_F hb
  · rintro ⟨w, hw⟩
    obtain ⟨-, h₂⟩ := rfOK_F.1 _ hw
    exact ⟨X_F.2 (clsB_id h₂), cls_clsB.2 h₂⟩
  · rintro ⟨hX, hr⟩
    have key : ∀ r ∈ esA.ids, clsB esA Event.isRead r = true → ∃ p ∈ rfA, p.2 = r := by decide
    obtain ⟨p, hp, rfl⟩ := key r (X_F.1 hX) (cls_clsB.1 hr)
    exact ⟨p.1, hp⟩
  · intro w r ew er h hw hr
    have key : ∀ p ∈ rfA, ∀ ew ∈ esA.events, ∀ er ∈ esA.events, ew.id = p.1 → er.id = p.2 →
        ew.loc.map (·.eval fOut) = er.loc.map (·.eval fOut) ∧
        ew.val.map (·.eval fOut) = er.val.map (·.eval fOut) := by decide
    have := key (w, r) h ew (ev_inv hw).1 er (ev_inv hr).1 (ev_inv hw).2 (ev_inv hr).2
    refine ⟨fun lw lr h₁ h₂ => ?_, fun vw vr h₁ h₂ => ?_⟩
    · have := this.1; rw [h₁, h₂] at this; exact Option.some.inj this
    · have := this.2; rw [h₁, h₂] at this; exact Option.some.inj this
  · intro a e α sz _ he hk
    obtain ⟨hm, -⟩ := ev_inv he
    simp only [esA, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hk
  · intro a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂ _ _ _ he₁ _ hk₁
    obtain ⟨hm, -⟩ := ev_inv he₁
    simp only [esA, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hk₁

def rkF (a : EventId) : Nat :=
  match a with
  | 0 => 0 | 1 => 0 | 5 => 1 | 6 => 2 | 3 => 3 | 2 => 4 | _ => 5

/-- No-Thin-Air holds: the backward pair `(r0, x := 1)` ends at an event with
    no edge out. -/
theorem ntaF : xF.NoThinAir esA := by
  have hstep : ∀ a b, xF.ppoStep esA a b → rkF a < rkF b := by
    intro a b h
    have hne : a ≠ b := by
      obtain ⟨-, -, ⟨j, -, hp, -⟩ | ⟨hs | ⟨hp, -⟩, -⟩⟩ := h
      · exact hp.2
      · exact hs.2
      · exact hp.2
    obtain ⟨Pa, Pr, hp⟩ := ppoStep_ppoM h
    have hm := ppoM_mem_f rfl gA (fun a a' h => remap_F h) hp
    have key : ∀ p ∈ (syncML esA ++ aliasL esA).map (fun p => (fF p.1, fF p.2)),
        p.1 ≠ p.2 → rkF p.1 < rkF p.2 := by decide
    exact key _ hm hne
  have mono : ∀ {R : Rel}, (∀ a b, R a b → rkF a < rkF b) →
      ∀ a b, Relation.TransGen R a b → rkF a < rkF b := by
    intro R hR a b h
    induction h with
    | single h => exact hR _ _ h
    | tail _ h ih => exact Nat.lt_trans ih (hR _ _ h)
  have hedge : ∀ a b, ((xF.dep esA).union xF.rf) a b → rkF a < rkF b := by
    rintro a b ((⟨-, -, hp⟩ | hd) | hrf)
    · exact mono hstep a b hp
    · exact absurd hd no_dp_F
    · have key : ∀ p ∈ rfA, rkF p.1 < rkF p.2 := by decide
      exact key _ hrf
  intro a h
  exact Nat.lt_irrefl _ (mono hedge a a h)

theorem locOf_F {a b : EventId} (h : xF.sameLoc esA a b) : locOf esA a = locOf esA b := by
  obtain ⟨ea, eb, la, lb, ha, hb, hla, hlb, heq⟩ := h
  obtain ⟨x, rfl⟩ := gA ea (ev_inv ha).1 _ hla
  obtain ⟨y, rfl⟩ := gA eb (ev_inv hb).1 _ hlb
  have := heq (fun _ => .num 0) (P_F _) _ _ rfl rfl
  cases this
  simp [locOf, ha, hb, hla, hlb]

theorem coherenceOrderT_F : xF.CoherenceOrderT esA (relL coF) where
  writes a b h := by
    have hw : ∀ p ∈ coF, clsB esA Event.isWrite p.1 = true ∧ clsB esA Event.isWrite p.2 = true ∧
        p.1 ∈ esA.ids ∧ p.2 ∈ esA.ids ∧ p.1 ≠ 4 ∧ p.2 ≠ 4 := by decide
    obtain ⟨h1, h2, i1, i2, n1, n2⟩ := hw _ h
    exact ⟨⟨X_F.2 i1, fun h => n1 (elided_F.1 h)⟩, ⟨X_F.2 i2, fun h => n2 (elided_F.1 h)⟩,
      cls_clsB.2 h1, cls_clsB.2 h2⟩
  irrefl a h := by
    have : ∀ p ∈ coF, p.1 ≠ p.2 := by decide
    exact this _ h rfl
  trans a b c h₁ h₂ := by
    have : Closed coF := by decide
    exact this _ h₁ _ h₂ rfl
  total a b ha hb hwa hwb hne hsl := by
    have key : ∀ a ∈ esA.ids.filter (· != 4), ∀ b ∈ esA.ids.filter (· != 4),
        clsB esA Event.isWrite a = true →
        clsB esA Event.isWrite b = true → a ≠ b → locOf esA a = locOf esA b →
        (a, b) ∈ coF ∨ (b, a) ∈ coF := by decide
    exact key a (List.mem_filter.2 ⟨X_F.1 ha.1, by simpa using fun h => ha.2 (elided_F.2 h)⟩)
      b (List.mem_filter.2 ⟨X_F.1 hb.1, by simpa using fun h => hb.2 (elided_F.2 h)⟩)
      (cls_clsB.1 hwa) (cls_clsB.1 hwb) hne (locOf_F hsl)

/-- A bound on `HB_T`. -/
def HF : List (EventId × EventId) := esA.po ++ [(6, 3), (5, 3), (6, 4), (5, 4)]
/-- A bound on `ECO`. -/
def EF : List (EventId × EventId) := [(6, 3), (0, 2), (2, 5), (0, 5), (1, 6), (1, 3)]

theorem coherenceT_F : xF.CoherenceT esA (relL coF) := by
  have hH : ∀ a b, xF.hbT esA a b → (a, b) ∈ HF := by
    intro a b h
    refine transGen_mem (fun c d s => ?_) (by decide) h
    rcases s with ⟨⟨-, -, hpo⟩, -⟩ | ⟨hs, -⟩
    · exact List.mem_append_left _ hpo
    · have hsw : ∀ p ∈ swL esA, p ∈ HF := by decide
      exact hsw _ (sw_mem hs)
  have hE : ∀ a b, xF.eco (relL coF) a b → (a, b) ∈ EF :=
    fun a b h => eco_mem (fun a b h => by
        have : ∀ p ∈ rfA, p ∈ EF := by decide
        exact this _ h)
      (fun a b h => by
        have : ∀ p ∈ coF, p ∈ EF := by decide
        exact this _ h)
      (fun a b h => by
        have : ∀ p ∈ frL rfA coF, p ∈ EF := by decide
        obtain ⟨w, hrf, hco⟩ := h
        exact this _ (List.mem_flatMap.2 ⟨(w, a), hrf, List.mem_map.2 ⟨(w, b),
          List.mem_filter.2 ⟨hco, by simp⟩, rfl⟩⟩))
      (by decide) h
  have hok : ∀ p ∈ HF, p.1 ≠ p.2 ∧ (p.2, p.1) ∉ EF := by decide
  rintro a ⟨b, hab, rfl | hba⟩
  · exact (hok _ (hH _ _ hab)).1 rfl
  · exact (hok _ (hH _ _ hab)).2 (hE _ _ hba)

/-- **`CoherenceT` admits the outcome RC11 forbids, by Forwarding across the
    acquire**: `xF` is an execution of sMRD with `φ`, No-Thin-Air and
    `CoherentT` under `coF`, in which `r0` reads `flag := 1` and `x := 2` is
    coherence-last among the writes to `x` of `X ∖ †`. -/
theorem fwd_admitted :
    xF.ConsistentT esA (fun _ => True) ∧ xF.CoherenceOrderT esA (relL coF) ∧
    xF.CoherenceT esA (relL coF) ∧ xF.rf 6 3 ∧ xF.elided 4 ∧
    ∀ w, xF.XT w → w ≠ 5 → (relL coF) w 5 ∨ ¬ xF.sameLoc esA w 5 := by
  refine ⟨⟨isExecution_F, phi_F, ntaF, relL coF, coherenceOrderT_F, coherenceT_F,
    fun r w h => by obtain ⟨-, -, ent, hm, -⟩ := h; cases hm⟩,
    coherenceOrderT_F, coherenceT_F, show (6, 3) ∈ rfA by decide, elided_F.2 rfl, ?_⟩
  intro w hw hne
  by_cases hs : xF.sameLoc esA w 5
  · left
    have key : ∀ w ∈ esA.ids.filter (· != 4), w ≠ 5 → locOf esA w = locOf esA 5 →
        (w, 5) ∈ coF := by decide
    exact key w (List.mem_filter.2 ⟨X_F.1 hw.1, by simpa using fun h => hw.2 (elided_F.2 h)⟩)
      hne (locOf_F hs)
  · exact .inr hs

/-- **`HB_v`-coherence forbids it**: `x := 2 ≼ flag := 1 →sw r0`, and the
    remapped `ppo_sync` pair `(r0, x := 1)` (from `(r0, x := 1)`, the second,
    forwarded onto the first) closes `x := 2 → x := 1 →co x := 2`. -/
theorem fwd_not_coherenceV : ¬ xF.CoherenceV esA (relL coF) := by
  intro h
  have X : ∀ a ∈ esA.ids, xF.X a := fun a ha => X_F.2 ha
  have X2 := X 2 (by decide)
  have X3 := X 3 (by decide)
  have X5 := X 5 (by decide)
  have X6 := X 6 (by decide)
  have canon : ∀ a, a ≠ 4 → xF.δ.Remap a a := fun a ha =>
    .canon fun c hc => ha (edge_F hc).2
  -- `x := 2 ≼ flag := 1`
  have p56 : xF.ppo esA 5 6 :=
    ⟨X5, X6, .single ⟨.inl X5, .inl X6, .inr ⟨.inl ⟨⟨5, 6,
      ⟨po_of (by decide), .inr ⟨_, rfl, rfl⟩⟩, canon 5 (by decide), canon 6 (by decide)⟩,
      by decide⟩, ⟨6, .inl X6, .inr (po_of (by decide)), .inl rfl⟩⟩⟩⟩
  -- `r0 ≼ x := 1` (the first), remapped
  have p32 : xF.ppo esA 3 2 :=
    ⟨X3, X2, .single ⟨.inl X3, .inl X2, .inr ⟨.inl ⟨⟨3, 4,
      ⟨po_of (by decide), .inl ⟨_, rfl, rfl⟩⟩, canon 3 (by decide),
      .step (.inl (by rw [δF]; simp)) (canon 2 (by decide))⟩, by decide⟩,
      ⟨3, .inl X3, .inl rfl, .inr (po_of (by decide))⟩⟩⟩⟩
  exact h 5 ⟨2, .tail (.tail (.single (.inl (.inl p56))) (.inr (sw63 (show (6, 3) ∈ rfA by decide))))
    (.inl (.inl p32)), .inr (.single (.inl (.inr (show (2, 5) ∈ coF by decide))))⟩

end FwdAcrossAcquire
