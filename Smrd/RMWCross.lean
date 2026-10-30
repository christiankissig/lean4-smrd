import Smrd.FwdEntailsRMW
import Smrd.FwdEntailsCheck
import Smrd.RMWElision

/-!
# Write Elision across an RMW access

`NoRevRMW` (`Smrd.FwdEntails`), the RMW part of `NoRevLoc`, does not follow
from the restrictions on Forwarding and Write Elision, nor from
`FwdEntailsAll`:

`y := 0; x := 1; a := FADD_rlx(y, 1); x := 2`, all accesses relaxed, with
`x := 1` elided into `x := 2`. The elision crosses the FADD, which is at
another location and synchronises with nothing, so `x := 1` is the immediate
`≼`-predecessor of `x := 2`; no release lies between, and the elided write is
no RMW access. `remap_δ` moves `x := 1` to `x := 2`, past the FADD's read: the
pair `x := 1 ⊑ e_r` is reversed.

* `rmwCross`: the execution is consistent (`ConsistentT`), satisfies every
  hypothesis of `dep_po_E` but `NoRevRMW`, `FwdEntailsAll`, and `RMWWF`; it
  violates `NoRevRMW`, `NoRevLoc` and `NoCrossRMW`, while `DP ∪ ≼ ⊆ ⊑` holds
  (`dep_po_R`). So `NoRevRMW` is not necessary for `DP ∪ ≼ ⊆ ⊑`, and
  `noRevLoc_of_fwdEntailsAll` has no version without an RMW hypothesis.

## `x := 1; FADD_rel(x, 1)`

The FADD's write `e_w` releases. Eliding `x := 1` into `e_w` would cross the
FADD's read `e_r`, which the release restriction allows (a relaxed read
publishes nothing). `pred` refuses it: `x := 1 ≼_sync e_w` and
`e_w ⊑ʳᵐʷ e_r` give `x := 1 ≼_rmw e_r`, and `e_r ≼_sync e_w`, so `e_r` is
`≼`-between, under every predicate (`not_weRel_fadd`, `fadd_not_generated`).
-/

namespace RMWCross

open EventStructure PpoKit PpoNecessity Execution WEAcrossRelease

/-! ## The program -/

/-- `y := 0; x := 1; a := FADD_rlx(y, 1); x := 2` -/
def prog : Stmt :=
  .seq (PpoStability.st .rlx "y" 0)
    (.seq (PpoStability.st .rlx "x" 1)
      (.seq (.fadd .rlx .rlx "a" "y" (.num 1)) (PpoStability.st .rlx "x" 2)))

/-- The write of a FADD on `y` reading `r`. -/
def FWy (i r : Nat) (pc : List Nat) : Event :=
  ⟨i, .write .rlx (Expr.glob "y") (.bin .add (.sym r) (.val (.num 1))) false, ⟨0, pc, []⟩, []⟩

def e0 : Event := W 0 0 [0] .rlx "y" 0
def e1 : Event := W 1 0 [1, 0] .rlx "x" 1
def e2 : Event := R 2 0 [1, 1, 0, 0] .rlx "y"
def e3 : Event := FWy 3 2 [1, 1, 0, 1]
def e4 : Event := W 4 0 [1, 1, 1] .rlx "x" 2

def esX : EventStructure :=
  ⟨[e0, e1, e2, e3, e4],
   [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)],
   [⟨2, .val (.bool true), 3⟩]⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esX := rfl

theorem SX0 : Simple { esX with rmw := [] } := ⟨by decide, by decide, rfl⟩

theorem nodupX : (esX.events.map (·.id)).Nodup := SX0.nodup

theorem holdsX {e : Event} (he : e ∈ esX.events) (f : Valuation) : e.valres.holds f :=
  SX0.holds (e := e) he f

theorem gX : GlobLocs esX := globLocs_of (by decide)

theorem po_of {a b : EventId} (h : (a, b) ∈ esX.po) : esX.poR a b := h

theorem syncX_nil : syncL esX = [] := by decide
theorem syncMX_nil : syncML esX = [] := by decide

theorem rmw23 : (⟨2, .val (.bool true), 3⟩ : RMWEntry) ∈ esX.rmw := by simp [esX]

theorem acc2 : esX.RMWAcc 2 := ⟨_, rmw23, .inl rfl⟩
theorem acc3 : esX.RMWAcc 3 := ⟨_, rmw23, .inr rfl⟩

/-- `≼` with `δ` empty, bounded by the alias pairs: no `ppo_sync`, hence no
    `ppo_rmw`. -/
theorem ppo_memX {P : Pred} {δ : FwdCtx} (hδ : ∀ a b, ¬ δ.edge a b) {a b : EventId}
    (h : esX.ppo P δ a b) : (a, b) ∈ aliasL esX := by
  obtain ⟨hab, -⟩ := h
  rcases (FwdCtx.remapRel_of_noEdge hδ).1 hab with (hs | ⟨⟨y, hs, -⟩ | ⟨y, -, hs⟩, -⟩) | ⟨hpo, hal⟩
  all_goals first
    | exact mayAlias_mem gX hpo hal
    | (have := ppoSync_mem hs; rw [syncX_nil] at this; cases this)

/-- MoRDor's `≼`, remapped by a function `g`, bounded by the alias pairs. -/
theorem ppoM_memX {Pa Pr : Pred} {δ : FwdCtx} {g : EventId → EventId}
    (hg : ∀ a a', δ.Remap a a' → a' = g a) {a b : EventId} (h : esX.ppoM Pa Pr δ a b) :
    (a, b) ∈ (aliasL esX).map (fun p => (g p.1, g p.2)) := by
  obtain ⟨⟨a₀, b₀, hab, ra, rb⟩, -⟩ := h
  have base : (a₀, b₀) ∈ aliasL esX := by
    rcases hab with (hs | (⟨y, hs, -⟩ | ⟨y, -, hs⟩)) | ⟨hpo, hm | hal⟩
    all_goals first
      | exact mustAlias_mem gX hpo hm
      | exact mayAlias_mem gX hpo hal
      | (have := ppoSyncM_mem hs; rw [syncMX_nil] at this; cases this)
  exact List.mem_map.2 ⟨_, base, by rw [hg _ _ ra, hg _ _ rb]⟩

/-! ## The elision -/

/-- `x := 2`'s pre-justification. -/
def jB : Justification := pj e4
/-- `x := 2`'s justification with `x := 1` elided: `WE = {(4, 1)}`. -/
def jWE : Justification := { jB with δ := { jB.δ with we := jB.δ.we ++ [(4, 1)] } }
/-- The FADD's write's pre-justification, depending on its read. -/
def j3 : Justification := ⟨e3.valres, [2], .empty, e3⟩
def JX : List Justification := [pj e0, jWE, j3]
def rfX : List (EventId × EventId) := [(0, 2)]
def xX : Execution := ⟨esX.Candidate, JX, fun w r => (w, r) ∈ rfX⟩
def coX : List (EventId × EventId) := [(0, 3)]

theorem pre_X {w : Event} {j : Justification} (hw : w ∈ esX.events) (hk : preJust w = some j) :
    esX.Generated (fun _ => True) j :=
  .pre hw hk ⟨fun _ => .num 0, holdsX hw _⟩

/-- **Write Elision elides `x := 1` into `x := 2` across the FADD**: `x := 1`
    is the immediate `≼`-predecessor of `x := 2`, no release lies between, and
    `x := 1` is no RMW access. -/
theorem we_14 : esX.weRel jB 1 4 := by
  have hδ0 : ∀ a b, ¬ jB.δ.edge a b := by
    intro a b h; rcases h with h | h <;> cases h
  refine ⟨⟨⟨⟨⟨(FwdCtx.remapRel_of_noEdge hδ0).2 (.inr
      ⟨po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl, fun _ => .num 0,
        holdsX (e := e4) (by simp [esX]) _,
        by simp [Expr.holds, Expr.eval, Expr.glob]⟩), by decide⟩, ?_⟩,
      po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl,
      fun _ _ _ _ h₁ h₂ => by rw [h₁] at h₂; cases h₂; rfl⟩,
    ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, fun ⟨e, he, hp⟩ => by cases he; simp [e1, W, Event.isVol] at hp⟩,
    weNoRel_of (by decide) (by decide),
    Execution.weNoJoin_of_poForest (poForest_of (by decide)) _ _, fun ⟨ent, hm, h⟩ => by
      simp only [esX, List.mem_cons, List.mem_nil_iff, or_false] at hm
      subst hm; simp at h⟩
  rintro ⟨e'', h₁, h₂⟩
  have m₁ := ppo_memX hδ0 h₁
  have m₂ := ppo_memX hδ0 h₂
  have key : ∀ p ∈ aliasL esX, ∀ q ∈ aliasL esX, p.1 = 1 → q.2 = 4 → p.2 = q.1 → False := by
    decide
  exact key _ m₁ _ m₂ rfl rfl rfl

theorem wf_we : FwdCtx.WF { jB.δ with we := jB.δ.we ++ [(4, 1)] } := by
  refine ⟨fun a ha => ?_, fun a b e ha hb => ?_⟩
  · have : ∀ c d, Relation.TransGen
        ({ jB.δ with we := jB.δ.we ++ [(4, 1)] } : FwdCtx).edge c d → c = 4 ∧ d = 1 := by
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

theorem gen_jB : esX.Generated (fun _ => True) jB := pre_X (w := e4) (by simp [esX]) rfl

theorem gen_jWE : esX.Generated (fun _ => True) jWE :=
  .we gen_jB we_14 wf_we ⟨fun _ => .num 0, holdsX (e := e4) (by simp [esX]) _, trivial⟩

/-! ## The execution -/

theorem δX : xX.δ = ⟨[], [(4, 1)]⟩ := rfl

theorem edge_X {a b : EventId} (h : xX.δ.edge a b) : a = 4 ∧ b = 1 := by
  rw [δX] at h
  rcases h with h | h
  · cases h
  · simp at h; exact h

theorem edge_41 : xX.δ.edge 4 1 := .inr (by rw [δX]; simp)

theorem elided_X {a : EventId} : xX.elided a ↔ a = 1 := by
  constructor
  · intro h; obtain ⟨b, hb⟩ := (xX.elided_iff a).1 h; exact (edge_X hb).2
  · rintro rfl; exact (xX.elided_iff 1).2 ⟨4, edge_41⟩

/-- `remap_δ` moves `x := 1` to `x := 2` and fixes the rest. -/
def gX' (a : EventId) : EventId := if a = 1 then 4 else a

theorem remap_X {a a' : EventId} (h : xX.δ.Remap a a') : a' = gX' a := by
  induction h with
  | @canon e hno =>
      unfold gX'
      split
      · subst_vars; exact absurd edge_41 (hno 4)
      · rfl
  | step he hr ih =>
      obtain ⟨rfl, rfl⟩ := edge_X he
      cases hr with
      | canon _ => rfl
      | step he' _ => exact absurd (edge_X he').2 (by decide)

theorem remap_canon {a : EventId} (h : a ≠ 1) : xX.δ.Remap a a :=
  .canon fun _ hc => h (edge_X hc).2

theorem remap_14 : xX.δ.Remap 1 4 := .step edge_41 (remap_canon (by decide))

theorem X_X {a : EventId} : xX.X a ↔ a ∈ esX.ids := by
  constructor
  · exact ids_of_cand
  · intro h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    exact cand_of_mem nodupX he (by revert e; decide) (by revert e; decide)

theorem mem_JX {j : Justification} (hj : j ∈ JX) : j = pj e0 ∨ j = jWE ∨ j = j3 := by
  simpa [JX] using hj

/-- Every justification of `xX` holds everywhere, none forwards, and only
    `j3` depends, on the FADD's read. -/
theorem J_X {j : Justification} (hj : j ∈ JX) : (∀ f, j.P.holds f) ∧ j.δ.f = [] ∧
    j.P.syms = [] ∧ (j.D = [] ∨ j = j3) := by
  rcases mem_JX hj with rfl | rfl | rfl <;>
    exact ⟨fun _ => by simp [jWE, jB, j3, pj, e0, e3, e4, W, FWy, Event.valres, Expr.conj,
      Expr.holds, Expr.eval, Expr.tt], by simp [jWE, jB, j3, pj, FwdCtx.empty],
      by simp [jWE, jB, j3, pj, e0, e3, e4, W, FWy, Event.valres, Expr.conj, Expr.syms, Expr.tt],
      by simp [jWE, jB, pj]⟩

theorem P_X (f : Valuation) : xX.P esX f := fun j hj =>
  ⟨(J_X hj).1 f, fun p hp => by rw [(J_X hj).2.1] at hp; cases hp⟩

theorem dp_X {a b : EventId} (h : xX.DP a b) : a = 2 ∧ b = 3 := by
  obtain ⟨-, -, j, hj, hw, h⟩ := h
  rw [(J_X hj).2.2.1] at h
  rcases (J_X hj).2.2.2 with hD | rfl
  · rw [hD] at h; rcases h with h | h <;> cases h
  · rcases h with h | h
    · cases h
    · simp [j3] at h; exact ⟨h, hw.symm⟩

theorem rfOK_X : RfOK esX rfX := by decide

theorem isExecution_X : xX.IsExecution esX (fun _ => True) where
  maximal := ⟨fun _ h => h, fun a b _ _ ⟨ea, eb, ha, hb, hn⟩ =>
      hn ⟨fun _ => .num 0, holdsX (ev_inv ha).1 _, holdsX (ev_inv hb).1 _⟩,
    fun _ hc hn => absurd hc hn⟩
  generated j hj := by
    rcases mem_JX hj with rfl | rfl | rfl
    · exact pre_X (w := e0) (by simp [esX]) rfl
    · exact gen_jWE
    · exact pre_X (w := e3) (by simp [esX]) rfl
  inX j hj := by
    rcases mem_JX hj with rfl | rfl | rfl <;> exact X_X.2 (by decide)
  consistent := ⟨fun _ => .num 0, fun j hj => (J_X hj).1 _,
    fun a e _ he => holdsX (ev_inv he).1 _⟩
  fwdWF := by
    rw [δX]
    refine ⟨fun a ha => ?_, fun a b e ha hb => ?_⟩
    · have : ∀ c d, Relation.TransGen (FwdCtx.edge ⟨[], [(4, 1)]⟩) c d → c = 4 ∧ d = 1 := by
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
    obtain ⟨h₁, h₂⟩ := rfOK_X.1 _ h
    have hw := cls_clsB.2 h₁
    have hr := cls_clsB.2 h₂
    exact ⟨hw, hr, cand_of_cls nodupX (fun e he => wr_nb e (.inl he)) hw,
      cand_of_cls nodupX (fun e he => wr_nb e (.inr he)) hr⟩
  rf_func w w' r h h' := rfOK_X.2 _ h _ h' rfl
  justified w hw he hn := by
    have hids : ∀ w ∈ esX.ids, clsB esX Event.isEffect w = true → w ≠ 1 →
        w = 0 ∨ w = 3 ∨ w = 4 := by decide
    have hw' := hids w (X_X.1 hw) (cls_clsB.1 he) (fun h => hn (elided_X.2 h))
    have uniq : ∀ j j', j ∈ JX → j' ∈ JX → j.w.id = j'.w.id → j' = j := by
      intro j j' hj hj' h
      rcases mem_JX hj with rfl | rfl | rfl <;>
        rcases mem_JX hj' with rfl | rfl | rfl <;>
        first | rfl | (simp [jWE, jB, j3, pj, e0, e3, e4, W, FWy] at h)
    rcases hw' with rfl | rfl | rfl
    · exact ⟨pj e0, by simp [xX, JX], rfl, fun j' hj' h => uniq _ _ (by simp [JX]) hj' h.symm⟩
    · exact ⟨j3, by simp [xX, JX], rfl, fun j' hj' h => uniq _ _ (by simp [JX]) hj' h.symm⟩
    · exact ⟨jWE, by simp [xX, JX], rfl, fun j' hj' h => uniq _ _ (by simp [JX]) hj' h.symm⟩

/-- The outcome: the FADD reads `0`. -/
def fOut : Valuation := fun _ => .num 0

theorem phi_X : xX.phi esX := by
  refine ⟨fun e h hel => ?_, fun r => ⟨?_, ?_⟩, fOut, P_X fOut, ⟨?_, ?_, ?_⟩⟩
  · rw [elided_X] at hel; subst hel
    rcases h with ⟨r, hr⟩ | ⟨b, hb⟩
    · have : ∀ p ∈ rfX, p.1 ≠ 1 := by decide
      exact this _ hr rfl
    · exact absurd (dp_X hb).1 (by decide)
  · rintro ⟨w, hw⟩
    obtain ⟨-, h₂⟩ := rfOK_X.1 _ hw
    exact ⟨X_X.2 (clsB_id h₂), cls_clsB.2 h₂⟩
  · rintro ⟨hX, hr⟩
    have key : ∀ r ∈ esX.ids, clsB esX Event.isRead r = true → ∃ p ∈ rfX, p.2 = r := by decide
    obtain ⟨p, hp, rfl⟩ := key r (X_X.1 hX) (cls_clsB.1 hr)
    exact ⟨p.1, hp⟩
  · intro w r ew er h hw hr
    have key : ∀ p ∈ rfX, ∀ ew ∈ esX.events, ∀ er ∈ esX.events, ew.id = p.1 → er.id = p.2 →
        ew.loc.map (·.eval fOut) = er.loc.map (·.eval fOut) ∧
        ew.val.map (·.eval fOut) = er.val.map (·.eval fOut) := by decide
    have := key (w, r) h ew (ev_inv hw).1 er (ev_inv hr).1 (ev_inv hw).2 (ev_inv hr).2
    refine ⟨fun lw lr h₁ h₂ => ?_, fun vw vr h₁ h₂ => ?_⟩
    · have := this.1; rw [h₁, h₂] at this; exact Option.some.inj this
    · have := this.2; rw [h₁, h₂] at this; exact Option.some.inj this
  · intro a e α sz _ he hk
    obtain ⟨hm, -⟩ := ev_inv he
    simp only [esX, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> cases hk
  · intro a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂ _ _ _ he₁ _ hk₁
    obtain ⟨hm, -⟩ := ev_inv he₁
    simp only [esX, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> cases hk₁

/-- `DP ∪ ≼ ∪ rf` increases the event id. -/
theorem ntaX : xX.NoThinAir esX := by
  have hstep : ∀ a b, xX.ppoStep esX a b → a < b := by
    intro a b h
    have hne : a ≠ b := by
      obtain ⟨-, -, ⟨j, -, hp, -⟩ | ⟨hs | ⟨hp, -⟩, -⟩⟩ := h
      · exact hp.2
      · exact hs.2
      · exact hp.2
    obtain ⟨Pa, Pr, hp⟩ := ppoStep_ppoM h
    have hm := ppoM_memX (fun a a' h => remap_X h) hp
    have key : ∀ p ∈ (aliasL esX).map (fun p => (gX' p.1, gX' p.2)),
        p.1 ≠ p.2 → p.1 < p.2 := by decide
    exact key _ hm hne
  have mono : ∀ {R : Rel}, (∀ a b, R a b → a < b) →
      ∀ a b, Relation.TransGen R a b → a < b := by
    intro R hR a b h
    induction h with
    | single h => exact hR _ _ h
    | tail _ h ih => exact Nat.lt_trans ih (hR _ _ h)
  have hedge : ∀ a b, ((xX.dep esX).union xX.rf) a b → a < b := by
    rintro a b ((⟨-, -, hp⟩ | hd) | hrf)
    · exact mono hstep a b hp
    · obtain ⟨rfl, rfl⟩ := dp_X hd; decide
    · have key : ∀ p ∈ rfX, p.1 < p.2 := by decide
      exact key _ hrf
  intro a h
  exact Nat.lt_irrefl _ (mono hedge a a h)

theorem locOf_X {a b : EventId} (h : xX.sameLoc esX a b) : locOf esX a = locOf esX b := by
  obtain ⟨ea, eb, la, lb, ha, hb, hla, hlb, heq⟩ := h
  obtain ⟨x, rfl⟩ := gX ea (ev_inv ha).1 _ hla
  obtain ⟨y, rfl⟩ := gX eb (ev_inv hb).1 _ hlb
  obtain ⟨f, hP, hrf⟩ := phi_X.2.2
  have := heq f hP hrf
  cases this
  simp [locOf, ha, hb, hla, hlb]

theorem coherenceOrderT_X : xX.CoherenceOrderT esX (relL coX) where
  writes a b h := by
    have hw : ∀ p ∈ coX, clsB esX Event.isWrite p.1 = true ∧ clsB esX Event.isWrite p.2 = true ∧
        p.1 ∈ esX.ids ∧ p.2 ∈ esX.ids ∧ p.1 ≠ 1 ∧ p.2 ≠ 1 := by decide
    obtain ⟨h1, h2, i1, i2, n1, n2⟩ := hw _ h
    exact ⟨⟨X_X.2 i1, fun h => n1 (elided_X.1 h)⟩, ⟨X_X.2 i2, fun h => n2 (elided_X.1 h)⟩,
      cls_clsB.2 h1, cls_clsB.2 h2⟩
  irrefl a h := by
    have : ∀ p ∈ coX, p.1 ≠ p.2 := by decide
    exact this _ h rfl
  trans a b c h₁ h₂ := by
    have : Closed coX := by decide
    exact this _ h₁ _ h₂ rfl
  total a b ha hb hwa hwb hne hsl := by
    have key : ∀ a ∈ esX.ids.filter (· != 1), ∀ b ∈ esX.ids.filter (· != 1),
        clsB esX Event.isWrite a = true →
        clsB esX Event.isWrite b = true → a ≠ b → locOf esX a = locOf esX b →
        (a, b) ∈ coX ∨ (b, a) ∈ coX := by decide
    exact key a (List.mem_filter.2 ⟨X_X.1 ha.1, by simpa using fun h => ha.2 (elided_X.2 h)⟩)
      b (List.mem_filter.2 ⟨X_X.1 hb.1, by simpa using fun h => hb.2 (elided_X.2 h)⟩)
      (cls_clsB.1 hwa) (cls_clsB.1 hwb) hne (locOf_X hsl)

/-- A bound on `ECO`. -/
def EX : List (EventId × EventId) := [(0, 2), (0, 3), (2, 3)]

theorem coherenceT_X : xX.CoherenceT esX (relL coX) := by
  have hH : ∀ a b, xX.hbT esX a b → (a, b) ∈ esX.po := by
    intro a b h
    refine transGen_mem (fun c d s => ?_) (by decide) h
    rcases s with ⟨⟨-, -, hpo⟩, -⟩ | ⟨hs, -⟩
    · exact hpo
    · have := sw_mem hs
      have hsw : swL esX = [] := by decide
      rw [hsw] at this; cases this
  have hE : ∀ a b, xX.eco (relL coX) a b → (a, b) ∈ EX :=
    fun a b h => eco_mem (fun a b h => by
        have : ∀ p ∈ rfX, p ∈ EX := by decide
        exact this _ h)
      (fun a b h => by
        have : ∀ p ∈ coX, p ∈ EX := by decide
        exact this _ h)
      (fun a b h => by
        have : ∀ p ∈ frL rfX coX, p ∈ EX := by decide
        obtain ⟨w, hrf, hco⟩ := h
        exact this _ (List.mem_flatMap.2 ⟨(w, a), hrf, List.mem_map.2 ⟨(w, b),
          List.mem_filter.2 ⟨hco, by simp⟩, rfl⟩⟩))
      (by decide) h
  have hok : ∀ p ∈ esX.po, p.1 ≠ p.2 ∧ (p.2, p.1) ∉ EX := by decide
  rintro a ⟨b, hab, rfl | hba⟩
  · exact (hok _ (hH _ _ hab)).1 rfl
  · exact (hok _ (hH _ _ hab)).2 (hE _ _ hba)

theorem atomicity_X : xX.Atomicity esX (relL coX) := by
  rintro r w ⟨-, -, ent, hm, rfl, rfl, -⟩ ⟨w', ⟨w₀, hrf, hco⟩, hco'⟩
  have key : ∀ ent ∈ esX.rmw, ∀ p ∈ rfX, ∀ q ∈ coX, ∀ s ∈ coX,
      p.2 = ent.r → q.1 = p.1 → s.1 = q.2 → s.2 = ent.w → False := by decide
  exact key ent hm (w₀, ent.r) hrf (w₀, w') hco (w', ent.w) hco' rfl rfl rfl rfl

theorem consistentT_X : xX.ConsistentT esX (fun _ => True) :=
  ⟨isExecution_X, phi_X, ntaX, relL coX, coherenceOrderT_X, coherenceT_X, atomicity_X⟩

/-! ## The hypotheses -/

theorem poTrans_X : ∀ a b c, esX.poR a b → esX.poR b c → esX.poR a c :=
  poTrans_of (by decide)

theorem poIrr_X : ∀ a, ¬ esX.poR a a := poIrr_of (by decide)

theorem poForest_X : PoForest esX := poForest_of (by decide)

theorem rmwTightR_X : RMWTightR esX xX := by
  refine ⟨fun ent hm a _ _ _ hpo => ?_, fun ent hm b _ _ _ hpo => ?_⟩ <;>
    simp only [esX, List.mem_cons, List.mem_nil_iff, or_false] at hm <;> subst hm
  · have : ∀ p ∈ esX.po, p.2 = 3 → p.1 = 2 ∨ (p.1, 2) ∈ esX.po := by decide
    exact this (a, 3) hpo rfl
  · have : ∀ p ∈ esX.po, p.1 = 2 → p.2 = 3 ∨ (3, p.2) ∈ esX.po := by decide
    exact this (2, b) hpo rfl

theorem dp_po_X : ∀ a b, xX.DP a b → esX.poR a b := fun a b h => by
  obtain ⟨rfl, rfl⟩ := dp_X h; exact po_of (by decide)

theorem sat_X : Sat (xX.P esX) := ⟨fOut, P_X fOut⟩

theorem locsEval_X : LocsEval esX := fun a e l f he hl => by
  obtain ⟨x, rfl⟩ := gX e (ev_inv he).1 _ hl
  simp [Expr.glob, Expr.eval]

theorem rmwWF_X : RMWWF esX := fun ent hm => by
  simp only [esX, List.mem_cons, List.mem_nil_iff, or_false] at hm
  subst hm
  exact ⟨po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl,
    fun _ _ _ h₁ h₂ => by rw [h₁] at h₂; cases h₂; rfl⟩

/-- The elision is generated against `x := 2`'s pre-justification, whose
    predicate is valid: every scope holds. -/
theorem fwdEntailsAll_X : FwdEntailsAll esX xX :=
  fwdEntailsOn_of_valid (fun s t he => by
    obtain ⟨rfl, rfl⟩ := edge_X he
    exact ⟨jB, 1, 4,
      ⟨.inr ⟨by rw [δX]; simp, rfl, rfl, we_14⟩, fun p hp => (by cases hp),
        fun p hp => (by cases hp)⟩,
      fun f => holdsX (e := e4) (by simp [esX]) f⟩) _

/-- **`NoRevRMW` fails**: `x := 1 ⊑ e_r`, remapped to `x := 2`, after `e_r`. -/
theorem not_noRevRMW : ¬ NoRevRMW esX xX := fun h =>
  h 1 2 4 2 (po_of (by decide)) remap_14 (remap_canon (by decide)) (.inr acc2) (po_of (by decide))

theorem not_noRevLoc : ¬ NoRevLoc esX xX := fun h => not_noRevRMW (noRevRMW_of_noRevLoc h)

theorem not_noCrossRMW : ¬ NoCrossRMW esX xX := fun h =>
  h 4 1 2 edge_41 (.inr ⟨po_of (by decide), po_of (by decide)⟩) acc2

/-- **`NoRevRMW` does not follow from the restrictions**: a consistent
    execution with every hypothesis of `dep_po_E` but `NoRevRMW`, and
    `FwdEntailsAll` (so every scope) and `RMWWF`, where `NoRevRMW`, `NoRevLoc`
    and `NoCrossRMW` fail and `DP ∪ ≼ ⊆ ⊑` holds. -/
theorem rmwCross :
    xX.ConsistentT esX (fun _ => True) ∧
    (∀ a b c, esX.poR a b → esX.poR b c → esX.poR a c) ∧ (∀ a, ¬ esX.poR a a) ∧
    PoForest esX ∧ RMWTightR esX xX ∧ (∀ a b, xX.DP a b → esX.poR a b) ∧
    Sat (xX.P esX) ∧ LocsEval esX ∧ RMWWF esX ∧ FwdEntailsAll esX xX ∧
    ¬ NoRevRMW esX xX ∧ ¬ NoRevLoc esX xX ∧ ¬ NoCrossRMW esX xX ∧
    (∀ a b, xX.dep esX a b → xX.poX esX a b) :=
  ⟨consistentT_X, poTrans_X, poIrr_X, poForest_X, rmwTightR_X, dp_po_X, sat_X, locsEval_X,
    rmwWF_X, fwdEntailsAll_X, not_noRevRMW, not_noRevLoc, not_noCrossRMW,
    fun _ _ h => dep_po_R isExecution_X poTrans_X poIrr_X rmwTightR_X dp_po_X sat_X
      locsEval_X (fwdEntailsAll_X.on _) rmwWF_X h⟩

/-- **`noRevLoc_of_fwdEntailsAll` needs an RMW hypothesis**: `FwdEntailsAll`
    with every other hypothesis does not give `NoRevLoc`. -/
theorem fwdEntailsAll_not_noRevLoc :
    ¬ ∀ (es : EventStructure) (x : Execution) (Ω : Pred), x.IsExecution es Ω →
      (∀ a b c, es.poR a b → es.poR b c → es.poR a c) → (∀ a, ¬ es.poR a a) →
      PoForest es → Sat (x.P es) → LocsEval es → FwdEntailsAll es x → NoRevLoc es x :=
  fun h => not_noRevLoc (h esX xX _ isExecution_X poTrans_X poIrr_X poForest_X sat_X locsEval_X
    fwdEntailsAll_X)

/-! ## `x := 1; FADD_rel(x, 1)`: `pred` refuses the elision -/

/-- `x := 1; a := FADD(x, 1)`, its read relaxed, its write releasing. -/
def progF : Stmt :=
  .seq (PpoStability.st .rlx "x" 1) (.fadd .rlx .rel "a" "x" (.num 1))

def f0 : Event := W 0 0 [0] .rlx "x" 1
def f1 : Event := R 1 0 [1, 0] .rlx "x"
def f2 : Event :=
  ⟨2, .write .rel (Expr.glob "x") (.bin .add (.sym 1) (.val (.num 1))) false, ⟨0, [1, 1], []⟩, []⟩

def esF : EventStructure :=
  ⟨[f0, f1, f2], [(0, 1), (0, 2), (1, 2)], [⟨1, .val (.bool true), 2⟩]⟩

unseal interp in
theorem denote_progF : denote (fun _ => 0) progF = esF := rfl

theorem rmwF : (⟨1, .val (.bool true), 2⟩ : RMWEntry) ∈ esF.rmw := by simp [esF]
theorem accF1 : esF.RMWAcc 1 := ⟨_, rmwF, .inl rfl⟩
theorem accF2 : esF.RMWAcc 2 := ⟨_, rmwF, .inr rfl⟩

/-- The other conditions of Write Elision hold: the read publishes nothing,
    and `x := 1` is no RMW access. -/
theorem weNoRel_02 : esF.weNoRel 0 2 ∧ ¬ esF.RMWAcc 0 :=
  ⟨weNoRel_of (by decide) (by decide), fun ⟨ent, hm, h⟩ => by
    simp only [esF, List.mem_cons, List.mem_nil_iff, or_false] at hm
    subst hm; simp at h⟩

/-- **`pred` refuses to elide `x := 1` into the FADD's write**, under every
    predicate, in every justification that leaves the FADD's accesses in
    place: `x := 1 ≼_rmw e_r ≼_sync e_w`. -/
theorem not_weRel_fadd {j : Justification} (h1 : ∀ a, ¬ j.δ.edge a 1)
    (h2 : ∀ a, ¬ j.δ.edge a 2) : ¬ esF.weRel j 0 2 := by
  rintro ⟨⟨⟨⟨⟨⟨a₀, b₀, -, ra, -⟩, -⟩, hno⟩, -⟩, -⟩, -⟩
  have r0 : j.δ.Remap 0 0 := .canon (Execution.canon_of_remap ra)
  have r1 : j.δ.Remap 1 1 := .canon h1
  have r2 : j.δ.Remap 2 2 := .canon h2
  have nFB : ∀ c, clsB esF Event.isFence c = false → clsB esF Event.isBranch c = false →
      ¬ (esF.cls Event.isFence c ∨ esF.cls Event.isBranch c) := by
    rintro c h₁ h₂ (h | h)
    · rw [cls_clsB.1 h] at h₁; cases h₁
    · rw [cls_clsB.1 h] at h₂; cases h₂
  have s02 : esF.ppoSync 0 2 := by
    simp only [EventStructure.ppoSync, Rel.excl, Rel.union, Rel.comp, diag]
    exact ⟨.inl (.inl ⟨2, (show (0, 2) ∈ esF.po by decide), rfl, cls_clsB.2 (by decide)⟩),
      nFB 0 (by decide) (by decide), nFB 2 (by decide) (by decide)⟩
  have s12 : esF.ppoSync 1 2 := by
    simp only [EventStructure.ppoSync, Rel.excl, Rel.union, Rel.comp, diag]
    exact ⟨.inl (.inl ⟨2, (show (1, 2) ∈ esF.po by decide), rfl, cls_clsB.2 (by decide)⟩),
      nFB 1 (by decide) (by decide), nFB 2 (by decide) (by decide)⟩
  have rp : esF.rmwPairs j.P.holds 2 1 :=
    ⟨_, rmwF, rfl, rfl, fun _ _ _ _ h₁ h₂ => by
      simp only [Expr.tt] at h₂; simp only at h₁; rw [h₁] at h₂; cases h₂; rfl⟩
  have p01 : esF.ppo j.P.holds j.δ 0 1 :=
    ⟨⟨0, 1, .inl (.inr ⟨.inl ⟨2, s02, rp⟩, by decide⟩), r0, r1⟩, by decide⟩
  have p12 : esF.ppo j.P.holds j.δ 1 2 :=
    ⟨⟨1, 2, .inl (.inl s12), r1, r2⟩, by decide⟩
  exact hno ⟨1, p01, p12⟩

/-- **No generated justification elides `x := 1` into the FADD's write.** -/
theorem fadd_not_generated {Ω : Pred} {j : Justification} (h : esF.Generated Ω j) :
    ¬ esF.weRel j 0 2 := by
  have hn := Generated.not_rmwAcc_elided esF h
  refine not_weRel_fadd (fun a ha => ?_) (fun a ha => ?_)
  · exact hn (a, 1) ha accF1
  · exact hn (a, 2) ha accF2

end RMWCross
