import Smrd.RMWWFDenote
import Smrd.DPPast
import Smrd.PpoNecessity

/-!
# Forwarding into the join: `≼` across threads, `PoForest` needed

`dep_po_T`, `dep_po_E` and `dep_po_R` (`DP ∪ ≼ ⊆ ⊑` over `X ∖ †`) assume that
`⊑` is a forest (`PoForest`): the events at or below one event are pairwise
comparable. `⟨P⟩_n` is not a forest once code follows a parallel block:
`(P₁ ∥ P₂); κ` joins, and every event of `κ` lies `⊑`-above both threads.
`PoForest` cannot be dropped from those theorems, for the event structures of
programs either. The program, with `r1 :=_acq z` in one thread and `x := 1` in
the other:

```
z := 0; (r1 :=_acq z ∥ x := 1); r2 := x; y := r2
```

* `y := r2` is justified by `jW`: its pre-justification `j4` with `r2 := x`
  forwarded from `x := 1` (store forwarding, `F = {(x := 1, r2)}`). Under the
  empty context, the immediate `≼`-predecessors of `r2` are `r1 :=_acq z`
  (`≼_sync`) and `x := 1` (`≼_alias`), which `⊑` does not order; so
  `x := 1 ∈ pred(r2)`, and every condition of `fwdRel` holds (`fwd_23`): no
  event lies `⊑`-between `x := 1` and `r2`, so the acquire restriction holds
  although `r1` acquires and is `⊑`-before `r2`.
* The execution `xP` of all events, `J = [z := 0, x := 1, jW]`, `r1` reading
  `z := 0` and `r2` reading `x := 1`, is consistent (`consistentT_P`).
* MoRDor's `ppo_sync` has `(r1, r2)` (an acquire read before a later event),
  and `remap_δ` sends `r2` onto `x := 1`. The pair `(r1, x := 1)` is anchored
  (`A`): both are `⊑`-below `r2` (and `y := r2`), which is on the path. So
  `≼` relates `r1 :=_acq z` to `x := 1` (`ppo_12`), two events of different
  threads that `⊑` does not order either way (`not_po_12`, `not_po_21`).

So `≼` relates `⊑`-incomparable events, and `≼ ⊄ ⊑` without any pair being
reversed. Every hypothesis of `dep_po_R_of_phi_denote` but `PoForest` holds
(`poForest_needed`), and also every hypothesis of `dep_po_T` but `PoForest`:
`NoRevLoc` holds (`noRevLoc_P`), as no remapped pair points `⊑`-backward.

The argument the cut to `A` rests on (Definition `def:freeze`: "parallel
composition has no join, so an anchored pair lies within one thread's
`⊑`-down-set") fails for the semantics with joins: the down-set of an event of
`κ` holds both threads, and Forwarding moves the end of a pair of `κ` into one
of them. Both uses of `PoForest` in the proofs fail here: `anchored_cmp`
(`(r1, x := 1)` is anchored and incomparable), and the remap-chain lemmas
(`remap_stay_up`, `remap_enter_up`, `remap_cross_pub`), which compare an event
with the source of a Forwarding edge below a common event (`r1` and `x := 1`
below `r2`).
-/

namespace FwdAcrossJoin

open EventStructure PpoKit Execution

def prog : Stmt :=
  .seq (.store .rlx "z" (.num 0) false)
  (.seq (.par (.load .acq "r1" "z" false) (.store .rlx "x" (.num 1) false))
  (.seq (.load .rlx "r2" "x" false) (.store .rlx "y" (.reg "r2") false)))

def e0 : Event := ⟨0, .write .rlx (Expr.glob "z") (Expr.num 0) false, ⟨0, [0], []⟩, []⟩
def e1 : Event := ⟨1, .read .acq (Expr.glob "z") 1 false, ⟨0, [1, 0, 0], []⟩, []⟩
def e2 : Event := ⟨2, .write .rlx (Expr.glob "x") (Expr.num 1) false, ⟨1, [1, 0, 1], []⟩, []⟩
def e3 : Event := ⟨3, .read .rlx (Expr.glob "x") 3 false, ⟨0, [1, 1, 0], []⟩, []⟩
def e4 : Event := ⟨4, .write .rlx (Expr.glob "y") (.sym 3) false, ⟨0, [1, 1, 1], []⟩, []⟩

/-- `⊑`: `z := 0` first, the two threads unordered, both before `r2` and
    `y := r2`. -/
def poL : List (EventId × EventId) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (3, 4), (1, 3), (1, 4), (2, 3), (2, 4)]

def esP : EventStructure := ⟨[e0, e1, e2, e3, e4], poL, []⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esP := rfl

theorem closed_poL : Closed poL := by decide
theorem SP : Simple esP := ⟨by decide, by decide, rfl⟩
theorem po_of {a b : EventId} (h : (a, b) ∈ esP.po) : esP.poR a b := h
theorem po_trans_P : ∀ a b c, esP.poR a b → esP.poR b c → esP.poR a c := poTrans_of closed_poL
theorem po_irr_P : ∀ a, ¬ esP.poR a a := poIrr_of (by decide)
theorem globP : GlobLocs esP := globLocs_of (by decide)

/-! ## The justifications -/

/-- The pre-justification of `y := r2`. -/
def j4 : Justification := ⟨e4.valres, [3], .empty, e4⟩
/-- … with `r2 := x` forwarded from `x := 1` (store forwarding). -/
def jW : Justification :=
  { P := j4.P.replace (.sym 3) (Expr.num 1)
    D := ((Expr.sym 3).replace (.sym 3) (Expr.num 1)).syms ++
      ((Expr.glob "y").replace (.sym 3) (Expr.num 1)).syms
    δ := { j4.δ with f := j4.δ.f ++ [(2, 3)] }
    w := { j4.w with
      kind := .write .rlx ((Expr.glob "y").replace (.sym 3) (Expr.num 1))
        ((Expr.sym 3).replace (.sym 3) (Expr.num 1)) false } }

def pj (w : Event) : Justification := ⟨w.valres, [], .empty, w⟩

theorem replace_self (q : Expr) (β : Sym) : (Expr.sym β).replace (.sym β) q = q := by
  unfold Expr.replace; simp

theorem jW_eq : jW =
    ({ P := e4.valres, D := [], δ := ⟨[(2, 3)], []⟩
       w := { e4 with kind := .write .rlx (Expr.glob "y") (Expr.num 1) false } } :
      Justification) := by
  have h₁ : j4.P.replace (.sym 3) (Expr.num 1) = j4.P :=
    Expr.replace_sym_of_not_mem (by decide)
  have h₂ : (Expr.glob "y").replace (.sym 3) (Expr.num 1) = Expr.glob "y" :=
    Expr.replace_sym_of_not_mem (by decide)
  simp only [jW, h₁, h₂, replace_self]
  rfl

/-- The outcome: `r1 = 0`, `r2 = 1`. -/
def fOut : Valuation := fun α => if α = 3 then .num 1 else .num 0

theorem valres_P (f : Valuation) {e : Event} (he : e ∈ esP.events) : e.valres.holds f :=
  SP.holds he f

theorem noEdge_empty : ∀ a b, ¬ FwdCtx.empty.edge a b := by
  intro a b h; rcases h with h | h <;> cases h

/-- The paper's `≼` under the empty context lies in `⊑`. -/
theorem ppo_empty {P : Pred} {a b : EventId} (h : esP.ppo P .empty a b) : (a, b) ∈ poL := by
  have := ppo_mem rfl globP noEdge_empty h
  have key : ∀ p ∈ syncL esP ++ aliasL esP, p ∈ poL := by decide
  exact key _ this

theorem wf23 : FwdCtx.WF ⟨[(2, 3)], []⟩ := by
  refine ⟨fun a ha => ?_, fun a b e ha hb => ?_⟩
  · have : ∀ c d, Relation.TransGen (FwdCtx.edge ⟨[(2, 3)], []⟩) c d → c = 2 ∧ d = 3 := by
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

theorem gen_j4 : esP.Generated (fun _ => True) j4 :=
  .pre (w := e4) (by simp [esP]) rfl ⟨fOut, valres_P _ (by simp [esP])⟩

/-- **Store forwarding of `r2 := x` from `x := 1`**, across the join: `x := 1`
    is an immediate `≼`-predecessor of `r2`, beside `r1 :=_acq z`, which `⊑`
    does not order against it. -/
theorem fwd_23 : esP.fwdRel j4 2 3 := by
  refine ⟨⟨⟨⟨⟨(FwdCtx.remapRel_of_noEdge noEdge_empty).2 (.inr
      ⟨po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl, fOut, valres_P _ (by simp [esP]),
        by simp [Expr.holds, Expr.eval, Expr.glob]⟩), by decide⟩,
      ?_⟩, po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl, ?_⟩,
    .inl ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩,
    fun ⟨e, he, hp⟩ => by cases he; simp [e3, Event.isVol] at hp⟩,
    fwdNoAcq_of (by decide) (by decide) (by decide), not_rmwAcc_of_nil _ rfl _⟩
  · rintro ⟨e'', h₁, h₂⟩
    have key : ∀ p ∈ poL, ∀ q ∈ poL, p.1 = 2 → q.2 = 3 → p.2 = q.1 → False := by decide
    exact key _ (ppo_empty h₁) _ (ppo_empty h₂) rfl rfl rfl
  · intro f _ v₁ v₂ h₁ h₂
    cases h₁; cases h₂
    simp

theorem gen_jW : esP.Generated (fun _ => True) jW := by
  have h₁ : j4.P.replace (.sym 3) (Expr.num 1) = j4.P := Expr.replace_sym_of_not_mem (by decide)
  exact .fwd (o := .rlx) (x := Expr.glob "y") (e := .sym 3) (b := false) (ev₁ := e2) (ev₂ := e3)
    (v₁ := Expr.num 1) (v₂ := .sym 3) gen_j4 rfl fwd_23 rfl rfl rfl rfl wf23
    ⟨fOut, by rw [h₁]; exact valres_P _ (by simp [esP]), trivial⟩

/-! ## The execution -/

def rfL : List (EventId × EventId) := [(0, 1), (2, 3)]
def JP : List Justification := [pj e0, pj e2, jW]
def xP : Execution := ⟨esP.Candidate, JP, fun w r => (w, r) ∈ rfL⟩

theorem δP : xP.δ = ⟨[(2, 3)], []⟩ := by
  simp only [xP, JP, Execution.δ, List.foldr, jW_eq]
  rfl

theorem edge_P {a b : EventId} (h : xP.δ.edge a b) : a = 2 ∧ b = 3 := by
  rw [δP] at h
  rcases h with h | h
  · simp at h; exact h
  · cases h

theorem edge_23 : xP.δ.edge 2 3 := .inl (by rw [δP]; simp)

theorem elided_P {a : EventId} : xP.elided a ↔ a = 3 := by
  constructor
  · intro h; obtain ⟨b, hb⟩ := (xP.elided_iff a).1 h; exact (edge_P hb).2
  · rintro rfl; exact (xP.elided_iff 3).2 ⟨2, edge_23⟩

/-- `remap_δ`: `r2 := x` onto `x := 1`. -/
def g (a : EventId) : EventId := if a = 3 then 2 else a

theorem remap_P {a a' : EventId} (h : xP.δ.Remap a a') : a' = g a := by
  induction h with
  | @canon e hno =>
      unfold g
      split
      · subst_vars; exact absurd edge_23 (hno 2)
      · rfl
  | step he hr ih =>
      obtain ⟨rfl, rfl⟩ := edge_P he
      cases hr with
      | canon _ => rfl
      | step he' _ => exact absurd (edge_P he').2 (by decide)

theorem remap_canon {a : EventId} (h : a ≠ 3) : xP.δ.Remap a a :=
  .canon fun _ hc => h (edge_P hc).2

theorem remap_32 : xP.δ.Remap 3 2 := .step edge_23 (remap_canon (by decide))

theorem X_P {a : EventId} : xP.X a ↔ a ∈ esP.ids := by
  constructor
  · exact PpoNecessity.ids_of_cand
  · intro h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    exact cand_of_mem SP.nodup he (by revert e; decide) (by revert e; decide)

theorem mem_JP {j : Justification} (hj : j ∈ JP) : j = pj e0 ∨ j = pj e2 ∨ j = jW := by
  simpa [JP] using hj

theorem holds_JP {j : Justification} (hj : j ∈ JP) (f : Valuation) : j.P.holds f := by
  rcases mem_JP hj with rfl | rfl | rfl
  · exact valres_P (e := e0) f (by simp [esP])
  · exact valres_P (e := e2) f (by simp [esP])
  · rw [jW_eq]; exact valres_P (e := e4) f (by simp [esP])

theorem psi_P (f : Valuation) (h : f 3 = .num 1) : xP.δ.psi esP f := by
  rw [δP]
  intro p hp e₁ e₂ v₁ v₂ h₁ h₂ hv₁ hv₂
  simp only [List.mem_singleton] at hp
  subst hp
  have h₁' : esP.ev 2 = some e2 := rfl
  have h₂' : esP.ev 3 = some e3 := rfl
  rw [h₁'] at h₁; rw [h₂'] at h₂; cases h₁; cases h₂
  cases hv₁; cases hv₂
  simp [Expr.holds, Expr.eval, Expr.num, h]

theorem isExecution_P : xP.IsExecution esP (fun _ => True) where
  maximal := ⟨fun _ h => h, fun a b _ _ ⟨ea, eb, ha, hb, hn⟩ =>
      hn ⟨fOut, SP.holds (ev_inv ha).1 _, SP.holds (ev_inv hb).1 _⟩,
    fun _ hc hn => absurd hc hn⟩
  generated j hj := by
    rcases mem_JP hj with rfl | rfl | rfl
    · exact .pre (w := e0) (by simp [esP]) rfl ⟨fOut, SP.holds (by simp [esP]) _⟩
    · exact .pre (w := e2) (by simp [esP]) rfl ⟨fOut, SP.holds (by simp [esP]) _⟩
    · exact gen_jW
  inX j hj := by
    rcases mem_JP hj with rfl | rfl | rfl <;> (try rw [jW_eq]) <;> exact X_P.2 (by decide)
  consistent := ⟨fOut, fun j hj => holds_JP hj fOut, fun a e _ he => SP.holds (ev_inv he).1 _⟩
  fwdWF := by rw [δP]; exact wf23
  rf_wr w r h := by
    have hok : ∀ p ∈ rfL, clsB esP Event.isWrite p.1 = true ∧ clsB esP Event.isRead p.2 = true := by
      decide
    obtain ⟨h₁, h₂⟩ := hok _ h
    have hw := cls_clsB.2 h₁
    have hr := cls_clsB.2 h₂
    exact ⟨hw, hr, cand_of_cls SP.nodup (fun e he => wr_nb e (.inl he)) hw,
      cand_of_cls SP.nodup (fun e he => wr_nb e (.inr he)) hr⟩
  rf_func w w' r h h' := by
    have : ∀ p ∈ rfL, ∀ q ∈ rfL, p.2 = q.2 → p.1 = q.1 := by decide
    exact this _ h _ h' rfl
  justified w hw he hn := by
    have hids : ∀ w ∈ esP.ids, clsB esP Event.isEffect w = true → w = 0 ∨ w = 2 ∨ w = 4 := by
      decide
    have hw' := hids w (X_P.1 hw) (cls_clsB.1 he)
    have hid : ∀ j ∈ JP, ∀ j' ∈ JP, j.w.id = j'.w.id → j' = j := by
      intro j hj j' hj' h
      rcases mem_JP hj with rfl | rfl | rfl <;> rcases mem_JP hj' with rfl | rfl | rfl <;>
        first | rfl | (rw [jW_eq] at h; cases h) | cases h
    have mk : ∀ j ∈ JP, j.w.id = w → ∃ j ∈ xP.J, j.w.id = w ∧ ∀ j' ∈ xP.J, j'.w.id = w → j' = j :=
      fun j hj h => ⟨j, hj, h, fun j' hj' h' => hid j hj j' hj' (h.trans h'.symm)⟩
    rcases hw' with rfl | rfl | rfl
    · exact mk (pj e0) (by simp [JP]) rfl
    · exact mk (pj e2) (by simp [JP]) rfl
    · exact mk jW (by simp [JP]) (by rw [jW_eq]; rfl)

/-! ## `φ`, No-Thin-Air and coherence -/

/-- `DP` is empty: no justification has a symbol in its predicate or its
    dependencies (`jW` depended on `r2`, which Forwarding replaced by `1`). -/
theorem dp_P {a b : EventId} : ¬ xP.DP a b := by
  rintro ⟨-, -, j, hj, -, h⟩
  have key : ∀ j ∈ JP, j.P.syms ++ j.D = [] := by
    rw [show JP = [pj e0, pj e2, _] from congrArg (fun j => [pj e0, pj e2, j]) jW_eq]
    decide
  have := key j hj
  rw [List.append_eq_nil_iff] at this
  rcases h with h | h
  · rw [this.1] at h; cases h
  · rw [this.2] at h; cases h

theorem psi_JP {j : Justification} (hj : j ∈ JP) : j.δ.psi esP fOut := by
  rcases mem_JP hj with rfl | rfl | rfl
  · intro p hp; cases hp
  · intro p hp; cases hp
  · rw [jW_eq]; have := psi_P fOut rfl; rw [δP] at this; exact this

theorem P_P : xP.P esP fOut := fun _ hj => ⟨holds_JP hj fOut, psi_JP hj⟩

theorem phiRf_P : xP.phiRf esP fOut := by
  refine ⟨?_, ?_, ?_⟩
  · intro w r ew er h hw hr
    have key : ∀ p ∈ rfL, ∀ ew ∈ esP.events, ∀ er ∈ esP.events, ew.id = p.1 → er.id = p.2 →
        ew.loc.map (·.eval fOut) = er.loc.map (·.eval fOut) ∧
        ew.val.map (·.eval fOut) = er.val.map (·.eval fOut) := by decide
    have := key (w, r) h ew (ev_inv hw).1 er (ev_inv hr).1 (ev_inv hw).2 (ev_inv hr).2
    refine ⟨fun lw lr h₁ h₂ => ?_, fun vw vr h₁ h₂ => ?_⟩
    · have := this.1; rw [h₁, h₂] at this; exact Option.some.inj this
    · have := this.2; rw [h₁, h₂] at this; exact Option.some.inj this
  · intro a e α sz _ he hk
    obtain ⟨hm, -⟩ := ev_inv he
    simp only [esP, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> cases hk
  · intro a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂ _ _ _ he₁ _ hk₁
    obtain ⟨hm, -⟩ := ev_inv he₁
    simp only [esP, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> cases hk₁

theorem phi_P : xP.phi esP := by
  refine ⟨fun e h hel => ?_, fun r => ⟨?_, ?_⟩, fOut, P_P, phiRf_P⟩
  · rw [elided_P] at hel; subst hel
    rcases h with ⟨r, hr⟩ | ⟨b, hb⟩
    · have : ∀ p ∈ rfL, p.1 ≠ 3 := by decide
      exact this _ hr rfl
    · exact dp_P hb
  · rintro ⟨w, hw⟩
    have hok : ∀ p ∈ rfL, clsB esP Event.isRead p.2 = true := by decide
    have h₂ := hok _ hw
    exact ⟨X_P.2 (clsB_id h₂), cls_clsB.2 h₂⟩
  · rintro ⟨hX, hr⟩
    have key : ∀ r ∈ esP.ids, clsB esP Event.isRead r = true → ∃ p ∈ rfL, p.2 = r := by decide
    obtain ⟨p, hp, rfl⟩ := key r (X_P.1 hX) (cls_clsB.1 hr)
    exact ⟨p.1, hp⟩

/-- A step of MoRDor's `ppoM` under `δ` is a `⊑`-pair moved by `g`. -/
theorem ppoM_bound {Pa Pr : Pred} {a b : EventId} (h : esP.ppoM Pa Pr xP.δ a b) :
    ∃ a₀ b₀, (a₀, b₀) ∈ poL ∧ a = g a₀ ∧ b = g b₀ ∧ a ≠ b := by
  obtain ⟨⟨a₀, b₀, hb, ra, rb⟩, hne⟩ := h
  refine ⟨a₀, b₀, ?_, remap_P ra, remap_P rb, hne⟩
  rcases hb with (hs | (⟨x, -, hx⟩ | ⟨x, hx, -⟩)) | ⟨hpo, -⟩
  · exact hs.1
  · exact absurd hx (not_rmwPairs rfl)
  · exact absurd hx (not_rmwPairs rfl)
  · exact hpo

theorem step_bound {a b : EventId} (h : xP.ppoStep esP a b) :
    ∃ a₀ b₀, (a₀, b₀) ∈ poL ∧ a = g a₀ ∧ b = g b₀ ∧ a ≠ b := by
  obtain ⟨-, -, ⟨j, -, hp, -⟩ | ⟨hs | ⟨hp, -⟩, -⟩⟩ := h
  · exact ppoM_bound hp
  · exact ppoM_bound (esP.ppoSyncRM_sub_ppoM (xP.Pm esP) (xP.Pm esP) xP.δ _ _ hs)
  · exact ppoM_bound hp

/-- Every step of `≼` ascends in the event ids. -/
theorem step_lt {a b : EventId} (h : xP.ppoStep esP a b) : a < b := by
  obtain ⟨a₀, b₀, hpo, rfl, rfl, hne⟩ := step_bound h
  have key : ∀ p ∈ poL, g p.1 ≠ g p.2 → g p.1 < g p.2 := by decide
  exact key _ hpo hne

theorem ntaP : xP.NoThinAir esP := by
  have mono : ∀ {R : Rel}, (∀ a b, R a b → a < b) →
      ∀ a b, Relation.TransGen R a b → a < b := by
    intro R hR a b h
    induction h with
    | single h => exact hR _ _ h
    | tail _ h ih => exact Nat.lt_trans ih (hR _ _ h)
  have hedge : ∀ a b, ((xP.dep esP).union xP.rf) a b → a < b := by
    rintro a b ((⟨-, -, hp⟩ | hd) | hrf)
    · exact mono (fun _ _ h => step_lt h) a b hp
    · exact absurd hd dp_P
    · have key : ∀ p ∈ rfL, p.1 < p.2 := by decide
      exact key _ hrf
  intro a h
  exact Nat.lt_irrefl _ (mono hedge a a h)

/-- Each location is written once in `X`, so the empty coherence order is one. -/
theorem coherentT_P : xP.CoherentT esP := by
  refine ⟨fun _ _ => False, ⟨fun _ _ h => h.elim, fun _ h => h, fun _ _ _ h => h.elim,
    fun a b ha hb hwa hwb hne hsl => ?_⟩, ?_, fun r w _ ⟨_, ⟨_, _, h⟩, _⟩ => h⟩
  · obtain ⟨ea, eb, la, lb, ha', hb', hla, hlb, heq⟩ := hsl
    have := heq fOut P_P phiRf_P
    have key : ∀ a ∈ esP.ids, ∀ b ∈ esP.ids, clsB esP Event.isWrite a = true →
        clsB esP Event.isWrite b = true → a ≠ b →
        (locOf esP a).map (·.eval fOut) ≠ (locOf esP b).map (·.eval fOut) := by decide
    exact absurd (by simp [locOf, ha', hb', hla, hlb, this])
      (key a (X_P.1 ha.1) b (X_P.1 hb.1) (cls_clsB.1 hwa) (cls_clsB.1 hwb) hne)
  · have hH : ∀ a b, xP.hbT esP a b → (a, b) ∈ poL := by
      intro a b h
      refine transGen_mem (fun c d s => ?_) closed_poL h
      rcases s with ⟨⟨-, -, hpo⟩, -⟩ | ⟨hs, -⟩
      · exact hpo
      · have : swL esP = [] := by decide
        have hm := sw_mem hs
        rw [this] at hm; cases hm
    have hE : ∀ a b, xP.eco (fun _ _ => False) a b → (a, b) ∈ rfL :=
      fun a b h => eco_mem (fun a b h => h) (fun _ _ h => h.elim)
        (fun _ _ ⟨_, _, h⟩ => h.elim) (by decide) h
    have hok : ∀ p ∈ poL, p.1 ≠ p.2 ∧ (p.2, p.1) ∉ rfL := by decide
    rintro a ⟨b, hab, rfl | hba⟩
    · exact (hok _ (hH _ _ hab)).1 rfl
    · exact (hok _ (hH _ _ hab)).2 (hE _ _ hba)

/-- **The execution is consistent**: `X ∖ †` drops `r2 := x`. -/
theorem consistentT_P : xP.ConsistentT esP (fun _ => True) :=
  ⟨isExecution_P, phi_P, ntaP, coherentT_P⟩

/-! ## `≼` relates the two threads -/

theorem X_of {a : EventId} (h : a ∈ esP.ids := by decide) : xP.X a := X_P.2 h

/-- **`≼` orders `r1 :=_acq z` before `x := 1`**: MoRDor's `ppo_sync` has
    `(r1, r2)`, `remap_δ` sends `r2` onto `x := 1`, and both ends are
    `⊑`-below `r2`, which is on the path. -/
theorem ppo_12 : xP.ppo esP 1 2 := by
  have hs : esP.ppoSyncM 1 3 := ⟨po_of (by decide), .inl ⟨e1, rfl, rfl⟩⟩
  exact ⟨X_of, X_of, .single ⟨.inl X_of, .inl X_of, .inr ⟨.inl
    ⟨⟨1, 3, hs, remap_canon (by decide), remap_32⟩, by decide⟩,
    ⟨3, .inl X_of, .inr (po_of (by decide)), .inr (po_of (by decide))⟩⟩⟩⟩

/-- The two ends of `ppo_12` lie in different threads. -/
theorem threads_12 : e1.label.thread ≠ e2.label.thread := by decide

theorem not_po_12 : ¬ esP.poR 1 2 := fun h => absurd (show (1, 2) ∈ poL from h) (by decide)
theorem not_po_21 : ¬ esP.poR 2 1 := fun h => absurd (show (2, 1) ∈ poL from h) (by decide)

/-- **`⊑` is not a forest**: `r1` and `x := 1` both lie below `r2`. -/
theorem not_poForest : ¬ PoForest esP := fun h => by
  rcases h 1 2 3 (.inr (po_of (by decide))) (.inr (po_of (by decide))) with h | h | h
  · cases h
  · exact not_po_12 h
  · exact not_po_21 h

/-- **`DP ∪ ≼ ⊄ ⊑`** on this execution. -/
theorem not_dep_po : ¬ ∀ a b, xP.dep esP a b → xP.poX esP a b :=
  fun h => not_po_12 (h 1 2 (.inl ppo_12)).2.2

/-! ## The other hypotheses hold -/

theorem rmwTightR_P : RMWTightR esP xP :=
  ⟨fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩

theorem locsEval_P : LocsEval esP := by
  intro a e l f he hl
  obtain ⟨hm, -⟩ := ev_inv he
  simp only [esP, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> cases hl <;> rfl

/-- The one Forwarding edge was generated against `j4`, whose predicate is
    valid, so every scope of `FwdEntailsOn` holds, `FwdEntailsImg` and
    `FwdEntailsAll` included. -/
theorem fwdEntails_P (scope) : FwdEntailsOn esP xP scope := by
  refine fwdEntailsOn_of_valid (fun s t he => ?_) scope
  obtain ⟨rfl, rfl⟩ := edge_P he
  exact ⟨j4, 2, 3, ⟨.inl ⟨by rw [δP]; simp, rfl, rfl, fwd_23⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩,
    fun f => valres_P f (by simp [esP])⟩

/-- No remapped pair of `⊑` points `⊑`-backward: `NoRevLoc` holds. -/
theorem noRevLoc_P : NoRevLoc esP xP := by
  intro a b a' b' hab ra rb _ hba
  rw [remap_P ra] at hba; rw [remap_P rb] at hba
  have key : ∀ p ∈ poL, (g p.2, g p.1) ∉ poL := by decide
  exact key (a, b) hab hba

theorem rmwWF_P : RMWWF esP := fun _ h => (List.not_mem_nil h).elim

/-- **`PoForest` cannot be dropped from `dep_po_R_of_phi_denote`, nor from
    `dep_po_T`, `dep_po_E`, `dep_po_R`**, for the event structure of a program:
    `⟨z := 0; (r1 :=_acq z ∥ x := 1); r2 := x; y := r2⟩` has a consistent
    execution, whose one Forwarding edge (`x := 1` into `r2`, across the join)
    was generated under Forwarding's restrictions, where every other
    hypothesis of those theorems holds; `PoForest` fails, and `≼` relates
    `r1 :=_acq z` to `x := 1`, which `⊑` does not order either way. -/
theorem poForest_needed :
    denote (fun _ => 0) prog = esP ∧
    xP.ConsistentT esP (fun _ => True) ∧
    (∀ a b c, esP.poR a b → esP.poR b c → esP.poR a c) ∧ (∀ a, ¬ esP.poR a a) ∧
    RMWTightR esP xP ∧ (∀ a b, xP.DP a b → esP.poR a b) ∧ LocsEval esP ∧
    FwdEntailsImg esP xP ∧ FwdEntailsAll esP xP ∧ NoRevLoc esP xP ∧ NoRevRMW esP xP ∧
    RMWWF esP ∧
    ¬ PoForest esP ∧
    xP.ppo esP 1 2 ∧ ¬ esP.poR 1 2 ∧ ¬ esP.poR 2 1 ∧
    ¬ (∀ a b, xP.dep esP a b → xP.poX esP a b) :=
  ⟨denote_prog, consistentT_P, po_trans_P, po_irr_P, rmwTightR_P,
    fun _ _ h => absurd h dp_P, locsEval_P, fwdEntails_P _, fwdEntails_P _, noRevLoc_P,
    noRevRMW_of_nil rfl, rmwWF_P, not_poForest, ppo_12, not_po_12, not_po_21, not_dep_po⟩

end FwdAcrossJoin
