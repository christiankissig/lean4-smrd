import Smrd.DepThread
import Smrd.PpoNecessity
import Smrd.RC11

/-!
# Strengthening against a later read: `DP` backwards within a thread

`y :=_rel 1; r := x ∥ (r2 :=_acq y; x := 1 ∥ x := 2)`. sMRD's published
Strengthening (`EventStructure.GeneratedStr`) strengthens the
pre-justification `(⊤, ∅) ⊢ y :=_rel 1` with a conjunct `r = v` on the read
`r := x` that the thread performs *after* the write: the read is
`⊑`-comparable with the write and not `≼`-after it (a release orders what is
before it, not what is after). Freezing an execution that takes the
justification gives the edge `(r := x, y :=_rel 1)` in `DP`, `⊑`-backwards
and within one thread: `DP ∪ ≼` is thread-internal (`threadInternal_C`), not
`⊑`-forward (`not_dep_po_C`). The restricted rule (`Generated.str`, origins
`⊑`-before the write) does not generate the justification (`not_generated`).

Two executions, each consistent but for the generation of the strengthened
justification, which the published rule provides (`genStr`):

* `xC` (`r = 2`, `r2 = 1`, `CO` on `x`: `x := 1` before `x := 2`): RC11's
  coherence holds, relaxed coherence (`HB_v ≜ (DP ∪ ≼ ∪ SW)⁺`) fails:
  `r →DP y :=_rel 1 →SW r2 →≼ x := 1 →CO x := 2 →rf r`. The step
  `RC11 coherence ⇒ relaxed coherence` (`coherenceV_of_coherence`, and with it
  `coherenceV_iff_coherence`, `coherenceV_of_coherenceT`,
  `Relaxed.consistentV_of_consistent`, …) needs `DP ∪ ≼ ⊆ ⊑`;
  thread-internality does not suffice (`coherenceV_fails`).
* `xN` (`r = 1`, `r2 = 1`, `r` reads `x := 1`): RC11-consistent (no
  elaboration moves an event, `⊑ ∪ rf` acyclic), yet `DP ∪ ≼ ∪ rf` has the
  cycle `r →DP y :=_rel 1 →rf r2 →≼ x := 1 →rf r`, so sMRD's No-Thin-Air fails
  (`noThinAir_fails`). `consistent_of_consistentRC11` and `consistentRC11_iff`
  need `DP ∪ ≼ ⊆ ⊑` for the justifications at hand. The justification only
  forbids an execution: with the pre-justification of `y :=_rel 1` the
  execution is sMRD-consistent, and RC11's executions remain implementable by
  justifications with `DP ⊆ ⊑` (`RC11.dep_po_of_noElision`, under the restricted
  rule).
-/

namespace StrBack

open EventStructure PpoKit Execution

/-- `y :=_rel 1; r := x ∥ (r2 :=_acq y; x := 1 ∥ x := 2)` -/
def prog : Stmt :=
  .par (.seq (PpoStability.st .rel "y" 1) (PpoStability.ld .rlx "r" "x"))
    (.par (.seq (PpoStability.ld .acq "r2" "y") (PpoStability.st .rlx "x" 1))
      (PpoStability.st .rlx "x" 2))

def e0 : Event := PpoStability.W 0 0 [0, 0] [] [] .rel "y" 1
def e1 : Event := PpoStability.R 1 0 [0, 1] [] [] .rlx "x"
def e2 : Event := PpoStability.R 2 1 [1, 0, 0] [] [] .acq "y"
def e3 : Event := PpoStability.W 3 1 [1, 0, 1] [] [] .rlx "x" 1
def e4 : Event := PpoStability.W 4 2 [1, 1] [] [] .rlx "x" 2

def esB : EventStructure := ⟨[e0, e1, e2, e3, e4], [(0, 1), (2, 3)], []⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esB := rfl

theorem SB : Simple esB := ⟨by decide, by decide, rfl⟩
theorem gB : GlobLocs esB := globLocs_of (by decide)

theorem poTrans : ∀ a b c, esB.poR a b → esB.poR b c → esB.poR a c := poTrans_of (by decide)

theorem symWF : esB.SymWF where
  past := by
    show ∀ e ∈ esB.events, ∀ α ∈ e.depSyms, (α, e.id) ∈ esB.po
    decide
  read_sym := by
    intro e he o l α v hk
    simp only [esB, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;>
      simp [e0, e1, e2, e3, e4, PpoStability.R, PpoStability.W] at hk ⊢ <;>
      exact hk.2.2.1.symm

theorem noEdge_empty : ∀ a b, ¬ FwdCtx.empty.edge a b := by
  intro a b h; rcases h with h | h <;> cases h

/-! ## The strengthened justification -/

/-- The conjunct `r = v` on the later read. -/
def Q (v : Nat) : Expr := .eq (.sym 1) (.val (.num v))

/-- `(⊤ ∧ (r = v ∧ ⊤), ∅) ⊢ y :=_rel 1`. -/
def jS (v : Nat) : Justification :=
  { PpoNecessity.pj e0 with P := esB.strPred (PpoNecessity.pj e0).P (Q v) [1] }

def j3 : Justification := PpoNecessity.pj e3
def j4 : Justification := PpoNecessity.pj e4

theorem syms_jS (v : Nat) : (jS v).P.syms = [1] := by
  simp [jS, strPred, Q, PpoNecessity.pj, e0, PpoStability.W, Event.valres, Expr.conj,
    Expr.syms, valresOf, Expr.tt, EventStructure.ev, esB, e1, PpoStability.R]

/-- The valuation of the executions: `r = v`, `r2 = 1`. -/
def fv (v : Nat) : Valuation := fun α => if α = 1 then .num v else if α = 2 then .num 1 else .num 0

theorem holds_jS (v : Nat) : (jS v).P.holds (fv v) := by
  simp [jS, strPred, Q, PpoNecessity.pj, e0, PpoStability.W, Event.valres, Expr.conj,
    valresOf, Expr.tt, EventStructure.ev, esB, e1, PpoStability.R, Expr.holds, Expr.eval, fv]

theorem no_ppo_01 {P : Pred} : ¬ esB.ppo P .empty 0 1 := fun h => by
  have := ppo_mem rfl gB noEdge_empty h
  revert this; decide

theorem pre0 {Ω : Pred} : esB.GeneratedStr Ω (PpoNecessity.pj e0) :=
  .pre (w := e0) (by simp [esB]) rfl ⟨fv 0, SB.holds (by simp [esB]) _⟩

/-- **The published Strengthening generates `jS v`**: the read `r := x` is
    `⊑`-after the write and not `≼`-after it. -/
theorem genStr (v : Nat) : esB.GeneratedStr (fun _ => True) (jS v) := by
  refine .str (Q v) [1] pre0 ?_ ?_ ?_ ⟨fv v, holds_jS v, trivial⟩
  · intro e
    have h : (esB.strPred (PpoNecessity.pj e0).P (Q v) [1]).syms = [1] := syms_jS v
    have h0 : (PpoNecessity.pj e0).P.syms = [] := by decide
    rw [h, h0]; simp
  · intro e _; exact .canon (fun a h => noEdge_empty a e h)
  · intro e he
    simp only [List.mem_singleton] at he; subst he
    exact ⟨.inr (show (0, 1) ∈ esB.po by decide), no_ppo_01⟩

/-- **The restricted rule does not**: its origins lie `⊑`-before the write
    (`Generated.past`), and `r := x` does not. -/
theorem not_generated {Ω : Pred} (v : Nat) : ¬ esB.Generated Ω (jS v) := fun h => by
  have := h.past symWF poTrans
    (fun p hp => by simp [jS, PpoNecessity.pj, FwdCtx.empty] at hp) 1
    (.inl (by rw [syms_jS]; simp))
  revert this; show (1, 0) ∉ esB.po; decide

/-! ## The executions -/

/-- All five events, `J = [jS v, j3, j4]`, and `rf` from a list. -/
def xOf (v : Nat) (rf : List (EventId × EventId)) : Execution :=
  ⟨esB.Candidate, [jS v, j3, j4], fun w r => (w, r) ∈ rf⟩

theorem δ_xOf (v : Nat) (rf : List (EventId × EventId)) : (xOf v rf).δ = .empty :=
  foldr_empty (by
    intro j hj
    simp only [xOf, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> rfl)

theorem noEdge (v : Nat) (rf : List (EventId × EventId)) : ∀ a b, ¬ (xOf v rf).δ.edge a b := by
  intro a b h; rw [δ_xOf] at h; rcases h with h | h <;> cases h

theorem not_elided (v : Nat) (rf : List (EventId × EventId)) (a : EventId) :
    ¬ (xOf v rf).elided a := by
  rintro ⟨p, hp, -⟩; rw [δ_xOf] at hp; rcases hp with hp | hp <;> cases hp

theorem X_iff {v : Nat} {rf : List (EventId × EventId)} {a : EventId} :
    (xOf v rf).X a ↔ a ∈ [0, 1, 2, 3, 4] := by
  constructor
  · rintro ⟨⟨e, he, rfl⟩, -, -⟩
    simp only [esB, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact cand_of_mem SB.nodup (e := e0) (by simp [esB]) rfl rfl
    · exact cand_of_mem SB.nodup (e := e1) (by simp [esB]) rfl rfl
    · exact cand_of_mem SB.nodup (e := e2) (by simp [esB]) rfl rfl
    · exact cand_of_mem SB.nodup (e := e3) (by simp [esB]) rfl rfl
    · exact cand_of_mem SB.nodup (e := e4) (by simp [esB]) rfl rfl

theorem holds_J {v : Nat} {rf : List (EventId × EventId)} :
    ∀ j ∈ (xOf v rf).J, j.P.holds (fv v) := by
  intro j hj
  simp only [xOf, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl
  · exact holds_jS v
  · exact SB.holds (e := e3) (by simp [esB]) _
  · exact SB.holds (e := e4) (by simp [esB]) _

theorem δ_J {v : Nat} {rf : List (EventId × EventId)} :
    ∀ j ∈ (xOf v rf).J, j.δ = .empty := by
  intro j hj
  simp only [xOf, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl <;> rfl

/-- **Were `jS v` generated, `xOf v rf` would be an execution.** Under the
    published rule it is (`genStr`). -/
theorem isExecution_of {v : Nat} {rf : List (EventId × EventId)} (hrf : RfOK esB rf)
    (hg : esB.Generated (fun _ => True) (jS v)) :
    (xOf v rf).IsExecution esB (fun _ => True) where
  maximal := ⟨fun _ h => h, fun a b _ _ ⟨ea, eb, ha, hb, hn⟩ =>
      hn ⟨fun _ => .num 0, SB.holds (ev_inv ha).1 _, SB.holds (ev_inv hb).1 _⟩,
    fun _ hc hn => absurd hc hn⟩
  generated j hj := by
    simp only [xOf, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · exact hg
    · exact .pre (w := e3) (by simp [esB]) rfl ⟨fv 0, SB.holds (by simp [esB]) _⟩
    · exact .pre (w := e4) (by simp [esB]) rfl ⟨fv 0, SB.holds (by simp [esB]) _⟩
  inX j hj := by
    simp only [xOf, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;>
      exact X_iff.2 (by simp [jS, j3, j4, PpoNecessity.pj, e0, e3, e4, PpoStability.W])
  consistent := ⟨fv v, holds_J, fun a e _ he => SB.holds (ev_inv he).1 _⟩
  fwdWF := by rw [δ_xOf]; exact FwdCtx.WF.empty
  rf_wr w r h := by
    obtain ⟨h₁, h₂⟩ := hrf.1 _ h
    have hw := cls_clsB.2 h₁
    have hr := cls_clsB.2 h₂
    exact ⟨hw, hr, cand_of_cls SB.nodup (fun e he => wr_nb e (.inl he)) hw,
      cand_of_cls SB.nodup (fun e he => wr_nb e (.inr he)) hr⟩
  rf_func w w' r h h' := hrf.2 _ h _ h' rfl
  notElided j _ := not_elided v rf j.w.id
  justified w hw he _ := by
    have hw' := X_iff.1 hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    have uniq : ∀ j ∈ (xOf v rf).J, ∀ j' ∈ (xOf v rf).J, j.w.id = j'.w.id → j = j' := by
      intro j hj j' hj' h
      simp only [xOf, List.mem_cons, List.not_mem_nil, or_false] at hj hj'
      rcases hj with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl <;>
        first | rfl | (simp [jS, j3, j4, PpoNecessity.pj, e0, e3, e4, PpoStability.W] at h)
    rcases hw' with rfl | rfl | rfl | rfl | rfl
    · exact ⟨jS v, by simp [xOf], rfl, fun j' hj' h => uniq _ hj' _ (by simp [xOf]) h⟩
    · exact absurd (cls_clsB.1 he) (by decide)
    · exact absurd (cls_clsB.1 he) (by decide)
    · exact ⟨j3, by simp [xOf], rfl, fun j' hj' h => uniq _ hj' _ (by simp [xOf]) h⟩
    · exact ⟨j4, by simp [xOf], rfl, fun j' hj' h => uniq _ hj' _ (by simp [xOf]) h⟩

/-- `φ`, where `rf` reads `r = v` and `r2 = 1` and reaches both reads. -/
theorem phi_of {v : Nat} {rf : List (EventId × EventId)} (hrf : RfOK esB rf)
    (hreads : ∀ e ∈ esB.events, e.isRead = true → ∃ p ∈ rf, p.2 = e.id)
    (hf : ∀ p ∈ rf, ∀ ew ∈ esB.events, ∀ er ∈ esB.events, ew.id = p.1 → er.id = p.2 →
      ew.loc.map (·.eval (fv v)) = er.loc.map (·.eval (fv v)) ∧
      ew.val.map (·.eval (fv v)) = er.val.map (·.eval (fv v))) :
    (xOf v rf).phi esB := by
  refine ⟨fun e _ hel => not_elided v rf e hel, fun r => ⟨?_, ?_⟩, fv v,
    fun j hj => ⟨holds_J j hj, fun p hp => by rw [δ_J j hj] at hp; cases hp⟩, ⟨?_, ?_, ?_⟩,
    fun a e _ he => SB.holds (ev_inv he).1 _⟩
  · rintro ⟨w, hw⟩
    obtain ⟨h₁, h₂⟩ := hrf.1 _ hw
    exact ⟨cand_of_cls SB.nodup (fun e he => wr_nb e (.inr he)) (cls_clsB.2 h₂), cls_clsB.2 h₂⟩
  · rintro ⟨-, e, he, hp⟩
    obtain ⟨hm, rfl⟩ := ev_inv he
    obtain ⟨p, hp', h2⟩ := hreads e hm hp
    exact ⟨p.1, by rw [← h2]; exact hp'⟩
  · intro w r ew er h hw hr
    have := hf (w, r) h ew (ev_inv hw).1 er (ev_inv hr).1 (ev_inv hw).2 (ev_inv hr).2
    refine ⟨fun lw lr h₁ h₂ => ?_, fun vw vr h₁ h₂ => ?_⟩
    · have := this.1; rw [h₁, h₂] at this; exact Option.some.inj this
    · have := this.2; rw [h₁, h₂] at this; exact Option.some.inj this
  · intro a e α sz _ he hk
    have := (ev_inv he).1
    simp only [esB, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl <;> cases hk
  · refine ⟨fun _ => none, ⟨fun _ _ h => (nomatch h), fun _ _ _ h => (nomatch h),
      fun _ _ h => (nomatch h)⟩, ?_⟩
    intro a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂ _ _ _ he₁ _ hk₁
    have := (ev_inv he₁).1
    simp only [esB, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl <;> cases hk₁

/-- `DP` has the one edge `(r := x, y :=_rel 1)`. -/
theorem dp_iff {v : Nat} {rf : List (EventId × EventId)} {a b : EventId} :
    (xOf v rf).DP a b ↔ a = 1 ∧ b = 0 := by
  constructor
  · rintro ⟨-, -, j, hj, rfl, hab⟩
    simp only [xOf, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · rw [syms_jS] at hab
      rcases hab with h | h
      · simp at h; exact ⟨h, rfl⟩
      · simp [jS, PpoNecessity.pj] at h
    all_goals
      rcases hab with h | h <;>
        simp [j3, j4, PpoNecessity.pj, e3, e4, PpoStability.W, Event.valres, Expr.conj,
          Expr.syms, Expr.tt] at h
  · rintro ⟨rfl, rfl⟩
    exact ⟨X_iff.2 (by decide), X_iff.2 (by decide), jS v, by simp [xOf], rfl,
      .inl (by rw [syms_jS]; simp)⟩

/-- `≼` lies in `{(r2, x := 1)}`. -/
theorem ppo_mem' {v : Nat} {rf : List (EventId × EventId)} {a b : EventId}
    (h : (xOf v rf).ppo esB a b) : (a, b) = (2, 3) := by
  have hm := transGen_mem (L := [(2, 3)])
    (fun c d hs => by
      have := ppoStep_mem rfl gB (noEdge v rf) hs
      revert this; generalize (c, d) = p; revert p; decide)
    (by decide) h.2.2
  simpa using hm

/-- `(r2, x := 1)`: an acquire read before a later event is in `≼`. -/
theorem ppo_23 {v : Nat} {rf : List (EventId × EventId)} : (xOf v rf).ppo esB 2 3 := by
  have X2 : (xOf v rf).X 2 := X_iff.2 (by decide)
  have X3 : (xOf v rf).X 3 := X_iff.2 (by decide)
  have hs : esB.ppoSyncM 2 3 := ⟨show (2, 3) ∈ esB.po by decide, .inl ⟨_, rfl, rfl⟩⟩
  exact ⟨X2, X3, .single ⟨.inl X2, .inl X3, .inr ⟨.inl ⟨(FwdCtx.remapRel_of_noEdge
    (noEdge v rf)).2 hs, by decide⟩, ⟨3, .inl X3, .inr hs.1, .inl rfl⟩⟩⟩⟩

/-- `DP ∪ ≼` is `{(r := x, y :=_rel 1), (r2, x := 1)}`. -/
theorem dep_iff {v : Nat} {rf : List (EventId × EventId)} {a b : EventId} :
    (xOf v rf).dep esB a b ↔ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) := by
  constructor
  · rintro (h | h)
    · have := ppo_mem' h; simp at this; exact .inr this
    · exact .inl (dp_iff.1 h)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact .inr (dp_iff.2 ⟨rfl, rfl⟩)
    · exact .inl ppo_23

/-- **`DP ∪ ≼` is thread-internal.** -/
theorem threadInternal {v : Nat} {rf : List (EventId × EventId)} :
    ThreadInternal esB ((xOf v rf).dep esB) := by
  intro a b h
  rcases dep_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact .inr (.inr (show (0, 1) ∈ esB.po by decide))
  · exact .inr (.inl (show (2, 3) ∈ esB.po by decide))

/-- **`DP ∪ ≼` is not `⊑`-forward.** -/
theorem not_dep_po {v : Nat} {rf : List (EventId × EventId)} :
    ¬ ∀ a b, (xOf v rf).dep esB a b → esB.poR a b := fun h => by
  have := h 1 0 (dep_iff.2 (.inl ⟨rfl, rfl⟩))
  revert this; show (1, 0) ∉ esB.po; decide

theorem sw_02 {v : Nat} {rf : List (EventId × EventId)} (h : (0, 2) ∈ rf) :
    (xOf v rf).sw esB 0 2 :=
  ⟨.inl ⟨_, rfl, rfl⟩, 0, 0, 2, .inl rfl,
    ⟨⟨_, rfl, rfl⟩, 0, .inl rfl, ⟨_, rfl, rfl⟩, .inl rfl⟩,
    h, ⟨_, rfl, rfl⟩, .inl rfl, .inl ⟨_, rfl, rfl⟩⟩

/-- `HB ⊆ {(y :=_rel 1, r), (r2, x := 1), (y :=_rel 1, r2), (y :=_rel 1, x := 1)}`. -/
def HB : List (EventId × EventId) := [(0, 1), (2, 3), (0, 2), (0, 3)]

theorem hb_mem {v : Nat} {rf : List (EventId × EventId)} {a b : EventId}
    (h : (xOf v rf).hb esB a b) : (a, b) ∈ HB :=
  transGen_mem (fun c d hs => by
    rcases hs with ⟨-, -, hp⟩ | hs
    · revert hp; show (c, d) ∈ esB.po → (c, d) ∈ HB
      generalize (c, d) = p; revert p; decide
    · have := sw_mem hs
      revert this; generalize (c, d) = p; revert p; decide) (by decide) h

/-- `ECO` over list-given `rf` and `co`, bounded by a closed list. -/
theorem eco_mem' {v : Nat} {rf co E : List (EventId × EventId)}
    (hE : ∀ p ∈ rf ++ co ++ PpoNecessity.frL rf co, p ∈ E) (hc : Closed E) {a b : EventId}
    (h : (xOf v rf).eco (PpoNecessity.relL co) a b) : (a, b) ∈ E := by
  refine eco_mem (fun c d h => hE _ (List.mem_append.2 (.inl (List.mem_append.2 (.inl h))))) (fun c d h => hE _ ?_) (fun c d h => hE _ ?_) hc h
  · exact List.mem_append.2 (.inl (List.mem_append.2 (.inr h)))
  · obtain ⟨w, hrf, hco⟩ := h
    exact List.mem_append.2 (.inr (List.mem_flatMap.2 ⟨(w, c), hrf, List.mem_map.2 ⟨(w, d),
      List.mem_filter.2 ⟨hco, by simp⟩, rfl⟩⟩))

/-- Locations at one place under a model of `P ∧ φ_rf`. -/
theorem locOf_of_sameLoc {v : Nat} {rf : List (EventId × EventId)} (hφ : (xOf v rf).phi esB)
    {a b : EventId} (h : (xOf v rf).sameLoc esB a b) : locOf esB a = locOf esB b := by
  obtain ⟨ea, eb, la, lb, ha, hb, hla, hlb, heq⟩ := h
  obtain ⟨x, rfl⟩ := gB ea (ev_inv ha).1 _ hla
  obtain ⟨y, rfl⟩ := gB eb (ev_inv hb).1 _ hlb
  obtain ⟨f, hP, hrf, -⟩ := hφ.2.2
  have := heq f hP hrf
  cases this
  simp [locOf, ha, hb, hla, hlb]

/-- `CO` from a list, total on `x`. -/
theorem coherenceOrder_of {v : Nat} {rf co : List (EventId × EventId)}
    (hφ : (xOf v rf).phi esB) (hco : co = [(3, 4)] ∨ co = [(4, 3)]) :
    (xOf v rf).CoherenceOrder esB (PpoNecessity.relL co) where
  writes a b h := by
    have h' : (a, b) = (3, 4) ∨ (a, b) = (4, 3) := by
      rcases hco with rfl | rfl <;> simp [PpoNecessity.relL] at h <;> simp [h]
    have w3 : esB.cls Event.isWrite 3 := ⟨_, rfl, rfl⟩
    have w4 : esB.cls Event.isWrite 4 := ⟨_, rfl, rfl⟩
    rcases h' with h' | h' <;> (simp only [Prod.mk.injEq] at h'; obtain ⟨rfl, rfl⟩ := h') <;>
      exact ⟨X_iff.2 (by decide), X_iff.2 (by decide), by assumption, by assumption⟩
  irrefl a h := by
    rcases hco with rfl | rfl <;>
      simp only [PpoNecessity.relL, List.mem_singleton, Prod.mk.injEq] at h <;> (obtain ⟨rfl, h⟩ := h; cases h)
  trans a b c h₁ h₂ := by
    rcases hco with rfl | rfl <;>
      simp only [PpoNecessity.relL, List.mem_singleton, Prod.mk.injEq] at h₁ h₂ <;> (obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨h, -⟩ := h₂; cases h)
  total a b ha hb hwa hwb hne hsl := by
    have hl := locOf_of_sameLoc hφ hsl
    have ha' := X_iff.1 ha
    have hb' := X_iff.1 hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha' hb'
    rcases hco with rfl | rfl <;>
    rcases ha' with rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hne
      | exact absurd (cls_clsB.1 hwa) (by decide)
      | exact absurd (cls_clsB.1 hwb) (by decide)
      | exact absurd hl (by decide)
      | (simp [PpoNecessity.relL])

/-- RC11's coherence, atomicity and SC axiom from list bounds. -/
theorem coherent_of {v : Nat} {rf co E : List (EventId × EventId)} (hφ : (xOf v rf).phi esB)
    (hco : co = [(3, 4)] ∨ co = [(4, 3)])
    (hE : ∀ p ∈ rf ++ co ++ PpoNecessity.frL rf co, p ∈ E) (hc : Closed E)
    (hok : ∀ p ∈ HB, p.1 ≠ p.2 ∧ (p.2, p.1) ∉ E) : (xOf v rf).Coherent esB := by
  refine ⟨_, coherenceOrder_of hφ hco, ?_, ?_, psc_of_noSC _ _ (scFree_of_es _ _ ?_) _⟩
  · rintro a ⟨b, hab, rfl | hba⟩
    · exact (hok _ (hb_mem hab)).1 rfl
    · exact (hok _ (hb_mem hab)).2 (eco_mem' hE hc hba)
  · rintro r w ⟨-, -, ent, hm, -⟩; cases hm
  · exact scFree_of_all _ (by decide)

/-! ## `xC`: RC11-coherent, not relaxed-coherent -/

def rfC : List (EventId × EventId) := [(4, 1), (0, 2)]
def coC : List (EventId × EventId) := [(3, 4)]
/-- `r = 2` (from `x := 2`), `r2 = 1`. -/
def xC : Execution := xOf 2 rfC

theorem phi_C : xC.phi esB :=
  phi_of (by decide) (by decide) (by decide)

/-- No-Thin-Air: `DP ∪ ≼ ∪ rf` lies in a closed list without loops. -/
theorem noThinAir_C : xC.NoThinAir esB := by
  intro a h
  have := transGen_mem (L := [(1, 0), (2, 3), (4, 1), (0, 2), (4, 0), (4, 2), (4, 3), (1, 2),
      (1, 3), (0, 3)])
    (fun c d s => by
      rcases s with s | s
      · rcases dep_iff.1 s with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      · revert s; show (c, d) ∈ rfC → _; generalize (c, d) = p; revert p; decide)
    (by decide) h
  exact (show ∀ p ∈ [(1, 0), (2, 3), (4, 1), (0, 2), (4, 0), (4, 2), (4, 3), (1, 2),
      (1, 3), (0, 3)], p.1 ≠ p.2 by decide) _ this rfl

theorem coherent_C : xC.Coherent esB :=
  coherent_of phi_C (.inl rfl) (E := [(4, 1), (0, 2), (3, 4), (3, 1)]) (by decide) (by decide)
    (by decide)

/-- **Consistent but for the generation of `jS 2`**, which the published rule
    provides (`genStr`). -/
theorem consistent_C (hg : esB.Generated (fun _ => True) (jS 2)) :
    xC.Consistent esB (fun _ => True) :=
  ⟨isExecution_of (by decide) hg, phi_C, noThinAir_C, coherent_C⟩

/-- **Relaxed coherence fails**: `r →DP y :=_rel 1 →SW r2 →≼ x := 1`, and
    `x := 1 →CO x := 2 →rf r`. -/
theorem not_coherenceV_C : ¬ xC.CoherenceV esB (PpoNecessity.relL coC) := by
  intro h
  have d10 : xC.dep esB 1 0 := dep_iff.2 (.inl ⟨rfl, rfl⟩)
  have d23 : xC.dep esB 2 3 := dep_iff.2 (.inr ⟨rfl, rfl⟩)
  exact h 1 ⟨3, .tail (.tail (.single (.inl d10)) (.inr (sw_02 (by decide)))) (.inl d23),
    .inr (.tail (.single (.inl (.inr (show (3, 4) ∈ coC by decide))))
      (.inl (.inl (show (4, 1) ∈ rfC by decide))))⟩

/-- **RC11 coherence does not imply relaxed coherence under thread-internal
    `DP ∪ ≼`**: `coherenceV_of_coherence` needs `DP ∪ ≼ ⊆ ⊑`. -/
theorem coherenceV_fails :
    xC.phi esB ∧ xC.NoThinAir esB ∧ xC.CoherenceOrder esB (PpoNecessity.relL coC) ∧
    xC.Coherence esB (PpoNecessity.relL coC) ∧ xC.FenceFree esB ∧
    ThreadInternal esB (xC.dep esB) ∧ ¬ (∀ a b, xC.dep esB a b → esB.poR a b) ∧
    ¬ xC.CoherenceV esB (PpoNecessity.relL coC) := by
  refine ⟨phi_C, noThinAir_C, coherenceOrder_of phi_C (.inl rfl), ?_, ?_, threadInternal,
    not_dep_po, not_coherenceV_C⟩
  · rintro a ⟨b, hab, rfl | hba⟩
    · exact (show ∀ p ∈ HB, p.1 ≠ p.2 by decide) _ (hb_mem hab) rfl
    · have := eco_mem' (v := 2) (rf := rfC) (co := coC) (E := [(4, 1), (0, 2), (3, 4), (3, 1)])
        (by decide) (by decide) hba
      exact (show ∀ p ∈ HB, (p.2, p.1) ∉ [(4, 1), (0, 2), (3, 4), (3, 1)] by decide)
        _ (hb_mem hab) this
  · rintro a - ⟨e, he, hf⟩
    obtain ⟨hm, rfl⟩ := ev_inv he
    simp only [esB, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> cases hf

/-! ## `xN`: RC11-consistent, not sMRD-consistent -/

def rfN : List (EventId × EventId) := [(3, 1), (0, 2)]
/-- `r = 1` (from `x := 1`), `r2 = 1`. -/
def xN : Execution := xOf 1 rfN

theorem phi_N : xN.phi esB :=
  phi_of (by decide) (by decide) (by decide)

theorem coherent_N : xN.Coherent esB :=
  coherent_of phi_N (.inl rfl) (E := [(3, 1), (0, 2), (3, 4), (1, 4)]) (by decide) (by decide)
    (by decide)

/-- RC11's No-Thin-Air: `⊑ ∪ rf` lies in a closed list without loops. -/
theorem noThinAirRC11_N : xN.NoThinAirRC11 esB := by
  intro a h
  have := transGen_mem (L := [(0, 1), (2, 3), (3, 1), (0, 2), (0, 3), (2, 1)])
    (fun c d s => by
      rcases s with ⟨-, -, s⟩ | s
      · revert s; show (c, d) ∈ esB.po → _; generalize (c, d) = p; revert p; decide
      · revert s; show (c, d) ∈ rfN → _; generalize (c, d) = p; revert p; decide)
    (by decide) h
  exact (show ∀ p ∈ [(0, 1), (2, 3), (3, 1), (0, 2), (0, 3), (2, 1)], p.1 ≠ p.2 by decide)
    _ this rfl

/-- **RC11-consistent but for the generation of `jS 1`**, which the published
    rule provides (`genStr`). -/
theorem consistentRC11_N (hg : esB.Generated (fun _ => True) (jS 1)) :
    Smrd.RC11.ConsistentRC11 esB xN (fun _ => True) :=
  ⟨isExecution_of (by decide) hg, phi_N, not_elided 1 rfN, noThinAirRC11_N, coherent_N⟩

/-- **sMRD's No-Thin-Air fails**: `r →DP y :=_rel 1 →rf r2 →≼ x := 1 →rf r`. -/
theorem noThinAir_fails :
    xN.phi esB ∧ Smrd.RC11.NoElision xN ∧ xN.NoThinAirRC11 esB ∧ xN.Coherent esB ∧
    ThreadInternal esB (xN.dep esB) ∧ ¬ xN.NoThinAir esB := by
  refine ⟨phi_N, not_elided 1 rfN, noThinAirRC11_N, coherent_N, threadInternal, fun h => ?_⟩
  have d10 : xN.dep esB 1 0 := dep_iff.2 (.inl ⟨rfl, rfl⟩)
  have d23 : xN.dep esB 2 3 := dep_iff.2 (.inr ⟨rfl, rfl⟩)
  exact h 1 (.tail (.tail (.tail (.single (.inl d10)) (.inr (show (0, 2) ∈ rfN by decide)))
    (.inl d23)) (.inr (show (3, 1) ∈ rfN by decide)))

end StrBack
