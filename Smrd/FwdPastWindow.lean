import Smrd.FwdEntails
import Smrd.FwdAcrossAlias

/-!
# `FwdEntails` as proposed does not give `DP ∪ ≼ ⊆ ⊑`

The program of `Smrd.FwdAcrossAlias` with `z := 1` moved between `r1 := *p`
and `r2 := x`, one thread:

```
ptr := &u; ptr2 := &x; x := 0; u := 0;
p := ptr; p2 := ptr2;
r0 := *p2; r1 := *p; z := 1; r2 := x;
y := r2
```

* `jW`, for `y := r2`, is strengthened by `p2 = &x ∧ p ≠ &x` (`jS`) and
  forwards `r0 → r2` (load forwarding), as in `Smrd.FwdAcrossAlias`;
  `z := 1` aliases neither, so `pred` holds (`fwd_69`).
* `jZ`, for `z := 1`, is strengthened by `p ≠ p2` only.

Now `r2` is outside `jZ`'s window, so `FwdEntails` (every `j` whose window
contains `e₂ = r2`) asks the entailment of `jW` alone, which holds
(`fwdEntails_P`). But `jZ`'s part of `≼` still orders `r1 ≼ r2` and remaps
`r2` onto `r0`, which is in its window: `≼` has `(r1, r0)` against `⊑`
(`ppo_76`). The execution is consistent (`consistentT_P`), satisfies every
hypothesis of `dep_po_T` but `NoRevLoc`, and `FwdEntails`; `NoRevLoc` and
`DP ∪ ≼ ⊆ ⊑` fail (`fwdEntails_insufficient`).

`FwdEntailsSrc` (window contains `e₁ = r0` or `e₂`) and `FwdEntailsImg`
(window contains `remap_δ(r2) = r0`) both rule it out (`not_fwdEntailsSrc`,
`not_fwdEntailsImg`). `Smrd.FwdChain` refutes `FwdEntailsSrc` in turn.

`NoRevLoc` fails here for a second reason, independent of `jZ`: the
initialising writes' pre-justifications have the valid predicate, so `r1` and
`r2` may alias under them, and `LocLinked` asks no window
(`locLinked_79_init`). No window-restricted condition can imply `NoRevLoc`;
`dep_po_E` (`Smrd.FwdEntails`) uses the window-aware form instead.
-/

namespace FwdPastWindow

open EventStructure PpoKit Execution

def prog : Stmt :=
  .seq (.addrOf "a" "u") (.seq (.store .rlx "ptr" (.reg "a") false)
  (.seq (.addrOf "b" "x") (.seq (.store .rlx "ptr2" (.reg "b") false)
  (.seq (.store .rlx "x" (.num 0) false) (.seq (.store .rlx "u" (.num 0) false)
  (.seq (.load .rlx "p" "ptr" false) (.seq (.load .rlx "p2" "ptr2" false)
  (.seq (.loadPtr .rlx "r0" (.reg "p2") false) (.seq (.loadPtr .rlx "r1" (.reg "p") false)
  (.seq (.store .rlx "z" (.num 1) false) (.seq (.load .rlx "r2" "x" false)
    (.store .rlx "y" (.reg "r2") false))))))))))))

def W (i : Nat) (pc : List Nat) (x : String) (v : Expr) : Event :=
  ⟨i, .write .rlx (Expr.glob x) v false, ⟨0, pc, []⟩, []⟩
def R (i : Nat) (pc : List Nat) (l : Expr) : Event :=
  ⟨i, .read .rlx l i false, ⟨0, pc, []⟩, []⟩

def e0 : Event := W 0 [1, 0] "ptr" (Expr.glob "u")
def e1 : Event := W 1 [1, 1, 1, 0] "ptr2" (Expr.glob "x")
def e2 : Event := W 2 [1, 1, 1, 1, 0] "x" (Expr.num 0)
def e3 : Event := W 3 [1, 1, 1, 1, 1, 0] "u" (Expr.num 0)
def e4 : Event := R 4 [1, 1, 1, 1, 1, 1, 0] (Expr.glob "ptr")
def e5 : Event := R 5 [1, 1, 1, 1, 1, 1, 1, 0] (Expr.glob "ptr2")
def e6 : Event := R 6 [1, 1, 1, 1, 1, 1, 1, 1, 0] (.sym 5)
def e7 : Event := R 7 [1, 1, 1, 1, 1, 1, 1, 1, 1, 0] (.sym 4)
def e8 : Event := W 8 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0] "z" (Expr.num 1)
def e9 : Event := R 9 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0] (Expr.glob "x")
def e10 : Event := W 10 [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] "y" (.sym 9)

/-- `⊑`: the total order on the eleven events (that of `Smrd.FwdAcrossAlias`). -/
abbrev poL := FwdAcrossAlias.poL

def esP : EventStructure := ⟨[e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10], poL, []⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esP := rfl

theorem mem_poL {a b : EventId} : (a, b) ∈ poL ↔ a < b ∧ b < 11 := FwdAcrossAlias.mem_poL
theorem closed_poL : Closed poL := FwdAcrossAlias.closed_poL

theorem SP : Simple esP := ⟨by decide, by decide, rfl⟩
theorem po_of {a b : EventId} (h : (a, b) ∈ esP.po) : esP.poR a b := h

/-! ## The justifications -/

def locX : Val := .loc ⟨.global "x", 0⟩

/-- `p2 = &x ∧ p ≠ &x` -/
def Qw : Expr := .and (.eq (.sym 5) (Expr.glob "x")) (.not (.eq (.sym 4) (Expr.glob "x")))
/-- `p ≠ p2` -/
def Qz : Expr := .not (.eq (.sym 4) (.sym 5))

/-- The pre-justification of `y := r2`. -/
def j10 : Justification := ⟨e10.valres, [9], .empty, e10⟩
/-- … strengthened by `p2 = &x ∧ p ≠ &x`. -/
def jS : Justification := { j10 with P := esP.strPred j10.P Qw [4, 5] }
/-- … with `r2 := x` forwarded from `r0 := *p2` (load forwarding). -/
def jW : Justification :=
  { P := jS.P.replace (.sym 9) (.sym 6)
    D := ((Expr.sym 9).replace (.sym 9) (.sym 6)).syms ++
      ((Expr.glob "y").replace (.sym 9) (.sym 6)).syms
    δ := { jS.δ with f := jS.δ.f ++ [(6, 9)] }
    w := { jS.w with
      kind := .write .rlx ((Expr.glob "y").replace (.sym 9) (.sym 6))
        ((Expr.sym 9).replace (.sym 9) (.sym 6)) false } }
/-- The pre-justification of `z := 1`, strengthened by `p ≠ p2` only. -/
def jZ : Justification := { (PpoNecessity.pj e8) with P := esP.strPred e8.valres Qz [4, 5] }

theorem replace_self (q : Expr) (β : Sym) : (Expr.sym β).replace (.sym β) q = q := by
  unfold Expr.replace; simp

theorem jW_eq : jW =
    ({ P := jS.P, D := [6], δ := ⟨[(6, 9)], []⟩
       w := { e10 with kind := .write .rlx (Expr.glob "y") (.sym 6) false } } : Justification) := by
  have h₁ : jS.P.replace (.sym 9) (.sym 6) = jS.P :=
    Expr.replace_sym_of_not_mem (by decide)
  have h₂ : (Expr.glob "y").replace (.sym 9) (.sym 6) = Expr.glob "y" :=
    Expr.replace_sym_of_not_mem (by decide)
  simp only [jW, h₁, h₂, replace_self]
  rfl

theorem ev4 : esP.ev 4 = some e4 := rfl
theorem ev5 : esP.ev 5 = some e5 := rfl

theorem holds_jS (f : Valuation) : jS.P.holds f ↔ f 5 = locX ∧ f 4 ≠ locX := by
  simp only [jS, j10, strPred, Qw, Expr.holds, Expr.eval, e10, W, Event.valres, Expr.conj,
    List.map, List.foldl, Expr.tt, valresOf, ev4, ev5, e4, e5, R, Option.map, Option.getD,
    Expr.glob, locX]
  by_cases h5 : f 5 = .loc ⟨.global "x", 0⟩ <;> by_cases h4 : f 4 = .loc ⟨.global "x", 0⟩ <;>
    simp [h4, h5]

theorem holds_jZ (f : Valuation) : jZ.P.holds f ↔ f 4 ≠ f 5 := by
  simp only [jZ, strPred, Qz, Expr.holds, Expr.eval, e8, W, Event.valres, Expr.conj,
    List.map, List.foldl, Expr.tt, valresOf, ev4, ev5, e4, e5, R, Option.map, Option.getD]
  by_cases h : f 4 = f 5 <;> simp [h]

/-- The outcome: `p = &u`, `p2 = &x`, every other read `0`. -/
def fOut : Valuation := fun α =>
  if α = 4 then .loc ⟨.global "u", 0⟩ else if α = 5 then locX else .num 0

theorem jS_sat : jS.P.holds fOut := (holds_jS fOut).2 ⟨rfl, by decide⟩
theorem jZ_sat : jZ.P.holds fOut := (holds_jZ fOut).2 (by decide)

theorem base_alias {P : Pred} {a b : EventId} (h : esP.ppoBase P a b) :
    esP.poR a b ∧ esP.mayAlias P a b := by
  rcases h with (hs | ⟨⟨x, -, hx⟩ | ⟨x, hx, -⟩, -⟩) | h
  · have : syncL esP = [] := by decide
    have hm := ppoSync_mem hs
    rw [this] at hm; cases hm
  · exact absurd hx (not_rmwPairs rfl)
  · exact absurd hx (not_rmwPairs rfl)
  · exact h

theorem noEdge_empty : ∀ a b, ¬ FwdCtx.empty.edge a b := by
  intro a b h; rcases h with h | h <;> cases h

theorem ppo_empty {P : Pred} {a b : EventId} (h : esP.ppo P .empty a b) :
    esP.poR a b ∧ esP.mayAlias P a b :=
  base_alias ((FwdCtx.remapRel_of_noEdge noEdge_empty).1 h.1)

/-- `r0 := *p2` and `r1 := *p` alias under neither strengthened predicate. -/
theorem not_alias_67 {P : Pred} (hP : ∀ f, P f → f 4 ≠ f 5) : ¬ esP.mayAlias P 6 7 := by
  rintro ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, hf, heq⟩
  cases h₁; cases h₂; cases hl₁; cases hl₂
  apply hP f hf
  simp only [Expr.holds, Expr.eval] at heq
  simpa [eq_comm] using heq

/-- `z := 1` and `r2 := x` never alias. -/
theorem not_alias_89 {P : Pred} : ¬ esP.mayAlias P 8 9 := by
  rintro ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, hf, heq⟩
  cases h₁; cases h₂; cases hl₁; cases hl₂
  simp [Expr.holds, Expr.eval, Expr.glob] at heq

theorem wf69 : FwdCtx.WF ⟨[(6, 9)], []⟩ := by
  refine ⟨fun a ha => ?_, fun a b e ha hb => ?_⟩
  · have : ∀ c d, Relation.TransGen (FwdCtx.edge ⟨[(6, 9)], []⟩) c d → c = 6 ∧ d = 9 := by
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

theorem pre10 : esP.Generated (fun _ => True) j10 :=
  .pre (w := e10) (by simp [esP]) rfl ⟨fOut, SP.holds (by simp [esP]) _⟩

theorem pre8 : esP.Generated (fun _ => True) (PpoNecessity.pj e8) :=
  .pre (w := e8) (by simp [esP]) rfl ⟨fOut, SP.holds (by simp [esP]) _⟩

theorem gen_jS : esP.Generated (fun _ => True) jS := by
  have hsyms : (esP.strPred j10.P Qw [4, 5]).syms = [5, 4] := by decide
  refine .str Qw [4, 5] pre10 (fun e => ?_) (fun e _ => .canon fun a h => noEdge_empty a e h)
    (fun e he => ⟨?_, fun h => ?_⟩) ⟨fOut, jS_sat, trivial⟩
  · rw [hsyms]
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    have : j10.P.syms = [] := rfl
    rw [this]
    by_cases h4 : e = 4 <;> by_cases h5 : e = 5 <;> simp_all
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl <;> exact po_of (by decide)
  · have := (ppo_empty h).1
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl <;> exact absurd (show (_, _) ∈ poL from this) (by decide)

theorem gen_jZ : esP.Generated (fun _ => True) jZ := by
  have hsyms : (esP.strPred (PpoNecessity.pj e8).P Qz [4, 5]).syms = [4, 5] := by decide
  refine .str Qz [4, 5] pre8 (fun e => ?_) (fun e _ => .canon fun a h => noEdge_empty a e h)
    (fun e he => ⟨?_, fun h => ?_⟩) ⟨fOut, jZ_sat, trivial⟩
  · rw [hsyms]
    have : (PpoNecessity.pj e8).P.syms = [] := rfl
    rw [this]; simp
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl <;> exact po_of (by decide)
  · have := (ppo_empty h).1
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl <;> exact absurd (show (_, _) ∈ poL from this) (by decide)

/-- **Load forwarding of `r2 := x` from `r0 := *p2`**, under `jS`: neither
    `r1 := *p` (`p ≠ &x`) nor `z := 1` is `≼`-between. -/
theorem fwd_69 : esP.fwdRel jS 6 9 := by
  refine ⟨⟨⟨⟨⟨(FwdCtx.remapRel_of_noEdge noEdge_empty).2 (.inr
      ⟨po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl, fOut, jS_sat,
        by simp [Expr.holds, Expr.eval, fOut, locX, Expr.glob]⟩), by decide⟩,
      ?_⟩, po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl, ?_⟩,
    .inr (.inr ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩),
    fun ⟨e, he, hp⟩ => by cases he; simp [e9, R, Event.isVol] at hp⟩,
    fwdNoAcq_of (by decide) (by decide) (by decide),
    Execution.fwdNoJoin_of_poForest (poForest_of FwdAcrossAlias.forestL_poL) _ _, not_rmwAcc_of_nil _ rfl _⟩
  · rintro ⟨e'', h₁, h₂⟩
    have p₁ := (ppo_empty h₁).1
    have p₂ := (ppo_empty h₂).1
    have key : ∀ p ∈ poL, ∀ q ∈ poL, p.1 = 6 → q.2 = 9 → p.2 = q.1 → p.2 = 7 ∨ p.2 = 8 := by
      decide
    rcases key _ p₁ _ p₂ rfl rfl rfl with h | h
    · subst h
      exact not_alias_67 (fun f hf => by
        obtain ⟨h5, h4⟩ := (holds_jS f).1 hf
        rw [h5]; exact h4) (ppo_empty h₁).2
    · subst h
      exact not_alias_89 (ppo_empty h₂).2
  · intro f hf v₁ v₂ h₁ h₂
    have h5 := ((holds_jS f).1 hf.1).1
    obtain rfl : f 5 = v₁ := Option.some.inj h₁
    obtain rfl : locX = v₂ := Option.some.inj h₂
    exact h5

theorem gen_jW : esP.Generated (fun _ => True) jW := by
  have h₁ : jS.P.replace (.sym 9) (.sym 6) = jS.P := Expr.replace_sym_of_not_mem (by decide)
  exact .fwd (o := .rlx) (x := Expr.glob "y") (e := .sym 9) (b := false) (ev₁ := e6) (ev₂ := e9)
    (v₁ := .sym 6) (v₂ := .sym 9) gen_jS rfl fwd_69 rfl rfl rfl rfl wf69
    ⟨fOut, by rw [h₁]; exact jS_sat, trivial⟩

/-! ## The execution -/

def rfL : List (EventId × EventId) := [(0, 4), (1, 5), (2, 6), (3, 7), (2, 9)]
def JP : List Justification :=
  [PpoNecessity.pj e0, PpoNecessity.pj e1, PpoNecessity.pj e2, PpoNecessity.pj e3, jW, jZ]
def xP : Execution := ⟨esP.Candidate, JP, fun w r => (w, r) ∈ rfL⟩

theorem δP : xP.δ = ⟨[(6, 9)], []⟩ := by
  simp only [xP, JP, Execution.δ, List.foldr, jW_eq]
  rfl

theorem edge_P {a b : EventId} (h : xP.δ.edge a b) : a = 6 ∧ b = 9 := by
  rw [δP] at h
  rcases h with h | h
  · simp at h; exact h
  · cases h

theorem edge_69 : xP.δ.edge 6 9 := .inl (by rw [δP]; simp)

theorem elided_P {a : EventId} : xP.elided a ↔ a = 9 := by
  constructor
  · intro h; obtain ⟨b, hb⟩ := (xP.elided_iff a).1 h; exact (edge_P hb).2
  · rintro rfl; exact (xP.elided_iff 9).2 ⟨6, edge_69⟩

/-- `remap_δ`: `r2 := x` onto `r0 := *p2`. -/
def g (a : EventId) : EventId := if a = 9 then 6 else a

theorem remap_P {a a' : EventId} (h : xP.δ.Remap a a') : a' = g a := by
  induction h with
  | @canon e hno =>
      unfold g
      split
      · subst_vars; exact absurd edge_69 (hno 6)
      · rfl
  | step he hr ih =>
      obtain ⟨rfl, rfl⟩ := edge_P he
      cases hr with
      | canon _ => rfl
      | step he' _ => exact absurd (edge_P he').2 (by decide)

theorem remap_canon {a : EventId} (h : a ≠ 9) : xP.δ.Remap a a :=
  .canon fun _ hc => h (edge_P hc).2

theorem remap_96 : xP.δ.Remap 9 6 := .step edge_69 (remap_canon (by decide))

theorem X_P {a : EventId} : xP.X a ↔ a ∈ esP.ids := by
  constructor
  · exact PpoNecessity.ids_of_cand
  · intro h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    exact cand_of_mem SP.nodup he (by revert e; decide) (by revert e; decide)

theorem mem_JP {j : Justification} (hj : j ∈ JP) :
    j = PpoNecessity.pj e0 ∨ j = PpoNecessity.pj e1 ∨ j = PpoNecessity.pj e2 ∨
      j = PpoNecessity.pj e3 ∨ j = jW ∨ j = jZ := by
  simpa [JP] using hj

theorem pre_P {w : Event} (hw : w ∈ esP.events) (hk : preJust w = some (PpoNecessity.pj w)) :
    esP.Generated (fun _ => True) (PpoNecessity.pj w) :=
  .pre hw hk ⟨fOut, SP.holds hw _⟩

theorem holds_JP {j : Justification} (hj : j ∈ JP) : j.P.holds fOut := by
  rcases mem_JP hj with rfl | rfl | rfl | rfl | rfl | rfl
  · exact SP.holds (e := e0) (by simp [esP]) _
  · exact SP.holds (e := e1) (by simp [esP]) _
  · exact SP.holds (e := e2) (by simp [esP]) _
  · exact SP.holds (e := e3) (by simp [esP]) _
  · rw [jW_eq]; exact jS_sat
  · exact jZ_sat

theorem psi_P (f : Valuation) (h : f 6 = f 9) : xP.δ.psi esP f := by
  rw [δP]
  intro p hp e₁ e₂ v₁ v₂ h₁ h₂ hv₁ hv₂
  simp only [List.mem_singleton] at hp
  subst hp
  have h₁' : esP.ev 6 = some e6 := rfl
  have h₂' : esP.ev 9 = some e9 := rfl
  rw [h₁'] at h₁; rw [h₂'] at h₂; cases h₁; cases h₂
  cases hv₁; cases hv₂
  simp [Expr.holds, Expr.eval, h]

theorem isExecution_P : xP.IsExecution esP (fun _ => True) where
  maximal := ⟨fun _ h => h, fun a b _ _ ⟨ea, eb, ha, hb, hn⟩ =>
      hn ⟨fOut, SP.holds (ev_inv ha).1 _, SP.holds (ev_inv hb).1 _⟩,
    fun _ hc hn => absurd hc hn⟩
  generated j hj := by
    rcases mem_JP hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact pre_P (by simp [esP]) rfl
    · exact pre_P (by simp [esP]) rfl
    · exact pre_P (by simp [esP]) rfl
    · exact pre_P (by simp [esP]) rfl
    · exact gen_jW
    · exact gen_jZ
  inX j hj := by
    rcases mem_JP hj with rfl | rfl | rfl | rfl | rfl | rfl <;> (try rw [jW_eq]) <;>
      exact X_P.2 (by decide)
  consistent := ⟨fOut, fun j hj => holds_JP hj, fun a e _ he => SP.holds (ev_inv he).1 _⟩
  fwdWF := by rw [δP]; exact wf69
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
    have hids : ∀ w ∈ esP.ids, clsB esP Event.isEffect w = true →
        w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 8 ∨ w = 10 := by decide
    have hw' := hids w (X_P.1 hw) (cls_clsB.1 he)
    have hid : ∀ j ∈ JP, ∀ j' ∈ JP, j.w.id = j'.w.id → j' = j := by
      intro j hj j' hj' h
      rcases mem_JP hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases mem_JP hj' with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | (rw [jW_eq] at h; cases h) | cases h
    have mk : ∀ j ∈ JP, j.w.id = w → ∃ j ∈ xP.J, j.w.id = w ∧ ∀ j' ∈ xP.J, j'.w.id = w → j' = j :=
      fun j hj h => ⟨j, hj, h, fun j' hj' h' => hid j hj j' hj' (h.trans h'.symm)⟩
    rcases hw' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact mk (PpoNecessity.pj e0) (by simp [JP]) rfl
    · exact mk (PpoNecessity.pj e1) (by simp [JP]) rfl
    · exact mk (PpoNecessity.pj e2) (by simp [JP]) rfl
    · exact mk (PpoNecessity.pj e3) (by simp [JP]) rfl
    · exact mk jZ (by simp [JP]) rfl
    · exact mk jW (by simp [JP]) (by rw [jW_eq]; rfl)

/-! ## `φ`, No-Thin-Air and coherence -/

/-- `DP`: the symbols of `jW` (`p`, `p2`, and `r0` after forwarding) and of
    `jZ` (`p`, `p2`). -/
def dpL : List (EventId × EventId) := [(5, 10), (4, 10), (6, 10), (4, 8), (5, 8)]

theorem dp_P {a b : EventId} (h : xP.DP a b) : (a, b) ∈ dpL := by
  obtain ⟨-, -, j, hj, rfl, h⟩ := h
  have key : ∀ j ∈ JP, ∀ a ∈ j.P.syms ++ j.D, (a, j.w.id) ∈ dpL := by
    rw [show JP = [PpoNecessity.pj e0, PpoNecessity.pj e1, PpoNecessity.pj e2,
      PpoNecessity.pj e3, _, jZ] from congrArg (fun j => [PpoNecessity.pj e0, PpoNecessity.pj e1,
        PpoNecessity.pj e2, PpoNecessity.pj e3, j, jZ]) jW_eq]
    decide
  exact key j hj a (List.mem_append.2 h)

theorem psi_JP {j : Justification} (hj : j ∈ JP) : j.δ.psi esP fOut := by
  rcases mem_JP hj with rfl | rfl | rfl | rfl | rfl | rfl
  · intro p hp; cases hp
  · intro p hp; cases hp
  · intro p hp; cases hp
  · intro p hp; cases hp
  · rw [jW_eq]; have := psi_P fOut rfl; rw [δP] at this; exact this
  · intro p hp; cases hp

theorem P_P : xP.P esP fOut := fun _ hj => ⟨holds_JP hj, psi_JP hj⟩

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
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hk
  · intro a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂ _ _ _ he₁ _ hk₁
    obtain ⟨hm, -⟩ := ev_inv he₁
    simp only [esP, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hk₁

theorem phi_P : xP.phi esP := by
  refine ⟨fun e h hel => ?_, fun r => ⟨?_, ?_⟩, fOut, P_P, phiRf_P⟩
  · rw [elided_P] at hel; subst hel
    rcases h with ⟨r, hr⟩ | ⟨b, hb⟩
    · have : ∀ p ∈ rfL, p.1 ≠ 9 := by decide
      exact this _ hr rfl
    · have : ∀ p ∈ dpL, p.1 ≠ 9 := by decide
      exact this _ (dp_P hb) rfl
  · rintro ⟨w, hw⟩
    have hok : ∀ p ∈ rfL, clsB esP Event.isRead p.2 = true := by decide
    have h₂ := hok _ hw
    exact ⟨X_P.2 (clsB_id h₂), cls_clsB.2 h₂⟩
  · rintro ⟨hX, hr⟩
    have key : ∀ r ∈ esP.ids, clsB esP Event.isRead r = true → ∃ p ∈ rfL, p.2 = r := by decide
    obtain ⟨p, hp, rfl⟩ := key r (X_P.1 hX) (cls_clsB.1 hr)
    exact ⟨p.1, hp⟩

theorem not_must_67 : ¬ esP.mustAlias 6 7 := by
  rintro ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, hs⟩
  cases h₁; cases h₂; cases hl₁; cases hl₂
  have := hs (fun α => .num α) _ _ rfl rfl
  cases this

theorem not_must_89 : ¬ esP.mustAlias 8 9 := by
  rintro ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, hs⟩
  cases h₁; cases h₂; cases hl₁; cases hl₂
  have := hs (fun α => .num α) _ _ rfl rfl
  revert this; decide

theorem ppoM_bound {Pa Pr : Pred} {a b : EventId} (h : esP.ppoM Pa Pr xP.δ a b) :
    ∃ a₀ b₀, (a₀, b₀) ∈ poL ∧ ((a₀, b₀) = (6, 7) → esP.mayAlias Pa 6 7) ∧ (a₀, b₀) ≠ (8, 9) ∧
      a = g a₀ ∧ b = g b₀ ∧ a ≠ b := by
  obtain ⟨⟨a₀, b₀, hb, ra, rb⟩, hne⟩ := h
  refine ⟨a₀, b₀, ?_, ?_, ?_, remap_P ra, remap_P rb, hne⟩
  · rcases hb with (hs | (⟨x, -, hx⟩ | ⟨x, hx, -⟩)) | ⟨hpo, -⟩
    · have : syncML esP = [] := by decide
      have hm := ppoSyncM_mem hs
      rw [this] at hm; cases hm
    · exact absurd hx (not_rmwPairs rfl)
    · exact absurd hx (not_rmwPairs rfl)
    · exact hpo
  · intro he
    cases he
    rcases hb with (hs | (⟨x, -, hx⟩ | ⟨x, hx, -⟩)) | ⟨-, hm | hal⟩
    · have : syncML esP = [] := by decide
      have hm := ppoSyncM_mem hs
      rw [this] at hm; cases hm
    · exact absurd hx (not_rmwPairs rfl)
    · exact absurd hx (not_rmwPairs rfl)
    · exact absurd hm not_must_67
    · exact hal
  · intro he
    cases he
    rcases hb with (hs | (⟨x, -, hx⟩ | ⟨x, hx, -⟩)) | ⟨-, hm | hal⟩
    · have : syncML esP = [] := by decide
      have hm := ppoSyncM_mem hs
      rw [this] at hm; cases hm
    · exact absurd hx (not_rmwPairs rfl)
    · exact absurd hx (not_rmwPairs rfl)
    · exact not_must_89 hm
    · exact not_alias_89 hal

theorem jZ_mem : jZ ∈ xP.J := by simp [xP, JP]
theorem jW_mem : jW ∈ xP.J := by simp [xP, JP]

theorem ne45_jZ {P : Pred} (h : ∀ f, P f → jZ.P.holds f) : ∀ f, P f → f 4 ≠ f 5 :=
  fun f hf => (holds_jZ f).1 (h f hf)

theorem step_bound {a b : EventId} (h : xP.ppoStep esP a b) :
    ∃ a₀ b₀, (a₀, b₀) ∈ poL ∧ (a₀, b₀) ≠ (6, 7) ∧ (a₀, b₀) ≠ (8, 9) ∧ a = g a₀ ∧ b = g b₀ ∧
      a ≠ b := by
  obtain ⟨-, -, ⟨j, hj, hp, hwa, -⟩ | ⟨hs | ⟨hp, -⟩, -⟩⟩ := h
  · obtain ⟨a₀, b₀, hpo, h67, h89, rfl, rfl, hne⟩ := ppoM_bound hp
    refine ⟨a₀, b₀, hpo, fun he => ?_, h89, rfl, rfl, hne⟩
    have hal := h67 he
    cases he
    rcases mem_JP hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hwa (by simp only [Win, g, EventStructure.poR]; decide)
    · exact absurd hwa (by simp only [Win, g, EventStructure.poR]; decide)
    · exact absurd hwa (by simp only [Win, g, EventStructure.poR]; decide)
    · exact absurd hwa (by simp only [Win, g, EventStructure.poR]; decide)
    · exact not_alias_67 (fun f hf => by
        have := hf.1; rw [jW_eq] at this
        obtain ⟨h5, h4⟩ := (holds_jS f).1 this
        rw [h5]; exact h4) hal
    · exact not_alias_67 (ne45_jZ fun f hf => hf.1) hal
  · obtain ⟨⟨a₀, b₀, hs, -, -⟩, -⟩ := hs
    have : syncML esP = [] := by decide
    have hm := ppoSyncM_mem hs
    rw [this] at hm; cases hm
  · obtain ⟨a₀, b₀, hpo, h67, h89, rfl, rfl, hne⟩ := ppoM_bound hp
    exact ⟨a₀, b₀, hpo, fun he => not_alias_67 (ne45_jZ fun f hf => hf.1 jZ jZ_mem) (h67 he),
      h89, rfl, rfl, hne⟩

/-- `r1` before `r0`, otherwise program order. -/
def rk (a : EventId) : Nat := if a = 6 then 7 else if a = 7 then 6 else a

theorem ntaP : xP.NoThinAir esP := by
  have hstep : ∀ a b, xP.ppoStep esP a b → rk a < rk b := by
    intro a b h
    obtain ⟨a₀, b₀, hpo, h67, h89, rfl, rfl, hne⟩ := step_bound h
    have key : ∀ p ∈ poL, p ≠ (6, 7) → p ≠ (8, 9) → g p.1 ≠ g p.2 →
        rk (g p.1) < rk (g p.2) := by decide
    exact key _ hpo h67 h89 hne
  have mono : ∀ {R : Rel}, (∀ a b, R a b → rk a < rk b) →
      ∀ a b, Relation.TransGen R a b → rk a < rk b := by
    intro R hR a b h
    induction h with
    | single h => exact hR _ _ h
    | tail _ h ih => exact Nat.lt_trans ih (hR _ _ h)
  have hedge : ∀ a b, ((xP.dep esP).union xP.rf) a b → rk a < rk b := by
    rintro a b ((⟨-, -, hp⟩ | hd) | hrf)
    · exact mono hstep a b hp
    · have key : ∀ p ∈ dpL, rk p.1 < rk p.2 := by decide
      exact key _ (dp_P hd)
    · have key : ∀ p ∈ rfL, rk p.1 < rk p.2 := by decide
      exact key _ hrf
  intro a h
  exact Nat.lt_irrefl _ (mono hedge a a h)

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

/-! ## `≼` against `⊑`, and the conditions -/

/-- `r1 := *p` and `r2 := x` may alias under `jZ`'s predicate `p ≠ p2`. -/
theorem alias_79 : esP.mayAlias (xP.PJ esP jZ) 7 9 := by
  let f : Valuation := fun α => if α = 4 then locX else if α = 5 then .loc ⟨.global "u", 0⟩
    else .num 0
  exact ⟨e7, e9, _, _, rfl, rfl, rfl, rfl, f,
    ⟨(holds_jZ f).2 (by decide), psi_P f rfl⟩, by simp [Expr.holds, Expr.eval, f, locX, Expr.glob]⟩

/-- … and under the initialising write `ptr := &u`'s pre-justification, whose
    window ends before both: `LocLinked` asks no window. -/
theorem locLinked_79_init : esP.mayAlias (xP.PJ esP (PpoNecessity.pj e0)) 7 9 := by
  let f : Valuation := fun α => if α = 4 then locX else .num 0
  exact ⟨e7, e9, _, _, rfl, rfl, rfl, rfl, f,
    ⟨SP.holds (e := e0) (by simp [esP]) f, psi_P f rfl⟩,
    by simp [Expr.holds, Expr.eval, f, locX, Expr.glob]⟩

theorem not_noRevLoc : ¬ NoRevLoc esP xP := fun h =>
  h 7 9 7 6 (po_of (by decide)) (remap_canon (by decide)) remap_96
    (.inr (.inr (.inl ⟨jZ, jZ_mem, alias_79⟩))) (po_of (by decide))

/-- **`≼` has a pair against `⊑`**: `jZ`'s part orders `r1 := *p` before
    `r2 := x`, remapped onto `r0 := *p2`; both are in `jZ`'s window. -/
theorem ppo_76 : xP.ppo esP 7 6 := by
  have X7 : xP.X 7 := X_P.2 (by decide)
  have X6 : xP.X 6 := X_P.2 (by decide)
  exact ⟨X7, X6, .single ⟨.inl X7, .inl X6, .inl ⟨jZ, jZ_mem,
    ⟨⟨7, 9, .inr ⟨po_of (by decide), .inr alias_79⟩, remap_canon (by decide), remap_96⟩,
      by decide⟩, .inr (po_of (by decide)), .inr (po_of (by decide))⟩⟩⟩

theorem not_dep_po : ¬ ∀ a b, xP.dep esP a b → xP.poX esP a b := fun h => by
  have h₁ : esP.poR 7 6 := (h 7 6 (.inl ppo_76)).2.2
  exact absurd (show (7, 6) ∈ poL from h₁) (by decide)

theorem rmwTightR_P : RMWTightR esP xP :=
  ⟨fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩

theorem dp_po_P : ∀ a b, xP.DP a b → esP.poR a b := fun a b h => by
  have key : ∀ p ∈ dpL, p ∈ poL := by decide
  exact key _ (dp_P h)

/-- **`FwdEntails` holds**: the only justification whose window contains
    `r2 := x` is `jW`, whose predicate is the forwarding one. -/
theorem fwdEntails_P : FwdEntails esP xP := by
  intro s t he
  obtain ⟨rfl, rfl⟩ := edge_P he
  refine ⟨jS, 6, 9, ⟨.inl ⟨by rw [δP]; simp, rfl, rfl, fwd_69⟩, fun p hp => (by cases hp),
    fun p hp => (by cases hp)⟩, fun j hj hw => ?_, fun f hf => ?_⟩
  · rcases mem_JP hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
    · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
    · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
    · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
    · intro f hf
      have := hf.1; rw [jW_eq] at this
      exact ⟨this, fun p hp => (by cases hp)⟩
    · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
  · have := hf.1 jW jW_mem; rw [jW_eq] at this
    exact ⟨this, fun p hp => (by cases hp)⟩

/-- A model of `P_jZ ∧ ψ_δ` with `p2 = &u`. -/
def fZ : Valuation := fun α =>
  if α = 4 then locX else if α = 5 then .loc ⟨.global "u", 0⟩ else .num 0

theorem not_entails_69 {j₀ : Justification} {u v : EventId} (hg : EdgeGen esP xP j₀ 6 9 u v) :
    ¬ Entails (xP.PJ esP jZ) (PredOf esP j₀) := by
  intro h
  rcases hg.1 with ⟨-, rfl, rfl, -⟩ | ⟨hw, -⟩
  · obtain ⟨-, -, ev₁, ev₂, l₁, l₂, h₁, h₂, hl₁, hl₂, hq⟩ := hg.base
    cases h₁; cases h₂; cases hl₁; cases hl₂
    have := hq fZ (h fZ ⟨(holds_jZ fZ).2 (by decide), psi_P fZ rfl⟩) _ _ rfl rfl
    simp [fZ] at this
  · rw [δP] at hw; cases hw

/-- **`FwdEntailsSrc` fails**: `jZ`'s window contains `r0 := *p2`. -/
theorem not_fwdEntailsSrc : ¬ FwdEntailsSrc esP xP := fun h => by
  obtain ⟨j₀, u, v, hg, hJ, -⟩ := h 6 9 edge_69
  have hu : u = 6 := by
    rcases hg.1 with ⟨-, rfl, -, -⟩ | ⟨hw, -⟩
    · rfl
    · rw [δP] at hw; cases hw
  subst hu
  exact not_entails_69 hg (hJ jZ jZ_mem (.inl (.inr (po_of (by decide)))))

/-- **`FwdEntailsImg` fails**: `jZ`'s window contains `remap_δ(r2) = r0`. -/
theorem not_fwdEntailsImg : ¬ FwdEntailsImg esP xP := fun h => by
  obtain ⟨j₀, u, v, hg, hJ, -⟩ := h 6 9 edge_69
  exact not_entails_69 hg (hJ jZ jZ_mem ⟨6, remap_96, .inr (po_of (by decide))⟩)

/-- **`FwdEntails` does not give `DP ∪ ≼ ⊆ ⊑`**: a consistent execution with
    every hypothesis of `dep_po_T` but `NoRevLoc`, and `FwdEntails`, where
    `NoRevLoc` and `DP ∪ ≼ ⊆ ⊑` fail; `FwdEntailsSrc` and `FwdEntailsImg`
    fail too. -/
theorem fwdEntails_insufficient :
    xP.ConsistentT esP (fun _ => True) ∧
    (∀ a b c, esP.poR a b → esP.poR b c → esP.poR a c) ∧ (∀ a, ¬ esP.poR a a) ∧
    PoForest esP ∧ RMWTightR esP xP ∧ (∀ a b, xP.DP a b → esP.poR a b) ∧
    FwdEntails esP xP ∧ ¬ FwdEntailsSrc esP xP ∧ ¬ FwdEntailsImg esP xP ∧
    ¬ NoRevLoc esP xP ∧ ¬ (∀ a b, xP.dep esP a b → xP.poX esP a b) :=
  ⟨consistentT_P, poTrans_of closed_poL,
    poIrr_of fun p hp => by
      obtain ⟨a, b⟩ := p
      have := (mem_poL.1 hp).1
      exact Nat.ne_of_lt this,
    poForest_of FwdAcrossAlias.forestL_poL, rmwTightR_P, dp_po_P, fwdEntails_P,
    not_fwdEntailsSrc, not_fwdEntailsImg, not_noRevLoc, not_dep_po⟩

end FwdPastWindow
