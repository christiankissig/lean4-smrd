import Smrd.DepThread
import Smrd.PpoNecessity

/-!
# Strengthening against a later read, then Lifting

`r1 := a; if r1 = 0 then (y := 1; r4 := z) else (r3 := z; y := r3) ∥ r2 := y; a := r2`,
all accesses relaxed.

Under Strengthening as `Generated` has it (sMRD's Def. 4.11):

1. the `then` arm's `(r1 = 0, ∅) ⊢ y := 1` is strengthened with `r4 = 1`, a
   conjunct on the read `r4 := z` that the arm performs *after* the write
   (`gen_j₁`);
2. the `else` arm's `(¬ r1 = 0, {r3}) ⊢ y := r3` is strengthened with `r3 = 1`
   (a read before its write), and Value Assignment gives
   `(¬ r1 = 0 ∧ r3 = 1, ∅) ⊢ y := 1` (`gen_j₂`);
3. Lifting the first into the second under `Λ = [r4 ↦ r3]` (the two reads of
   `z`, on the two outcomes of the branching) factors out the shared
   `r3 = 1` and leaves the disjunction `r1 = 0 ∨ ¬ r1 = 0` (`gen_jL`), which
   Weakening drops: `(r3 = 1, ∅) ⊢ y := 1` (`gen_jW`). The `else` arm's write
   no longer depends on `r1` (`jW_syms`).

Every lifting condition holds, Lifting's own `⊑`-restriction included
(`⟦P₁⟧_Λ`'s symbols `r1`, `r3` lie `⊑`-before the `else` arm's write). Only
the first step uses an origin `⊑`-after the write; the variant
`GeneratedPast` (origins `⊑`-before the write) refuses it (`not_gen_j₁`). If
the `then` arm reads `z` before writing `y`, `r4 := z; y := 1`,
`GeneratedPast` derives the same justification (not mechanised).

## The outcome

With `(r3 = 1, ∅) ⊢ y := 1`, the execution taking the `else` arm with
`r1 = 1`, `r3 = 1` (from an initial `z := 1`) and `r2 = 1` has no
`DP ∪ ≼ ∪ rf` cycle: load buffering. RC11 forbids it, as every instance of
load buffering. It is not out of thin air: a compiler may reorder the `then`
arm to `r4 := z; y := 1`, hoist the load of `z` common to both arms above
the branching and above `r1 := a` (relaxed loads of different locations), and
case-split on its value: if it is `1`, both arms store `1` to `y`, and the
store moves above `r1 := a`. A fact about a later read is available at the
write once the read is hoisted above it, and Strengthening's side condition
`w ⋠ e` is that nothing orders the read after the write.

`GeneratedPast` does not reach this justification: the `then` arm has
no symbol `⊑`-before its write that `Λ` could map to `r3`, so the first
disjunct of every lift into the `else` arm is over `r1` alone, and the
disjunction is valid only if the `else` arm's premise is, which it is not
while it fixes `r3 = 1`. The restriction to origins before the write
therefore changes this outcome, towards forbidding an outcome that compilers
produce (not mechanised: that every justification of `GeneratedPast` of the
`else` arm's write keeps `r1`).
MoRDor admits the outcome through its strengthening for lifting, which
strengthens the `then` arm with the `else` arm's `r3 = 1`, a symbol in
conflict with the write.
-/

namespace LiftLater

open EventStructure PpoKit

/-- `r1 := a; if r1 = 0 then (y := 1; r4 := z) else (r3 := z; y := r3) ∥ r2 := y; a := r2` -/
def prog : Stmt :=
  .par (.seq (PpoStability.ld .rlx "r1" "a") (.ite (.eq (.reg "r1") (.num 0))
      (.seq (PpoStability.st .rlx "y" 1) (PpoStability.ld .rlx "r4" "z"))
      (.seq (PpoStability.ld .rlx "r3" "z") (.store .rlx "y" (.reg "r3") false))))
    (.seq (PpoStability.ld .rlx "r2" "y") (.store .rlx "a" (.reg "r2") false))

/-- The branch condition `r1 = 0`. -/
def cond : Expr := .eq (.sym 0) (.val (.num 0))
def gT : Guard := ⟨1, cond, true⟩
def gF : Guard := ⟨1, cond, false⟩

def e0 : Event := PpoStability.R 0 0 [0, 0] [] [] .rlx "a"
def e1 : Event := ⟨1, .branch cond, ⟨0, [0, 1], []⟩, []⟩
def e2 : Event := PpoStability.W 2 0 [0, 1, 0, 0] [] [gT] .rlx "y" 1
def e3 : Event := PpoStability.R 3 0 [0, 1, 0, 1] [] [gT] .rlx "z"
def e4 : Event := PpoStability.R 4 0 [0, 1, 1, 0] [] [gF] .rlx "z"
def e5 : Event := ⟨5, .write .rlx (Expr.glob "y") (.sym 4) false, ⟨0, [0, 1, 1, 1], []⟩, [gF]⟩
def e6 : Event := PpoStability.R 6 1 [1, 0] [] [] .rlx "y"
def e7 : Event := ⟨7, .write .rlx (Expr.glob "a") (.sym 6) false, ⟨1, [1, 1], []⟩, []⟩

def esL : EventStructure := ⟨[e0, e1, e2, e3, e4, e5, e6, e7],
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (4, 5),
    (6, 7)], []⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esL := rfl

theorem nodupL : (esL.events.map (·.id)).Nodup := by decide
theorem gL : GlobLocs esL := globLocs_of (by decide)

theorem ev_e (e : Event) (he : e ∈ esL.events) : esL.ev e.id = some e :=
  PpoKit.ev_of_mem nodupL he

theorem poTrans : ∀ a b c, esL.poR a b → esL.poR b c → esL.poR a c := poTrans_of (by decide)

theorem symWF : esL.SymWF where
  past := by
    show ∀ e ∈ esL.events, ∀ α ∈ e.depSyms, (α, e.id) ∈ esL.po
    decide
  read_sym := by
    intro e he o l α v hk
    simp only [esL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [e0, e1, e2, e3, e4, e5, e6, e7, PpoStability.R, PpoStability.W] at hk ⊢ <;>
      exact hk.2.2.1.symm

/-- Nothing is ordered by `≼`, whatever the predicate: no synchronisation, and
    no two `⊑`-ordered accesses at one location. -/
theorem no_ppo {P : Pred} {a b : EventId} : ¬ esL.ppo P .empty a b := by
  intro h
  have := ppo_mem rfl gL (fun _ _ h => by rcases h with h | h <;> cases h) h
  have hl : syncL esL ++ aliasL esL = [] := by decide
  rw [hl] at this; cases this

theorem no_pred {P : Pred} {e x : EventId} : ¬ esL.pred .empty e P x := fun h => no_ppo h.1

/-- `r1 = 0`, `r3 = r4 = 1`: the `then` arm. -/
def fT : Valuation := fun α => if α = 0 then .num 0 else .num 1
/-- Every symbol `1`: the `else` arm. -/
def fF : Valuation := fun _ => .num 1

/-! ## The `then` arm: Strengthening with the later read -/

/-- The conjunct `s = 1`. -/
def Q (s : Sym) : Expr := .eq (.sym s) (.val (.num 1))

/-- `(r1 = 0, ∅) ⊢ y := 1` -/
def j₁₀ : Justification := ⟨e2.valres, [], .empty, e2⟩
/-- `(r1 = 0 ∧ r4 = 1 ∧ …, ∅) ⊢ y := 1`, with `r4 := z` `⊑`-after `y := 1`. -/
def j₁ : Justification := { j₁₀ with P := esL.strPred j₁₀.P (Q 3) [3] }

theorem j₁_syms : j₁.P.syms = [0, 3, 0] := by decide

theorem gen_j₁ : esL.Generated (fun _ => True) j₁ := by
  refine .str (Q 3) [3] (.pre (w := e2) (by simp [esL]) rfl ⟨fT, by unfold Expr.holds; decide⟩)
    ?_ ?_ ?_ ⟨fT, by unfold Expr.holds; decide, trivial⟩
  · intro e
    have h : (esL.strPred j₁₀.P (Q 3) [3]).syms = [0, 3, 0] := j₁_syms
    have h0 : j₁₀.P.syms = [0] := by decide
    rw [h, h0]; simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro rfl; decide
    · rintro ⟨h | h | h, h'⟩ <;> simp_all
  · intro e _; exact .canon (fun a h => by rcases h with h | h <;> cases h)
  · intro e he
    simp only [List.mem_singleton] at he; subst he
    exact ⟨.inr (show (2, 3) ∈ esL.po by decide), no_ppo⟩

/-- **`GeneratedPast` refuses the strengthening**: `r4 := z` is not
    `⊑`-before `y := 1` (`GeneratedPast.past`). -/
theorem not_gen_j₁ {Ω : Pred} : ¬ esL.GeneratedPast Ω j₁ := fun h => by
  have := h.past symWF poTrans
    (fun p hp => by simp [j₁, j₁₀, FwdCtx.empty] at hp) 3 (.inl (by rw [j₁_syms]; simp))
  revert this; show (3, 2) ∉ esL.po; decide

/-! ## The `else` arm: Strengthening and Value Assignment -/

/-- `(¬ r1 = 0, {r3}) ⊢ y := r3` -/
def j₂₀ : Justification := ⟨e5.valres, [4], .empty, e5⟩
/-- `(¬ r1 = 0 ∧ r3 = 1 ∧ …, {r3}) ⊢ y := r3` -/
def j₂₁ : Justification := { j₂₀ with P := esL.strPred j₂₀.P (Q 4) [4] }
/-- The `else` arm's write after Value Assignment, `y := 1`. -/
def w₂ : Event :=
  { j₂₁.w with
    kind := .write .rlx ((Expr.glob "y").subst 4 (.val (.num 1))) ((Expr.sym 4).subst 4 (.val (.num 1))) false }
/-- `(¬ r1 = 0 ∧ r3 = 1 ∧ …, ∅) ⊢ y := 1`, by Value Assignment. -/
def j₂ : Justification :=
  { P := j₂₁.P
    D := ((Expr.glob "y").subst 4 (.val (.num 1))).syms ++ ((Expr.sym 4).subst 4 (.val (.num 1))).syms
    δ := j₂₁.δ
    w := w₂ }

theorem gen_j₂₁ : esL.Generated (fun _ => True) j₂₁ := by
  refine .str (Q 4) [4] (.pre (w := e5) (by simp [esL]) rfl ⟨fF, by unfold Expr.holds; decide⟩)
    ?_ ?_ ?_ ⟨fF, by unfold Expr.holds; decide, trivial⟩
  · intro e
    have h : (esL.strPred j₂₀.P (Q 4) [4]).syms = [0, 4, 0] := by decide
    have h0 : j₂₀.P.syms = [0] := by decide
    rw [h, h0]; simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro rfl; decide
    · rintro ⟨h | h | h, h'⟩ <;> simp_all
  · intro e _; exact .canon (fun a h => by rcases h with h | h <;> cases h)
  · intro e he
    simp only [List.mem_singleton] at he; subst he
    exact ⟨.inl (show (4, 5) ∈ esL.po by decide), no_ppo⟩

theorem gen_j₂ : esL.Generated (fun _ => True) j₂ := by
  refine .va (α := 4) (v := .num 1) (o := .rlx) (x := Expr.glob "y") (e := .sym 4) (b := false) gen_j₂₁ rfl ?_
    ⟨fF, by unfold Expr.holds; decide, trivial⟩
  intro f hf v₁ v₂ h₁ h₂
  have hq := ((Expr.holds_and _ _ f).1 ((Expr.holds_and _ _ f).1 hf).2).1
  simp only [Q, Expr.holds, Expr.eval, Option.some.injEq, Val.bool.injEq,
    decide_eq_true_eq] at hq
  simp only [Expr.eval, Option.some.injEq] at h₁ h₂
  rw [← h₁, ← h₂, hq]

/-! ## The lift and the weakening -/

/-- `Λ = [r4 ↦ r3]`, the read of `z` of the `then` arm to that of the `else` arm. -/
def Λ : Relabelling := fun α => if α = 3 then some 4 else none

/-- `(… ∧ r3 = 1 ∧ … ∧ ((r1 = 0 ∧ r1 = 0) ∨ (¬ r1 = 0 ∧ ¬ r1 = 0)), ∅) ⊢ y := 1` -/
def jL : Justification := { j₂ with P := Expr.liftPred (j₁.P.rename Λ) j₂.P }
/-- The shared conjuncts: `r3 = 1`. -/
def PW : Expr := Expr.conj [Expr.tt, Q 4, Expr.tt, Expr.tt]
/-- The factored disjunction. -/
def Pv : Expr := .or (Expr.conj [cond, cond]) (Expr.conj [.not cond, .not cond])
/-- `(r3 = 1, ∅) ⊢ y := 1`: no dependency on `r1`. -/
def jW : Justification := { j₂ with P := PW }

theorem jL_P : jL.P = .and PW Pv := by decide

/-- The writes are closed relabel-equivalent under `Λ`: both write `1` to `y`,
    and neither has a `≼`-predecessor. -/
theorem cre : esL.ClosedRelabEq .empty Λ j₁.P j₁.w j₂.P j₂.w := by
  refine .mk ?_ ⟨fun _ _ => no_pred, fun _ _ => no_pred⟩ (fun _ _ _ _ h => (no_pred h).elim)
  simp only [relabEq, j₁, j₁₀, j₂, j₂₁, j₂₀, e2, e5, PpoStability.W, Event.isRead, Event.isWrite,
    Event.isAlloc, Event.loc, Event.val]
  exact ⟨⟨_, _, rfl, rfl, Expr.glob "y", AgreesUnder.refl _ _, AgreesUnder.refl _ _⟩,
    ⟨_, _, rfl, rfl, .val (.num 1), AgreesUnder.refl _ _, AgreesUnder.refl _ _⟩⟩

theorem liftBranch : esL.LiftBranch Λ j₁.w.id j₂.w.id := by
  refine ⟨gT, gF, ⟨e2, ev_e e2 (by simp [esL]), by decide⟩, ⟨e5, ev_e e5 (by simp [esL]), by decide⟩,
    rfl, rfl, by decide, fun α β h => ?_⟩
  simp only [Λ] at h
  split at h
  · rename_i hα; cases h; subst hα
    exact ⟨⟨e3, ev_e e3 (by simp [esL]), by decide⟩, ⟨e4, ev_e e4 (by simp [esL]), by decide⟩,
      ⟨e4, ev_e e4 (by simp [esL]), by decide⟩⟩
  · cases h

/-- **The lift is generated**, with every lifting condition of the restricted
    rule. -/
theorem gen_jL : esL.Generated (fun _ => True) jL := by
  refine .lift Λ gen_j₁ gen_j₂ rfl ?_ liftBranch ?_ cre ?_ ?_ ?_ ?_ ?_ ?_ ⟨fF, ?_, trivial⟩
  · intro a b c ha hb
    simp only [Λ] at ha hb
    split at ha <;> split at hb <;> simp_all
  · unfold Relabelling.InjOn; decide
  · intro e
    show e ∈ ([] ++ [] : List EventId) ↔ ∃ α ∈ ([] : List EventId), Λ.app α = e
    simp
  · intro α h; nomatch h
  · intro h; have := cls_clsB.1 h; revert this; decide
  · intro h; have := cls_clsB.1 h; revert this; decide
  · intro α h
    have key : ∀ α ∈ j₁.D ++ j₂.D, clsB esL Event.isVol α = false := by decide
    intro hv; have := key α h; rw [cls_clsB.1 hv] at this; cases this
  · intro α h
    have key : ∀ α ∈ (j₁.P.rename Λ).syms, (α, 5) ∈ esL.po := by decide
    exact key α h
  · unfold Expr.holds; decide

theorem Pv_valid : Entails (fun _ => True) Pv.holds := by
  intro f _
  simp only [Pv, cond, Expr.holds, Expr.conj, List.foldl, Expr.eval, Expr.tt]
  by_cases h : f 0 = .num 0 <;> simp [h]

/-- **The weakened justification is generated**: the `else` arm's write
    depends on `r3` only. -/
theorem gen_jW : esL.Generated (fun _ => True) jW :=
  .weak (j₁ := jL) (P' := PW) (Pw := Pv) gen_jL (by rw [jL_P]; exact Expr.ConjEq.refl _) Pv_valid
    ⟨fF, by unfold Expr.holds; decide, trivial⟩

/-- `r1` is no symbol of the weakened justification. -/
theorem jW_syms : jW.P.syms = [4] ∧ jW.D = [] ∧ jW.w.id = 5 := by decide

end LiftLater
