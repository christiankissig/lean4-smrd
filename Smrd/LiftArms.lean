import Smrd.PpoNecessity

/-!
# Lifting an invariant store out of a branching

`rc := c; if rc = 1 then (r1 := y; x := r1) else (r2 := y; x := r2)`, all accesses relaxed: the
same store in both arms, the case sMRD's Lifting is for (Richards et al., §4.7: "equivalent
writes in each branch", "invariant stores on conflicting branches"). Lifting the
pre-justification `(rc = 1, {r1}) ⊢ x := r1` into `(¬ rc = 1, {r2}) ⊢ x := r2` under
`Λ = [r1 ↦ r2]` gives `(⊤ ∧ (rc = 1 ∨ ¬ rc = 1), {r2}) ⊢ x := r2`, and Weakening leaves
`(⊤, {r2}) ⊢ x := r2`: the store depends on the read of `y`, not on `rc`.

The restricted rule (`Generated.lift`) admits the lift: the writes lie on the two outcomes of
the branching on `rc = 1`, `Λ` maps the read `r1` of the `then` arm into the read `r2` of the
`else` arm and leaves `rc`, read before the branching, fixed (`liftBranch`), and `⟦·⟧_Λ` is
one-to-one on the symbols `rc`, `r1` of the first premise (`injOn`).

* `gen_jL`, `gen_jW`: the lifted and the weakened justification are generated.
* `jW_syms`: `rc` is not a symbol of the weakened justification.
-/

namespace LiftArms

open EventStructure PpoKit

/-- `rc := c; if rc = 1 then (r1 := y; x := r1) else (r2 := y; x := r2)` -/
def prog : Stmt :=
  .seq (PpoStability.ld .rlx "rc" "c")
    (.ite (.eq (.reg "rc") (.num 1))
      (.seq (PpoStability.ld .rlx "r1" "y") (.store .rlx "x" (.reg "r1") false))
      (.seq (PpoStability.ld .rlx "r2" "y") (.store .rlx "x" (.reg "r2") false)))

/-- The branch condition `rc = 1`. -/
def cond : Expr := .eq (.sym 0) (.val (.num 1))

/-- The guards of the two arms. -/
def gT : Guard := ⟨1, cond, true⟩
def gF : Guard := ⟨1, cond, false⟩

def e0 : Event := PpoStability.R 0 0 [0] [] [] .rlx "c"
def e1 : Event := ⟨1, .branch cond, ⟨0, [1], []⟩, []⟩
def e2 : Event := PpoStability.R 2 0 [1, 0, 0] [] [gT] .rlx "y"
def e3 : Event := ⟨3, .write .rlx (Expr.glob "x") (.sym 2) false, ⟨0, [1, 0, 1], []⟩, [gT]⟩
def e4 : Event := PpoStability.R 4 0 [1, 1, 0] [] [gF] .rlx "y"
def e5 : Event := ⟨5, .write .rlx (Expr.glob "x") (.sym 4) false, ⟨0, [1, 1, 1], []⟩, [gF]⟩

def esL : EventStructure :=
  ⟨[e0, e1, e2, e3, e4, e5], [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4),
    (1, 5), (2, 3), (4, 5)], []⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esL := rfl

theorem nodupL : (esL.events.map (·.id)).Nodup := by decide

theorem gL : GlobLocs esL := globLocs_of (by decide)

theorem ev_e (e : Event) (he : e ∈ esL.events) : esL.ev e.id = some e :=
  PpoKit.ev_of_mem nodupL he

/-- The valuation with every symbol `0`: the `else` arm. -/
def f₀ : Valuation := fun _ => .num 0
/-- `rc = 1`: the `then` arm. -/
def f₁ : Valuation := fun _ => .num 1

/-- No event has a `≼`-predecessor, whatever the predicate: the accesses to `y` are reads, and
    nothing synchronises. -/
theorem no_ppo {P : Pred} {a b : EventId} : ¬ esL.ppo P .empty a b := by
  intro h
  have := ppo_mem rfl gL (fun _ _ h => by rcases h with h | h <;> cases h) h
  have hl : syncL esL ++ aliasL esL = [] := by decide
  rw [hl] at this; cases this

theorem no_pred {P : Pred} {e x : EventId} : ¬ esL.pred .empty e P x := fun h => no_ppo h.1

/-! ## The lift -/

/-- `(rc = 1, {r1}) ⊢ x := r1` -/
def j₁ : Justification := ⟨e3.valres, [2], .empty, e3⟩
/-- `(¬ rc = 1, {r2}) ⊢ x := r2` -/
def j₂ : Justification := ⟨e5.valres, [4], .empty, e5⟩
/-- `Λ = [r1 ↦ r2]` -/
def Λ : Relabelling := fun α => if α = 2 then some 4 else none

/-- The lifted justification `(⊤ ∧ (rc = 1 ∨ ¬ rc = 1), {r2}) ⊢ x := r2`. -/
def jL : Justification := { j₂ with P := Expr.liftPred (j₁.P.rename Λ) j₂.P }
/-- The shared conjuncts, `⊤`. -/
def PW : Expr := Expr.conj [Expr.tt]
/-- The factored disjunction `rc = 1 ∨ ¬ rc = 1`. -/
def Pv : Expr := .or (Expr.conj [cond]) (Expr.conj [.not cond])
/-- The weakened justification `(⊤, {r2}) ⊢ x := r2`. -/
def jW : Justification := { j₂ with P := PW }

theorem jL_P : jL.P = .and PW Pv := by decide

theorem pre₁ : esL.Generated (fun _ => True) j₁ :=
  .pre (w := e3) (by simp [esL]) rfl ⟨f₁, by unfold Expr.holds; decide⟩

theorem pre₂ : esL.Generated (fun _ => True) j₂ :=
  .pre (w := e5) (by simp [esL]) rfl ⟨f₀, by unfold Expr.holds; decide⟩

/-- The reads of `y` are closed relabel-equivalent under `Λ`. -/
theorem cre_24 : esL.ClosedRelabEq .empty Λ j₁.P e2 j₂.P e4 := by
  refine .mk ?_ ⟨fun _ _ => no_pred, fun _ _ => no_pred⟩ (fun _ _ _ _ h => (no_pred h).elim)
  simp only [relabEq, e2, e4, PpoStability.R, Event.isRead, Event.isWrite, Event.isAlloc,
    Event.loc, Event.val, Bool.and_self, Bool.true_or, if_true]
  exact ⟨⟨_, _, rfl, rfl, Expr.glob "y", AgreesUnder.refl _ _, AgreesUnder.refl _ _⟩,
    ⟨_, _, rfl, rfl, .sym 4, AgreesUnder.refl _ _, AgreesUnder.refl _ _⟩⟩

/-- The writes of `x` are closed relabel-equivalent under `Λ`. -/
theorem cre_35 : esL.ClosedRelabEq .empty Λ j₁.P e3 j₂.P e5 := by
  refine .mk ?_ ⟨fun _ _ => no_pred, fun _ _ => no_pred⟩ (fun _ _ _ _ h => (no_pred h).elim)
  simp only [relabEq, e3, e5, Event.isRead, Event.isWrite, Event.isAlloc, Event.loc, Event.val,
    Bool.and_self, Bool.or_true]
  exact ⟨⟨_, _, rfl, rfl, Expr.glob "x", AgreesUnder.refl _ _, AgreesUnder.refl _ _⟩,
    ⟨_, _, rfl, rfl, .sym 4, AgreesUnder.refl _ _, AgreesUnder.refl _ _⟩⟩

/-- Every condition of the unrestricted Lifting holds. -/
theorem lift_conds : esL.LiftConds (fun _ => True) Λ j₁ j₂ := by
  refine ⟨rfl, ?_, cre_35, ?_, ?_, ?_, ?_, ?_, ?_, ⟨f₀, ?_, trivial⟩⟩
  · intro a b c ha hb
    simp only [Λ] at ha hb
    split at ha <;> split at hb <;> simp_all
  · intro e
    show e ∈ [4] ↔ ∃ α ∈ [2], Λ.app α = e
    simp [Relabelling.app, Λ, eq_comm]
  · intro α h
    simp only [j₁, List.mem_cons, List.not_mem_nil, or_false] at h; subst h
    exact ⟨e2, e4, ev_e e2 (by simp [esL]), ev_e e4 (by simp [esL]), cre_24⟩
  · intro h; have := cls_clsB.1 h; revert this; decide
  · intro h; have := cls_clsB.1 h; revert this; decide
  · intro α h
    have key : ∀ α ∈ j₁.D ++ j₂.D, clsB esL Event.isVol α = false := by decide
    intro hv; have := key α h; rw [cls_clsB.1 hv] at this; cases this
  · intro α h
    have key : ∀ α ∈ (j₁.P.rename Λ).syms, (α, 5) ∈ esL.po := by decide
    exact key α h
  · unfold Expr.holds; decide

/-- **The branching restriction holds**: `x := r1` and `x := r2` lie on the two outcomes of
    the branching on `rc = 1`, and `Λ` maps `r1`, of the `then` arm, to `r2`, of the `else`
    arm. -/
theorem liftBranch : esL.LiftBranch Λ j₁.w.id j₂.w.id := by
  refine ⟨gT, gF, ⟨e3, ev_e e3 (by simp [esL]), by decide⟩, ⟨e5, ev_e e5 (by simp [esL]), by decide⟩,
    rfl, rfl, by decide, fun α β h => ?_⟩
  simp only [Λ] at h
  split at h
  · rename_i hα; cases h; subst hα
    exact ⟨⟨e2, ev_e e2 (by simp [esL]), by decide⟩, ⟨e4, ev_e e4 (by simp [esL]), by decide⟩⟩
  · cases h

/-- **The renaming is one-to-one** on `rc` and `r1`. -/
theorem injOn : Λ.InjOn (j₁.P.syms ++ j₁.D) := by unfold Relabelling.InjOn; decide

/-- **The lift is generated under the restricted rule.** -/
theorem gen_jL : esL.Generated (fun _ => True) jL :=
  .lift' pre₁ pre₂ lift_conds liftBranch injOn

theorem Pv_valid : Entails (fun _ => True) Pv.holds := by
  intro f _
  simp only [Pv, Expr.holds, Expr.conj, List.foldl, Expr.eval, Expr.tt, cond]
  cases f 0 <;> simp
  all_goals (rename_i n; by_cases h : n = 1 <;> simp [h])

/-- **The weakened justification is generated**: the invariant store depends on the read of
    `y` only. -/
theorem gen_jW : esL.Generated (fun _ => True) jW :=
  .weak (j₁ := jL) (P' := PW) (Pw := Pv) gen_jL (by rw [jL_P]; exact Expr.ConjEq.refl _) Pv_valid
    ⟨f₀, by unfold Expr.holds; decide, trivial⟩

/-- `rc` is not a symbol of the weakened justification; its dependency is `r2`. -/
theorem jW_syms : 0 ∉ jW.P.syms ∧ jW.D = [4] := by decide

end LiftArms
