import Smrd.DPPast
import Smrd.PpoNecessity

/-!
# Lifting a guard into another thread

`r := y; if r = 0 then x := 1 ∥ x := 1`, all accesses relaxed. The two writes
`x := 1` are closed relabel-equivalent under the empty relabelling: they write
the same value to the same location, and neither has a `≼`-predecessor. The
paper's Lifting (`def:elab-lift`) then lifts the guarded write's premise
`r = 0` into the unguarded write of the other thread,
`(⊤ ∧ (r = 0 ∨ ⊤), ∅) ⊢ x := 1`, and freezing an execution that takes this
justification gives the edge `(r, x := 1)` in `DP`, across threads, against
`⊑`.

Closed relabel-equivalence constrains the relabelling on `D₁` only; a symbol
of `P₁` outside `D₁` keeps an origin `⊑`-before `w₁`, which here lies in
another thread than `w₂`. Execution-level arguments (`X` conflict-free) do not
exclude the edge: both endpoints are on the paths the execution takes.

* `lift_conds`: every condition of the paper's Lifting holds, on generated
  premises.
* `not_liftPast`: so the hypothesis `LiftPast` fails for this program, whose
  event structure is `SymWF` (`symWF`).
* `isExecution_C`, `dp_C`: were the lift generated, `xC` would be an
  execution with `DP` edge `(0, 3)`, and `¬ 0 ⊑ 3`.
* `not_generated`, `not_execution`: under the restriction of `Generated.lift`
  (origins of `⟦P₁⟧_Λ` `⊑`-before `w₂`) it is not, and `xC` is no execution.

Within one thread, with `w₁` `⊑`-after `w₂` and a symbol of `P₁` between
them, the recursion of closed relabel-equivalence through `pred` gets in the
way: a write to the same location `⊑`-before `w₁` is a `≼`-predecessor of
`w₁`, and `w₂` then needs a matching one. No instance is mechanised; the
restriction excludes it either way.
-/

namespace LiftCross

open EventStructure PpoKit Execution

/-- `r := y; if r = 0 then x := 1 ∥ x := 1` -/
def prog : Stmt :=
  .par (.seq (PpoStability.ld .rlx "r" "y")
      (.ite (.eq (.reg "r") (.num 0)) (PpoStability.st .rlx "x" 1) .skip))
    (PpoStability.st .rlx "x" 1)

/-- The branch condition `r = 0`. -/
def cond : Expr := .eq (.sym 0) (.val (.num 0))

def e0 : Event := PpoStability.R 0 0 [0, 0] [] [] .rlx "y"
def e1 : Event := ⟨1, .branch cond, ⟨0, [0, 1], []⟩, []⟩
def e2 : Event := PpoStability.W 2 0 [0, 1, 0] [] [⟨1, cond, true⟩] .rlx "x" 1
def e3 : Event := PpoStability.W 3 1 [1] [] [] .rlx "x" 1

def esC : EventStructure := ⟨[e0, e1, e2, e3], [(0, 1), (0, 2), (1, 2)], []⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esC := rfl

theorem nodupC : (esC.events.map (·.id)).Nodup := by decide

theorem gC : GlobLocs esC := globLocs_of (by decide)

/-- The valuation `r = 0`, under which every value restriction holds. -/
def f₀ : Valuation := fun _ => .num 0

theorem holdsC {e : Event} (he : e ∈ esC.events) : e.valres.holds f₀ := by
  simp only [esC, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> unfold Expr.holds <;> decide

/-- The event structure introduces symbols before their uses. -/
theorem symWF : esC.SymWF where
  past := by
    show ∀ e ∈ esC.events, ∀ α ∈ e.depSyms, (α, e.id) ∈ esC.po
    decide
  read_sym := by
    intro e he o l α v hk
    simp only [esC, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [e0, e1, e2, e3, PpoStability.R, PpoStability.W] at hk ⊢
    exact hk.2.2.1.symm

/-- No event has a `≼`-predecessor, whatever the predicate. -/
theorem no_ppo {P : Pred} {a b : EventId} : ¬ esC.ppo P .empty a b := by
  intro h
  have := ppo_mem rfl gC (fun _ _ h => by rcases h with h | h <;> cases h) h
  have hl : syncL esC ++ aliasL esC = [] := by decide
  rw [hl] at this; cases this

theorem no_pred {P : Pred} {e x : EventId} : ¬ esC.pred .empty e P x := fun h => no_ppo h.1

/-! ## The lift -/

/-- The pre-justification `(r = 0, ∅) ⊢ x := 1` of thread 0's write. -/
def j₁ : Justification := PpoNecessity.pj e2
/-- The pre-justification `(⊤, ∅) ⊢ x := 1` of thread 1's write. -/
def j₂ : Justification := PpoNecessity.pj e3
/-- The empty relabelling. -/
def Λ₀ : Relabelling := fun _ => none
/-- The lifted justification `(⊤ ∧ (r = 0 ∨ ⊤), ∅) ⊢ x := 1` of thread 1's write. -/
def jL : Justification := { j₂ with P := Expr.liftPred (j₁.P.rename Λ₀) j₂.P }

theorem pre₁ : esC.Generated (fun _ => True) j₁ :=
  .pre (w := e2) (by simp [esC]) rfl ⟨f₀, holdsC (by simp [esC])⟩

theorem pre₂ : esC.Generated (fun _ => True) j₂ :=
  .pre (w := e3) (by simp [esC]) rfl ⟨f₀, holdsC (by simp [esC])⟩

/-- `x := 1` is closed relabel-equivalent to `x := 1` under `Λ₀`. -/
theorem relabEq_12 : esC.ClosedRelabEq .empty Λ₀ j₁.P e2 j₂.P e3 := by
  refine .mk ?_ ⟨fun _ _ => no_pred, fun _ _ => no_pred⟩ (fun _ _ _ _ h => (no_pred h).elim)
  have key : ∀ P₁ P₂ : Expr, (∀ f, ∃ b, P₁.eval f = some (.bool b)) →
      (∀ f, ∃ b, P₂.eval f = some (.bool b)) →
      esC.relabEqExpr .empty Λ₀ P₁ (.val (.num 1)) P₂ (.val (.num 1)) ∧
      esC.relabEqExpr .empty Λ₀ P₁ (Expr.glob "x") P₂ (Expr.glob "x") := by
    intro P₁ P₂ h₁ h₂
    have ren : ∀ E : Expr, E.rename Λ₀ = E := by
      intro E
      induction E with
      | val => rfl
      | sym => rfl
      | bin _ _ _ iha ihb | eq _ _ iha ihb | le _ _ iha ihb | and _ _ iha ihb
      | or _ _ iha ihb => simp [Expr.rename, iha, ihb]
      | not _ iha => simp [Expr.rename, iha]
    refine ⟨⟨.val (.num 1), ?_⟩, ⟨Expr.glob "x", ?_⟩⟩ <;>
    · intro f _ v₁ v₂ hv₁ hv₂
      obtain ⟨b₁, hb₁⟩ := h₁ f
      obtain ⟨b₂, hb₂⟩ := h₂ f
      simp [ren, Expr.imp, Expr.eval, Expr.tt, Expr.glob, hb₁, hb₂] at hv₁ hv₂
      rw [← hv₁, ← hv₂]
  have b₁ : ∀ f, ∃ b, j₁.P.eval f = some (.bool b) := fun f =>
    ⟨decide (f 0 = .num 0), by simp [j₁, PpoNecessity.pj, e2, PpoStability.W, Event.valres,
      Expr.conj, Guard.expr, cond, Expr.eval, Expr.tt]⟩
  have b₂ : ∀ f, ∃ b, j₂.P.eval f = some (.bool b) := fun _ =>
    ⟨true, by simp [j₂, PpoNecessity.pj, e3, PpoStability.W, Event.valres, Expr.conj,
      Expr.eval, Expr.tt]⟩
  obtain ⟨hv, hl⟩ := key _ _ b₁ b₂
  simp only [relabEq, e2, e3, PpoStability.W, Event.isRead, Event.isWrite, Event.isAlloc,
    Event.loc, Event.val]
  simp only [Bool.and_self, Bool.or_true]
  exact ⟨⟨_, _, rfl, rfl, hl⟩, ⟨_, _, rfl, rfl, hv⟩⟩

/-- Every condition of the paper's Lifting holds. -/
theorem lift_conds :
    j₁.δ = j₂.δ ∧ Λ₀.Injective ∧ esC.ClosedRelabEq j₁.δ Λ₀ j₁.P j₁.w j₂.P j₂.w ∧
    (∀ e, e ∈ j₂.D ↔ ∃ α ∈ j₁.D, Λ₀.app α = e) ∧
    (∀ α ∈ j₁.D, ∃ ev₁ ev₂, esC.ev α = some ev₁ ∧ esC.ev (Λ₀.app α) = some ev₂ ∧
      esC.ClosedRelabEq j₁.δ Λ₀ j₁.P ev₁ j₂.P ev₂) ∧
    ¬ esC.cls Event.isVol j₁.w.id ∧ ¬ esC.cls Event.isVol j₂.w.id ∧
    (∀ α ∈ j₁.D ++ j₂.D, ¬ esC.cls Event.isVol α) ∧
    Sat (Pred.and (Expr.liftPred (j₁.P.rename Λ₀) j₂.P).holds (fun _ => True)) := by
  refine ⟨rfl, ?_, relabEq_12, ?_, ?_, ?_, ?_, ?_, f₀, ?_, trivial⟩
  · intro a b c h; simp [Λ₀] at h
  · intro e
    show e ∈ ([] : List EventId) ↔ ∃ α ∈ ([] : List EventId), Λ₀.app α = e
    simp
  · intro α h; nomatch h
  · intro h; have := cls_clsB.1 h; revert this; decide
  · intro h; have := cls_clsB.1 h; revert this; decide
  · intro α h; nomatch h
  · unfold Expr.holds; decide

/-- The guard's read is a symbol of the lifted premise, and not `⊑`-before the
    other thread's write. -/
theorem guard_sym : 0 ∈ (j₁.P.rename Λ₀).syms ∧ 0 ∈ jL.P.syms ∧ ¬ esC.poR 0 j₂.w.id :=
  ⟨by decide, by decide, by show (0, 3) ∉ esC.po; decide⟩

/-- **`LiftPast` fails** for a program. -/
theorem not_liftPast : ¬ esC.LiftPast (fun _ => True) := by
  intro h
  obtain ⟨hδ, hΛ, hrel, hD, -⟩ := lift_conds
  exact guard_sym.2.2 (h j₁ j₂ Λ₀ pre₁ pre₂ hδ hΛ hrel hD 0 guard_sym.1)

/-- Under the restriction of `Generated.lift` the lift is not generated. -/
theorem not_generated {Ω : Pred} : ¬ esC.Generated Ω jL := by
  intro h
  have hpo : ∀ a b c, esC.poR a b → esC.poR b c → esC.poR a c := by
    have : ∀ p ∈ esC.po, ∀ q ∈ esC.po, p.2 = q.1 → (p.1, q.2) ∈ esC.po := by decide
    intro a b c h₁ h₂
    exact this (a, b) h₁ (b, c) h₂ rfl
  exact guard_sym.2.2
    (h.past symWF hpo (fun p hp => by simp [jL, j₂, PpoNecessity.pj, FwdCtx.empty] at hp) 0
      (.inl guard_sym.2.1))

/-! ## The execution -/

/-- Thread 0 takes its branch; thread 1's write carries the lifted
    justification. -/
def xC : Execution := ⟨esC.Candidate, [j₁, jL], fun _ _ => False⟩

theorem δC : xC.δ = .empty := foldr_empty (by
  intro j hj
  simp only [xC, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl <;> rfl)

theorem X_C {a : EventId} : xC.X a ↔ a = 0 ∨ a = 2 ∨ a = 3 := by
  constructor
  · rintro ⟨⟨e, he, rfl⟩, hb, -⟩
    simp only [esC, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact .inl rfl
    · exact absurd ⟨e1, PpoKit.ev_of_mem nodupC (by simp [esC]), rfl⟩ hb
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact cand_of_mem nodupC (e := e0) (by simp [esC]) rfl rfl
    · exact cand_of_mem nodupC (e := e2) (by simp [esC]) rfl rfl
    · exact cand_of_mem nodupC (e := e3) (by simp [esC]) rfl rfl

/-- **Were the lift generated, `xC` would be an execution**: every other
    condition of `IsExecution` holds. -/
theorem isExecution_C (hg : esC.Generated (fun _ => True) jL) :
    xC.IsExecution esC (fun _ => True) where
  maximal := ⟨fun _ h => h, fun a b _ _ ⟨ea, eb, ha, hb, hn⟩ =>
      hn ⟨f₀, holdsC (ev_inv ha).1, holdsC (ev_inv hb).1⟩,
    fun _ hc hn => absurd hc hn⟩
  generated j hj := by
    simp only [xC, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact pre₁
    · exact hg
  inX j hj := by
    simp only [xC, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact X_C.2 (.inr (.inl rfl))
    · exact X_C.2 (.inr (.inr rfl))
  consistent := ⟨f₀, fun j hj => by
      simp only [xC, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> unfold Expr.holds <;> decide,
    fun a e _ he => holdsC (ev_inv he).1⟩
  fwdWF := by rw [δC]; exact FwdCtx.WF.empty
  rf_wr _ _ h := h.elim
  rf_func _ _ _ h := h.elim
  justified w hw he _ := by
    rcases X_C.1 hw with rfl | rfl | rfl
    · exact absurd (cls_clsB.1 he) (by decide)
    · refine ⟨j₁, by simp [xC], rfl, fun j' hj' h => ?_⟩
      simp only [xC, List.mem_cons, List.not_mem_nil, or_false] at hj'
      rcases hj' with rfl | rfl
      · rfl
      · cases h
    · refine ⟨jL, by simp [xC], rfl, fun j' hj' h => ?_⟩
      simp only [xC, List.mem_cons, List.not_mem_nil, or_false] at hj'
      rcases hj' with rfl | rfl
      · cases h
      · rfl

/-- **`DP` runs against `⊑`**: freezing `xC` gives the edge from thread 0's
    read to thread 1's write. -/
theorem dp_C : xC.DP 0 3 ∧ ¬ esC.poR 0 3 :=
  ⟨⟨X_C.2 (.inl rfl), X_C.2 (.inr (.inr rfl)), jL, by simp [xC], rfl, .inl guard_sym.2.1⟩,
    guard_sym.2.2⟩

/-- Under the restriction `xC` is no execution. -/
theorem not_execution {Ω : Pred} : ¬ xC.IsExecution esC Ω :=
  fun hx => not_generated (hx.generated jL (by simp [xC]))

end LiftCross
