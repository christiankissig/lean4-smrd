import Smrd.FwdEntails
import Smrd.FwdAcrossAlias

/-!
# `FwdEntails` on the repository's examples

* `Smrd.FwdAcrossAlias` (#22): its execution violates every scope of the
  condition (`FwdAcrossAlias.not_fwdEntails`, `not_fwdEntailsImg`, …):
  `z := 1`'s justification, strengthened by `p ≠ p2` only, has `r2 := x` in its
  window and admits `p2 = &u`, while `fwdBase` asked `*p2` and `x` to be one
  location under the forwarding predicate.
* The positive executions with an `F ∪ WE` edge, `Smrd.PpoNecessity`'s
  `x := 0; (x := 1 ∥ x := 2)` (`xWW`) and `x := 1; x := 2` (`xC`), each with
  `x := 0` / `x := 1` elided: the elision is generated against a
  pre-justification whose predicate is valid, so every scope holds
  (`fwdEntailsAll_WW`, `fwdEntailsAll_C`, by `fwdEntailsOn_of_valid`). The other
  positive executions have no edge (`fwdEntailsOn_of_noEdge`).
-/

open EventStructure PpoKit Execution

namespace FwdAcrossAlias

/-- A model of `P_jZ ∧ ψ_δ` with `p = &x` and `p2 = &u`. -/
def fZ : Valuation := fun α =>
  if α = 4 then locX else if α = 5 then .loc ⟨.global "u", 0⟩ else .num 0

theorem PJ_jZ_fZ : xP.PJ esP jZ fZ := ⟨(holds_jZ fZ).2 (by decide), psi_P fZ rfl⟩

/-- **`jZ` does not entail the predicate of any `j₀` that generated the
    forwarding `(r0, r2)`**: `fwdBase` makes `*p2` and `x` one location under
    `P_{j₀} ∧ ψ_{δ_{j₀}}`, which `fZ` refutes. -/
theorem not_entails_68 {j₀ : Justification} {u v : EventId} (hg : EdgeGen esP xP j₀ 6 8 u v) :
    ¬ Entails (xP.PJ esP jZ) (PredOf esP j₀) := by
  intro h
  rcases hg.1 with ⟨-, rfl, rfl, -⟩ | ⟨hw, -⟩
  · obtain ⟨-, -, ev₁, ev₂, l₁, l₂, h₁, h₂, hl₁, hl₂, hq⟩ := hg.base
    cases h₁; cases h₂; cases hl₁; cases hl₂
    have := hq fZ (h fZ PJ_jZ_fZ) _ _ rfl rfl
    simp [fZ] at this
  · rw [δP] at hw; cases hw

theorem v_68 {j₀ : Justification} {u v : EventId} (hg : EdgeGen esP xP j₀ 6 8 u v) : v = 8 := by
  rcases hg.1 with ⟨-, -, rfl, -⟩ | ⟨hw, -⟩
  · rfl
  · rw [δP] at hw; cases hw

/-- **The execution of `Smrd.FwdAcrossAlias` violates `FwdEntails`**:
    `jZ`'s window contains `r2 := x`. -/
theorem not_fwdEntails : ¬ FwdEntails esP xP := fun h => by
  obtain ⟨j₀, u, v, hg, hJ, -⟩ := h 6 8 edge_68
  have hv := v_68 hg
  subst hv
  exact not_entails_68 hg (hJ jZ jZ_mem (.inr (po_of (by decide))))

/-- … and `FwdEntailsImg`: `jZ`'s window contains `remap_δ(r2) = r0`. -/
theorem not_fwdEntailsImg : ¬ FwdEntailsImg esP xP := fun h => by
  obtain ⟨j₀, u, v, hg, hJ, -⟩ := h 6 8 edge_68
  exact not_entails_68 hg (hJ jZ jZ_mem ⟨6, remap_86, .inr (po_of (by decide))⟩)

theorem not_fwdEntailsSrc : ¬ FwdEntailsSrc esP xP := fun h => not_fwdEntails h.fwdEntails

theorem not_fwdEntailsAll : ¬ FwdEntailsAll esP xP := fun h => not_fwdEntailsImg (h.on _)

end FwdAcrossAlias

namespace PpoNecessity

/-- `x := 0 -WE→ x := 1` against `x := 1`'s pre-justification. -/
theorem we_WW : esWW.weRel (pj (W 1 0 [1, 0] .rlx "x" 1)) 0 1 := by
  have hδ0 : ∀ a b, ¬ (pj (W 1 0 [1, 0] .rlx "x" 1)).δ.edge a b := by
    intro a b h; rcases h with h | h <;> cases h
  have hppo : ∀ a b, esWW.ppo (pj (W 1 0 [1, 0] .rlx "x" 1)).P.holds
      (pj (W 1 0 [1, 0] .rlx "x" 1)).δ a b → (a, b) ∈ syncL esWW ++ aliasL esWW :=
    fun a b h => ppo_mem rfl gWW hδ0 h
  refine ⟨⟨⟨⟨⟨(FwdCtx.remapRel_of_noEdge hδ0).2 (.inr
      ⟨show (0, 1) ∈ esWW.po by decide, _, _, _, _, rfl, rfl, rfl, rfl, fun _ => .num 0,
        SWW.holds (e := W 1 0 [1, 0] .rlx "x" 1) (by simp [esWW]) _,
        by simp [Expr.holds, Expr.eval, Expr.glob]⟩), by decide⟩, ?_⟩,
      show (0, 1) ∈ esWW.po by decide,
      _, _, _, _, rfl, rfl, rfl, rfl, fun _ _ _ _ h₁ h₂ => by rw [h₁] at h₂; cases h₂; rfl⟩,
    ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, fun ⟨e, he, hp⟩ => by cases he; simp [W, Event.isVol] at hp⟩,
    weNoRel_of (by decide) (by decide),
    Execution.weNoJoin_of_poForest (poForest_of (by decide)) _ _,
    EventStructure.not_rmwAcc_of_nil _ rfl _⟩
  rintro ⟨e'', h₁, h₂⟩
  have m₁ := hppo _ _ h₁
  have m₂ := hppo _ _ h₂
  have key : ∀ p ∈ syncL esWW ++ aliasL esWW, ∀ q ∈ syncL esWW ++ aliasL esWW,
      p.1 = 0 → q.2 = 1 → p.2 = q.1 → False := by decide
  exact key _ m₁ _ m₂ rfl rfl rfl

/-- **`x := 0; (x := 1 ∥ x := 2)` with `x := 0` elided satisfies every scope.** -/
theorem fwdEntailsAll_WW : FwdEntailsAll esWW xWW :=
  fwdEntailsOn_of_valid (fun s t he => by
    obtain ⟨rfl, rfl⟩ := edge_WW he
    exact ⟨pj (W 1 0 [1, 0] .rlx "x" 1), 0, 1,
      ⟨.inr ⟨by rw [δWW]; simp, rfl, rfl, we_WW⟩, fun p hp => (by cases hp), fun p hp => (by cases hp)⟩,
      fun f => SWW.holds (e := W 1 0 [1, 0] .rlx "x" 1) (by simp [esWW]) f⟩) _

/-- `x := 1 -WE→ x := 2` against `x := 2`'s pre-justification. -/
theorem we_C : esC.weRel (pj (W 1 0 [1] .rlx "x" 2)) 0 1 := by
  have hδ0 : ∀ a b, ¬ (pj (W 1 0 [1] .rlx "x" 2)).δ.edge a b := by
    intro a b h; rcases h with h | h <;> cases h
  have hppo : ∀ a b, esC.ppo (pj (W 1 0 [1] .rlx "x" 2)).P.holds
      (pj (W 1 0 [1] .rlx "x" 2)).δ a b → (a, b) ∈ syncL esC ++ aliasL esC :=
    fun a b h => ppo_mem rfl gC hδ0 h
  refine ⟨⟨⟨⟨⟨(FwdCtx.remapRel_of_noEdge hδ0).2 (.inr
      ⟨show (0, 1) ∈ esC.po by decide, _, _, _, _, rfl, rfl, rfl, rfl, fun _ => .num 0,
        SC.holds (e := W 1 0 [1] .rlx "x" 2) (by simp [esC]) _,
        by simp [Expr.holds, Expr.eval, Expr.glob]⟩), by decide⟩, ?_⟩,
      show (0, 1) ∈ esC.po by decide,
      _, _, _, _, rfl, rfl, rfl, rfl, fun _ _ _ _ h₁ h₂ => by rw [h₁] at h₂; cases h₂; rfl⟩,
    ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, fun ⟨e, he, hp⟩ => by cases he; simp [W, Event.isVol] at hp⟩,
    weNoRel_of (by decide) (by decide),
    Execution.weNoJoin_of_poForest (poForest_of (by decide)) _ _,
    EventStructure.not_rmwAcc_of_nil _ rfl _⟩
  rintro ⟨e'', h₁, h₂⟩
  have m₁ := hppo _ _ h₁
  have m₂ := hppo _ _ h₂
  have key : ∀ p ∈ syncL esC ++ aliasL esC, ∀ q ∈ syncL esC ++ aliasL esC,
      p.1 = 0 → q.2 = 1 → p.2 = q.1 → False := by decide
  exact key _ m₁ _ m₂ rfl rfl rfl

/-- **`x := 1; x := 2` with `x := 1` elided satisfies every scope.** -/
theorem fwdEntailsAll_C : FwdEntailsAll esC xC :=
  fwdEntailsOn_of_valid (fun s t he => by
    obtain ⟨rfl, rfl⟩ := edge_C he
    exact ⟨pj (W 1 0 [1] .rlx "x" 2), 0, 1,
      ⟨.inr ⟨by rw [δC]; simp, rfl, rfl, we_C⟩, fun p hp => (by cases hp), fun p hp => (by cases hp)⟩,
      fun f => SC.holds (e := W 1 0 [1] .rlx "x" 2) (by simp [esC]) f⟩) _

end PpoNecessity
