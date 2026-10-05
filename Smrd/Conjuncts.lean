import Smrd.Types

/-!
# Predicates as Sets of Conjuncts (Paragraph `par:conj`)

The predicate of a justification is read up to its set of conjuncts,
`conj(P₁ ∧ P₂) = conj(P₁) ∪ conj(P₂)` and `conj(P) = {P}` for `P` not a
conjunction. Weakening removes any one conjunct, Strengthening adds conjuncts,
and Lifting keeps the conjuncts its premises share outside the disjunction it
forms (`Smrd.Justifications`).

`conjuncts P` is a list; two predicates are identified when their lists have
the same members (`ConjEq`). Predicates so identified are equivalent
(`ConjEq.holds_iff`) and have the same symbols (`ConjEq.mem_syms_iff`), so the
identification is invisible to the semantic queries and to the dependencies
freezing reads off the symbols (`Execution.DP`).
-/

namespace Expr

/-- `conj(P)`: the conjuncts of `P`, flattening nested conjunctions. -/
def conjuncts : Expr → List Expr
  | .and a b => a.conjuncts ++ b.conjuncts
  | e => [e]

/-- `P` and `Q` have the same set of conjuncts. -/
def ConjEq (P Q : Expr) : Prop := ∀ c, c ∈ P.conjuncts ↔ c ∈ Q.conjuncts

theorem ConjEq.refl (P : Expr) : ConjEq P P := fun _ => Iff.rfl

theorem ConjEq.symm {P Q : Expr} (h : ConjEq P Q) : ConjEq Q P := fun c => (h c).symm

theorem ConjEq.trans {P Q R : Expr} (h₁ : ConjEq P Q) (h₂ : ConjEq Q R) : ConjEq P R :=
  fun c => (h₁ c).trans (h₂ c)

/-- No conjunct is itself a conjunction. -/
theorem conjuncts_not_and {P c : Expr} (h : c ∈ P.conjuncts) : ∀ a b, c ≠ .and a b := by
  induction P with
  | and a b iha ihb =>
      simp only [conjuncts, List.mem_append] at h
      exact h.elim iha ihb
  | _ =>
      simp only [conjuncts, List.mem_singleton] at h
      subst h; intro _ _ h; cases h

theorem holds_and (a b : Expr) (f : Valuation) :
    (Expr.and a b).holds f ↔ a.holds f ∧ b.holds f := by
  simp only [Expr.holds, Expr.eval]
  cases ha : a.eval f with
  | none => simp
  | some va =>
    cases hb : b.eval f with
    | none => cases va <;> simp
    | some vb =>
      cases va <;> cases vb <;> simp

/-- A predicate holds iff all its conjuncts do. -/
theorem holds_iff_conjuncts (P : Expr) (f : Valuation) :
    P.holds f ↔ ∀ c ∈ P.conjuncts, c.holds f := by
  induction P with
  | and a b iha ihb =>
      simp only [holds_and, iha, ihb, conjuncts, List.mem_append]
      constructor
      · rintro ⟨ha, hb⟩ c (hc | hc)
        · exact ha c hc
        · exact hb c hc
      · intro h; exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  | _ => simp [conjuncts]

/-- The symbols of a predicate are those of its conjuncts. -/
theorem mem_syms_iff_conjuncts (P : Expr) (α : Sym) :
    α ∈ P.syms ↔ ∃ c ∈ P.conjuncts, α ∈ c.syms := by
  induction P with
  | and a b iha ihb =>
      simp only [syms, conjuncts, List.mem_append, iha, ihb]
      constructor
      · rintro (⟨c, hc, h⟩ | ⟨c, hc, h⟩)
        · exact ⟨c, Or.inl hc, h⟩
        · exact ⟨c, Or.inr hc, h⟩
      · rintro ⟨c, hc | hc, h⟩
        · exact Or.inl ⟨c, hc, h⟩
        · exact Or.inr ⟨c, hc, h⟩
  | _ => simp [conjuncts]

/-- Predicates with the same conjuncts are equivalent. -/
theorem ConjEq.holds_iff {P Q : Expr} (h : ConjEq P Q) (f : Valuation) :
    P.holds f ↔ Q.holds f := by
  rw [holds_iff_conjuncts, holds_iff_conjuncts]
  exact ⟨fun hP c hc => hP c ((h c).2 hc), fun hQ c hc => hQ c ((h c).1 hc)⟩

/-- Predicates with the same conjuncts have the same symbols. -/
theorem ConjEq.mem_syms_iff {P Q : Expr} (h : ConjEq P Q) (α : Sym) :
    α ∈ P.syms ↔ α ∈ Q.syms := by
  rw [mem_syms_iff_conjuncts, mem_syms_iff_conjuncts]
  exact ⟨fun ⟨c, hc, hα⟩ => ⟨c, (h c).1 hc, hα⟩, fun ⟨c, hc, hα⟩ => ⟨c, (h c).2 hc, hα⟩⟩

theorem conjEq_and_comm (a b : Expr) : ConjEq (.and a b) (.and b a) := by
  intro c; simp only [conjuncts, List.mem_append]; exact or_comm

end Expr
