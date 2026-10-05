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

Lifting's predicate `C ∧ (⋀A₁ ∨ ⋀A₂)` (`liftPred`) is equivalent to
`P₁ ∨ P₂` and has the same symbols (`liftPred_holds_iff`,
`mem_syms_liftPred_iff`). As `∨` holds only where both disjuncts denote
booleans, the equivalence tracks definedness (`IsBool`).
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

/-! ## Definedness and the connectives -/

/-- `e` denotes a boolean under `f`. `P ∨ Q` holds only where both sides
    denote booleans, so the factoring of Lifting must keep track of it. -/
def IsBool (e : Expr) (f : Valuation) : Prop := ∃ b, e.eval f = some (.bool b)

theorem IsBool.of_holds {e : Expr} {f : Valuation} (h : e.holds f) : e.IsBool f := ⟨true, h⟩

theorem isBool_and (a b : Expr) (f : Valuation) :
    (Expr.and a b).IsBool f ↔ a.IsBool f ∧ b.IsBool f := by
  simp only [IsBool, Expr.eval]
  cases ha : a.eval f with
  | none => simp
  | some va =>
    cases hb : b.eval f with
    | none => cases va <;> simp
    | some vb => cases va <;> cases vb <;> simp

theorem holds_or (a b : Expr) (f : Valuation) :
    (Expr.or a b).holds f ↔ a.IsBool f ∧ b.IsBool f ∧ (a.holds f ∨ b.holds f) := by
  simp only [Expr.holds, IsBool, Expr.eval]
  cases ha : a.eval f with
  | none => simp
  | some va =>
    cases hb : b.eval f with
    | none => cases va <;> simp
    | some vb =>
      cases va <;> cases vb <;> simp

theorem isBool_iff_conjuncts (P : Expr) (f : Valuation) :
    P.IsBool f ↔ ∀ c ∈ P.conjuncts, c.IsBool f := by
  induction P with
  | and a b iha ihb =>
      simp only [isBool_and, iha, ihb, conjuncts, List.mem_append]
      constructor
      · rintro ⟨ha, hb⟩ c (hc | hc)
        · exact ha c hc
        · exact hb c hc
      · intro h; exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  | _ => simp [conjuncts]

/-! ## Conjunctions of lists (`⋀ L`, with `⋀∅ = ⊤`) -/

theorem holds_conj_foldl (L : List Expr) (acc : Expr) (f : Valuation) :
    (L.foldl .and acc).holds f ↔ acc.holds f ∧ ∀ e ∈ L, e.holds f := by
  induction L generalizing acc with
  | nil => simp
  | cons e L ih =>
      simp only [List.foldl, ih, holds_and, List.mem_cons]
      constructor
      · rintro ⟨⟨ha, he⟩, hL⟩
        exact ⟨ha, fun x hx => hx.elim (fun h => h ▸ he) (hL x)⟩
      · rintro ⟨ha, hL⟩
        exact ⟨⟨ha, hL e (Or.inl rfl)⟩, fun x hx => hL x (Or.inr hx)⟩

theorem isBool_conj_foldl (L : List Expr) (acc : Expr) (f : Valuation) :
    (L.foldl .and acc).IsBool f ↔ acc.IsBool f ∧ ∀ e ∈ L, e.IsBool f := by
  induction L generalizing acc with
  | nil => simp
  | cons e L ih =>
      simp only [List.foldl, ih, isBool_and, List.mem_cons]
      constructor
      · rintro ⟨⟨ha, he⟩, hL⟩
        exact ⟨ha, fun x hx => hx.elim (fun h => h ▸ he) (hL x)⟩
      · rintro ⟨ha, hL⟩
        exact ⟨⟨ha, hL e (Or.inl rfl)⟩, fun x hx => hL x (Or.inr hx)⟩

theorem mem_syms_conj_foldl (L : List Expr) (acc : Expr) (α : Sym) :
    α ∈ (L.foldl .and acc).syms ↔ α ∈ acc.syms ∨ ∃ e ∈ L, α ∈ e.syms := by
  induction L generalizing acc with
  | nil => simp
  | cons e L ih =>
      simp only [List.foldl, ih, syms, List.mem_append, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨x, hx, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨e, Or.inl rfl, h⟩
        · exact Or.inr ⟨x, Or.inr hx, h⟩
      · rintro (h | ⟨x, rfl | hx, h⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨x, hx, h⟩

theorem holds_conj (L : List Expr) (f : Valuation) :
    (Expr.conj L).holds f ↔ ∀ e ∈ L, e.holds f := by
  rw [Expr.conj, holds_conj_foldl]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem isBool_conj (L : List Expr) (f : Valuation) :
    (Expr.conj L).IsBool f ↔ ∀ e ∈ L, e.IsBool f := by
  rw [Expr.conj, isBool_conj_foldl]
  exact ⟨fun h => h.2, fun h => ⟨⟨true, rfl⟩, h⟩⟩

theorem mem_syms_conj (L : List Expr) (α : Sym) :
    α ∈ (Expr.conj L).syms ↔ ∃ e ∈ L, α ∈ e.syms := by
  rw [Expr.conj, mem_syms_conj_foldl]
  simp [tt, syms]

/-! ## Lifting factors out the shared conjuncts (Definition `def:elab-lift`) -/

/-- `C ∧ (⋀A₁ ∨ ⋀A₂)`, where `C = conj(P₁) ∩ conj(P₂)` are the shared
    conjuncts and `A₁ = conj(P₁) ∖ C`, `A₂ = conj(P₂) ∖ C` the rest. -/
def liftPred (P₁ P₂ : Expr) : Expr :=
  let C  := P₁.conjuncts.filter (fun c => decide (c ∈ P₂.conjuncts))
  let A₁ := P₁.conjuncts.filter (fun c => decide (c ∉ P₂.conjuncts))
  let A₂ := P₂.conjuncts.filter (fun c => decide (c ∉ P₁.conjuncts))
  .and (Expr.conj C) (.or (Expr.conj A₁) (Expr.conj A₂))

/-- The factored predicate is equivalent to `P₁ ∨ P₂`. -/
theorem liftPred_holds_iff (P₁ P₂ : Expr) (f : Valuation) :
    (liftPred P₁ P₂).holds f ↔ (Expr.or P₁ P₂).holds f := by
  simp only [liftPred, holds_and, holds_or, holds_conj, isBool_conj, List.mem_filter,
    decide_eq_true_eq, holds_iff_conjuncts P₁, holds_iff_conjuncts P₂,
    isBool_iff_conjuncts P₁, isBool_iff_conjuncts P₂]
  constructor
  · rintro ⟨hC, hB₁, hB₂, hA₁ | hA₂⟩
    · have h₁ : ∀ c ∈ P₁.conjuncts, c.holds f := fun c hc => by
        by_cases h : c ∈ P₂.conjuncts
        · exact hC c ⟨hc, h⟩
        · exact hA₁ c ⟨hc, h⟩
      refine ⟨fun c hc => IsBool.of_holds (h₁ c hc), fun c hc => ?_, Or.inl h₁⟩
      by_cases h : c ∈ P₁.conjuncts
      · exact IsBool.of_holds (hC c ⟨h, hc⟩)
      · exact hB₂ c ⟨hc, h⟩
    · have h₂ : ∀ c ∈ P₂.conjuncts, c.holds f := fun c hc => by
        by_cases h : c ∈ P₁.conjuncts
        · exact hC c ⟨h, hc⟩
        · exact hA₂ c ⟨hc, h⟩
      refine ⟨fun c hc => ?_, fun c hc => IsBool.of_holds (h₂ c hc), Or.inr h₂⟩
      by_cases h : c ∈ P₂.conjuncts
      · exact IsBool.of_holds (hC c ⟨hc, h⟩)
      · exact hB₁ c ⟨hc, h⟩
  · rintro ⟨hB₁, hB₂, h₁ | h₂⟩
    · exact ⟨fun c hc => h₁ c hc.1, fun c hc => hB₁ c hc.1, fun c hc => hB₂ c hc.1,
        Or.inl (fun c hc => h₁ c hc.1)⟩
    · exact ⟨fun c hc => h₂ c hc.2, fun c hc => hB₁ c hc.1, fun c hc => hB₂ c hc.1,
        Or.inr (fun c hc => h₂ c hc.1)⟩

/-- The factored predicate has the symbols of `P₁ ∨ P₂`. -/
theorem mem_syms_liftPred_iff (P₁ P₂ : Expr) (α : Sym) :
    α ∈ (liftPred P₁ P₂).syms ↔ α ∈ (Expr.or P₁ P₂).syms := by
  simp only [liftPred, syms, List.mem_append, mem_syms_conj, List.mem_filter,
    decide_eq_true_eq, mem_syms_iff_conjuncts P₁, mem_syms_iff_conjuncts P₂]
  constructor
  · rintro (⟨c, ⟨hc, -⟩, h⟩ | ⟨c, ⟨hc, -⟩, h⟩ | ⟨c, ⟨hc, -⟩, h⟩)
    · exact Or.inl ⟨c, hc, h⟩
    · exact Or.inl ⟨c, hc, h⟩
    · exact Or.inr ⟨c, hc, h⟩
  · rintro (⟨c, hc, h⟩ | ⟨c, hc, h⟩)
    · by_cases h₂ : c ∈ P₂.conjuncts
      · exact Or.inl ⟨c, ⟨hc, h₂⟩, h⟩
      · exact Or.inr (Or.inl ⟨c, ⟨hc, h₂⟩, h⟩)
    · by_cases h₁ : c ∈ P₁.conjuncts
      · exact Or.inl ⟨c, ⟨h₁, hc⟩, h⟩
      · exact Or.inr (Or.inr ⟨c, ⟨hc, h₁⟩, h⟩)

theorem conjuncts_of_mem {P c : Expr} (h : c ∈ P.conjuncts) : c.conjuncts = [c] := by
  have hna := conjuncts_not_and h
  cases c with
  | and a b => exact absurd rfl (hna a b)
  | _ => rfl

theorem mem_conjuncts_conj_foldl (L : List Expr) (acc c : Expr) :
    c ∈ (L.foldl .and acc).conjuncts ↔ c ∈ acc.conjuncts ∨ ∃ e ∈ L, c ∈ e.conjuncts := by
  induction L generalizing acc with
  | nil => simp
  | cons e L ih =>
      simp only [List.foldl, ih, conjuncts, List.mem_append, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨x, hx, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨e, Or.inl rfl, h⟩
        · exact Or.inr ⟨x, Or.inr hx, h⟩
      · rintro (h | ⟨x, rfl | hx, h⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨x, hx, h⟩

/-- The shared conjuncts stay conjuncts of the factored predicate, available
    to Weakening. -/
theorem conjuncts_liftPred {P₁ P₂ c : Expr} (h₁ : c ∈ P₁.conjuncts) (h₂ : c ∈ P₂.conjuncts) :
    c ∈ (liftPred P₁ P₂).conjuncts := by
  simp only [liftPred, conjuncts, List.mem_append]
  refine Or.inl ((mem_conjuncts_conj_foldl _ _ _).2 (Or.inr ⟨c, ?_, ?_⟩))
  · exact List.mem_filter.2 ⟨h₁, decide_eq_true h₂⟩
  · rw [conjuncts_of_mem h₁]; exact List.mem_singleton_self c

end Expr
