import Smrd.ElabDec.Kleene

/-!
# Bounded arithmetic and its decision oracle

The fragment of the paper's Assumption `a:locations` (Appendix
`s:app-locations`): *terms* are built from symbols, values, `+`, `-`, the
bitwise operators, and multiplication and division by a numeral (division by a
non-zero one) (`Expr.isTerm`); *bounded predicates* are boolean combinations
of `=` and `≤` between terms, of equations between bounded predicates, and of
terms read as booleans (`Expr.isBPred`). The numerals that multiply or divide
are drawn from a list `M`, so that the fragment can be kept closed under
Forwarding (below).

Satisfiability of bounded predicates is decidable (Büchi arithmetic; Bruyère
et al. 1994), which is not mechanised: it enters as an `Oracle`, a Boolean
decision for satisfiability on the fragment with a model-value witness, each
with its correctness proof. Equivalence under a predicate
(`EquivUnder`, `def:sem-equiv`) reduces to satisfiability (`equivUnder_iff`),
and so does the alias query of `≼_alias`.

## Closure under the elaborations

The fragment is closed under renaming symbols (Lifting, `isBPred_rename`),
under the connectives (Strengthening's and Lifting's conjunctions and
disjunctions, `isBPred_conj`, `isBPred_liftPred`, `isBPred_strPred`), under
substituting a value for a symbol (Value Assignment), and under Forwarding's
replacement `g = [val(e₂) ↦ val(e₁)]` (`isBPred_replace`) provided the
replaced expression is not a numeral of `M`.

That proviso is needed. The paper's proof of Lemma `l:loc-decidable` argues
that "`𝒯` is closed under substituting its terms for symbols and
subterms", but for store-store forwarding `val(e₂)` is the expression a
relaxed write writes, which may be a numeral, and `Expr.replace` replaces
every occurrence of it, also where it multiplies: replacing `2` by `β` in
`α * 2 = 4` gives the non-linear `α * β = 4` (`replace_leaves_fragment`).
Condition `NumFwd` (no relaxed write writes a numeral of `M`) excludes it.
-/

namespace Expr

/-- A numeral of `M`. -/
def isNumIn (M : List Nat) : Expr → Bool
  | .val (.num c) => M.contains c
  | _ => false

/-- Terms of bounded arithmetic, multiplying and dividing only by numerals of
    `M`, dividing by non-zero ones. -/
def isTerm (M : List Nat) : Expr → Bool
  | .val _ => true
  | .sym _ => true
  | .bin .mul a b => (isTerm M a && isNumIn M b) || (isNumIn M a && isTerm M b)
  | .bin .div a b => isTerm M a && isNumIn M b && b != .val (.num 0)
  | .bin _ a b => isTerm M a && isTerm M b
  | _ => false

/-- Bounded predicates. -/
def isBPred (M : List Nat) : Expr → Bool
  | .eq a b => (isTerm M a && isTerm M b) || (isBPred M a && isBPred M b)
  | .le a b => isTerm M a && isTerm M b
  | .not a => isBPred M a
  | .and a b => isBPred M a && isBPred M b
  | .or a b => isBPred M a && isBPred M b
  | e => isTerm M e

theorem isNumIn_iff {M : List Nat} {e : Expr} : isNumIn M e = true ↔ ∃ c ∈ M, e = .val (.num c) := by
  constructor
  · intro h
    match e, h with
    | .val (.num c), h => exact ⟨c, by simpa [isNumIn] using h, rfl⟩
  · rintro ⟨c, hc, rfl⟩; simpa [isNumIn] using hc

theorem isTerm_not_conn {M : List Nat} {e : Expr} (h : isTerm M e = true) : e.IsConn = false := by
  cases e <;> simp_all [isTerm, IsConn]

theorem isTerm_isBPred {M : List Nat} {e : Expr} (h : isTerm M e = true) : isBPred M e = true := by
  cases e <;> simp_all [isTerm, isBPred]

theorem replace_numIn {M : List Nat} {b p q : Expr} (hb : isNumIn M b = true)
    (hp : ∀ c ∈ M, p ≠ .val (.num c)) : b.replace p q = b := by
  obtain ⟨c, hc, rfl⟩ := isNumIn_iff.1 hb
  exact replace_val (fun h => hp c hc h.symm)

/-- Terms are closed under replacing a term that is not a numeral of `M` by a
    term. -/
theorem isTerm_replace {M : List Nat} {p q : Expr} (hq : isTerm M q = true)
    (hp : ∀ c ∈ M, p ≠ .val (.num c)) :
    ∀ t : Expr, isTerm M t = true → isTerm M (t.replace p q) = true := by
  intro t
  induction t with
  | val v => intro _; by_cases h : Expr.val v = p
             · rw [replace_eq_self h]; exact hq
             · rw [replace_val h]; rfl
  | sym v => intro _; by_cases h : Expr.sym v = p
             · rw [replace_eq_self h]; exact hq
             · rw [replace_sym h]; rfl
  | bin o a b iha ihb =>
      intro ht
      by_cases h : Expr.bin o a b = p
      · rw [replace_eq_self h]; exact hq
      · rw [replace_bin h]
        cases o with
        | mul =>
            simp only [isTerm, Bool.or_eq_true, Bool.and_eq_true] at ht ⊢
            rcases ht with ⟨ha, hb⟩ | ⟨ha, hb⟩
            · exact Or.inl ⟨iha ha, by rw [replace_numIn hb hp]; exact hb⟩
            · exact Or.inr ⟨by rw [replace_numIn ha hp]; exact ha, ihb hb⟩
        | div =>
            simp only [isTerm, Bool.and_eq_true] at ht ⊢
            obtain ⟨⟨ha, hb⟩, hz⟩ := ht
            rw [replace_numIn hb hp]; exact ⟨⟨iha ha, hb⟩, hz⟩
        | _ =>
            simp only [isTerm, Bool.and_eq_true] at ht ⊢
            exact ⟨iha ht.1, ihb ht.2⟩
  | _ => intro ht; simp [isTerm] at ht

theorem ne_of_isTerm_eq {M : List Nat} {p a b : Expr} (hp : isTerm M p = true) : Expr.eq a b ≠ p := by
  rintro rfl; simp [isTerm] at hp

theorem ne_of_isTerm_le {M : List Nat} {p a b : Expr} (hp : isTerm M p = true) : Expr.le a b ≠ p := by
  rintro rfl; simp [isTerm] at hp

/-- Bounded predicates are closed under Forwarding's replacement of a term
    that is not a numeral of `M` by a term. -/
theorem isBPred_replace {M : List Nat} {p q : Expr} (hpt : isTerm M p = true)
    (hq : isTerm M q = true) (hp : ∀ c ∈ M, p ≠ .val (.num c)) :
    ∀ e : Expr, isBPred M e = true → isBPred M (e.replace p q) = true := by
  have hpc := isTerm_not_conn hpt
  intro e
  induction e with
  | eq a b iha ihb =>
      intro he
      rw [replace_eq (ne_of_isTerm_eq hpt)]
      simp only [isBPred, Bool.or_eq_true, Bool.and_eq_true] at he ⊢
      rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl ⟨isTerm_replace hq hp a ha, isTerm_replace hq hp b hb⟩
      · exact Or.inr ⟨iha ha, ihb hb⟩
  | le a b =>
      intro he
      rw [replace_le (ne_of_isTerm_le hpt)]
      simp only [isBPred, Bool.and_eq_true] at he ⊢
      exact ⟨isTerm_replace hq hp a he.1, isTerm_replace hq hp b he.2⟩
  | not a ih =>
      intro he; rw [replace_not (ne_of_conn rfl hpc)]; exact ih he
  | and a b iha ihb =>
      intro he; rw [replace_and (ne_of_conn rfl hpc)]
      simp only [isBPred, Bool.and_eq_true] at he ⊢; exact ⟨iha he.1, ihb he.2⟩
  | or a b iha ihb =>
      intro he; rw [replace_or (ne_of_conn rfl hpc)]
      simp only [isBPred, Bool.and_eq_true] at he ⊢; exact ⟨iha he.1, ihb he.2⟩
  | val v => intro he; exact isTerm_isBPred (isTerm_replace hq hp _ he)
  | sym v => intro he; exact isTerm_isBPred (isTerm_replace hq hp _ he)
  | bin o a b => intro he; exact isTerm_isBPred (isTerm_replace hq hp _ he)

theorem isNumIn_rename {M : List Nat} (Λ : Sym → Option Sym) (e : Expr) :
    isNumIn M (e.rename Λ) = isNumIn M e := by
  cases e with
  | val v => rfl
  | _ => rfl

theorem isTerm_rename {M : List Nat} (Λ : Sym → Option Sym) :
    ∀ e : Expr, isTerm M (e.rename Λ) = isTerm M e
  | .val _ | .sym _ => rfl
  | .bin o a b => by
      cases o <;> simp only [rename, isTerm, isTerm_rename Λ a, isTerm_rename Λ b, isNumIn_rename]
      cases b with
      | val v => rfl
      | _ => rfl
  | .eq _ _ | .le _ _ | .not _ | .and _ _ | .or _ _ => rfl

theorem isBPred_rename {M : List Nat} (Λ : Sym → Option Sym) :
    ∀ e : Expr, isBPred M (e.rename Λ) = isBPred M e
  | .eq a b => by simp [rename, isBPred, isTerm_rename, isBPred_rename Λ a, isBPred_rename Λ b]
  | .le a b => by simp [rename, isBPred, isTerm_rename]
  | .not a => by simp [rename, isBPred, isBPred_rename Λ a]
  | .and a b | .or a b => by simp [rename, isBPred, isBPred_rename Λ a, isBPred_rename Λ b]
  | .val _ | .sym _ => rfl
  | .bin o a b => by
      show isTerm M ((Expr.bin o a b).rename Λ) = isTerm M (.bin o a b)
      exact isTerm_rename Λ _

theorem isTerm_subst_val {M : List Nat} (α : Sym) (v : Val) :
    ∀ e : Expr, isTerm M e = true → isTerm M (e.subst α (.val v)) = true
  | .val _, h => h
  | .sym β, _ => by simp only [subst]; split <;> rfl
  | .bin o a b, h => by
      have hn : ∀ x, isNumIn M x = true → x.subst α (.val v) = x := fun x hx => by
        obtain ⟨c, _, rfl⟩ := isNumIn_iff.1 hx; rfl
      cases o <;> simp only [isTerm, subst, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
      · exact ⟨isTerm_subst_val α v a h.1, isTerm_subst_val α v b h.2⟩
      · exact ⟨isTerm_subst_val α v a h.1, isTerm_subst_val α v b h.2⟩
      · rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Or.inl ⟨isTerm_subst_val α v a ha, by rw [hn b hb]; exact hb⟩
        · exact Or.inr ⟨by rw [hn a ha]; exact ha, isTerm_subst_val α v b hb⟩
      · rw [hn b h.1.2]; exact ⟨⟨isTerm_subst_val α v a h.1.1, h.1.2⟩, h.2⟩
      · exact ⟨isTerm_subst_val α v a h.1, isTerm_subst_val α v b h.2⟩
      · exact ⟨isTerm_subst_val α v a h.1, isTerm_subst_val α v b h.2⟩
      · exact ⟨isTerm_subst_val α v a h.1, isTerm_subst_val α v b h.2⟩
  | .eq _ _, h | .le _ _, h | .not _, h | .and _ _, h | .or _ _, h => by simp [isTerm] at h

theorem isBPred_conjuncts {M : List Nat} :
    ∀ (P : Expr), isBPred M P = true → ∀ c ∈ P.conjuncts, isBPred M c = true
  | .and a b, h, c, hc => by
      simp only [isBPred, Bool.and_eq_true] at h
      simp only [conjuncts, List.mem_append] at hc
      exact hc.elim (isBPred_conjuncts a h.1 c) (isBPred_conjuncts b h.2 c)
  | .not _, h, c, hc | .or _ _, h, c, hc | .val _, h, c, hc | .sym _, h, c, hc
  | .bin _ _ _, h, c, hc | .eq _ _, h, c, hc | .le _ _, h, c, hc => by
      simp only [conjuncts, List.mem_singleton] at hc; subst hc; exact h

theorem isBPred_foldl {M : List Nat} :
    ∀ (L : List Expr) (acc : Expr), isBPred M acc = true → (∀ e ∈ L, isBPred M e = true) →
      isBPred M (L.foldl .and acc) = true
  | [], _, ha, _ => ha
  | e :: L, acc, ha, hL => isBPred_foldl L _ (by
      simp only [isBPred, Bool.and_eq_true]; exact ⟨ha, hL e (List.mem_cons_self ..)⟩)
      (fun x hx => hL x (List.mem_cons_of_mem _ hx))

theorem isBPred_conj {M : List Nat} {L : List Expr} (h : ∀ e ∈ L, isBPred M e = true) :
    isBPred M (Expr.conj L) = true := isBPred_foldl L _ rfl h

theorem isBPred_liftPred {M : List Nat} {A B : Expr} (hA : isBPred M A = true)
    (hB : isBPred M B = true) : isBPred M (Expr.liftPred A B) = true := by
  simp only [liftPred, isBPred, Bool.and_eq_true]
  refine ⟨isBPred_conj ?_, isBPred_conj ?_, isBPred_conj ?_⟩ <;>
    (intro e he; simp only [List.mem_filter] at he)
  · exact isBPred_conjuncts A hA e he.1
  · exact isBPred_conjuncts A hA e he.1
  · exact isBPred_conjuncts B hB e he.1

end Expr

open Expr

/-- The decision oracle for bounded arithmetic: satisfiability on bounded
    predicates, and, for a satisfiable one, the value one of its models gives
    a symbol. Not mechanised: Büchi arithmetic `⟨ℕ, +, V₂⟩` defines every
    operation of the fragment and has a decidable first-order theory, and its
    models of an existential formula are 2-automatic and so computable. -/
structure Oracle where
  sat : Expr → Bool
  sat_iff : ∀ (M : List Nat) (e : Expr), isBPred M e = true → (sat e = true ↔ Sat e.holds)
  witness : Expr → Sym → Val
  witness_spec : ∀ (M : List Nat) (e : Expr) (α : Sym), isBPred M e = true → Sat e.holds →
    ∃ f, e.holds f ∧ f α = witness e α

theorem holds_not_eq {a b : Expr} {f : Valuation} :
    (Expr.not (.eq a b)).holds f ↔ ∃ v₁ v₂, a.eval f = some v₁ ∧ b.eval f = some v₂ ∧ v₁ ≠ v₂ := by
  simp only [Expr.holds, Expr.eval]
  cases ha : a.eval f with
  | none => simp
  | some v₁ =>
    cases hb : b.eval f with
    | none => simp
    | some v₂ => by_cases h : v₁ = v₂ <;> simp [h]

/-- `a ≡_P b` iff `P ∧ a ≠ b` is unsatisfiable. -/
theorem equivUnder_iff (P : Expr) (a b : Expr) :
    EquivUnder P.holds a b ↔ ¬ Sat (Expr.and P (.not (.eq a b))).holds := by
  constructor
  · rintro h ⟨f, hf⟩
    rw [holds_and] at hf
    obtain ⟨v₁, v₂, h₁, h₂, hne⟩ := holds_not_eq.1 hf.2
    exact hne (h f hf.1 v₁ v₂ h₁ h₂)
  · intro h f hP v₁ v₂ h₁ h₂
    refine Classical.byContradiction fun hne => h ⟨f, (holds_and _ _ f).2 ⟨hP, ?_⟩⟩
    exact holds_not_eq.2 ⟨v₁, v₂, h₁, h₂, hne⟩

namespace Oracle

variable (O : Oracle)

/-- `a ≡_P b`, decided. -/
def equivB (P a b : Expr) : Bool := !O.sat (.and P (.not (.eq a b)))

theorem equivB_iff {M : List Nat} {P a b : Expr} (hP : isBPred M P = true)
    (hab : isBPred M (.eq a b) = true) : O.equivB P a b = true ↔ EquivUnder P.holds a b := by
  have h := O.sat_iff M (.and P (.not (.eq a b))) (by simp [isBPred, hP]; simpa [isBPred] using hab)
  rw [equivUnder_iff, equivB, Bool.not_eq_true', ← h]
  cases O.sat _ <;> simp

/-- Satisfiability of a conjunction. -/
def satAnd (P Q : Expr) : Bool := O.sat (.and P Q)

theorem satAnd_iff {M : List Nat} {P Q : Expr} (hP : isBPred M P = true) (hQ : isBPred M Q = true) :
    O.satAnd P Q = true ↔ Sat (Pred.and P.holds Q.holds) := by
  rw [satAnd, O.sat_iff M _ (by simp [isBPred, hP, hQ])]
  constructor
  · rintro ⟨f, hf⟩; exact ⟨f, (holds_and _ _ f).1 hf⟩
  · rintro ⟨f, hf⟩; exact ⟨f, (holds_and _ _ f).2 hf⟩

end Oracle

/-- An example: a store-store forwarding of `x := 2` from `x := β` replaces the
    multiplier of `α * 2 = 4`, leaving the fragment. -/
theorem replace_leaves_fragment :
    Expr.isBPred [2] (.eq (.bin .mul (.sym 0) (.num 2)) (.num 4)) = true ∧
      ∀ M, Expr.isBPred M ((Expr.eq (.bin .mul (.sym 0) (.num 2)) (.num 4)).replace (.num 2) (.sym 1))
        = false := by
  refine ⟨by decide, fun M => ?_⟩
  simp [Expr.replace, Expr.num, Expr.isBPred, Expr.isTerm, Expr.isNumIn]

namespace EventStructure

variable (es : EventStructure)

/-- `ψ_δ` as an expression: the equations `val(e₁) = val(e₂)` of the
    forwarding edges between events with values. -/
def psiE (δ : FwdCtx) : Expr :=
  Expr.conj (δ.f.filterMap fun p =>
    match es.ev p.1, es.ev p.2 with
    | some e₁, some e₂ =>
        match e₁.val, e₂.val with
        | some v₁, some v₂ => some (.eq v₁ v₂)
        | _, _ => none
    | _, _ => none)

theorem psi_iff (δ : FwdCtx) (g : Valuation) : δ.psi es g ↔ (es.psiE δ).holds g := by
  rw [psiE, holds_conj]
  constructor
  · intro h e he
    obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.1 he
    revert hpe
    cases h₁ : es.ev p.1 with
    | none => simp
    | some e₁ =>
      cases h₂ : es.ev p.2 with
      | none => simp
      | some e₂ =>
        simp only
        cases hv₁ : e₁.val with
        | none => simp
        | some v₁ =>
          cases hv₂ : e₂.val with
          | none => simp
          | some v₂ =>
            simp only [Option.some.injEq]; rintro rfl
            exact h p hp e₁ e₂ v₁ v₂ h₁ h₂ hv₁ hv₂
  · intro h p hp e₁ e₂ v₁ v₂ h₁ h₂ hv₁ hv₂
    apply h
    exact List.mem_filterMap.2 ⟨p, hp, by simp [h₁, h₂, hv₁, hv₂]⟩

theorem isBPred_psiE {M : List Nat} (hv : ∀ e ∈ es.events, ∀ v, e.val = some v → isTerm M v = true)
    (δ : FwdCtx) : isBPred M (es.psiE δ) = true := by
  apply isBPred_conj
  intro e he
  obtain ⟨p, _, hpe⟩ := List.mem_filterMap.1 he
  revert hpe
  cases h₁ : es.ev p.1 with
  | none => simp
  | some e₁ =>
    cases h₂ : es.ev p.2 with
    | none => simp
    | some e₂ =>
      simp only
      cases hv₁ : e₁.val with
      | none => simp
      | some v₁ =>
        cases hv₂ : e₂.val with
        | none => simp
        | some v₂ =>
          simp only [Option.some.injEq]; rintro rfl
          have m₁ : e₁ ∈ es.events := List.mem_of_find?_eq_some h₁
          have m₂ : e₂ ∈ es.events := List.mem_of_find?_eq_some h₂
          simp [isBPred, hv e₁ m₁ v₁ hv₁, hv e₂ m₂ v₂ hv₂]

end EventStructure
