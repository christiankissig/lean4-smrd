import Smrd.Justifications

/-!
# Predicates over their atoms

The finiteness and decidability results of `Smrd.ElabDec` read a predicate as
a boolean combination of its *atoms*: the maximal subexpressions not headed by
`¬`, `∧` or `∨` (`Expr.atoms`). Evaluation is strict in every operand
(`Expr.eval`), so a predicate denotes a boolean exactly where all its atoms do,
and its value is the strict three-valued (Kleene) combination of theirs
(`Expr.kval`, `Expr.toB_eval`).

Two predicates are *propositionally equivalent*, `PEq`, when they agree under
every assignment of `none`/`some true`/`some false` to atoms. This is finer
than semantic equivalence and does not need a decision procedure for the
underlying arithmetic: it is decided by enumerating the assignments to the
atoms of both sides (`PEq.decide_iff`). It is preserved by what the
elaborations do to predicates -- subexpression replacement and renaming of
atoms (`PEq.replace`, `PEq.rename`), conjunction with the same set of conjuncts
(`kval_conj_congr`), and Lifting's factoring (`kval_liftPred`) -- and fixes the
atoms, the symbols and the denotation (`PEq.mem_atoms`, `PEq.mem_syms`,
`PEq.holds_iff`).

The module also collects the list tools the finiteness argument uses:
expression size and value leaves, the expressions of bounded size over finite
alphabets (`allExprs`), assignments (`allFuns`), sublists (`subs`), lists of
bounded length (`allLists`), and the pigeonhole principle for duplicate-free
lists (`length_le_of_nodup_subset`).
-/

namespace Smrd.ElabDec

/-! ## List tools -/

/-- A duplicate-free list inside `L` is no longer than `L`. -/
theorem length_le_of_nodup_subset {α : Type} [DecidableEq α] :
    ∀ {l L : List α}, l.Nodup → (∀ x ∈ l, x ∈ L) → l.length ≤ L.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, L, hn, hs => by
      have ha : a ∈ L := hs a (List.mem_cons_self ..)
      have hn' := List.nodup_cons.1 hn
      have ih := length_le_of_nodup_subset (l := l) (L := L.erase a) hn'.2 (fun x hx => by
        have hne : x ≠ a := fun h => hn'.1 (h ▸ hx)
        exact (List.mem_erase_of_ne hne).2 (hs x (List.mem_cons_of_mem _ hx)))
      rw [List.length_erase_of_mem ha] at ih
      have : 0 < L.length := List.length_pos_of_mem ha
      simp only [List.length_cons]; omega

/-- If the images under `g` of a list are pairwise distinct and lie in `L`,
    the list is no longer than `L`. -/
theorem length_le_of_map_nodup {α β : Type} [DecidableEq β] {l : List α} {L : List β}
    (g : α → β) (hn : (l.map g).Nodup) (hs : ∀ x ∈ l, g x ∈ L) : l.length ≤ L.length := by
  have := length_le_of_nodup_subset hn (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy; exact hs x hx)
  simpa using this

/-- The sublists of a list, keeping the order. -/
def subs {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: l => subs l ++ (subs l).map (a :: ·)

theorem filter_mem_subs {α : Type} (p : α → Bool) : ∀ l : List α, l.filter p ∈ subs l
  | [] => by simp [subs]
  | a :: l => by
      simp only [List.filter, subs, List.mem_append, List.mem_map]
      cases p a
      · exact Or.inl (filter_mem_subs p l)
      · exact Or.inr ⟨_, filter_mem_subs p l, rfl⟩

theorem mem_of_mem_subs {α : Type} : ∀ {l s : List α}, s ∈ subs l → ∀ x ∈ s, x ∈ l
  | [], s, h, x, hx => by simp [subs] at h; subst h; cases hx
  | a :: l, s, h, x, hx => by
      simp only [subs, List.mem_append, List.mem_map] at h
      rcases h with h | ⟨t, ht, rfl⟩
      · exact List.mem_cons_of_mem _ (mem_of_mem_subs h x hx)
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (mem_of_mem_subs ht x hx)

/-- All assignments of values from `vs` to the elements of `dom`, as
    association lists in the order of `dom`. -/
def allFuns {α β : Type} (dom : List α) (vs : List β) : List (List (α × β)) :=
  dom.foldr (fun a acc => vs.flatMap fun v => acc.map ((a, v) :: ·)) [[]]

theorem map_mem_allFuns {α β : Type} (vs : List β) (g : α → β) :
    ∀ dom : List α, (∀ a ∈ dom, g a ∈ vs) → dom.map (fun a => (a, g a)) ∈ allFuns dom vs
  | [], _ => by simp [allFuns]
  | a :: dom, h => by
      simp only [allFuns, List.foldr_cons, List.map_cons, List.mem_flatMap, List.mem_map]
      exact ⟨g a, h a (List.mem_cons_self ..), _,
        map_mem_allFuns vs g dom (fun b hb => h b (List.mem_cons_of_mem _ hb)), rfl⟩

theorem lookup_map_self {α β : Type} [DecidableEq α] (g : α → β) :
    ∀ (dom : List α) (a : α), a ∈ dom → (dom.map (fun a => (a, g a))).lookup a = some (g a)
  | [], _, h => by cases h
  | b :: dom, a, h => by
      simp only [List.map_cons, List.lookup_cons]
      by_cases hab : a = b
      · subst hab; simp
      · have : (a == b) = false := by simpa using hab
        rw [this]
        exact lookup_map_self g dom a ((List.mem_cons.1 h).resolve_left hab)

theorem lookup_mem_of_mem_allFuns {α β : Type} [DecidableEq α] {vs : List β} :
    ∀ {dom : List α} {l : List (α × β)}, l ∈ allFuns dom vs →
      ∀ a v, l.lookup a = some v → a ∈ dom ∧ v ∈ vs
  | [], l, hl, a, v, h => by simp [allFuns] at hl; subst hl; simp at h
  | b :: dom, l, hl, a, v, h => by
      simp only [allFuns, List.foldr_cons, List.mem_flatMap, List.mem_map] at hl
      obtain ⟨w, hw, l', hl', rfl⟩ := hl
      simp only [List.lookup_cons] at h
      by_cases hab : a = b
      · subst hab; simp at h; subst h; exact ⟨List.mem_cons_self .., hw⟩
      · have : (a == b) = false := by simpa using hab
        rw [this] at h
        have := lookup_mem_of_mem_allFuns hl' a v h
        exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

/-- Lists of length `n` over `vs`. -/
def allLists {β : Type} (vs : List β) : Nat → List (List β)
  | 0 => [[]]
  | n + 1 => vs.flatMap fun v => (allLists vs n).map (v :: ·)

theorem mem_allLists {β : Type} {vs : List β} :
    ∀ (l : List β), (∀ x ∈ l, x ∈ vs) → l ∈ allLists vs l.length
  | [], _ => by simp [allLists]
  | a :: l, h => by
      simp only [List.length_cons, allLists, List.mem_flatMap, List.mem_map]
      exact ⟨a, h a (List.mem_cons_self ..), l,
        mem_allLists l (fun x hx => h x (List.mem_cons_of_mem _ hx)), rfl⟩

/-- Lists of length at most `n` over `vs`. -/
def allListsUpTo {β : Type} (vs : List β) (n : Nat) : List (List β) :=
  (List.range (n + 1)).flatMap (allLists vs)

theorem mem_allListsUpTo {β : Type} {vs : List β} {n : Nat} {l : List β}
    (h : ∀ x ∈ l, x ∈ vs) (hn : l.length ≤ n) : l ∈ allListsUpTo vs n :=
  List.mem_flatMap.2 ⟨l.length, List.mem_range.2 (by omega), mem_allLists l h⟩

end Smrd.ElabDec

namespace Expr

open Smrd.ElabDec

/-! ## Atoms and the three-valued reading -/

/-- `e` is headed by a connective `¬`, `∧`, `∨`. -/
def IsConn : Expr → Bool
  | .not _ | .and _ _ | .or _ _ => true
  | _ => false

/-- The atoms of a predicate: its maximal subexpressions not headed by a
    connective, with repetitions. -/
def atoms : Expr → List Expr
  | .not a => a.atoms
  | .and a b => a.atoms ++ b.atoms
  | .or a b => a.atoms ++ b.atoms
  | e => [e]

theorem atoms_of_not_conn {e : Expr} (h : e.IsConn = false) : e.atoms = [e] := by
  cases e <;> simp_all [IsConn, atoms]

theorem not_conn_of_mem_atoms {e a : Expr} (h : a ∈ e.atoms) : a.IsConn = false := by
  induction e with
  | not x ih => exact ih h
  | and x y ihx ihy | or x y ihx ihy =>
      simp only [atoms, List.mem_append] at h; exact h.elim ihx ihy
  | _ => simp only [atoms, List.mem_singleton] at h; subst h; rfl

/-- Strict three-valued conjunction, disjunction and negation. -/
def kAnd : Option Bool → Option Bool → Option Bool
  | some x, some y => some (x && y)
  | _, _ => none

def kOr : Option Bool → Option Bool → Option Bool
  | some x, some y => some (x || y)
  | _, _ => none

def kNot : Option Bool → Option Bool
  | some x => some (!x)
  | none => none

/-- The value of a predicate under an assignment `ρ` of three-valued truth
    values to its atoms. -/
def kval (ρ : Expr → Option Bool) : Expr → Option Bool
  | .not a => kNot (kval ρ a)
  | .and a b => kAnd (kval ρ a) (kval ρ b)
  | .or a b => kOr (kval ρ a) (kval ρ b)
  | e => ρ e

theorem kval_atom {ρ : Expr → Option Bool} {e : Expr} (h : e.IsConn = false) :
    kval ρ e = ρ e := by
  cases e <;> simp_all [IsConn, kval]

/-- A value read as a three-valued truth value. -/
def toB : Option Val → Option Bool
  | some (.bool b) => some b
  | _ => none

/-- The assignment of truth values to atoms given by a valuation. -/
def atomVal (f : Valuation) (a : Expr) : Option Bool := toB (a.eval f)

/-- Evaluation is the three-valued combination of the atoms' values. -/
theorem toB_eval (f : Valuation) (e : Expr) : toB (e.eval f) = kval (atomVal f) e := by
  induction e with
  | not a ih =>
      rw [kval, ← ih]; simp only [eval]
      cases h : a.eval f with
      | none => rfl
      | some v => cases v <;> rfl
  | and a b iha ihb | or a b iha ihb =>
      rw [kval, ← iha, ← ihb]; simp only [eval]
      cases ha : a.eval f with
      | none => cases b.eval f <;> rfl
      | some va =>
        cases hb : b.eval f with
        | none => cases va <;> rfl
        | some vb => cases va <;> cases vb <;> rfl
  | _ => rfl

theorem holds_iff_kval (e : Expr) (f : Valuation) :
    e.holds f ↔ kval (atomVal f) e = some true := by
  rw [← toB_eval, holds]
  cases h : e.eval f with
  | none => simp [toB]
  | some v => cases v <;> simp [toB]

theorem kval_congr {ρ σ : Expr → Option Bool} :
    ∀ (e : Expr), (∀ a ∈ e.atoms, ρ a = σ a) → kval ρ e = kval σ e
  | .not a, h => by rw [kval, kval, kval_congr a h]
  | .and a b, h => by
      simp only [atoms, List.mem_append] at h
      rw [kval, kval, kval_congr a (fun x hx => h x (Or.inl hx)),
        kval_congr b (fun x hx => h x (Or.inr hx))]
  | .or a b, h => by
      simp only [atoms, List.mem_append] at h
      rw [kval, kval, kval_congr a (fun x hx => h x (Or.inl hx)),
        kval_congr b (fun x hx => h x (Or.inr hx))]
  | .val v, h | .sym v, h => h _ (List.mem_singleton_self _)
  | .bin o x y, h | .eq x y, h | .le x y, h => h _ (List.mem_singleton_self _)

/-- Strictness: a predicate with an undefined atom is undefined. -/
theorem kval_eq_none {ρ : Expr → Option Bool} :
    ∀ (e : Expr) (a : Expr), a ∈ e.atoms → ρ a = none → kval ρ e = none
  | .not x, a, h, hn => by rw [kval, kval_eq_none x a h hn]; rfl
  | .and x y, a, h, hn => by
      simp only [atoms, List.mem_append] at h
      rw [kval]; rcases h with h | h
      · rw [kval_eq_none x a h hn]; rfl
      · rw [kval_eq_none y a h hn]; cases kval ρ x <;> rfl
  | .or x y, a, h, hn => by
      simp only [atoms, List.mem_append] at h
      rw [kval]; rcases h with h | h
      · rw [kval_eq_none x a h hn]; rfl
      · rw [kval_eq_none y a h hn]; cases kval ρ x <;> rfl
  | .val _, a, h, hn | .sym _, a, h, hn | .bin _ _ _, a, h, hn | .eq _ _, a, h, hn
  | .le _ _, a, h, hn => by simp only [atoms, List.mem_singleton] at h; subst h; exact hn

/-- A predicate whose atoms are all defined is defined. -/
theorem kval_isSome {ρ : Expr → Option Bool} :
    ∀ (e : Expr), (∀ a ∈ e.atoms, (ρ a).isSome) → (kval ρ e).isSome
  | .not x, h => by
      rw [kval]; have := kval_isSome x h
      cases hx : kval ρ x <;> simp_all [kNot]
  | .and x y, h => by
      simp only [atoms, List.mem_append] at h
      have hx := kval_isSome x (fun a ha => h a (Or.inl ha))
      have hy := kval_isSome y (fun a ha => h a (Or.inr ha))
      rw [kval]; cases h1 : kval ρ x <;> cases h2 : kval ρ y <;> simp_all [kAnd]
  | .or x y, h => by
      simp only [atoms, List.mem_append] at h
      have hx := kval_isSome x (fun a ha => h a (Or.inl ha))
      have hy := kval_isSome y (fun a ha => h a (Or.inr ha))
      rw [kval]; cases h1 : kval ρ x <;> cases h2 : kval ρ y <;> simp_all [kOr]
  | .val _, h | .sym _, h | .bin _ _ _, h | .eq _ _, h | .le _ _, h =>
      h _ (List.mem_singleton_self _)

theorem mem_syms_iff_atoms (e : Expr) (α : Sym) :
    α ∈ e.syms ↔ ∃ a ∈ e.atoms, α ∈ a.syms := by
  induction e with
  | not x ih => exact ih
  | and x y ihx ihy | or x y ihx ihy =>
      simp only [syms, atoms, List.mem_append, ihx, ihy]
      constructor
      · rintro (⟨a, ha, h⟩ | ⟨a, ha, h⟩)
        · exact ⟨a, Or.inl ha, h⟩
        · exact ⟨a, Or.inr ha, h⟩
      · rintro ⟨a, ha | ha, h⟩
        · exact Or.inl ⟨a, ha, h⟩
        · exact Or.inr ⟨a, ha, h⟩
  | _ => simp [atoms]

/-! ## Propositional equivalence -/

/-- Propositional equivalence: equal three-valued values under every
    assignment to atoms. -/
def PEq (P Q : Expr) : Prop := ∀ ρ, kval ρ P = kval ρ Q

theorem PEq.refl (P : Expr) : PEq P P := fun _ => rfl
theorem PEq.symm {P Q : Expr} (h : PEq P Q) : PEq Q P := fun ρ => (h ρ).symm
theorem PEq.trans {P Q R : Expr} (h₁ : PEq P Q) (h₂ : PEq Q R) : PEq P R :=
  fun ρ => (h₁ ρ).trans (h₂ ρ)

/-- Propositionally equivalent predicates have the same atoms. -/
theorem PEq.mem_atoms {P Q : Expr} (h : PEq P Q) {a : Expr} (ha : a ∈ P.atoms) : a ∈ Q.atoms := by
  classical
  refine Classical.byContradiction fun hq => ?_
  let ρ : Expr → Option Bool := fun b => if b = a then none else some true
  have h1 : kval ρ P = none := kval_eq_none P a ha (by simp [ρ])
  have h2 : (kval ρ Q).isSome := kval_isSome Q (fun b hb => by
    have : b ≠ a := fun e => hq (e ▸ hb)
    simp [ρ, this])
  rw [← h ρ, h1] at h2; cases h2

theorem PEq.mem_syms {P Q : Expr} (h : PEq P Q) {α : Sym} (hα : α ∈ P.syms) : α ∈ Q.syms := by
  rw [mem_syms_iff_atoms] at hα ⊢
  obtain ⟨a, ha, h'⟩ := hα
  exact ⟨a, h.mem_atoms ha, h'⟩

theorem PEq.holds_iff {P Q : Expr} (h : PEq P Q) (f : Valuation) : P.holds f ↔ Q.holds f := by
  rw [holds_iff_kval, holds_iff_kval, h]

/-- The assignment read off an association list, `none` off it. -/
def assignOf (l : List (Expr × Option Bool)) (a : Expr) : Option Bool := (l.lookup a).getD none

/-- The three truth values. -/
def tvals : List (Option Bool) := [none, some true, some false]

theorem mem_tvals (v : Option Bool) : v ∈ tvals := by
  rcases v with _ | _ | _ <;> simp [tvals]

/-- `PEq`, decided by enumerating the assignments to the atoms of both sides. -/
def peqB (P Q : Expr) : Bool :=
  (allFuns (P.atoms ++ Q.atoms) tvals).all fun l => kval (assignOf l) P == kval (assignOf l) Q

theorem peqB_iff (P Q : Expr) : peqB P Q = true ↔ PEq P Q := by
  constructor
  · intro h ρ
    let dom := P.atoms ++ Q.atoms
    have hl := map_mem_allFuns tvals ρ dom (fun a _ => mem_tvals _)
    have h' := (List.all_eq_true.1 h) _ hl
    have hag : ∀ a ∈ dom, assignOf (dom.map fun a => (a, ρ a)) a = ρ a := fun a ha => by
      simp [assignOf, lookup_map_self ρ dom a ha]
    rw [kval_congr P (fun a ha => (hag a (List.mem_append_left _ ha)).symm),
      kval_congr Q (fun a ha => (hag a (List.mem_append_right _ ha)).symm)]
    simpa using h'
  · intro h; exact List.all_eq_true.2 (fun l _ => by simp [h (assignOf l)])

instance (P Q : Expr) : Decidable (PEq P Q) := decidable_of_iff _ (peqB_iff P Q)

/-! ## Replacement and renaming act on atoms -/

theorem replace_eq_self {e p q : Expr} (h : e = p) : e.replace p q = q := by
  rw [Expr.replace.eq_def, if_pos h]

theorem replace_not {a p q : Expr} (h : Expr.not a ≠ p) :
    (Expr.not a).replace p q = .not (a.replace p q) := by
  rw [Expr.replace.eq_def, if_neg h]

theorem replace_and {a b p q : Expr} (h : Expr.and a b ≠ p) :
    (Expr.and a b).replace p q = .and (a.replace p q) (b.replace p q) := by
  rw [Expr.replace.eq_def, if_neg h]

theorem replace_or {a b p q : Expr} (h : Expr.or a b ≠ p) :
    (Expr.or a b).replace p q = .or (a.replace p q) (b.replace p q) := by
  rw [Expr.replace.eq_def, if_neg h]

theorem replace_bin {o : ArithOp} {a b p q : Expr} (h : Expr.bin o a b ≠ p) :
    (Expr.bin o a b).replace p q = .bin o (a.replace p q) (b.replace p q) := by
  rw [Expr.replace.eq_def, if_neg h]

theorem replace_eq {a b p q : Expr} (h : Expr.eq a b ≠ p) :
    (Expr.eq a b).replace p q = .eq (a.replace p q) (b.replace p q) := by
  rw [Expr.replace.eq_def, if_neg h]

theorem replace_le {a b p q : Expr} (h : Expr.le a b ≠ p) :
    (Expr.le a b).replace p q = .le (a.replace p q) (b.replace p q) := by
  rw [Expr.replace.eq_def, if_neg h]

theorem replace_val {v : Val} {p q : Expr} (h : Expr.val v ≠ p) :
    (Expr.val v).replace p q = .val v := by
  rw [Expr.replace.eq_def, if_neg h]

theorem replace_sym {β : Sym} {p q : Expr} (h : Expr.sym β ≠ p) :
    (Expr.sym β).replace p q = .sym β := by
  rw [Expr.replace.eq_def, if_neg h]

/-- Replacement keeps an expression not headed by a connective so, when the
    replacing expression is not. -/
theorem replace_not_conn {e p q : Expr} (he : e.IsConn = false) (hq : q.IsConn = false) :
    (e.replace p q).IsConn = false := by
  by_cases h : e = p
  · rw [replace_eq_self h]; exact hq
  · cases e with
    | not _ | and _ _ | or _ _ => simp [IsConn] at he
    | val v => rw [replace_val h]; rfl
    | sym v => rw [replace_sym h]; rfl
    | bin o a b => rw [replace_bin h]; rfl
    | eq a b => rw [replace_eq h]; rfl
    | le a b => rw [replace_le h]; rfl

theorem ne_of_conn {e p : Expr} (he : e.IsConn = true) (hp : p.IsConn = false) : e ≠ p := by
  rintro rfl; rw [he] at hp; cases hp

theorem kval_replace {p q : Expr} (hp : p.IsConn = false) (hq : q.IsConn = false)
    (ρ : Expr → Option Bool) :
    ∀ e : Expr, kval ρ (e.replace p q) = kval (fun a => ρ (a.replace p q)) e
  | .not a => by
      rw [replace_not (ne_of_conn rfl hp), kval, kval, kval_replace hp hq ρ a]
  | .and a b => by
      rw [replace_and (ne_of_conn rfl hp), kval, kval, kval_replace hp hq ρ a,
        kval_replace hp hq ρ b]
  | .or a b => by
      rw [replace_or (ne_of_conn rfl hp), kval, kval, kval_replace hp hq ρ a,
        kval_replace hp hq ρ b]
  | .val v => by rw [kval_atom (replace_not_conn rfl hq)]; rfl
  | .sym v => by rw [kval_atom (replace_not_conn rfl hq)]; rfl
  | .bin o a b => by rw [kval_atom (replace_not_conn rfl hq)]; rfl
  | .eq a b => by rw [kval_atom (replace_not_conn rfl hq)]; rfl
  | .le a b => by rw [kval_atom (replace_not_conn rfl hq)]; rfl

theorem atoms_replace {p q : Expr} (hp : p.IsConn = false) (hq : q.IsConn = false) :
    ∀ e : Expr, (e.replace p q).atoms = e.atoms.map (·.replace p q)
  | .not a => by rw [replace_not (ne_of_conn rfl hp)]; exact atoms_replace hp hq a
  | .and a b => by
      rw [replace_and (ne_of_conn rfl hp)]
      simp only [atoms, List.map_append, atoms_replace hp hq a, atoms_replace hp hq b]
  | .or a b => by
      rw [replace_or (ne_of_conn rfl hp)]
      simp only [atoms, List.map_append, atoms_replace hp hq a, atoms_replace hp hq b]
  | .val v => by rw [atoms_of_not_conn (replace_not_conn rfl hq)]; rfl
  | .sym v => by rw [atoms_of_not_conn (replace_not_conn rfl hq)]; rfl
  | .bin o a b => by rw [atoms_of_not_conn (replace_not_conn rfl hq)]; rfl
  | .eq a b => by rw [atoms_of_not_conn (replace_not_conn rfl hq)]; rfl
  | .le a b => by rw [atoms_of_not_conn (replace_not_conn rfl hq)]; rfl

theorem PEq.replace {P P' p q : Expr} (hp : p.IsConn = false) (hq : q.IsConn = false)
    (h : PEq P P') : PEq (P.replace p q) (P'.replace p q) := fun ρ => by
  rw [kval_replace hp hq, kval_replace hp hq]; exact h _

theorem kval_rename (Λ : Sym → Option Sym) (ρ : Expr → Option Bool) :
    ∀ e : Expr, kval ρ (e.rename Λ) = kval (fun a => ρ (a.rename Λ)) e
  | .not a => by rw [rename, kval, kval, kval_rename Λ ρ a]
  | .and a b => by rw [rename, kval, kval, kval_rename Λ ρ a, kval_rename Λ ρ b]
  | .or a b => by rw [rename, kval, kval, kval_rename Λ ρ a, kval_rename Λ ρ b]
  | .val _ | .sym _ | .bin _ _ _ | .eq _ _ | .le _ _ => rfl

theorem atoms_rename (Λ : Sym → Option Sym) :
    ∀ e : Expr, (e.rename Λ).atoms = e.atoms.map (·.rename Λ)
  | .not a => atoms_rename Λ a
  | .and a b | .or a b => by
      simp only [rename, atoms, List.map_append, atoms_rename Λ a, atoms_rename Λ b]
  | .val _ | .sym _ | .bin _ _ _ | .eq _ _ | .le _ _ => rfl

theorem PEq.rename {P P' : Expr} (Λ : Sym → Option Sym) (h : PEq P P') :
    PEq (P.rename Λ) (P'.rename Λ) := fun ρ => by
  rw [kval_rename, kval_rename]; exact h _

/-! ## Conjunctions -/

/-- The strict conjunction of a list of truth values. -/
def kAll (l : List (Option Bool)) : Option Bool :=
  if none ∈ l then none else some (l.all (· == some true))

theorem kAll_congr {l m : List (Option Bool)} (h : ∀ v, v ∈ l ↔ v ∈ m) : kAll l = kAll m := by
  unfold kAll
  have hall : l.all (· == some true) = m.all (· == some true) := by
    apply Bool.eq_iff_iff.2
    simp only [List.all_eq_true, h]
  rw [hall]; simp only [h]

theorem kAll_cons (v : Option Bool) (l : List (Option Bool)) :
    kAll (v :: l) = kAnd v (kAll l) := by
  unfold kAll
  rcases v with _ | b
  · simp [kAnd]
  · by_cases hn : none ∈ l
    · simp [hn, kAnd]
    · simp [hn, kAnd]

theorem kAll_append (l m : List (Option Bool)) : kAll (l ++ m) = kAnd (kAll l) (kAll m) := by
  induction l with
  | nil =>
      unfold kAll; simp only [List.nil_append, List.not_mem_nil, if_false, List.all_nil]
      cases h : (if none ∈ m then none else some (m.all (· == some true))) with
      | none => rfl
      | some b => simp [kAnd]
  | cons v l ih =>
      rw [List.cons_append, kAll_cons, kAll_cons, ih]
      rcases v with _ | x <;> rcases kAll l with _ | y <;> rcases kAll m with _ | z <;>
        simp [kAnd, Bool.and_assoc]

theorem kAll_singleton (v : Option Bool) : kAll [v] = v := by
  rcases v with _ | b <;> simp [kAll]

theorem kval_foldl_and (ρ : Expr → Option Bool) :
    ∀ (L : List Expr) (acc : Expr),
      kval ρ (L.foldl .and acc) = kAll ((acc :: L).map (kval ρ))
  | [], acc => by simp [kAll_singleton]
  | e :: L, acc => by
      rw [List.foldl_cons, kval_foldl_and ρ L, List.map_cons, List.map_cons, kval, kAll_cons,
        kAll_cons, List.map_cons, kAll_cons]
      rcases kval ρ acc with _ | x <;> rcases kval ρ e with _ | y <;>
        rcases kAll (L.map (kval ρ)) with _ | z <;> simp [kAnd, Bool.and_assoc]

theorem kval_conj (ρ : Expr → Option Bool) (L : List Expr) :
    kval ρ (Expr.conj L) = kAll (ρ Expr.tt :: L.map (kval ρ)) := by
  rw [Expr.conj, kval_foldl_and, List.map_cons]; rfl

/-- A predicate is the strict conjunction of its conjuncts. -/
theorem kval_conjuncts (ρ : Expr → Option Bool) :
    ∀ P : Expr, kval ρ P = kAll (P.conjuncts.map (kval ρ))
  | .and a b => by rw [kval, conjuncts, List.map_append, kAll_append, ← kval_conjuncts ρ a,
      ← kval_conjuncts ρ b]
  | .not _ | .or _ _ | .val _ | .sym _ | .bin _ _ _ | .eq _ _ | .le _ _ => by
      simp [conjuncts, kAll_singleton]

/-- Conjunctions of lists with the same members are propositionally
    equivalent. -/
theorem kval_conj_congr {L M : List Expr} (h : ∀ e, e ∈ L ↔ e ∈ M) (ρ : Expr → Option Bool) :
    kval ρ (Expr.conj L) = kval ρ (Expr.conj M) := by
  rw [kval_conj, kval_conj]
  apply kAll_congr
  intro v; simp only [List.mem_cons, List.mem_map, h]

theorem kAll_eq_none_iff (l : List (Option Bool)) : kAll l = none ↔ none ∈ l := by
  unfold kAll; split <;> simp_all

theorem kAll_eq_some_iff (l : List (Option Bool)) (b : Bool) :
    kAll l = some b ↔ none ∉ l ∧ (b = true ↔ ∀ v ∈ l, v = some true) := by
  unfold kAll
  split
  · simp_all
  · rename_i hn
    simp only [Option.some.injEq, hn, not_false_eq_true, true_and]
    constructor
    · rintro rfl; simp [List.all_eq_true]
    · intro h
      cases b
      · cases hb : l.all (· == some true)
        · rfl
        · exact absurd (h.2 (by simpa [List.all_eq_true] using hb)) (by simp)
      · simpa [List.all_eq_true] using h.1 rfl

private theorem kAll_split {ρ : Expr → Option Bool} {L C A₁ : List Expr}
    (h : ∀ c, c ∈ L ↔ c ∈ C ∨ c ∈ A₁) :
    kAll (L.map (kval ρ)) = kAnd (kAll (C.map (kval ρ))) (kAll (A₁.map (kval ρ))) := by
  rw [← kAll_append]
  apply kAll_congr
  intro v; simp only [List.mem_map, List.mem_append]
  constructor
  · rintro ⟨c, hc, rfl⟩; rcases (h c).1 hc with h' | h'
    · exact Or.inl ⟨c, h', rfl⟩
    · exact Or.inr ⟨c, h', rfl⟩
  · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    · exact ⟨c, (h c).2 (Or.inl hc), rfl⟩
    · exact ⟨c, (h c).2 (Or.inr hc), rfl⟩

/-- Lifting's factored predicate, read three-valued: `⊤ ∧ (P₁ ∨ P₂)`, with
    the `⊤` of the empty conjunctions as an atom. -/
theorem kval_liftPred (ρ : Expr → Option Bool) (A B : Expr) :
    kval ρ (Expr.liftPred A B) = kAnd (ρ Expr.tt) (kOr (kval ρ A) (kval ρ B)) := by
  classical
  simp only [liftPred, kval, kval_conj]
  rw [kval_conjuncts ρ A, kval_conjuncts ρ B]
  rw [kAll_split (C := A.conjuncts.filter (fun c => decide (c ∈ B.conjuncts)))
      (A₁ := A.conjuncts.filter (fun c => decide (c ∉ B.conjuncts))) (fun c => by
        simp only [List.mem_filter, decide_eq_true_eq]
        by_cases h : c ∈ B.conjuncts <;> simp [h]),
    kAll_split (L := B.conjuncts) (C := A.conjuncts.filter (fun c => decide (c ∈ B.conjuncts)))
      (A₁ := B.conjuncts.filter (fun c => decide (c ∉ A.conjuncts))) (fun c => by
        simp only [List.mem_filter, decide_eq_true_eq]
        by_cases h : c ∈ A.conjuncts <;> by_cases h' : c ∈ B.conjuncts <;> simp [h, h']),
    kAll_cons, kAll_cons, kAll_cons]
  generalize ρ Expr.tt = t
  generalize kAll (List.map (kval ρ) (List.filter (fun c => decide (c ∈ B.conjuncts)) A.conjuncts)) = c
  generalize kAll (List.map (kval ρ) (List.filter (fun c => decide ¬c ∈ B.conjuncts) A.conjuncts)) = a
  generalize kAll (List.map (kval ρ) (List.filter (fun c => decide ¬c ∈ A.conjuncts) B.conjuncts)) = b
  rcases t with _ | t <;> rcases c with _ | c <;> rcases a with _ | a <;> rcases b with _ | b <;>
    simp [kAnd, kOr] <;> cases t <;> cases c <;> cases a <;> cases b <;> rfl

theorem PEq.liftPred {A A' B B' : Expr} (hA : PEq A A') (hB : PEq B B') :
    PEq (Expr.liftPred A B) (Expr.liftPred A' B') := fun ρ => by
  rw [kval_liftPred, kval_liftPred, hA ρ, hB ρ]

theorem PEq.and {A A' B B' : Expr} (hA : PEq A A') (hB : PEq B B') :
    PEq (Expr.and A B) (Expr.and A' B') := fun ρ => by
  rw [kval, kval, hA ρ, hB ρ]

/-! ## Size, value leaves, and expressions of bounded size -/

def size : Expr → Nat
  | .val _ | .sym _ => 1
  | .bin _ a b | .eq a b | .le a b | .and a b | .or a b => a.size + b.size + 1
  | .not a => a.size + 1

/-- The values occurring in an expression. -/
def vals : Expr → List Val
  | .val v => [v]
  | .sym _ => []
  | .bin _ a b | .eq a b | .le a b | .and a b | .or a b => a.vals ++ b.vals
  | .not a => a.vals

theorem size_pos (e : Expr) : 1 ≤ e.size := by cases e <;> simp [size] <;> omega

private theorem mul_bound {a b s a' b' : Nat} (hs : 1 ≤ s) (ha : a' ≤ a * s) (hb : b' ≤ b * s) :
    a' + b' + 1 ≤ (a + b + 1) * s := by
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
  generalize a * s = x at *; generalize b * s = y at *; omega

private theorem mul_bound1 {a s a' : Nat} (hs : 1 ≤ s) (ha : a' ≤ a * s) :
    a' + 1 ≤ (a + 1) * s := by
  rw [Nat.add_mul, Nat.one_mul]; generalize a * s = x at *; omega

theorem size_replace (p q : Expr) : ∀ e : Expr, (e.replace p q).size ≤ e.size * q.size := by
  intro e
  induction e with
  | val v =>
      by_cases h : Expr.val v = p
      · rw [replace_eq_self h]; simp [size]
      · rw [replace_val h]; simp only [size]; exact Nat.le_mul_of_pos_right _ (size_pos q)
  | sym v =>
      by_cases h : Expr.sym v = p
      · rw [replace_eq_self h]; simp [size]
      · rw [replace_sym h]; simp only [size]; exact Nat.le_mul_of_pos_right _ (size_pos q)
  | bin o a b iha ihb =>
      by_cases h : Expr.bin o a b = p
      · rw [replace_eq_self h]; exact Nat.le_mul_of_pos_left _ (size_pos _)
      · rw [replace_bin h]; exact mul_bound (size_pos q) iha ihb
  | eq a b iha ihb =>
      by_cases h : Expr.eq a b = p
      · rw [replace_eq_self h]; exact Nat.le_mul_of_pos_left _ (size_pos _)
      · rw [replace_eq h]; exact mul_bound (size_pos q) iha ihb
  | le a b iha ihb =>
      by_cases h : Expr.le a b = p
      · rw [replace_eq_self h]; exact Nat.le_mul_of_pos_left _ (size_pos _)
      · rw [replace_le h]; exact mul_bound (size_pos q) iha ihb
  | and a b iha ihb =>
      by_cases h : Expr.and a b = p
      · rw [replace_eq_self h]; exact Nat.le_mul_of_pos_left _ (size_pos _)
      · rw [replace_and h]; exact mul_bound (size_pos q) iha ihb
  | or a b iha ihb =>
      by_cases h : Expr.or a b = p
      · rw [replace_eq_self h]; exact Nat.le_mul_of_pos_left _ (size_pos _)
      · rw [replace_or h]; exact mul_bound (size_pos q) iha ihb
  | not a iha =>
      by_cases h : Expr.not a = p
      · rw [replace_eq_self h]; exact Nat.le_mul_of_pos_left _ (size_pos _)
      · rw [replace_not h]; exact mul_bound1 (size_pos q) iha

theorem syms_replace (p q : Expr) :
    ∀ (e : Expr) (α : Sym), α ∈ (e.replace p q).syms → α ∈ e.syms ∨ α ∈ q.syms := by
  intro e
  induction e with
  | val v =>
      intro α h; by_cases hp : Expr.val v = p
      · rw [replace_eq_self hp] at h; exact Or.inr h
      · rw [replace_val hp] at h; exact Or.inl h
  | sym v =>
      intro α h; by_cases hp : Expr.sym v = p
      · rw [replace_eq_self hp] at h; exact Or.inr h
      · rw [replace_sym hp] at h; exact Or.inl h
  | not a ih =>
      intro α h; by_cases hp : Expr.not a = p
      · rw [replace_eq_self hp] at h; exact Or.inr h
      · rw [replace_not hp] at h; exact ih α h
  | bin o a b iha ihb =>
      intro α h; by_cases hp : Expr.bin o a b = p
      · rw [replace_eq_self hp] at h; exact Or.inr h
      · rw [replace_bin hp] at h; simp only [syms, List.mem_append] at h ⊢
        rcases h with h | h
        · exact (iha α h).imp Or.inl id
        · exact (ihb α h).imp Or.inr id
  | eq a b iha ihb =>
      intro α h; by_cases hp : Expr.eq a b = p
      · rw [replace_eq_self hp] at h; exact Or.inr h
      · rw [replace_eq hp] at h; simp only [syms, List.mem_append] at h ⊢
        rcases h with h | h
        · exact (iha α h).imp Or.inl id
        · exact (ihb α h).imp Or.inr id
  | le a b iha ihb =>
      intro α h; by_cases hp : Expr.le a b = p
      · rw [replace_eq_self hp] at h; exact Or.inr h
      · rw [replace_le hp] at h; simp only [syms, List.mem_append] at h ⊢
        rcases h with h | h
        · exact (iha α h).imp Or.inl id
        · exact (ihb α h).imp Or.inr id
  | and a b iha ihb =>
      intro α h; by_cases hp : Expr.and a b = p
      · rw [replace_eq_self hp] at h; exact Or.inr h
      · rw [replace_and hp] at h; simp only [syms, List.mem_append] at h ⊢
        rcases h with h | h
        · exact (iha α h).imp Or.inl id
        · exact (ihb α h).imp Or.inr id
  | or a b iha ihb =>
      intro α h; by_cases hp : Expr.or a b = p
      · rw [replace_eq_self hp] at h; exact Or.inr h
      · rw [replace_or hp] at h; simp only [syms, List.mem_append] at h ⊢
        rcases h with h | h
        · exact (iha α h).imp Or.inl id
        · exact (ihb α h).imp Or.inr id

theorem vals_replace (p q : Expr) :
    ∀ (e : Expr) (v : Val), v ∈ (e.replace p q).vals → v ∈ e.vals ∨ v ∈ q.vals := by
  intro e
  induction e with
  | val w =>
      intro v h; by_cases hp : Expr.val w = p
      · rw [replace_eq_self hp] at h; exact Or.inr h
      · rw [replace_val hp] at h; exact Or.inl h
  | sym w =>
      intro v h; by_cases hp : Expr.sym w = p
      · rw [replace_eq_self hp] at h; exact Or.inr h
      · rw [replace_sym hp] at h; exact Or.inl h
  | not a ih =>
      intro v h; by_cases hp : Expr.not a = p
      · rw [replace_eq_self hp] at h; exact Or.inr h
      · rw [replace_not hp] at h; exact ih v h
  | bin o a b iha ihb =>
      intro v h; by_cases hp : Expr.bin o a b = p
      · rw [replace_eq_self hp] at h; exact Or.inr h
      · rw [replace_bin hp] at h; simp only [vals, List.mem_append] at h ⊢
        rcases h with h | h
        · exact (iha v h).imp Or.inl id
        · exact (ihb v h).imp Or.inr id
  | eq a b iha ihb =>
      intro v h; by_cases hp : Expr.eq a b = p
      · rw [replace_eq_self hp] at h; exact Or.inr h
      · rw [replace_eq hp] at h; simp only [vals, List.mem_append] at h ⊢
        rcases h with h | h
        · exact (iha v h).imp Or.inl id
        · exact (ihb v h).imp Or.inr id
  | le a b iha ihb =>
      intro v h; by_cases hp : Expr.le a b = p
      · rw [replace_eq_self hp] at h; exact Or.inr h
      · rw [replace_le hp] at h; simp only [vals, List.mem_append] at h ⊢
        rcases h with h | h
        · exact (iha v h).imp Or.inl id
        · exact (ihb v h).imp Or.inr id
  | and a b iha ihb =>
      intro v h; by_cases hp : Expr.and a b = p
      · rw [replace_eq_self hp] at h; exact Or.inr h
      · rw [replace_and hp] at h; simp only [vals, List.mem_append] at h ⊢
        rcases h with h | h
        · exact (iha v h).imp Or.inl id
        · exact (ihb v h).imp Or.inr id
  | or a b iha ihb =>
      intro v h; by_cases hp : Expr.or a b = p
      · rw [replace_eq_self hp] at h; exact Or.inr h
      · rw [replace_or hp] at h; simp only [vals, List.mem_append] at h ⊢
        rcases h with h | h
        · exact (iha v h).imp Or.inl id
        · exact (ihb v h).imp Or.inr id

theorem size_rename (Λ : Sym → Option Sym) : ∀ e : Expr, (e.rename Λ).size = e.size
  | .val _ | .sym _ => rfl
  | .not a => by simp [rename, size, size_rename Λ a]
  | .bin _ a b | .eq a b | .le a b | .and a b | .or a b => by
      simp [rename, size, size_rename Λ a, size_rename Λ b]

theorem vals_rename (Λ : Sym → Option Sym) : ∀ e : Expr, (e.rename Λ).vals = e.vals
  | .val _ | .sym _ => rfl
  | .not a => by simp [rename, vals, vals_rename Λ a]
  | .bin _ a b | .eq a b | .le a b | .and a b | .or a b => by
      simp [rename, vals, vals_rename Λ a, vals_rename Λ b]

theorem syms_rename (Λ : Sym → Option Sym) :
    ∀ e : Expr, (e.rename Λ).syms = e.syms.map (fun α => (Λ α).getD α)
  | .val _ | .sym _ => rfl
  | .not a => by simp [rename, syms, syms_rename Λ a]
  | .bin _ a b | .eq a b | .le a b | .and a b | .or a b => by
      simp [rename, syms, syms_rename Λ a, syms_rename Λ b]

theorem rename_congr {Λ Λ' : Sym → Option Sym} :
    ∀ e : Expr, (∀ α ∈ e.syms, (Λ α).getD α = (Λ' α).getD α) → e.rename Λ = e.rename Λ'
  | .val _, _ => rfl
  | .sym β, h => by simp only [rename]; rw [h β (List.mem_singleton_self _)]
  | .not a, h => by rw [rename, rename, rename_congr a h]
  | .bin o a b, h | .eq a b, h | .le a b, h | .and a b, h | .or a b, h => by
      simp only [syms, List.mem_append] at h
      simp only [rename]
      rw [rename_congr a (fun α hα => h α (Or.inl hα)), rename_congr b (fun α hα => h α (Or.inr hα))]

theorem subst_of_not_mem {α : Sym} {v : Expr} :
    ∀ e : Expr, α ∉ e.syms → e.subst α v = e
  | .val _, _ => rfl
  | .sym β, h => by
      simp only [syms, List.mem_singleton] at h
      simp only [subst]; rw [if_neg (Ne.symm h)]
  | .not a, h => by rw [subst, subst_of_not_mem a h]
  | .bin o a b, h | .eq a b, h | .le a b, h | .and a b, h | .or a b, h => by
      simp only [syms, List.mem_append, not_or] at h
      simp only [subst]; rw [subst_of_not_mem a h.1, subst_of_not_mem b h.2]

theorem size_subst_val (α : Sym) (v : Val) : ∀ e : Expr, (e.subst α (.val v)).size = e.size
  | .val _ => rfl
  | .sym β => by simp only [subst]; split <;> rfl
  | .not a => by simp [subst, size, size_subst_val α v a]
  | .bin _ a b | .eq a b | .le a b | .and a b | .or a b => by
      simp [subst, size, size_subst_val α v a, size_subst_val α v b]

theorem syms_subst_val (α : Sym) (v : Val) :
    ∀ (e : Expr) (β : Sym), β ∈ (e.subst α (.val v)).syms → β ∈ e.syms
  | .val _, _, h => h
  | .sym γ, β, h => by
      simp only [subst] at h; split at h
      · cases h
      · exact h
  | .not a, β, h => syms_subst_val α v a β h
  | .bin _ a b, β, h | .eq a b, β, h | .le a b, β, h | .and a b, β, h | .or a b, β, h => by
      simp only [subst, syms, List.mem_append] at h ⊢
      exact h.imp (syms_subst_val α v a β) (syms_subst_val α v b β)

theorem vals_subst_val (α : Sym) (v : Val) :
    ∀ (e : Expr) (w : Val), w ∈ (e.subst α (.val v)).vals → w ∈ e.vals ∨ w = v
  | .val _, _, h => Or.inl h
  | .sym γ, w, h => by
      simp only [subst] at h; split at h
      · simp [vals] at h; exact Or.inr h
      · cases h
  | .not a, w, h => vals_subst_val α v a w h
  | .bin _ a b, w, h | .eq a b, w, h | .le a b, w, h | .and a b, w, h | .or a b, w, h => by
      simp only [subst, vals, List.mem_append] at h ⊢
      rcases h with h | h
      · exact (vals_subst_val α v a w h).imp Or.inl id
      · exact (vals_subst_val α v b w h).imp Or.inr id

/-- Every expression of size at most `n` with symbols in `SU` and values in
    `VU` (`mem_allExprs`). -/
def allExprs (SU : List Sym) (VU : List Val) : Nat → List Expr
  | 0 => []
  | n + 1 =>
      let L := allExprs SU VU n
      let pairs := L.flatMap fun a => L.map fun b => (a, b)
      VU.map .val ++ SU.map .sym ++ L.map .not ++
        pairs.flatMap fun ab =>
          [.eq ab.1 ab.2, .le ab.1 ab.2, .and ab.1 ab.2, .or ab.1 ab.2,
           .bin .add ab.1 ab.2, .bin .sub ab.1 ab.2, .bin .mul ab.1 ab.2, .bin .div ab.1 ab.2,
           .bin .band ab.1 ab.2, .bin .bxor ab.1 ab.2, .bin .bor ab.1 ab.2]

/-- `e` is small: of size at most `n`, with symbols in `SU` and values in
    `VU`. -/
def Small (SU : List Sym) (VP : Val → Prop) (n : Nat) (e : Expr) : Prop :=
  e.size ≤ n ∧ (∀ α ∈ e.syms, α ∈ SU) ∧ (∀ v ∈ e.vals, VP v)

theorem mem_allExprs {SU : List Sym} {VU : List Val} :
    ∀ (n : Nat) (e : Expr), Small SU (· ∈ VU) n e → e ∈ allExprs SU VU n
  | 0, e, ⟨h, _⟩ => absurd h (by have := size_pos e; omega)
  | n + 1, e, ⟨hs, hsy, hv⟩ => by
      simp only [allExprs, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons,
        List.mem_nil_iff, or_false]
      have pair : ∀ a b, a.size + b.size + 1 ≤ n + 1 → (∀ α ∈ a.syms ++ b.syms, α ∈ SU) →
          (∀ v ∈ a.vals ++ b.vals, v ∈ VU) →
          a ∈ allExprs SU VU n ∧ b ∈ allExprs SU VU n := fun a b h h1 h2 =>
        ⟨mem_allExprs n a ⟨by omega, fun α hα => h1 α (List.mem_append_left _ hα),
            fun v hv => h2 v (List.mem_append_left _ hv)⟩,
         mem_allExprs n b ⟨by omega, fun α hα => h1 α (List.mem_append_right _ hα),
            fun v hv => h2 v (List.mem_append_right _ hv)⟩⟩
      cases e with
      | val v => exact Or.inl (Or.inl (Or.inl ⟨v, hv v (List.mem_singleton_self _), rfl⟩))
      | sym α => exact Or.inl (Or.inl (Or.inr ⟨α, hsy α (List.mem_singleton_self _), rfl⟩))
      | not a =>
          exact Or.inl (Or.inr ⟨a, mem_allExprs n a ⟨by simp [size] at hs; omega, hsy, hv⟩, rfl⟩)
      | bin o a b | eq a b | le a b | and a b | or a b =>
          obtain ⟨ha, hb⟩ := pair a b (by simpa [size] using hs) hsy hv
          refine Or.inr ⟨(a, b), ⟨a, ha, b, hb, rfl⟩, ?_⟩
          try (cases o)
          all_goals simp

end Expr
