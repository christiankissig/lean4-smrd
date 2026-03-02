/-!
# SMRD.Properties

Well-formedness conditions and structural lemmas for Labeled Event Structures.

## Well-formedness

A *well-formed* event structure satisfies:
1. **Unique identifiers** – no two distinct events share the same `EventId`.
2. **Order irreflexivity** – `(a, a) ∉ es.order` for all `a`.
3. **Conflict symmetry** – `(a, b) ∈ es.conflict ↔ (b, a) ∈ es.conflict`.
4. **Conflict irreflexivity** – `(a, a) ∉ es.conflict` for all `a`.

## Key lemmas proved

* `empty_wf`              – the empty LES is well-formed.
* `empty_conflictFree`    – every set is conflict-free in the empty LES.
* `empty_isConfiguration` – `[]` is always a configuration of the empty LES.
* `nil_isConfiguration`   – `[]` is a configuration of any LES.
* `singleton_wf`          – a single-event LES is well-formed.

The structural preservation lemmas (`product_wf`, `coproduct_wf`,
`conflictFree_product_left`, `coproduct_conflictFree_left`) are stated with
their intended types and proof strategies documented; their complete Lean proofs
are deferred (`sorry`) for a subsequent formalisation step.
-/

import SMRD.EventStructure

namespace LES

variable {Loc Val Reg : Type}

/-! ## Well-formedness predicates -/

/-- A LES has *unique identifiers* when its event-ID list has no duplicates. -/
def UniqueIds (es : LES Loc Val Reg) : Prop :=
  es.ids.Pairwise (· ≠ ·)

/-- The causality relation is *irreflexive*: no event causes itself. -/
def OrderIrrefl (es : LES Loc Val Reg) : Prop :=
  ∀ a, (a, a) ∉ es.order

/-- The conflict relation is *symmetric*. -/
def ConflictSymm (es : LES Loc Val Reg) : Prop :=
  ∀ a b, (a, b) ∈ es.conflict → (b, a) ∈ es.conflict

/-- The conflict relation is *irreflexive*: no event conflicts with itself. -/
def ConflictIrrefl (es : LES Loc Val Reg) : Prop :=
  ∀ a, (a, a) ∉ es.conflict

/-- The conflict and order relations are *well-scoped*: all identifiers that
    appear in a relation pair are declared events of the same LES. -/
def WellScoped (es : LES Loc Val Reg) : Prop :=
  (∀ a b, (a, b) ∈ es.conflict → es.hasId a ∧ es.hasId b) ∧
  (∀ a b, (a, b) ∈ es.order    → es.hasId a ∧ es.hasId b)

/-- A LES is *well-formed* when all structural conditions hold simultaneously. -/
structure WF (es : LES Loc Val Reg) : Prop where
  uniqueIds      : UniqueIds es
  orderIrrefl    : OrderIrrefl es
  conflictSymm   : ConflictSymm es
  conflictIrrefl : ConflictIrrefl es

/-! ## Empty LES -/

@[simp]
theorem empty_uniqueIds :
    UniqueIds (LES.empty (Loc := Loc) (Val := Val) (Reg := Reg)) := by
  simp [UniqueIds, empty, ids, List.Pairwise]

@[simp]
theorem empty_orderIrrefl :
    OrderIrrefl (LES.empty (Loc := Loc) (Val := Val) (Reg := Reg)) := by
  simp [OrderIrrefl, empty]

@[simp]
theorem empty_conflictSymm :
    ConflictSymm (LES.empty (Loc := Loc) (Val := Val) (Reg := Reg)) := by
  simp [ConflictSymm, empty]

@[simp]
theorem empty_conflictIrrefl :
    ConflictIrrefl (LES.empty (Loc := Loc) (Val := Val) (Reg := Reg)) := by
  simp [ConflictIrrefl, empty]

/-- The empty LES is well-formed. -/
theorem empty_wf : WF (LES.empty (Loc := Loc) (Val := Val) (Reg := Reg)) where
  uniqueIds      := empty_uniqueIds
  orderIrrefl    := empty_orderIrrefl
  conflictSymm   := empty_conflictSymm
  conflictIrrefl := empty_conflictIrrefl

/-- Every set is conflict-free in the empty LES. -/
@[simp]
theorem empty_conflictFree (S : List EventId) :
    (LES.empty (Loc := Loc) (Val := Val) (Reg := Reg)).conflictFree S = true := by
  simp [conflictFree, empty]

/-- `[]` is a configuration of the empty LES. -/
@[simp]
theorem empty_isConfiguration :
    (LES.empty (Loc := Loc) (Val := Val) (Reg := Reg)).isConfiguration [] = true := by
  simp [isConfiguration, conflictFree, downwardClosed, empty]

/-- `[]` is a configuration of any LES. -/
@[simp]
theorem nil_isConfiguration (es : LES Loc Val Reg) :
    es.isConfiguration [] = true := by
  simp [isConfiguration, conflictFree, downwardClosed]

/-! ## Singleton LES -/

@[simp]
theorem singleton_uniqueIds (id : EventId) (lbl : Label Loc Val Reg) :
    UniqueIds (singleton id lbl) := by
  simp [UniqueIds, singleton, ids, List.Pairwise]

@[simp]
theorem singleton_orderIrrefl (id : EventId) (lbl : Label Loc Val Reg) :
    OrderIrrefl (singleton id lbl) := by
  simp [OrderIrrefl, singleton]

@[simp]
theorem singleton_conflictSymm (id : EventId) (lbl : Label Loc Val Reg) :
    ConflictSymm (singleton id lbl) := by
  simp [ConflictSymm, singleton]

@[simp]
theorem singleton_conflictIrrefl (id : EventId) (lbl : Label Loc Val Reg) :
    ConflictIrrefl (singleton id lbl) := by
  simp [ConflictIrrefl, singleton]

/-- A single-event LES with no order or conflict pairs is well-formed. -/
theorem singleton_wf (id : EventId) (lbl : Label Loc Val Reg) :
    WF (singleton id lbl) where
  uniqueIds      := singleton_uniqueIds id lbl
  orderIrrefl    := singleton_orderIrrefl id lbl
  conflictSymm   := singleton_conflictSymm id lbl
  conflictIrrefl := singleton_conflictIrrefl id lbl

/-! ## Structural preservation under product and coproduct

The following theorems establish that the operations on event structures
preserve well-formedness and conflict-freedom when applied to structurally
compatible inputs.  They are stated with their correct types and informal proof
strategies; complete formal proofs are deferred (`sorry`) for a subsequent
formalisation step.
-/

/-- If `S` is conflict-free in `es₁`, the conflict pairs of `es₂` are
    well-scoped (each first endpoint is in `es₂.ids`), and `S` contains no
    `es₂`-identifier, then `S` is conflict-free in `es₁.product es₂`.

    **Proof sketch.**  The product adds only conflict pairs from `es₂.conflict`.
    Each such pair `(a, b)` has `a ∈ es₂.ids` by well-scopedness; but `a ∉ S`
    by `hdisj`, so the pair does not fire. -/
theorem conflictFree_product_left (es₁ es₂ : LES Loc Val Reg) (S : List EventId)
    (hcf    : es₁.conflictFree S = true)
    (hscope : ∀ a b, (a, b) ∈ es₂.conflict → es₂.hasId a)
    (hdisj  : ∀ id, es₂.hasId id → ¬S.contains id) :
    (es₁.product es₂).conflictFree S = true := by
  sorry

/-- If `S` is conflict-free in `es₁`, conflict pairs in `es₂` are well-scoped,
    and `S` contains no `es₂`-identifier, then `S` is conflict-free in
    `es₁.coproduct es₂`.

    **Proof sketch.**  The coproduct adds pairs from `es₂.conflict` (ruled out
    by well-scopedness + `hdisj`) and cross pairs `(x, y)` with `x ∈ ids₁`,
    `y ∈ ids₂` (ruled out by `hdisj` on `y`) and `(y, x)` (ruled out on
    `y` as well). -/
theorem coproduct_conflictFree_left
    (es₁ es₂ : LES Loc Val Reg) (S : List EventId)
    (hcf    : es₁.conflictFree S = true)
    (hscope : ∀ a b, (a, b) ∈ es₂.conflict → es₂.hasId a)
    (hdisj  : ∀ id, es₂.hasId id → ¬S.contains id) :
    (es₁.coproduct es₂).conflictFree S = true := by
  sorry

/-- The product of two well-formed event structures with disjoint identifier
    sets is well-formed.

    **Proof sketch.**
    * *OrderIrrefl / ConflictIrrefl* – union of two irreflexive relations is
      irreflexive.
    * *ConflictSymm* – union of two symmetric relations is symmetric.
    * *UniqueIds* – concatenation of two pairwise-distinct ID lists that are
      also mutually disjoint (given by `hdisj`) is pairwise-distinct. -/
theorem product_wf (es₁ es₂ : LES Loc Val Reg)
    (h₁    : WF es₁) (h₂ : WF es₂)
    (hdisj : ∀ id, ¬(es₁.hasId id ∧ es₂.hasId id)) :
    WF (es₁.product es₂) where
  uniqueIds := by
    sorry
  orderIrrefl := fun a hmem => by
    simp [product, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact h₁.orderIrrefl a hmem
    · exact h₂.orderIrrefl a hmem
  conflictSymm := fun a b hmem => by
    simp [product, List.mem_append] at hmem ⊢
    rcases hmem with hmem | hmem
    · exact Or.inl (h₁.conflictSymm a b hmem)
    · exact Or.inr (h₂.conflictSymm a b hmem)
  conflictIrrefl := fun a hmem => by
    simp [product, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact h₁.conflictIrrefl a hmem
    · exact h₂.conflictIrrefl a hmem

/-- The coproduct of two well-formed event structures with disjoint identifier
    sets is well-formed.

    **Proof sketch.**  As for `product_wf`, plus:
    * *ConflictSymm* for cross pairs – `coproduct` adds both `(x, y)` and
      `(y, x)` for every `x ∈ ids₁`, `y ∈ ids₂`, so symmetry is built in.
    * *ConflictIrrefl* for cross pairs – `(a, a)` would require `a ∈ ids₁ ∩ ids₂`,
      which is empty by `hdisj`. -/
theorem coproduct_wf (es₁ es₂ : LES Loc Val Reg)
    (h₁    : WF es₁) (h₂ : WF es₂)
    (hdisj : ∀ id, ¬(es₁.hasId id ∧ es₂.hasId id)) :
    WF (es₁.coproduct es₂) where
  uniqueIds := by sorry
  orderIrrefl := fun a hmem => by
    simp [coproduct, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact h₁.orderIrrefl a hmem
    · exact h₂.orderIrrefl a hmem
  conflictSymm := fun a b hmem => by
    simp only [coproduct, List.mem_append, List.mem_bind, List.mem_map,
               Prod.mk.injEq] at hmem ⊢
    rcases hmem with ((hmem | hmem) |
                      ⟨x, hx, y, hy, rfl, rfl⟩) |
                      ⟨x, hx, y, hy, rfl, rfl⟩
    · exact Or.inl (Or.inl (h₁.conflictSymm a b hmem))
    · exact Or.inl (Or.inr (h₂.conflictSymm a b hmem))
    · exact Or.inr ⟨b, hy, a, hx, rfl, rfl⟩
    · exact Or.inl ⟨b, hy, a, hx, rfl, rfl⟩
  conflictIrrefl := fun a hmem => by
    simp only [coproduct, List.mem_append, List.mem_bind, List.mem_map,
               Prod.mk.injEq] at hmem
    rcases hmem with ((hmem | hmem) |
                      ⟨x, hx, y, hy, hxa, hya⟩) |
                      ⟨x, hx, y, hy, hxa, hya⟩
    · exact h₁.conflictIrrefl a hmem
    · exact h₂.conflictIrrefl a hmem
    · subst hxa; subst hya
      exact hdisj x ⟨by simp [hasId, ids, List.contains_iff]; exact hx,
                       by simp [hasId, ids, List.contains_iff]; exact hy⟩
    · subst hxa; subst hya
      exact hdisj x ⟨by simp [hasId, ids, List.contains_iff]; exact hy,
                       by simp [hasId, ids, List.contains_iff]; exact hx⟩

end LES
