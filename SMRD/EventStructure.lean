/-!
# SMRD.EventStructure

This module defines *Labeled Event Structures* (LES) and the operations on them
that make up the compositional MRD semantics.

## Background

A Labeled Event Structure `(E, ≤, #, λ)` consists of:
* `E`  – a finite set of events, each carrying a label.
* `≤`  – a partial order (causality) on event identifiers.
* `#`  – a conflict relation (irreflexive and symmetric) on event identifiers.

A *configuration* is a conflict-free, downward-closed subset of `E`.

The three fundamental operations on event structures used by the MRD semantics
are:
* **product** (parallel composition) – events from both structures can occur.
* **coproduct** (choice) – events from the two structures are mutually
  exclusive (cross-product conflict is added).
* **sequence** – events of the second structure are causally dependent on a
  *conflict-free* choice of leaves of the first.
-/

import SMRD.Basic

/-- A unique identifier for an event within a labeled event structure. -/
abbrev EventId := Nat

/-- A binary relation on `α`, represented as a list of pairs. -/
abbrev Rel (α : Type) := List (α × α)

namespace Rel

/-- Union of two relations. -/
def union (r₁ r₂ : Rel α) : Rel α := r₁ ++ r₂

/-- Invert a relation (swap each pair). -/
def invert (r : Rel α) : Rel α := r.map (fun (a, b) => (b, a))

/-- Relational composition: `(a, c) ∈ r₁.comp r₂` iff `∃ b, (a,b) ∈ r₁ ∧ (b,c) ∈ r₂`. -/
def comp [BEq α] (r₁ r₂ : Rel α) : Rel α :=
  r₁.bind (fun (a, b) => r₂.filterMap (fun (b', c) => if b == b' then some (a, c) else none))

/-- Check whether a relation is irreflexive (no pair `(a, a)` present). -/
def isIrreflexive [BEq α] (r : Rel α) : Bool :=
  !r.any (fun (a, b) => a == b)

/-- Check whether a relation is symmetric. -/
def isSymmetric [BEq α] (r : Rel α) : Bool :=
  r.all (fun (a, b) => r.contains (b, a))

end Rel

/-!
## Labeled Event Structures
-/

/-- A *Labeled Event Structure* `(E, ≤, #)` where every event carries a label.

The event set is stored as a list of `(EventId, Label)` pairs.  The
causality relation `≤` (`order`) is a partial order on `EventId`s.
The conflict relation `#` (`conflict`) is irreflexive and symmetric. -/
structure LES (Loc Val Reg : Type) where
  /-- The set of events, each identified by a unique `EventId` and carrying a
      label that describes the memory operation it performs. -/
  events   : List (EventId × Label Loc Val Reg)
  /-- The causality (partial order) relation: `(a, b) ∈ order` means event `a`
      must occur before event `b` in every execution. -/
  order    : Rel EventId
  /-- The conflict relation: `(a, b) ∈ conflict` means events `a` and `b`
      cannot both occur in the same configuration. -/
  conflict : Rel EventId
  deriving Repr

namespace LES

variable {Loc Val Reg : Type}

/-! ### Constructors -/

/-- The empty event structure containing no events. -/
def empty : LES Loc Val Reg :=
  { events := [], order := [], conflict := [] }

/-- Build an event structure from a single event. -/
def singleton (id : EventId) (lbl : Label Loc Val Reg) : LES Loc Val Reg :=
  { events := [(id, lbl)], order := [], conflict := [] }

/-! ### Accessors -/

/-- The list of all event identifiers in the structure. -/
def ids (es : LES Loc Val Reg) : List EventId :=
  es.events.map (·.1)

/-- Check whether `id` is an event in this structure. -/
def hasId (es : LES Loc Val Reg) (id : EventId) : Bool :=
  es.ids.contains id

/-- Look up the label of event `id`, if it exists. -/
def getLabel (es : LES Loc Val Reg) (id : EventId) : Option (Label Loc Val Reg) :=
  (es.events.find? (·.1 == id)).map (·.2)

/-- The *leaves* of the event structure: events that are not preceded by any
    other event, i.e., maximal elements under the *reverse* order or,
    equivalently, events that do not appear as the `snd` of any order pair. -/
def leaves (es : LES Loc Val Reg) : List EventId :=
  let successors := es.order.map (·.2)
  es.ids.filter (fun id => !successors.contains id)

/-! ### Conflict-freedom and configurations -/

/-- A set `S` of event identifiers is *conflict-free* in `es` if no two events
    in `S` are in conflict. -/
def conflictFree (es : LES Loc Val Reg) (S : List EventId) : Bool :=
  !es.conflict.any (fun (a, b) => S.contains a && S.contains b)

/-- A set `S` is *downward-closed* with respect to the order relation: if
    `b ∈ S` and `(a, b) ∈ es.order` then `a ∈ S`. -/
def downwardClosed (es : LES Loc Val Reg) (S : List EventId) : Bool :=
  es.order.all (fun (a, b) => !S.contains b || S.contains a)

/-- `S` is a *configuration* of `es` if it is both conflict-free and
    downward-closed.  Configurations represent finite, consistent partial
    executions of a concurrent program. -/
def isConfiguration (es : LES Loc Val Reg) (S : List EventId) : Bool :=
  es.conflictFree S && es.downwardClosed S

/-! ### Operations on event structures -/

/-- **Product** (parallel composition): the events, order and conflict of both
    structures are combined.  Events of `es₁` and `es₂` are independent; the
    resulting structure represents all interleavings of the two. -/
def product (es₁ es₂ : LES Loc Val Reg) : LES Loc Val Reg :=
  { events   := es₁.events   ++ es₂.events
  , order    := es₁.order    ++ es₂.order
  , conflict := es₁.conflict ++ es₂.conflict }

/-- **Coproduct** (choice / disjunction): adds a cross-product conflict
    between every event of `es₁` and every event of `es₂`, making the two
    sets of events mutually exclusive.  The result represents a *choice*
    between the two programs. -/
def coproduct (es₁ es₂ : LES Loc Val Reg) : LES Loc Val Reg :=
  let ids₁ := es₁.ids
  let ids₂ := es₂.ids
  -- Every event of es₁ conflicts with every event of es₂ and vice versa.
  let cross := (ids₁.bind (fun a => ids₂.map (fun b => (a, b))))
             ++ (ids₂.bind (fun b => ids₁.map (fun a => (b, a))))
  { events   := es₁.events   ++ es₂.events
  , order    := es₁.order    ++ es₂.order
  , conflict := es₁.conflict ++ es₂.conflict ++ cross }

/-- **Relabeling**: apply a renaming function `f` to all event identifiers.
    Used internally to ensure that fresh copies of an event structure have
    disjoint identifiers from existing structures. -/
def relabel (f : EventId → EventId) (es : LES Loc Val Reg) : LES Loc Val Reg :=
  { events   := es.events.map   (fun (id, lbl) => (f id, lbl))
  , order    := es.order.map    (fun (a, b)    => (f a, f b))
  , conflict := es.conflict.map (fun (a, b)    => (f a, f b)) }

/-! ### Projection helpers (for axiom checking) -/

/-- All events labeled as reads. -/
def reads (es : LES Loc Val Reg) : List (EventId × Label Loc Val Reg) :=
  es.events.filter (·.2.isRead)

/-- All events labeled as writes. -/
def writes (es : LES Loc Val Reg) : List (EventId × Label Loc Val Reg) :=
  es.events.filter (·.2.isWrite)

/-- All events that are memory accesses (reads or writes). -/
def memoryAccesses (es : LES Loc Val Reg) : List (EventId × Label Loc Val Reg) :=
  es.events.filter (·.2.isMemoryAccess)

/-- All non-atomic memory access events. -/
def nonAtomicAccesses (es : LES Loc Val Reg) : List (EventId × Label Loc Val Reg) :=
  es.events.filter (·.2.isNonAtomic)

end LES
