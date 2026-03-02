/-!
# SMRD.Basic

Core types for the Symbolic Memory Recurrence Diagram (SMRD) formalization.

We define memory access orderings, exclusivity flags, read-modify-write
strengths, and the central `Label` inductive type that classifies memory
operations.  All definitions are parameterized over abstract types `Loc`, `Val`
and `Reg` for memory locations, stored values, and register names respectively.
This parametericity is what makes the semantics *symbolic*: every statement
holds for any instantiation of those domains.
-/

/-- Memory access orderings following the C11/C++11 memory model. -/
inductive Ordering : Type where
  | nonAtomic : Ordering
  | relaxed   : Ordering
  | acquire   : Ordering
  | release   : Ordering
  | sc        : Ordering
  deriving DecidableEq, BEq, Repr, Hashable

/-- Exclusivity flag for load operations (used in load-exclusive / RMW pairs). -/
inductive Exclusivity : Type where
  | exclusive    : Exclusivity
  | notExclusive : Exclusivity
  deriving DecidableEq, BEq, Repr

/-- Strength of read-modify-write (RMW) operations. -/
inductive RMWStrength : Type where
  | normal : RMWStrength
  | strong : RMWStrength
  deriving DecidableEq, BEq, Repr

/-!
## Event labels

`Label Loc Val Reg` classifies the kind of memory operation that an event
performs.  The type is parameterized so that the formalization is independent
of any particular concrete domain of locations, values or register names.
-/

/-- Labels for memory events.

    * `read  l v r o e` – a load of value `v` from location `l` into register `r`
      with ordering `o` and exclusivity `e`.
    * `write l v o s`   – a store of value `v` to location `l` with ordering `o`
      and RMW strength `s`.
    * `fence o`         – a memory fence with ordering `o`.
    * `observable v`    – an observable output of value `v` (used for assertion
      checking).
    * `lock`            – a mutex lock acquisition.
    * `unlock`          – a mutex lock release.
-/
inductive Label (Loc Val Reg : Type) : Type where
  | read       : Loc → Val → Reg → Ordering → Exclusivity → Label Loc Val Reg
  | write      : Loc → Val → Ordering → RMWStrength → Label Loc Val Reg
  | fence      : Ordering → Label Loc Val Reg
  | observable : Val → Label Loc Val Reg
  | lock       : Label Loc Val Reg
  | unlock     : Label Loc Val Reg
  deriving Repr

namespace Label

variable {Loc Val Reg : Type}

/-- Extract the memory location accessed by this label, if any.
    Only reads and writes have a location; fences, observables and
    lock/unlock operations return `none`. -/
def location? : Label Loc Val Reg → Option Loc
  | .read  l _ _ _ _ => some l
  | .write l _ _ _   => some l
  | _                => none

/-- Extract the value associated with this label, if any.
    Reads, writes and observables carry a value; fences and lock operations
    do not. -/
def value? : Label Loc Val Reg → Option Val
  | .read  _ v _ _ _ => some v
  | .write _ v _ _   => some v
  | .observable v    => some v
  | _                => none

/-- Extract the memory ordering of this label, if any.
    Reads, writes and fences have an ordering; observables and
    lock/unlock do not. -/
def ordering? : Label Loc Val Reg → Option Ordering
  | .read  _ _ _ o _ => some o
  | .write _ _ o _   => some o
  | .fence o         => some o
  | _                => none

/-- True iff this label represents a load (read) operation. -/
def isRead : Label Loc Val Reg → Bool
  | .read _ _ _ _ _ => true
  | _               => false

/-- True iff this label represents a store (write) operation. -/
def isWrite : Label Loc Val Reg → Bool
  | .write _ _ _ _ => true
  | _              => false

/-- True iff this label represents a memory fence. -/
def isFence : Label Loc Val Reg → Bool
  | .fence _ => true
  | _        => false

/-- True iff this label is an observable output. -/
def isObservable : Label Loc Val Reg → Bool
  | .observable _ => true
  | _             => false

/-- True iff this label is a lock acquisition. -/
def isLock : Label Loc Val Reg → Bool
  | .lock => true
  | _     => false

/-- True iff this label is a lock release (unlock). -/
def isUnlock : Label Loc Val Reg → Bool
  | .unlock => true
  | _       => false

/-- True iff this label is a memory access (i.e., a read or a write). -/
def isMemoryAccess (l : Label Loc Val Reg) : Bool :=
  l.isRead || l.isWrite

/-- True iff this label is a non-atomic memory access.
    A non-atomic access is a read or write with `nonAtomic` ordering. -/
def isNonAtomic : Label Loc Val Reg → Bool
  | .read  _ _ _ .nonAtomic _ => true
  | .write _ _ .nonAtomic _   => true
  | _                         => false

/-- Two labels access the same memory location. -/
def sameLocation [DecidableEq Loc] (l₁ l₂ : Label Loc Val Reg) : Bool :=
  match l₁.location?, l₂.location? with
  | some a, some b => a == b
  | _,      _      => false

/-- Two labels carry the same value. -/
def sameValue [DecidableEq Val] (l₁ l₂ : Label Loc Val Reg) : Bool :=
  match l₁.value?, l₂.value? with
  | some v₁, some v₂ => v₁ == v₂
  | _,        _       => false

/-! ### Basic lemmas about label predicates -/

@[simp]
theorem isMemoryAccess_read (l : Loc) (v : Val) (r : Reg) (o : Ordering) (e : Exclusivity) :
    (Label.read l v r o e : Label Loc Val Reg).isMemoryAccess = true := rfl

@[simp]
theorem isMemoryAccess_write (l : Loc) (v : Val) (o : Ordering) (s : RMWStrength) :
    (Label.write l v o s : Label Loc Val Reg).isMemoryAccess = true := rfl

@[simp]
theorem isMemoryAccess_fence (o : Ordering) :
    (Label.fence o : Label Loc Val Reg).isMemoryAccess = false := rfl

@[simp]
theorem location?_read (l : Loc) (v : Val) (r : Reg) (o : Ordering) (e : Exclusivity) :
    (Label.read l v r o e : Label Loc Val Reg).location? = some l := rfl

@[simp]
theorem location?_write (l : Loc) (v : Val) (o : Ordering) (s : RMWStrength) :
    (Label.write l v o s : Label Loc Val Reg).location? = some l := rfl

@[simp]
theorem location?_fence (o : Ordering) :
    (Label.fence o : Label Loc Val Reg).location? = none := rfl

end Label
