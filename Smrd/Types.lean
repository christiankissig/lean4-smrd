import Lean

/-! # Event Structures -/

/-- A symbol (variable name) used as the result of a read -/
abbrev Symbol := String

/-- An environment maps symbols to integer values. -/
abbrev Env := List (Symbol × Int)

def Env.lookup (f : Env) (s : Symbol) : Option Int :=
  (f.find? (·.1 == s)).map (·.2)

/-- Expressions -/
inductive Expr : Type where
  | lit    : Int → Expr
  | var    : Symbol → Expr
  | add    : Expr → Expr → Expr
  | sub    : Expr → Expr → Expr
  | mul    : Expr → Expr → Expr
  | div    : Expr → Expr → Expr
  | deref  : Expr → Expr
  | eq     : Expr → Expr → Expr   -- boolean: e₁ = e₂
  | le     : Expr → Expr → Expr   -- boolean: e₁ ≤ e₂
  | lt     : Expr → Expr → Expr   -- boolean: e₁ < e₂
  | neg    : Expr → Expr          -- boolean negation
  | and    : Expr → Expr → Expr   -- boolean conjunction
  | or     : Expr → Expr → Expr   -- boolean disjunction
  deriving Repr, DecidableEq

/-- Evaluate an expression under environment f: ⟦e⟧_f. -/
def Expr.eval (f : Env) : Expr → Option Int
  | .lit n     => some n
  | .var α     => f.lookup α
  | .add a b   => do pure ((← a.eval f) + (← b.eval f))
  | .sub a b   => do pure ((← a.eval f) - (← b.eval f))
  | .mul a b   => do pure ((← a.eval f) * (← b.eval f))
  | .div a b   => do
      let bv ← b.eval f
      if bv == 0 then none else pure ((← a.eval f) / bv)
  | .deref _   => none  -- heap dereference not evaluated symbolically
  | .eq  a b   => do pure (if (← a.eval f) == (← b.eval f) then 1 else 0)
  | .le  a b   => do pure (if (← a.eval f) <= (← b.eval f) then 1 else 0)
  | .lt  a b   => do pure (if (← a.eval f) < (← b.eval f) then 1 else 0)
  | .neg e     => do pure (if (← e.eval f) == 0 then 1 else 0)
  | .and a b   => do pure (if (← a.eval f) != 0 && (← b.eval f) != 0 then 1 else 0)
  | .or  a b   => do pure (if (← a.eval f) != 0 || (← b.eval f) != 0 then 1 else 0)

/-- Boolean expressions -/
inductive BoolExpr : Type where
  | top                              : BoolExpr
  | bot                              : BoolExpr
  | eq     : Expr → Expr → BoolExpr
  | le     : Expr → Expr → BoolExpr
  | lt     : Expr → Expr → BoolExpr
  | neg    : BoolExpr → BoolExpr
  | and    : BoolExpr → BoolExpr → BoolExpr
  | or     : BoolExpr → BoolExpr → BoolExpr
  deriving Repr, DecidableEq

/-- Evaluate a BoolExpr under environment f. -/
def BoolExpr.eval (f : Env) : BoolExpr → Option Bool
  | .top       => some true
  | .bot       => some false
  | .eq  a b   => do pure ((← a.eval f) == (← b.eval f))
  | .le  a b   => do pure ((← a.eval f) <= (← b.eval f))
  | .lt  a b   => do pure ((← a.eval f) < (← b.eval f))
  | .neg b     => do pure (!(← b.eval f))
  | .and a b   => do pure ((← a.eval f) && (← b.eval f))
  | .or  a b   => do pure ((← a.eval f) || (← b.eval f))

/-- Embed a BoolExpr into Expr (for use in Expr contexts). -/
def BoolExpr.toExpr : BoolExpr → Expr
  | .top       => .eq (.lit 1) (.lit 1)
  | .bot       => .eq (.lit 0) (.lit 1)
  | .eq  a b   => .eq  a b
  | .le  a b   => .le  a b
  | .lt  a b   => .lt  a b
  | .neg b     => .neg b.toExpr
  | .and a b   => .and a.toExpr b.toExpr
  | .or  a b   => .or  a.toExpr b.toExpr

/-- Memory ordering annotations -/
inductive MemOrd : Type where
  | none    : MemOrd
  | relaxed : MemOrd
  | acquire : MemOrd
  | release : MemOrd
  | acqrel  : MemOrd
  | seqcst  : MemOrd
  deriving Repr, DecidableEq, BEq

/-- The payload of each event kind -/
inductive EventKind : Type where
  | read       (loc : Expr) (result : Symbol) (ord : MemOrd) : EventKind
  | write      (loc : Expr) (val : Expr)      (ord : MemOrd) : EventKind
  | branch     (cond : BoolExpr)                             : EventKind
  | fence      (ord : MemOrd)                                : EventKind
  | lock                                                     : EventKind
  | unlock                                                   : EventKind
  | allocate   (result : Symbol) (size : Expr)               : EventKind
  | deallocate (ptr : Expr)                                  : EventKind
  deriving Repr

/-- An event node, identified by a unique id -/
structure Event : Type where
  id      : Nat
  kind    : EventKind
  valRest : BoolExpr
  deriving Repr

/-- A ternary RMW entry: (readId, condition, writeId) ∈ ⊑ʳᵐʷ -/
structure RMWEntry : Type where
  readId  : Nat
  cond    : BoolExpr
  writeId : Nat
  deriving Repr

/-- Program-order edge between two events -/
structure POEdge : Type where
  from_ : Nat
  to_   : Nat
  deriving Repr, DecidableEq

/-- A binary relation over event ids. -/
abbrev Rel := List (Nat × Nat)

/-- An event structure: events connected by program order, with RMW triples -/
structure EventStructure : Type where
  events  : List Event
  po      : Rel            -- program order ⊑ (as pairs of ids)
  rmw     : List RMWEntry  -- read-modify-write triples
  deriving Repr

/-! ## Event classifiers -/

/-- Is this event a write? -/
def Event.isWrite (e : Event) : Bool :=
  match e.kind with | .write .. => true | _ => false

/-- Is this event a read? -/
def Event.isRead (e : Event) : Bool :=
  match e.kind with | .read .. => true | _ => false

/-- Is this event a fence? -/
def Event.isFence (e : Event) : Bool :=
  match e.kind with | .fence .. => true | _ => false

/-- Is this event a branch? -/
def Event.isBranch (e : Event) : Bool :=
  match e.kind with | .branch .. => true | _ => false

/-- Is this event a releasing write (W_rel, W_acqrel, or W_sc)? -/
def Event.isRelWrite (e : Event) : Bool :=
  match e.kind with
  | .write _ _ ord => ord == .release || ord == .acqrel || ord == .seqcst
  | _ => false

/-- Is this event an acquiring read (R_acq, R_acqrel, or R_sc)? -/
def Event.isAcqRead (e : Event) : Bool :=
  match e.kind with
  | .read _ _ ord => ord == .acquire || ord == .acqrel || ord == .seqcst
  | _ => false

/-- Is this event a releasing fence (F_rel, F_acqrel, or F_sc)? -/
def Event.isRelFence (e : Event) : Bool :=
  match e.kind with
  | .fence ord => ord == .release || ord == .acqrel || ord == .seqcst
  | _ => false

/-- Is this event an acquiring fence (F_acq, F_acqrel, or F_sc)? -/
def Event.isAcqFence (e : Event) : Bool :=
  match e.kind with
  | .fence ord => ord == .acquire || ord == .acqrel || ord == .seqcst
  | _ => false

/-- Memory location of an event (partial). -/
def Event.loc (e : Event) : Option Expr :=
  match e.kind with
  | .read  loc _ _   => some loc
  | .write loc _ _   => some loc
  | .deallocate ptr  => some ptr
  | _                => none

/-! ## Relations over event ids -/

/-- Diagonal relation Δ_X = {(x,x) | x ∈ X}. -/
def diagonal (ids : List Nat) : Rel :=
  ids.map (fun id => (id, id))

/-- Restrict a relation R to pairs where both endpoints are not in excl.
    R_{∖X} ≜ R ∩ (E ∖ X)² -/
def Rel.restrictExcluding (r : Rel) (excl : List Nat) : Rel :=
  r.filter (fun (a, b) => !excl.contains a && !excl.contains b)

/-- Relational composition r₁ ; r₂ -/
def Rel.comp (r₁ r₂ : Rel) : Rel :=
  r₁.flatMap (fun (a, b) => r₂.filterMap (fun (c, d) => if b == c then some (a, d) else none))

/-- Union of two relations. -/
def Rel.union (r₁ r₂ : Rel) : Rel := r₁ ++ r₂

/-- Filter a relation to pairs where both endpoints satisfy a predicate on events. -/
def Rel.filterEvents (r : Rel) (events : List Event) (p : Event → Bool) : Rel :=
  r.filter fun (a, b) =>
    events.any (fun e => e.id == a && p e) &&
    events.any (fun e => e.id == b && p e)
