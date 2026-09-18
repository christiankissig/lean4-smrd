/-!
# Expressions, Events and Event Structures

Appendix A.1–A.2 of the paper: expressions in event structures
(Definition `def:es-expressions`), their semantics (`def:expr-sem`),
semantic equivalence (`def:sem-equiv`) and symbolic event structures
(`def:event-structures`).

## Representation choices

* **Symbols are event ids.** Every read and allocation event introduces a
  fresh symbol (Paragraph `par:order-symb`). We name the symbol introduced by
  the event with id `k` by `k` itself, so that `origin α = α`.
* **Predicates are semantic.** A predicate is a set of valuations
  `Valuation → Prop`. Syntactic predicates (value restrictions, the
  predicates of justifications) are expressions, and denote a predicate via
  `Expr.holds`. Satisfiability, entailment and `≡_P` are stated semantically,
  which is how the paper quantifies over environments `f`.
* **Relations and sets are predicates** on event ids (`Rel`, `EvSet`), as the
  paper's definitions are not computable (they quantify over environments).
-/

/-- Event identifiers. -/
abbrev EventId := Nat

/-- Symbols `α`. The symbol `k` is the one introduced by the event with id `k`,
    so that `origin α = α`. -/
abbrev Sym := Nat

/-- Registers (thread-local state). -/
abbrev Reg := String

/-- Global variables. -/
abbrev Var := String

/-- Loop identifiers, indexed from `1`; `0` is reserved for "outside every loop". -/
abbrev LoopId := Nat

/-- Thread identifiers. -/
abbrev ThreadId := Nat

/-! ## Values and expressions (Definitions A.2, A.4) -/

/-- The base of a memory location: a global variable, or a heap cell handed out
    by an allocation. -/
inductive LocBase where
  | global (x : Var)
  | heap   (n : Nat)
  deriving Repr, DecidableEq

/-- A memory location: a base shifted by a constant offset, so that the
    location expressions `α + c` of Definition `def:const-offsets` evaluate. -/
structure Loc where
  base : LocBase
  off  : Nat := 0
  deriving Repr, DecidableEq

/-- Values `Val`: naturals, locations and booleans (Definition A.4). -/
inductive Val where
  | num  (n : Nat)
  | loc  (l : Loc)
  | bool (b : Bool)
  deriving Repr, DecidableEq

/-- Arithmetic operators, including the bitwise ones used by seqlock. -/
inductive ArithOp where
  | add | sub | mul | div | band | bxor | bor
  deriving Repr, DecidableEq

/-- Expressions in event structures (Definition `def:es-expressions`): no
    registers and no dereferences, but symbols `α`. Arithmetic and boolean
    expressions share one type. -/
inductive Expr where
  | val  (v : Val)
  | sym  (α : Sym)
  | bin  (op : ArithOp) (a b : Expr)
  | eq   (a b : Expr)
  | le   (a b : Expr)
  | not  (a : Expr)
  | and  (a b : Expr)
  | or   (a b : Expr)
  deriving Repr, DecidableEq

namespace Expr

def tt : Expr := .val (.bool true)
def ff : Expr := .val (.bool false)
def num (n : Nat) : Expr := .val (.num n)
def glob (x : Var) : Expr := .val (.loc ⟨.global x, 0⟩)
/-- Implication, as `¬a ∨ b`. -/
def imp (a b : Expr) : Expr := .or (.not a) b

/-- The symbols `symbols(e)` of an expression. -/
def syms : Expr → List Sym
  | .val _      => []
  | .sym α      => [α]
  | .bin _ a b  => a.syms ++ b.syms
  | .eq a b     => a.syms ++ b.syms
  | .le a b     => a.syms ++ b.syms
  | .not a      => a.syms
  | .and a b    => a.syms ++ b.syms
  | .or a b     => a.syms ++ b.syms

/-- Substitute the expression `v` for the symbol `α`: `e[α := v]`. -/
def subst (α : Sym) (v : Expr) : Expr → Expr
  | .val w      => .val w
  | .sym β      => if β = α then v else .sym β
  | .bin op a b => .bin op (subst α v a) (subst α v b)
  | .eq a b     => .eq (subst α v a) (subst α v b)
  | .le a b     => .le (subst α v a) (subst α v b)
  | .not a      => .not (subst α v a)
  | .and a b    => .and (subst α v a) (subst α v b)
  | .or a b     => .or (subst α v a) (subst α v b)

/-- Replace every occurrence of the subexpression `p` by `q`. This is the
    environment `g = [val(e₂) ↦ val(e₁)]` of Forwarding (Definition
    `def:elab-fwd`), which for store-store forwarding maps an expression rather
    than a symbol. -/
def replace (p q : Expr) (e : Expr) : Expr :=
  if e = p then q else
    match e with
    | .val w      => .val w
    | .sym β      => .sym β
    | .bin op a b => .bin op (replace p q a) (replace p q b)
    | .eq a b     => .eq (replace p q a) (replace p q b)
    | .le a b     => .le (replace p q a) (replace p q b)
    | .not a      => .not (replace p q a)
    | .and a b    => .and (replace p q a) (replace p q b)
    | .or a b     => .or (replace p q a) (replace p q b)
termination_by e

/-- Rename symbols along a relabelling, `⟦e⟧_Λ`; symbols outside the domain of
    `Λ` are left alone (Definition A.4, `α ∉ Dom(f)`). -/
def rename (Λ : Sym → Option Sym) : Expr → Expr
  | .val w      => .val w
  | .sym β      => .sym ((Λ β).getD β)
  | .bin op a b => .bin op (a.rename Λ) (b.rename Λ)
  | .eq a b     => .eq (a.rename Λ) (b.rename Λ)
  | .le a b     => .le (a.rename Λ) (b.rename Λ)
  | .not a      => .not (a.rename Λ)
  | .and a b    => .and (a.rename Λ) (b.rename Λ)
  | .or a b     => .or (a.rename Λ) (b.rename Λ)

/-- Conjunction of a list of expressions, `⊤` for the empty list. -/
def conj (es : List Expr) : Expr := es.foldl .and tt

end Expr

/-! ## Semantics of expressions (Definition `def:expr-sem`) -/

/-- A valuation: a total environment mapping every symbol to a value. The
    paper's partial environments `f` enter only through
    `⟦e⟧_f ∈ Val`, which holds exactly for environments defined on
    `symbols(e)`; quantifying over total valuations is equivalent. -/
abbrev Valuation := Sym → Val

def ArithOp.apply : ArithOp → Nat → Nat → Option Nat
  | .add,  a, b => some (a + b)
  | .sub,  a, b => some (a - b)
  | .mul,  a, b => some (a * b)
  | .div,  a, b => if b = 0 then none else some (a / b)
  | .band, a, b => some (a &&& b)
  | .bxor, a, b => some (a ^^^ b)
  | .bor,  a, b => some (a ||| b)

/-- Arithmetic on values. Locations support adding and subtracting a
    constant offset, which is what location expressions `α + c` need. -/
def ArithOp.applyVal : ArithOp → Val → Val → Option Val
  | op,   .num a, .num b => (op.apply a b).map .num
  | .add, .loc l, .num c => some (.loc { l with off := l.off + c })
  | .add, .num c, .loc l => some (.loc { l with off := l.off + c })
  | .sub, .loc l, .num c => some (.loc { l with off := l.off - c })
  | _,    _,      _      => none

/-- `⟦e⟧_f`: evaluation under a valuation. `none` marks an ill-typed
    expression or a division by zero, on which the paper is silent. -/
def Expr.eval (f : Valuation) : Expr → Option Val
  | .val v      => some v
  | .sym α      => some (f α)
  | .bin op a b =>
      match a.eval f, b.eval f with
      | some x, some y => op.applyVal x y
      | _, _ => none
  | .eq a b =>
      match a.eval f, b.eval f with
      | some x, some y => some (.bool (decide (x = y)))
      | _, _ => none
  | .le a b =>
      match a.eval f, b.eval f with
      | some (.num x), some (.num y) => some (.bool (decide (x ≤ y)))
      | _, _ => none
  | .not a =>
      match a.eval f with
      | some (.bool x) => some (.bool (!x))
      | _ => none
  | .and a b =>
      match a.eval f, b.eval f with
      | some (.bool x), some (.bool y) => some (.bool (x && y))
      | _, _ => none
  | .or a b =>
      match a.eval f, b.eval f with
      | some (.bool x), some (.bool y) => some (.bool (x || y))
      | _, _ => none

/-- Evaluation only reads the symbols of the expression. -/
theorem Expr.eval_congr (e : Expr) (f g : Valuation)
    (h : ∀ α ∈ e.syms, f α = g α) : e.eval f = e.eval g := by
  induction e with
  | val v => rfl
  | sym α => simp [Expr.eval, h α (by simp [Expr.syms])]
  | bin op a b iha ihb | eq a b iha ihb | le a b iha ihb | and a b iha ihb
  | or a b iha ihb =>
      simp only [Expr.syms, List.mem_append] at h
      simp only [Expr.eval]
      rw [iha (fun α hα => h α (Or.inl hα)), ihb (fun α hα => h α (Or.inr hα))]
  | not a iha =>
      simp only [Expr.eval]
      rw [iha h]

/-! ## Predicates, satisfiability and equivalence (Definition `def:sem-equiv`) -/

/-- Semantic predicates: sets of valuations. -/
abbrev Pred := Valuation → Prop

namespace Pred
def top : Pred := fun _ => True
def and (P Q : Pred) : Pred := fun f => P f ∧ Q f
def or  (P Q : Pred) : Pred := fun f => P f ∨ Q f
end Pred

/-- The predicate a boolean expression denotes: the valuations under which it
    evaluates to `⊤`. -/
def Expr.holds (b : Expr) : Pred := fun f => b.eval f = some (.bool true)

/-- `P ≢ ⊥`: `P` is satisfiable. -/
def Sat (P : Pred) : Prop := ∃ f, P f

/-- `P ⇒ Q` for all valuations. -/
def Entails (P Q : Pred) : Prop := ∀ f, P f → Q f

/-- `e₁ ≡ e₂`: wherever both sides denote values, they denote the same one. -/
def SemEquiv (e₁ e₂ : Expr) : Prop :=
  ∀ f v₁ v₂, e₁.eval f = some v₁ → e₂.eval f = some v₂ → v₁ = v₂

/-- `e₁ ≡_P e₂ ≜ (P ⇒ e₁ = e₂) ≡ ⊤`, with `P` a semantic predicate. -/
def EquivUnder (P : Pred) (e₁ e₂ : Expr) : Prop :=
  ∀ f, P f → ∀ v₁ v₂, e₁.eval f = some v₁ → e₂.eval f = some v₂ → v₁ = v₂

/-! ## Memory orders and events -/

/-- C11 memory orders `o ∈ {rlx, rel, acq}` of the program syntax, and `sc`,
    which the classes of preserved program order mention. -/
inductive MemOrd where
  | rlx | acq | rel | sc
  deriving Repr, DecidableEq

def MemOrd.isRelSc : MemOrd → Bool
  | .rel | .sc => true
  | _ => false

def MemOrd.isAcqSc : MemOrd → Bool
  | .acq | .sc => true
  | _ => false

/-- The action of an event: reads `R_o loc α`, writes `W_o loc val`,
    fences `F_o`, branchings on a condition, allocations `A α size` and
    deallocations `D loc`. -/
inductive EventKind where
  | read    (ord : MemOrd) (loc : Expr) (α : Sym)
  | write   (ord : MemOrd) (loc val : Expr)
  | fence   (ord : MemOrd)
  | branch  (cond : Expr)
  | alloc   (α : Sym) (size : Expr)
  | dealloc (loc : Expr)
  deriving Repr, DecidableEq

/-- A control label (Definition `def:atomic-set-unravel`): the thread, the
    program counter, and the iteration of every loop nesting the step, ordered
    from the outermost loop inwards. `loopfun` and `iter` are read off it.
    Program counters are syntactic positions, so that the composite
    read-modify-write operations get one per event. -/
structure Label where
  thread : ThreadId
  pc     : List Nat
  iter   : List (LoopId × Nat)
  deriving Repr, DecidableEq

/-- One outcome of a branching decision on the path to an event: the branching
    event, its condition, and whether the `then` (`pos = true`) or `else`
    outcome was taken. Value restrictions are conjunctions of these. -/
structure Guard where
  branch : EventId
  cond   : Expr
  pos    : Bool
  deriving Repr, DecidableEq

def Guard.expr (g : Guard) : Expr := if g.pos then g.cond else .not g.cond

/-- An event of a symbolic event structure. The value restriction `valres(e)`
    is kept as the list of branching outcomes accumulated along `⊑` up to the
    event (the predicate `φ` of Definition `def:gen-es`), so that the
    conditions contributed by a given branching event -- and so by a given loop
    iteration -- can be recovered (Condition `episodic:cond`). -/
structure Event where
  id     : EventId
  kind   : EventKind
  label  : Label
  guards : List Guard
  deriving Repr, DecidableEq

namespace Event

/-- `valres(e)`: the conjunction of the branching outcomes up to `e`. -/
def valres (e : Event) : Expr := Expr.conj (e.guards.map Guard.expr)

def isRead (e : Event) : Bool := match e.kind with | .read .. => true | _ => false
def isWrite (e : Event) : Bool := match e.kind with | .write .. => true | _ => false
def isFence (e : Event) : Bool := match e.kind with | .fence .. => true | _ => false
def isBranch (e : Event) : Bool := match e.kind with | .branch .. => true | _ => false
def isAlloc (e : Event) : Bool := match e.kind with | .alloc .. => true | _ => false
def isDealloc (e : Event) : Bool := match e.kind with | .dealloc .. => true | _ => false

/-- Effectful events `Eff = W ∪ A ∪ D` (Definition `def:justs`). -/
def isEffect (e : Event) : Bool := e.isWrite || e.isAlloc || e.isDealloc

/-- `W_{rel,sc}` -/
def isRelW (e : Event) : Bool := match e.kind with | .write o .. => o.isRelSc | _ => false
/-- `R_{acq,sc}` -/
def isAcqR (e : Event) : Bool := match e.kind with | .read o .. => o.isAcqSc | _ => false
/-- `F_{rel,sc}` -/
def isRelF (e : Event) : Bool := match e.kind with | .fence o => o.isRelSc | _ => false
/-- `F_{acq,sc}` -/
def isAcqF (e : Event) : Bool := match e.kind with | .fence o => o.isAcqSc | _ => false
/-- `R_rlx` -/
def isRlxR (e : Event) : Bool := match e.kind with | .read .rlx .. => true | _ => false
/-- `W_rlx` -/
def isRlxW (e : Event) : Bool := match e.kind with | .write .rlx .. => true | _ => false

/-- `loc(e)`: the location of a read, write or deallocation, and the symbol an
    allocation introduces. -/
def loc (e : Event) : Option Expr :=
  match e.kind with
  | .read _ l _   => some l
  | .write _ l _  => some l
  | .alloc α _    => some (.sym α)
  | .dealloc l    => some l
  | _             => none

/-- `val(e)`: the value written, the symbol read, the size allocated. It is the
    empty expression (`none`, with no symbols) for deallocations, fences and
    branchings. -/
def val (e : Event) : Option Expr :=
  match e.kind with
  | .read _ _ α   => some (.sym α)
  | .write _ _ v  => some v
  | .alloc _ s    => some s
  | _             => none

/-- `cond(e)` of a branching event. -/
def cond (e : Event) : Option Expr :=
  match e.kind with
  | .branch c => some c
  | _ => none

def locSyms (e : Event) : List Sym := (e.loc.map Expr.syms).getD []
def valSyms (e : Event) : List Sym := (e.val.map Expr.syms).getD []

/-- `loopfun(e)`: the loops nesting the event, outermost first. -/
def loops (e : Event) : List LoopId := e.label.iter.map Prod.fst

/-- `iter(e)(ℓ)`, a partial function. -/
def iter (e : Event) (ℓ : LoopId) : Option Nat := e.label.iter.lookup ℓ

def thread (e : Event) : ThreadId := e.label.thread

def pc (e : Event) : List Nat := e.label.pc

end Event

/-! ## Event structures (Definition `def:event-structures`) -/

/-- A ternary entry `(e_r, c, e_w) ∈ ⊑ʳᵐʷ`. -/
structure RMWEntry where
  r    : EventId
  cond : Expr
  w    : EventId
  deriving Repr, DecidableEq

/-- A symbolic event structure `(E, ⊑, ⊑ʳᵐʷ, valres)`; `valres` is carried by
    the events themselves. -/
structure EventStructure where
  events : List Event
  po     : List (EventId × EventId)
  rmw    : List RMWEntry
  deriving Repr

/-- Binary relations over event ids. -/
abbrev Rel := EventId → EventId → Prop

/-- Sets of event ids. -/
abbrev EvSet := EventId → Prop

namespace Rel

def union (R S : Rel) : Rel := fun a b => R a b ∨ S a b
def comp (R S : Rel) : Rel := fun a c => ∃ b, R a b ∧ S b c
def inv (R : Rel) : Rel := fun a b => R b a
/-- `R_{∖X} ≜ R ∩ (E ∖ X)²` -/
def excl (R : Rel) (X : EvSet) : Rel := fun a b => R a b ∧ ¬ X a ∧ ¬ X b
/-- `R ∩ X²` -/
def restrict (R : Rel) (X : EvSet) : Rel := fun a b => R a b ∧ X a ∧ X b
def Subset (R S : Rel) : Prop := ∀ a b, R a b → S a b

/-- `R⁺` -/
abbrev plus (R : Rel) : Rel := Relation.TransGen R

/-- `R` is acyclic: `R⁺` is irreflexive. -/
def Acyclic (R : Rel) : Prop := ∀ a, ¬ Relation.TransGen R a a

theorem transGen_head {R : Rel} {a b c : EventId} (h : R a b)
    (h' : Relation.TransGen R b c) : Relation.TransGen R a c := by
  induction h' with
  | single hbc => exact .tail (.single h) hbc
  | tail _ hcd ih => exact .tail ih hcd

end Rel

/-- `Δ_X = {(x, x) | x ∈ X}` -/
def diag (X : EvSet) : Rel := fun a b => a = b ∧ X a

namespace EventStructure

def empty : EventStructure := ⟨[], [], []⟩

def ids (es : EventStructure) : List EventId := es.events.map (·.id)

/-- The event with a given id. -/
def ev (es : EventStructure) (id : EventId) : Option Event :=
  es.events.find? (·.id == id)

/-- `id ∈ E` -/
def inE (es : EventStructure) : EvSet := fun id => ∃ e ∈ es.events, e.id = id

/-- The ids of events satisfying a classifier, e.g. `es.cls Event.isWrite` is
    `W`. -/
def cls (es : EventStructure) (p : Event → Bool) : EvSet :=
  fun id => ∃ e, es.ev id = some e ∧ p e = true

/-- Program order `⊑` as a relation. -/
def poR (es : EventStructure) : Rel := fun a b => (a, b) ∈ es.po

/-- `iter(e)(ℓ)` for an event id. -/
def iterOf (es : EventStructure) (id : EventId) (ℓ : LoopId) : Option Nat :=
  (es.ev id).bind (·.iter ℓ)

/-- `thread(e)` for an event id. -/
def threadOf (es : EventStructure) (id : EventId) : Option ThreadId :=
  (es.ev id).map (·.thread)

end EventStructure
