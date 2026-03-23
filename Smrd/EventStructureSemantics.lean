import Smrd.Types

/-!
# Event Structure Semantics of Program Statements

This file defines the denotational semantics of program statements as event
structures, following the OCaml interpreter in `interpret.ml`.

## Design

Statements are interpreted as **continuations**: each statement form takes a
*continuation* event structure (the semantics of the remaining statements) and
produces a new event structure by prefixing or combining events.

The three core combinators mirror `SymbolicEventStructure` in OCaml:

- `dot e k φ`    — sequential prefix: add event `e` before continuation `k`
                   under path condition `φ` (OCaml: `dot event' cont phi`)
- `plus s1 s2`   — non-deterministic choice (OCaml: `plus s1 s2`)
- `cross s1 s2`  — parallel composition, disjoint-union then combine PO/RMW
                   (OCaml: `cross s1 s2`)

## Step-Counter Semantics

A single global step counter `n : ℕ` is threaded through interpretation.
When `n = 0` the semantics of any loop is the empty event structure (no
events, no edges).  For `n > 0`, each loop body unrolling decrements `n` by
one and recurses.  This gives a **global** step counter shared across all
sequential and nested loops, matching the `per_loop = false` branch of
`interpret_statements_step_counter` in OCaml.

## Statements

```
stmt ::= skip
       | store(loc, val, ord)          -- global/deref store
       | load(reg, loc, ord)           -- global/deref load
       | regStore(reg, expr)           -- register assignment
       | fence(ord)
       | lock | unlock
       | malloc(reg, size)
       | free(reg)
       | fadd(reg, loc, operand, rmode, wmode)   -- fetch-and-add RMW
       | cas(reg, loc, expected, desired, rmode, wmode) -- CAS RMW
       | if(cond, thenBody, elseBody)
       | while(cond, body)
       | do(body, cond)
       | seq(s1, s2)                   -- sequential composition
       | par(s1, s2)                   -- parallel composition
```
-/

/-! ## Preliminary: fresh-id monad -/

/-- State for the event-ID generator. -/
structure GenState : Type where
  nextId : Nat
  deriving Repr

/-- A simple state monad carrying `GenState`. -/
def Gen (α : Type) : Type := GenState → α × GenState

instance : Monad Gen where
  pure a := fun s => (a, s)
  bind m f := fun s =>
    let (a, s') := m s
    f a s'

/-- Allocate a fresh event id. -/
def freshId : Gen Nat := fun s => (s.nextId, { nextId := s.nextId + 1 })

/-- Run a `Gen` computation starting from id 0. -/
def Gen.run (m : Gen α) : α := (m { nextId := 0 }).1

/-! ## Statement syntax -/

/-- A program statement (shallow embedding). -/
inductive Stmt : Type where
  /-- No-op. -/
  | skip : Stmt
  /-- Store `val` to memory location `loc` with ordering `ord`. -/
  | store  (loc val : Expr) (ord : MemOrd) : Stmt
  /-- Load from memory location `loc` into result symbol `result` with ordering
      `ord`. -/
  | load   (loc : Expr) (result : Symbol) (ord : MemOrd) : Stmt
  /-- Register assignment: bind `sym` to the evaluated `expr` in the
      environment.  Produces no event. -/
  | regStore (sym : Symbol) (expr : Expr) : Stmt
  /-- Memory fence. -/
  | fence  (ord : MemOrd) : Stmt
  /-- Acquire a lock (optional variable name). -/
  | lock   (global : Option Symbol) : Stmt
  /-- Release a lock (optional variable name). -/
  | unlock (global : Option Symbol) : Stmt
  /-- Heap allocation: result symbol receives the fresh address. -/
  | malloc (result : Symbol) (size : Expr) : Stmt
  /-- Heap deallocation of the address held in `ptr`. -/
  | free   (ptr : Expr) : Stmt
  /-- Fetch-and-add RMW: atomically read, add `operand`, and write back. -/
  | fadd   (result : Symbol) (loc operand : Expr)
           (rmode wmode : MemOrd) : Stmt
  /-- Compare-and-swap RMW: atomically compare, conditionally swap. -/
  | cas    (result : Symbol) (loc expected desired : Expr)
           (rmode wmode : MemOrd) : Stmt
  /-- Conditional: `if cond then thenBody else elseBody`. -/
  | ite    (cond : BoolExpr) (thenBody elseBody : Stmt) : Stmt
  /-- While loop: `while cond do body`. -/
  | whileLoop  (cond : BoolExpr) (body : Stmt) : Stmt
  /-- Do-while loop: `do body while cond`. -/
  | doLoop     (body : Stmt) (cond : BoolExpr) : Stmt
  /-- Sequential composition. -/
  | seq    (s1 s2 : Stmt) : Stmt
  /-- Parallel composition (concurrently running threads). -/
  | par    (s1 s2 : Stmt) : Stmt
  deriving Repr

/-! ## Event structure combinators -/

/-- The empty event structure (unit for `plus`; used when step counter = 0). -/
def EventStructure.empty : EventStructure :=
  { events := [], po := [], rmw := [] }

/-- Collect all event ids in an event structure. -/
def EventStructure.ids (es : EventStructure) : List Nat :=
  es.events.map (·.id)

/-- Sequential prefix: prepend event `e` before `k`.

    Concretely:
    - Add `e` to the event set.
    - Add a PO edge `(e.id, init)` for every *minimal* event of `k` (those with
      no incoming PO edge from within `k`).
    - Inherit all other events, PO edges, and RMW triples from `k`.

    This mirrors `SymbolicEventStructure.dot event' cont phi defacto` in OCaml.
    The path condition `phi` and de-facto constraints influence validity
    conditions in the full model; here we attach them via `valRest` on the
    event.  We assume the caller has already set `e.valRest` appropriately.
-/
def EventStructure.dot (e : Event) (k : EventStructure) : EventStructure :=
  -- Minimal events of k: those not the target of any PO edge in k.
  let kTargets := k.po.map (·.2)
  let kMinimal := k.ids.filter (fun id => !kTargets.contains id)
  -- New PO edges from e to every minimal event of k.
  let newPO    := kMinimal.map (fun id => (e.id, id))
  { events := e :: k.events
    po     := newPO ++ k.po
    rmw    := k.rmw }

/-- Non-deterministic choice: disjoint union of two event structures.

    Both `s1` and `s2` are possible executions; their event ids must be disjoint
    (ensured by the fresh-id monad).  Mirrors `SymbolicEventStructure.plus`.
-/
def EventStructure.plus (s1 s2 : EventStructure) : EventStructure :=
  { events := s1.events ++ s2.events
    po     := s1.po     ++ s2.po
    rmw    := s1.rmw    ++ s2.rmw }

/-- Parallel composition: disjoint union with no additional PO between threads.

    Threads run concurrently so we simply take the union of events, PO
    (per-thread), and RMW.  Mirrors `SymbolicEventStructure.cross`.
-/
def EventStructure.cross (s1 s2 : EventStructure) : EventStructure :=
  { events := s1.events ++ s2.events
    po     := s1.po     ++ s2.po
    rmw    := s1.rmw    ++ s2.rmw }

/-- Add an RMW triple to an event structure. -/
def EventStructure.addRMW (es : EventStructure) (r : RMWEntry) : EventStructure :=
  { es with rmw := r :: es.rmw }

/-! ## Step-counter semantics -/

/-- Evaluate a `BoolExpr` as a validity restriction `BoolExpr`.
    For the semantics we simply propagate it unchanged; in a full model this
    would be conjoined with the existing `valRest`. -/
def mkEvent (id : Nat) (kind : EventKind) (valRest : BoolExpr) : Event :=
  { id, kind, valRest }

/-- Evaluate an `Expr` under an `Env`, returning `Expr.lit 0` on failure. -/
def evalExpr (env : Env) (e : Expr) : Expr :=
  match e.eval env with
  | some v => .lit v
  | none   => e   -- keep symbolic if unevaluable

/-- Evaluate a `BoolExpr` under an `Env`, returning `BoolExpr.top` on failure. -/
def evalBool (env : Env) (b : BoolExpr) : BoolExpr :=
  match b.eval env with
  | some true  => .top
  | some false => .bot
  | none       => b

/-- Extend the `Env` with a new binding. -/
def envBind (env : Env) (s : Symbol) (v : Int) : Env :=
  (s, v) :: env.filter (·.1 != s)

/-! ## Sequential append of two event structures

`appendES es1 es2` sequences `es1` before `es2`: every maximal event of
`es1` gets a PO edge to every minimal event of `es2`.  This is the
multi-event generalisation of `dot`.
-/

/-- Returns the set of *maximal* event ids: those with no outgoing PO edge
    within `es`. -/
private def maximalIds (es : EventStructure) : List Nat :=
  let sources := es.po.map (·.1)
  es.ids.filter (fun id => !sources.contains id)

/-- Returns the set of *minimal* event ids: those with no incoming PO edge
    within `es`. -/
private def minimalIds (es : EventStructure) : List Nat :=
  let targets := es.po.map (·.2)
  es.ids.filter (fun id => !targets.contains id)

/-- Sequentially append `es2` after `es1`. -/
private def appendES (es1 es2 : EventStructure) : EventStructure :=
  let newPO := (maximalIds es1).flatMap
                 (fun src => (minimalIds es2).map (fun tgt => (src, tgt)))
  { events := es1.events ++ es2.events
    po     := es1.po ++ newPO ++ es2.po
    rmw    := es1.rmw ++ es2.rmw }

/-- Interpret a statement as an event structure with global step counter `n`.

    Parameters:
    - `n`   : global step counter (shared across all loops).
    - `env` : current register / symbol environment.
    - `phi` : current path condition (conjunction of `BoolExpr`s).
    - `stmt`: the statement to interpret.

    Returns a `Gen EventStructure` so that every event allocation gets a fresh
    unique id.

    **Step-counter rule for loops** (global, matching `per_loop = false` in OCaml):
    - If `n = 0`: return `EventStructure.empty` (no iterations).
    - Otherwise: unroll the loop one step (consume one unit from `n`),
      recursively interpret the continuation with `n - 1`.
-/
def interpStmt (n : Nat) (env : Env) (phi : List BoolExpr) :
    Stmt → Gen EventStructure
  -- ------------------------------------------------------------------ skip
  | .skip =>
      pure EventStructure.empty

  -- -------------------------------------------------------- register store
  -- No event emitted; bind the evaluated expression in the environment and
  -- return the empty structure (the caller must supply the continuation via
  -- `seq`).
  | .regStore _sym _expr =>
      -- Register stores are pure environment updates; they produce no events.
      pure EventStructure.empty

  -- ----------------------------------------------------------------- store
  | .store loc val ord => do
      let id ← freshId
      let evt := mkEvent id (.write (evalExpr env loc) (evalExpr env val) ord)
                          (phi.foldl (fun acc b => .and acc b) .top)
      pure (EventStructure.dot evt EventStructure.empty)

  -- ------------------------------------------------------------------ load
  | .load loc result ord => do
      let id ← freshId
      let evt := mkEvent id (.read (evalExpr env loc) result ord)
                          (phi.foldl (fun acc b => .and acc b) .top)
      pure (EventStructure.dot evt EventStructure.empty)

  -- ----------------------------------------------------------------- fence
  | .fence ord => do
      let id ← freshId
      let evt := mkEvent id (.fence ord)
                          (phi.foldl (fun acc b => .and acc b) .top)
      pure (EventStructure.dot evt EventStructure.empty)

  -- ------------------------------------------------------------------ lock
  | .lock _global => do
      let id ← freshId
      let evt := mkEvent id .lock
                          (phi.foldl (fun acc b => .and acc b) .top)
      pure (EventStructure.dot evt EventStructure.empty)

  -- ---------------------------------------------------------------- unlock
  | .unlock _global => do
      let id ← freshId
      let evt := mkEvent id .unlock
                          (phi.foldl (fun acc b => .and acc b) .top)
      pure (EventStructure.dot evt EventStructure.empty)

  -- ---------------------------------------------------------------- malloc
  | .malloc result size => do
      let id ← freshId
      let evt := mkEvent id (.allocate result (evalExpr env size))
                          (phi.foldl (fun acc b => .and acc b) .top)
      pure (EventStructure.dot evt EventStructure.empty)

  -- ------------------------------------------------------------------ free
  | .free ptr => do
      let id ← freshId
      let evt := mkEvent id (.deallocate (evalExpr env ptr))
                          (phi.foldl (fun acc b => .and acc b) .top)
      pure (EventStructure.dot evt EventStructure.empty)

  -- -------------------------------------------------------------- fadd RMW
  -- Fetch-and-add: emit a Read followed by a Write, linked by an RMW triple.
  | .fadd result loc operand rmode wmode => do
      let rId ← freshId
      let wId ← freshId
      let locE    := evalExpr env loc
      let opE     := evalExpr env operand
      -- The written value is (loaded_symbol + operand); kept symbolic here.
      let wvalE   : Expr := .add (.var result) opE
      let valCond := phi.foldl (fun acc b => .and acc b) .top
      let rEvt    := mkEvent rId (.read  locE result rmode) valCond
      let wEvt    := mkEvent wId (.write locE wvalE  wmode) valCond
      -- Build: rEvt → wEvt (sequential)
      let inner   := EventStructure.dot rEvt
                       (EventStructure.dot wEvt EventStructure.empty)
      -- Add RMW triple (unconditional CAS condition = top)
      let rmwEntry : RMWEntry := { readId := rId, cond := .top, writeId := wId }
      pure (inner.addRMW rmwEntry)

  -- --------------------------------------------------------------- CAS RMW
  -- Compare-and-swap: emit a Read; on success (cond) emit a Write linked by RMW,
  -- on failure skip.  The two branches are joined with `plus`.
  | .cas result loc expected desired rmode wmode => do
      let rId ← freshId
      let wId ← freshId
      let locE  := evalExpr env loc
      let expE  := evalExpr env expected
      let desE  := evalExpr env desired
      let valCond := phi.foldl (fun acc b => .and acc b) .top
      -- Read event
      let rEvt  := mkEvent rId (.read locE result rmode) valCond
      -- Condition: loaded value = expected  (expressed as a BoolExpr)
      let cond  : BoolExpr := .eq (.var result) expE
      -- Success branch: write + RMW
      let wEvt  := mkEvent wId (.write locE desE wmode) (.and valCond cond)
      let succStr := (EventStructure.dot wEvt EventStructure.empty).addRMW
                       { readId := rId, cond := cond, writeId := wId }
      -- Failure branch: no write, path-conditioned on ¬cond
      let failStr := EventStructure.empty
      -- Combine: Read → (succ ⊕ fail)
      let inner   := EventStructure.plus succStr failStr
      pure (EventStructure.dot rEvt inner)

  -- --------------------------------------------------------------- if-then-else
  | .ite cond thenBody elseBody => do
      let condE   := evalBool env cond
      let ncondE  : BoolExpr := .neg condE
      -- Branch event
      let brId ← freshId
      let valCond := phi.foldl (fun acc b => .and acc b) .top
      let brEvt   := mkEvent brId (.branch condE) valCond
      -- Then / else branches with extended path conditions
      let thenStr ← interpStmt n env (condE  :: phi) thenBody
      let elseStr ← interpStmt n env (ncondE :: phi) elseBody
      let branches := EventStructure.plus thenStr elseStr
      pure (EventStructure.dot brEvt branches)

  -- ------------------------------------------------------------ while loop
  -- Global step-counter rule:
  --   n = 0  →  empty (no iterations)
  --   n > 0  →  if cond then (body; while cond body) else skip,
  --             with step counter n - 1 for the recursive while.
  | .whileLoop cond body =>
      match n with
      | 0     => pure EventStructure.empty
      | n' + 1 => do
          let condE  := evalBool env cond
          let ncondE : BoolExpr := .neg condE
          let brId ← freshId
          let valCond := phi.foldl (fun acc b => .and acc b) .top
          let brEvt   := mkEvent brId (.branch condE) valCond
          -- Loop body followed by the recursive while (step counter n')
          let bodyStr  ← interpStmt n' env (condE  :: phi) body
          let recStr   ← interpStmt n' env (condE  :: phi) (.whileLoop cond body)
          -- Exit branch
          let exitStr  := EventStructure.empty
          -- then-arm: body ; while  (sequential: body dots into recStr)
          let thenArm  := appendES bodyStr recStr
          let branches := EventStructure.plus thenArm exitStr
          pure (EventStructure.dot brEvt branches)

  -- ------------------------------------------------------------- do-while loop
  -- Global step-counter rule:
  --   n = 0  →  empty
  --   n > 0  →  body ; if cond then (do body while cond) else skip,
  --             with step counter n - 1 for the recursive do.
  | .doLoop body cond =>
      match n with
      | 0     => pure EventStructure.empty
      | n' + 1 => do
          -- Execute the body unconditionally first.
          let bodyStr ← interpStmt n' env phi body
          -- Then check the condition.
          let condE  := evalBool env cond
          let ncondE : BoolExpr := .neg condE
          let brId ← freshId
          let valCond := phi.foldl (fun acc b => .and acc b) .top
          let brEvt   := mkEvent brId (.branch condE) valCond
          -- Continue branch: recursive do-while
          let recStr  ← interpStmt n' env (condE :: phi) (.doLoop body cond)
          -- Exit branch: empty
          let exitStr := EventStructure.empty
          let branches := EventStructure.plus recStr exitStr
          let contStr  := EventStructure.dot brEvt branches
          pure (appendES bodyStr contStr)

  -- ------------------------------------------------------- sequential composition
  | .seq s1 s2 => do
      let es1 ← interpStmt n env phi s1
      let es2 ← interpStmt n env phi s2
      pure (appendES es1 es2)

  -- ---------------------------------------------------- parallel composition
  | .par s1 s2 => do
      let es1 ← interpStmt n env phi s1
      let es2 ← interpStmt n env phi s2
      pure (EventStructure.cross es1 es2)

/-! ## Top-level interpretation entry point -/

/-- Interpret a statement with a given global step counter.

    Equivalent to `StepCounterSemantics.interpret ~step_counter` in OCaml
    (with `per_loop = false`).

    @param n     Global step counter: maximum number of loop-body unrollings
                 across the entire program.
    @param stmt  The program statement to interpret.
    @return      The event structure denoting the program.
-/
def interpProgram (n : Nat) (stmt : Stmt) : EventStructure :=
  Gen.run (interpStmt n [] [] stmt)

/-! ## Convenience: interpret with explicit environment and path condition -/

/-- Like `interpProgram` but with an initial environment and path condition. -/
def interpProgramWith (n : Nat) (env : Env) (phi : List BoolExpr) (stmt : Stmt) :
    EventStructure :=
  Gen.run (interpStmt n env phi stmt)

/-! ## Small examples (sanity checks) -/

section Examples

/-- A single store to a global variable `x`. -/
private def exStore : Stmt :=
  .store (.var "x") (.lit 42) .seqcst

#eval interpProgram 1 exStore

/-- A load followed by a store (a simple read-then-write). -/
private def exLoadStore : Stmt :=
  .seq (.load (.var "x") "α" .acquire) (.store (.var "x") (.var "α") .release)

#eval interpProgram 1 exLoadStore

/-- A while loop bounded by step counter 3. -/
private def exWhile : Stmt :=
  .whileLoop (.lt (.var "i") (.lit 10))
    (.store (.var "i") (.add (.var "i") (.lit 1)) .none)

#eval interpProgram 3 exWhile

/-- A do-while loop bounded by step counter 2. -/
private def exDo : Stmt :=
  .doLoop
    (.store (.var "i") (.add (.var "i") (.lit 1)) .none)
    (.lt (.var "i") (.lit 5))

#eval interpProgram 2 exDo

/-- A simple CAS: attempt to swap x from 0 to 1. -/
private def exCAS : Stmt :=
  .cas "r" (.var "x") (.lit 0) (.lit 1) .acquire .release

#eval interpProgram 1 exCAS

end Examples
