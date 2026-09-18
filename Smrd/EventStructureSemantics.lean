import Smrd.Types

/-!
# Event Structure Semantics of Programs

Appendix A.2 of the paper: program syntax (Definition `def:prog-syntax`,
Figure `fig:grammar`), the interpretation of program expressions against a
register state (Definition `def:prog-expr-sem`), and the event structure
semantics `⟨P⟩_{n ρ κ φ}` (Definition `def:gen-es`) with per-loop
step-counters (Paragraph "The step-counter per loop").

The semantics is in continuation-passing style, as in the paper:

* `ρ` is the register state, mapping registers to expressions over symbols;
* `κ` is the continuation, mapping a register state and a value restriction
  to the event structure interpreting the tail of the program;
* `φ` accumulates the branching outcomes on the path, and becomes the value
  restriction `valres` of each event generated.

The branches of an `if`, and the two outcomes of a `cas`, each invoke the
continuation, so events after a join are generated once per path, with
distinct ids and value restrictions, as the paper requires for conflict to be
carried by `valres` alone.

## Deviations from the paper

* **Strict program order.** The prefix `e[φ]·𝔼` of the paper adds
  `{e} × ({e} ∪ E)` to `⊑`, making `⊑` reflexive. We add `{e} × E` only. With
  the reflexive pairs, `⊑ ; Δ_{W_rel,sc}` would contain `(w, w)` for every
  releasing write, so `≼_sync` would not be irreflexive as Appendix A.2 claims,
  `≼_alias` would contain `(e, e)` for every access, and `No-Thin-Air` would
  fail for every execution containing an access.
* **Loop identifiers** are part of the `while` syntax, as the paper assumes
  in Section 3.1.
* **Dereferences** occur only as the pointer of `r := *e` and `*e₁ := e₂`.
  The grammar of Definition `def:expressions` admits `*e` inside arithmetic
  expressions, but Definition `def:gen-es` gives it no semantics there.
* The branching event of an `if` carries the value restriction `φ` of its
  context; the paper writes it without one.
* An unassigned register reads as `0`.
-/

/-! ## Program expressions and syntax -/

/-- Program expressions (Definition `def:expressions`), over registers. -/
inductive PExpr where
  | reg (r : Reg)
  | num (n : Nat)
  | bin (op : ArithOp) (a b : PExpr)
  | eq  (a b : PExpr)
  | le  (a b : PExpr)
  | not (a : PExpr)
  | and (a b : PExpr)
  | or  (a b : PExpr)
  deriving Repr, DecidableEq

/-- Register states `ρ : Registers → Expressions`. -/
abbrev RegState := List (Reg × Expr)

def RegState.get (ρ : RegState) (r : Reg) : Expr := (ρ.lookup r).getD (Expr.num 0)

/-- `ρ[r ↦ e]` -/
def RegState.set (ρ : RegState) (r : Reg) (e : Expr) : RegState := (r, e) :: ρ

/-- `⟦e⟧_ρ`: resolve the registers of a program expression
    (Definition `def:prog-expr-sem`). -/
def PExpr.den (ρ : RegState) : PExpr → Expr
  | .reg r      => ρ.get r
  | .num n      => .num n
  | .bin op a b => .bin op (a.den ρ) (b.den ρ)
  | .eq a b     => .eq (a.den ρ) (b.den ρ)
  | .le a b     => .le (a.den ρ) (b.den ρ)
  | .not a      => .not (a.den ρ)
  | .and a b    => .and (a.den ρ) (b.den ρ)
  | .or a b     => .or (a.den ρ) (b.den ρ)

/-- Programs (Figure `fig:grammar`). -/
inductive Stmt where
  | skip
  | seq      (s₁ s₂ : Stmt)
  | par      (s₁ s₂ : Stmt)
  | ite      (b : PExpr) (s₁ s₂ : Stmt)
  | while    (ℓ : LoopId) (b : PExpr) (body : Stmt)
  /-- `r := e` -/
  | assign   (r : Reg) (e : PExpr)
  /-- `r :=_o x` -/
  | load     (o : MemOrd) (r : Reg) (x : Var)
  /-- `x :=_o e` -/
  | store    (o : MemOrd) (x : Var) (e : PExpr)
  /-- `r := &x` -/
  | addrOf   (r : Reg) (x : Var)
  /-- `r :=_o *e` -/
  | loadPtr  (o : MemOrd) (r : Reg) (e : PExpr)
  /-- `*e₁ :=_o e₂` -/
  | storePtr (o : MemOrd) (e₁ e₂ : PExpr)
  | fence    (o : MemOrd)
  /-- `r := FADD^{o_r,o_w}(x, e)` -/
  | fadd     (or ow : MemOrd) (r : Reg) (x : Var) (e : PExpr)
  /-- `r := CAS^{o_r,o_w}(x, e₁, e₂)` -/
  | cas      (or ow : MemOrd) (r : Reg) (x : Var) (e₁ e₂ : PExpr)
  /-- `r := malloc(e)` -/
  | malloc   (r : Reg) (e : PExpr)
  /-- `free(r)` -/
  | free     (r : Reg)
  deriving Repr

/-- The loop identifiers occurring in a program, with multiplicity. -/
def Stmt.loops : Stmt → List LoopId
  | .seq s₁ s₂ | .par s₁ s₂ | .ite _ s₁ s₂ => s₁.loops ++ s₂.loops
  | .while ℓ _ body => ℓ :: body.loops
  | _ => []

/-! ## Event structure combinators -/

namespace EventStructure

/-- The prefix `e[φ_e] · (E, ⊑, ⊑ʳᵐʷ, valres)`; the value restriction is
    carried by `e`. Program order is strict, see the module header. -/
def «prefix» (e : Event) (k : EventStructure) : EventStructure :=
  { events := e :: k.events
    po     := k.events.map (fun e' => (e.id, e'.id)) ++ k.po
    rmw    := k.rmw }

/-- The coproduct `𝔼₁ + 𝔼₂`. Disjointness of the events is ensured by the
    fresh-id generator. -/
def plus (s₁ s₂ : EventStructure) : EventStructure :=
  ⟨s₁.events ++ s₂.events, s₁.po ++ s₂.po, s₁.rmw ++ s₂.rmw⟩

/-- `rmw(𝔼, e_r, e_w, b)` -/
def addRMW (es : EventStructure) (r : EventId) (b : Expr) (w : EventId) : EventStructure :=
  { es with rmw := ⟨r, b, w⟩ :: es.rmw }

end EventStructure

/-! ## Generation state, contexts and step-counters -/

structure GenState where
  nextId     : EventId := 0
  nextThread : ThreadId := 1
  deriving Repr

/-- Fresh event ids, and so fresh symbols, and fresh thread ids. -/
abbrev Gen := StateM GenState

def freshId : Gen EventId :=
  modifyGet fun s => (s.nextId, { s with nextId := s.nextId + 1 })

def freshThread : Gen ThreadId :=
  modifyGet fun s => (s.nextThread, { s with nextThread := s.nextThread + 1 })

/-- The part of a control label fixed by the context: the thread, and the
    iterations of the enclosing loops, outermost first. -/
structure Ctx where
  thread : ThreadId
  iter   : List (LoopId × Nat)
  deriving Repr

/-- Enter iteration `k` of loop `ℓ`. -/
def Ctx.enter (ctx : Ctx) (ℓ : LoopId) (k : Nat) : Ctx :=
  if ctx.iter.any (·.1 == ℓ) then
    { ctx with iter := ctx.iter.map fun p => if p.1 = ℓ then (ℓ, k) else p }
  else
    { ctx with iter := ctx.iter ++ [(ℓ, k)] }

/-- Per-loop step-counters, a map from loop indices to bounds. -/
abbrev Bounds := LoopId → Nat

/-- The uniform choice `⟨P⟩_n`, assigning the bound `n` to every loop. -/
def Bounds.uniform (k : Nat) : Bounds := fun _ => k

/-- Decrement the component of loop `ℓ` only. -/
def Bounds.dec (n : Bounds) (ℓ : LoopId) : Bounds :=
  fun m => if m = ℓ then n m - 1 else n m

/-- Sum of the bounds of a list of loops: the termination measure. -/
def sumB (ls : List LoopId) (n : Bounds) : Nat := (ls.map n).sum

theorem sumB_append (a b : List LoopId) (n : Bounds) :
    sumB (a ++ b) n = sumB a n + sumB b n := by
  induction a with
  | nil => simp [sumB]
  | cons m a ih => simp only [sumB, List.map_cons, List.cons_append, List.sum_cons] at *; omega

theorem sumB_cons (ℓ : LoopId) (ls : List LoopId) (n : Bounds) :
    sumB (ℓ :: ls) n = n ℓ + sumB ls n := by
  simp [sumB]

theorem Bounds.dec_le (n : Bounds) (ℓ m : LoopId) : n.dec ℓ m ≤ n m := by
  unfold Bounds.dec; split <;> omega

theorem Bounds.dec_self (n : Bounds) (ℓ : LoopId) : n.dec ℓ ℓ = n ℓ - 1 := by
  simp [Bounds.dec]

theorem sumB_dec_le (ls : List LoopId) (n : Bounds) (ℓ : LoopId) :
    sumB ls (n.dec ℓ) ≤ sumB ls n := by
  induction ls with
  | nil => simp [sumB]
  | cons m ls ih =>
      rw [sumB_cons, sumB_cons]
      have := Bounds.dec_le n ℓ m
      omega

/-- Continuations `κ`. -/
abbrev Cont := RegState → List Guard → Gen EventStructure

/-- Generate an event with a fresh id at program counter `pc` under the value
    restriction `φ`. The action may mention the event's own id, which is the
    symbol a read or allocation introduces. -/
def mkEvent (ctx : Ctx) (pc : List Nat) (φ : List Guard)
    (kind : EventId → EventKind) : Gen Event := do
  let id ← freshId
  pure { id, kind := kind id, label := ⟨ctx.thread, pc, ctx.iter⟩, guards := φ }

/-! ## The semantics `⟨P⟩_{n ρ κ φ}` (Definition `def:gen-es`) -/

open EventStructure in
/-- `⟨s⟩_{n ρ κ φ}` in context `ctx` at program counter `pc`. -/
def interp (n : Bounds) (ctx : Ctx) (pc : List Nat) (s : Stmt) (ρ : RegState)
    (κ : Cont) (φ : List Guard) : Gen EventStructure :=
  match s with
  | .skip => κ ρ φ
  | .assign r e => κ (ρ.set r (e.den ρ)) φ
  | .addrOf r x => κ (ρ.set r (Expr.glob x)) φ
  | .load o r x => do
      let e ← mkEvent ctx pc φ (fun α => .read o (Expr.glob x) α)
      let k ← κ (ρ.set r (.sym e.id)) φ
      pure («prefix» e k)
  | .loadPtr o r p => do
      let e ← mkEvent ctx pc φ (fun α => .read o (p.den ρ) α)
      let k ← κ (ρ.set r (.sym e.id)) φ
      pure («prefix» e k)
  | .store o x v => do
      let e ← mkEvent ctx pc φ (fun _ => .write o (Expr.glob x) (v.den ρ))
      let k ← κ ρ φ
      pure («prefix» e k)
  | .storePtr o p v => do
      let e ← mkEvent ctx pc φ (fun _ => .write o (p.den ρ) (v.den ρ))
      let k ← κ ρ φ
      pure («prefix» e k)
  | .fence o => do
      let e ← mkEvent ctx pc φ (fun _ => .fence o)
      let k ← κ ρ φ
      pure («prefix» e k)
  | .malloc r sz => do
      let e ← mkEvent ctx pc φ (fun α => .alloc α (sz.den ρ))
      let k ← κ (ρ.set r (.sym e.id)) φ
      pure («prefix» e k)
  | .free r => do
      let e ← mkEvent ctx pc φ (fun _ => .dealloc (ρ.get r))
      let k ← κ ρ φ
      pure («prefix» e k)
  | .fadd or ow r x v => do
      let er ← mkEvent ctx (pc ++ [0]) φ (fun α => .read or (Expr.glob x) α)
      let ew ← mkEvent ctx (pc ++ [1]) φ
        (fun _ => .write ow (Expr.glob x) (.bin .add (.sym er.id) (v.den ρ)))
      let k ← κ (ρ.set r (.sym er.id)) φ
      pure ((«prefix» er («prefix» ew k)).addRMW er.id Expr.tt ew.id)
  | .cas or ow r x e₁ e₂ => do
      let er ← mkEvent ctx (pc ++ [0]) φ (fun α => .read or (Expr.glob x) α)
      let c : Expr := .eq (.sym er.id) (e₁.den ρ)
      let ec ← mkEvent ctx (pc ++ [1]) φ (fun _ => .branch c)
      let φT := φ ++ [⟨ec.id, c, true⟩]
      let φF := φ ++ [⟨ec.id, c, false⟩]
      let ew ← mkEvent ctx (pc ++ [2]) φT (fun _ => .write ow (Expr.glob x) (e₂.den ρ))
      let kT ← κ (ρ.set r Expr.tt) φT
      let kF ← κ (ρ.set r Expr.ff) φF
      pure ((«prefix» er («prefix» ec ((«prefix» ew kT).plus kF))).addRMW er.id c ew.id)
  | .seq s₁ s₂ =>
      interp n ctx (pc ++ [0]) s₁ ρ (fun ρ' φ' => interp n ctx (pc ++ [1]) s₂ ρ' κ φ') φ
  | .par s₁ s₂ => do
      let t ← freshThread
      let k₁ ← interp n ctx (pc ++ [0]) s₁ ρ κ φ
      let k₂ ← interp n { ctx with thread := t } (pc ++ [1]) s₂ ρ κ φ
      pure (k₁.plus k₂)
  | .ite b s₁ s₂ => do
      let c := b.den ρ
      let eb ← mkEvent ctx pc φ (fun _ => .branch c)
      let k₁ ← interp n ctx (pc ++ [0]) s₁ ρ κ (φ ++ [⟨eb.id, c, true⟩])
      let k₂ ← interp n ctx (pc ++ [1]) s₂ ρ κ (φ ++ [⟨eb.id, c, false⟩])
      pure («prefix» eb (k₁.plus k₂))
  | .while ℓ b body =>
      -- `⟨while b P⟩ ≜ ∅` once the component of `ℓ` is exhausted, and otherwise
      -- `⟨if b then (P; while b P) else skip⟩` with that component decremented.
      if h : n ℓ = 0 then pure .empty else do
        let k := match ctx.iter.lookup ℓ with
          | some j => j + 1
          | none   => 0
        let ctx' := ctx.enter ℓ k
        let c := b.den ρ
        let eb ← mkEvent ctx' pc φ (fun _ => .branch c)
        let kT ← interp (n.dec ℓ) ctx' (pc ++ [0]) body ρ
          (fun ρ' φ' => interp (n.dec ℓ) ctx' pc (.while ℓ b body) ρ' κ φ')
          (φ ++ [⟨eb.id, c, true⟩])
        let kF ← κ ρ (φ ++ [⟨eb.id, c, false⟩])
        pure («prefix» eb (kT.plus kF))
termination_by sumB s.loops n + sizeOf s
decreasing_by
  all_goals simp only [Stmt.loops, sumB_append, sumB_cons, Stmt.seq.sizeOf_spec,
    Stmt.par.sizeOf_spec, Stmt.ite.sizeOf_spec, Stmt.while.sizeOf_spec]
  all_goals first
    | omega
    | (have := sumB_dec_le body.loops n ℓ
       have := Bounds.dec_self n ℓ
       omega)

/-- `⟨P⟩_{n ∅ (λρ φ. ∅) ⊤}`: the event structure of a program under the
    per-loop step-counters `n`. -/
def denote (n : Bounds) (P : Stmt) : EventStructure :=
  (interp n ⟨0, []⟩ [] P [] (fun _ _ => pure .empty) []).run' {}

/-!
## Monotonicity in the step-counter (Lemma `l:es-mono`)

Proved in `Smrd.Monotonicity` (`denote_mono`), up to a renaming of event ids
and threads, as the events of `⟨P⟩_n` and `⟨P⟩_{n+1}` are identified here by
ids allocated in generation order rather than by control label. Note that under
per-loop step-counters the base case of the paper's proof, "`𝔼₀` is empty",
does not hold: `⟨P⟩_0` contains every event before the first loop, as only
`while` is cut off at a zero bound.
-/

/-! ## Examples -/

section Examples

/-- `x :=_sc 42` -/
private def exStore : Stmt := .store .sc "x" (.num 42)

#eval (denote (.uniform 1) exStore).events.length

/-- `r :=_acq x; x :=_rel r` -/
private def exLoadStore : Stmt :=
  .seq (.load .acq "r" "x") (.store .rel "x" (.reg "r"))

#eval denote (.uniform 1) exLoadStore

/-- `while₁ (r < 10) { r :=_rlx x }`, unravelled twice. -/
private def exWhile : Stmt :=
  .while 1 (.not (.le (.num 10) (.reg "r"))) (.load .rlx "r" "x")

#eval (denote (.uniform 2) exWhile).events.map (fun e => (e.id, e.label.iter))

/-- `r := CAS^{acq,rel}(x, 0, 1); y :=_rlx 1`: the store after the `cas` is
    generated once per outcome. -/
private def exCAS : Stmt :=
  .seq (.cas .acq .rel "r" "x" (.num 0) (.num 1)) (.store .rlx "y" (.num 1))

#eval (denote (.uniform 1) exCAS).events.map (fun e => (e.id, e.label.pc, e.guards.length))

end Examples
