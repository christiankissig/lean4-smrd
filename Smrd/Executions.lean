import Smrd.Types
import Smrd.Forwardingcontext
import Smrd.Ppo
import Smrd.Justifications

/-!
# Executions, Freezing and the Memory Model (Appendix A.6)

Executions `𝕏 = (X, J, rf)` (Definition `def:executions`), freezing
`freeze(X, J, rf) = (DP, ≼, φ)` (Definition `def:freeze`), the axioms
`No-Thin-Air` and `Coherence` of MRD+C11 (Paragraph `def:mem-model-axiom`), and
use-after-free (Definition `def:uaf`).

`Frozen` abstracts an execution to the events and dependency relations the
futures of Appendix A.7 are built from (`EpisodicLoops.Futures`, in
`lean4-episodic-loops`).
-/

/-- An execution `(X, J, rf)`; `rf w r` reads "`r` reads from `w`". -/
structure Execution where
  X  : EvSet
  J  : List Justification
  rf : Rel

namespace EventStructure

variable (es : EventStructure)

/-! ## Executions (Definition `def:executions`) -/

/-- Events are in conflict if their value restrictions are incompatible. -/
def Conflict (a b : EventId) : Prop :=
  ∃ ea eb, es.ev a = some ea ∧ es.ev b = some eb ∧
    ¬ Sat (Pred.and ea.valres.holds eb.valres.holds)

/-- The events an execution may contain: `E ∖ (B ∪ F)`. -/
def Candidate : EvSet := fun a =>
  es.inE a ∧ ¬ es.cls Event.isBranch a ∧ ¬ es.cls Event.isFence a

/-- A maximal conflict-free set `X ⊆ E ∖ (B ∪ F)`. -/
def MaximalConflictFree (X : EvSet) : Prop :=
  (∀ a, X a → es.Candidate a) ∧
  (∀ a b, X a → X b → ¬ es.Conflict a b) ∧
  (∀ a, es.Candidate a → ¬ X a → ∃ b, X b ∧ es.Conflict a b)

end EventStructure

namespace Execution

variable (es : EventStructure) (x : Execution)

/-- `δ_J = ⋃_{j ∈ J} δ_j` -/
def δ : FwdCtx := x.J.foldr (fun j δ => j.δ.union δ) .empty

/-- `† = π₁ WE`: the events elided by the shared forwarding context. -/
def elided : EvSet := fun e => ∃ p ∈ x.δ.we, p.1 = e

/-- `⋀_{e ∈ X} valres(e)` -/
def valresX : Pred := fun f => ∀ a e, x.X a → es.ev a = some e → e.valres.holds f

/-- `⋀_{j ∈ J} P_j` -/
def predJ : Pred := fun f => ∀ j ∈ x.J, j.P.holds f

/-- An execution in `es` under global guarantees `Ω`. -/
structure IsExecution (Ω : Pred) : Prop where
  maximal   : es.MaximalConflictFree x.X
  generated : ∀ j ∈ x.J, es.Generated Ω j
  inX       : ∀ j ∈ x.J, x.X j.w.id
  consistent : Sat (Pred.and (x.predJ) (x.valresX es))
  rf_wr     : ∀ w r, x.rf w r → es.cls Event.isWrite w ∧ es.cls Event.isRead r ∧ x.X w ∧ x.X r
  /-- each read reads from at most one write -/
  rf_func   : ∀ w w' r, x.rf w r → x.rf w' r → w = w'
  /-- every effectful event of `X` not elided is uniquely justified -/
  justified : ∀ w, x.X w → es.cls Event.isEffect w → ¬ x.elided w →
    ∃ j ∈ x.J, j.w.id = w ∧ ∀ j' ∈ x.J, j'.w.id = w → j' = j

/-- A complete execution: `rf` assigns a write to every read. -/
def IsComplete (Ω : Pred) : Prop :=
  x.IsExecution es Ω ∧ ∀ r, x.X r → es.cls Event.isRead r → ∃ w, x.rf w r

/-! ## Freezing (Definition `def:freeze`) -/

/-- `DP ≜ ⋃_{j ∈ J} {(origin α, w_j) | α ∈ symbols(P_j) ∪ symbols(D_j)}`,
    within `X`. -/
def DP : Rel := fun a b =>
  x.X a ∧ x.X b ∧ ∃ j ∈ x.J, j.w.id = b ∧ (a ∈ j.P.syms ∨ a ∈ j.D)

/-- `P ≜ ⋀_{j ∈ J} P_j ∧ ψ_{δ_j}` -/
def P : Pred := fun f => ∀ j ∈ x.J, j.P.holds f ∧ j.δ.psi es f

/-- `≼ ≜ ⋃_{j ∈ J} ≼^{P_j}_δ ∩ {e ∈ X | e ⊑ w_j ∨ e = w_j}²` -/
def ppo : Rel := fun a b =>
  ∃ j ∈ x.J, es.ppo j.P.holds x.δ a b ∧
    x.X a ∧ x.X b ∧
    (a = j.w.id ∨ es.poR a j.w.id) ∧ (b = j.w.id ∨ es.poR b j.w.id)

/-- Disjointness of memory locations: the location an allocation introduces is
    not a global, and differs from that of any other allocation unless a
    deallocation of `X` frees one of the two. The paper leaves the order of the
    "intermediate" deallocation unspecified; we ask for none at all. -/
def allocDisjoint : Pred := fun f =>
  (∀ a e α sz, x.X a → es.ev a = some e → e.kind = .alloc α sz →
      ∀ y o, f α ≠ .loc ⟨.global y, o⟩) ∧
  (∀ a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂, x.X a₁ → x.X a₂ → a₁ ≠ a₂ →
    es.ev a₁ = some e₁ → es.ev a₂ = some e₂ →
    e₁.kind = .alloc α₁ s₁ → e₂.kind = .alloc α₂ s₂ →
    (¬ ∃ d ed l, x.X d ∧ es.ev d = some ed ∧ ed.kind = .dealloc l ∧
        (l.eval f = some (f α₁) ∨ l.eval f = some (f α₂))) →
    f α₁ ≠ f α₂)

/-- `φ_rf`: equal locations and values along `rf`, and disjoint allocations. -/
def phiRf : Pred := fun f =>
  (∀ w r ew er, x.rf w r → es.ev w = some ew → es.ev r = some er →
    (∀ lw lr, ew.loc = some lw → er.loc = some lr → lw.eval f = lr.eval f) ∧
    (∀ vw vr, ew.val = some vw → er.val = some vr → vw.eval f = vr.eval f)) ∧
  x.allocDisjoint es f

/-- `φ ≜ (π₁(rf ∪ DP) ∩ † = ∅) ∧ (π₂(rf) = X ∩ R) ∧ (P ∧ φ_rf ≢ ⊥)` -/
def phi : Prop :=
  (∀ e, ((∃ r, x.rf e r) ∨ (∃ b, x.DP e b)) → ¬ x.elided e) ∧
  (∀ r, (∃ w, x.rf w r) ↔ (x.X r ∧ es.cls Event.isRead r)) ∧
  Sat (Pred.and (x.P es) (x.phiRf es))

/-! ## Axiomatic memory consistency model -/

/-- The intra-thread dependency order `≼ ∪ DP`. -/
def dep : Rel := (x.ppo es).union (x.DP)

/-- `nta ≜ (DP ∪ ≼ ∪ rf)⁺` -/
def nta : Rel := Rel.plus ((x.dep es).union x.rf)

/-- `No-Thin-Air`: `DP ∪ ≼ ∪ rf` is acyclic. -/
def NoThinAir : Prop := Rel.Acyclic ((x.dep es).union x.rf)

/-- Two writes at the same location under the frozen predicate. -/
def sameLoc (a b : EventId) : Prop :=
  ∃ ea eb la lb, es.ev a = some ea ∧ es.ev b = some eb ∧
    ea.loc = some la ∧ eb.loc = some lb ∧ EquivUnder (x.P es) la lb

/-- A coherence order: a strict order on the writes of `X`, total on the writes
    to each location. -/
structure CoherenceOrder (co : Rel) : Prop where
  writes : ∀ a b, co a b → x.X a ∧ x.X b ∧ es.cls Event.isWrite a ∧ es.cls Event.isWrite b
  irrefl : ∀ a, ¬ co a a
  trans  : ∀ a b c, co a b → co b c → co a c
  total  : ∀ a b, x.X a → x.X b → es.cls Event.isWrite a → es.cls Event.isWrite b →
    a ≠ b → x.sameLoc es a b → co a b ∨ co b a

/-- `SW ≜ rf ∩ (W_rel × R_acq)` -/
def sw : Rel := fun w r => x.rf w r ∧ es.cls Event.isRelW w ∧ es.cls Event.isAcqR r

/-- `FR ≜ rf⁻¹ ; CO` -/
def fr (co : Rel) : Rel := fun r w' => ∃ w, x.rf w r ∧ co w w'

/-- `ECO ≜ (rf ∪ CO ∪ FR)⁺` -/
def eco (co : Rel) : Rel := Rel.plus ((x.rf.union co).union (x.fr co))

/-- `HB ≜ (DP ∪ ≼ ∪ SW)⁺` -/
def hb : Rel := Rel.plus ((x.dep es).union (x.sw es))

/-- `Coherence`: `ECO ∪ HB` is acyclic for some coherence order. -/
def Coherent : Prop :=
  ∃ co, x.CoherenceOrder es co ∧ Rel.Acyclic ((x.eco co).union (x.hb es))

/-- A consistent execution of MRD+C11. -/
def Consistent (Ω : Pred) : Prop :=
  x.IsExecution es Ω ∧ x.phi es ∧ x.NoThinAir es ∧ x.Coherent es

/-! ## Use-after-free (Definition `def:uaf`) -/

/-- `𝕏` exhibits a use-after-free under a model with no-thin-air order
    `nta_M`: an access `a` of the location a deallocation `d` frees, with
    `(a, d) ∉ nta_M`. The locations are compared under the frozen constraints
    `P ∧ φ_rf`. -/
def UseAfterFree (ntaM : Rel) : Prop :=
  ∃ d a ed ea ld la, x.X d ∧ x.X a ∧ es.ev d = some ed ∧ es.ev a = some ea ∧
    ed.kind = .dealloc ld ∧ (ea.isRead ∨ ea.isWrite) ∧ ea.loc = some la ∧
    EquivUnder (Pred.and (x.P es) (x.phiRf es)) la ld ∧ ¬ ntaM a d

end Execution

/-! ## Frozen executions -/

/-- The events of an execution with its frozen dependency relations. -/
structure Frozen where
  X   : EvSet
  ppo : Rel
  DP  : Rel

/-- `≼ ∪ DP` -/
def Frozen.dep (F : Frozen) : Rel := F.ppo.union F.DP

def Execution.frozen (es : EventStructure) (x : Execution) : Frozen :=
  ⟨x.X, x.ppo es, x.DP⟩
