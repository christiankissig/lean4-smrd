import Smrd.Types
import Smrd.Forwardingcontext
import Smrd.Ppo
import Smrd.PpoMordor
import Smrd.Justifications

/-!
# Executions, Freezing and the Memory Model (Appendix A.6)

Executions `𝕏 = (X, J, rf)` (Definition `def:executions`), freezing
`freeze(X, J, rf) = (DP, ≼, φ)` (Definition `def:freeze`), the axioms
`No-Thin-Air`, `Coherence` and `Atomicity` of MRD+C11 (Paragraph
`def:mem-model-axiom`), and use-after-free (Definition `def:uaf`).

`Coherent` asks for one coherence order under which both `Coherence` and
`Atomicity` hold, as the paper's axioms share `CO`.

## Deviations from the paper

* **Same location** (`sameLoc`, and so `⊑|loc`, `RS`, `SW`, `HB` and the
  totality of `CO`) compares locations under `P ∧ φ_rf`, the constraints of
  the execution (as use-after-free does, under `φ`), where the paper's `⊑|loc`
  takes `≡_P`; and it compares them as partial values, so that it is
  transitive and contains `rf` without further hypotheses.

`Frozen` abstracts an execution to the events and dependency relations the
futures of Appendix A.7 are built from.
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

/-- `† = π₂(F ∪ WE)`: the events `remap_δ` moves, the forwarded event of each
    forwarding and the earlier, shadowed write of each write elision (stored
    as `(e₂, e₁)`, see `Generated.we`). -/
def elided : EvSet := fun e => ∃ p, (p ∈ x.δ.f ∨ p ∈ x.δ.we) ∧ p.2 = e

/-- `†` is the set of events with an `F ∪ WE`-predecessor, those that
    `remap_δ` does not fix by its second case. -/
theorem elided_iff (e : EventId) : x.elided e ↔ ∃ a, x.δ.edge a e := by
  constructor
  · rintro ⟨⟨a, b⟩, h, rfl⟩; exact ⟨a, h⟩
  · rintro ⟨a, h⟩; exact ⟨(a, e), h, rfl⟩

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
  /-- the shared forwarding context is well-formed (`def:fwd-ctx`) -/
  fwdWF     : x.δ.WF
  rf_wr     : ∀ w r, x.rf w r → es.cls Event.isWrite w ∧ es.cls Event.isRead r ∧ x.X w ∧ x.X r
  /-- each read reads from at most one write -/
  rf_func   : ∀ w w' r, x.rf w r → x.rf w' r → w = w'
  /-- every effectful event of `X` not elided is uniquely justified; of the
      elided events only writes are effectful, so the exemption reaches
      writes only, and forwarded reads still need an `rf` (`phi`) -/
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

/-- `X_F ≜ {f ∈ E ∩ F | X ∪ {f} conflict-free}`: the fences on the branches
    `X` takes. An execution holds no fences (`Candidate`), but `⊑`, `SW` and
    `HB` range over `X ∪ X_F`. -/
def XF : EvSet := fun f =>
  es.inE f ∧ es.cls Event.isFence f ∧ ∀ a, x.X a → ¬ es.Conflict a f

/-- `X ∪ X_F` -/
def XwF : EvSet := fun a => x.X a ∨ x.XF es a

/-! ### Preserved program order

`≼` is MoRDor's frozen `ppo` (`Execution.ppo`, below). The paper's truncated `≼`
of Definition `def:freeze`, which is also sMRD's (Richards et al., Def. 4.9),
is kept as `ppoTrunc`, and MoRDor's own truncation of its `ppo` to the
justification windows (its experiment mode `MORDOR_PPO_TRUNC=paper`) as
`ppoWin`. -/

/-- The paper's `≼` (Definition `def:freeze`, sMRD Def. 4.9), truncated at the
    justification windows:
    `≼_trunc ≜ ⋃_{j ∈ J} ≼^{P_j}_δ ∩ {e ∈ X | e ⊑ w_j ∨ e = w_j}²`. -/
def ppoTrunc : Rel := fun a b =>
  ∃ j ∈ x.J, es.ppo j.P.holds x.δ a b ∧
    x.X a ∧ x.X b ∧
    (a = j.w.id ∨ es.poR a j.w.id) ∧ (b = j.w.id ∨ es.poR b j.w.id)

/-- The justification window of `j`, `{e | e ⊑ w_j ∨ e = w_j}`. -/
def Win (j : Justification) : EvSet := fun e => e = j.w.id ∨ es.poR e j.w.id

/-- Both events lie in one justification window. -/
def InWin (a b : EventId) : Prop := ∃ j ∈ x.J, Win es j a ∧ Win es j b

/-- MoRDor's combined predicate `p_combined` (`Freeze.prepare`),
    `⋀_{j ∈ J} P_j ∧ ψ_δ ∧ ⋀_{e ∈ X} valres(e)`, with the shared context's `ψ`.
    MoRDor's `path.p` takes the value restrictions of every event of the path,
    fences and its terminal events included; its `statex` (allocation
    disjointness) has no counterpart, see `ppo`. -/
def Pm : Pred := fun f => (∀ j ∈ x.J, j.P.holds f) ∧ x.δ.psi es f ∧ x.valresX es f

/-- The alias predicate of a justification's part, `P_j ∧ ψ_δ`. -/
def PJ (j : Justification) : Pred := Pred.and j.P.holds (x.δ.psi es)

/-- MoRDor's `ppos`: each justification's `ForwardingContext.ppo` under `P_j`,
    cut to its window. -/
def ppoJ : Rel := fun a b =>
  ∃ j ∈ x.J, es.ppoM (x.PJ es j) j.P.holds x.δ a b ∧ Win es j a ∧ Win es j b

/-- Both events lie at or `⊑`-below one event of the path `X ∪ X_F`:
    `∃ e ∈ X ∪ X_F. (a ⊑ e ∨ a = e) ∧ (b ⊑ e ∨ b = e)`. sMRD's windows
    `{e | e ⊑ w_j ∨ e = w_j}` (Def. 4.9) anchor the same cut at the justified
    writes only. Parallel composition has no join, so an anchored pair lies
    within one thread's `⊑`-down-set (and its sequential prefix). -/
def Anchored (a b : EventId) : Prop :=
  ∃ e, x.XwF es e ∧ (a = e ∨ es.poR a e) ∧ (b = e ∨ es.poR b e)

/-- The relation `freeze_ppo` closes: the per-justification parts, and the
    remapped `ppo_sync` and `ppo_loc` under `p_combined` cut to `Anchored`
    pairs, restricted to the path `X ∪ X_F`. -/
def ppoStep : Rel := fun a b =>
  x.XwF es a ∧ x.XwF es b ∧
    (x.ppoJ es a b ∨ ((es.ppoSyncRM x.δ a b ∨ es.ppoLocM (x.Pm es) x.δ a b) ∧ x.Anchored es a b))

/-- **`≼`, MoRDor's frozen `ppo`** (`mordor/src/executions.ml`, `Freeze.freeze_ppo`,
    MoRDor branch `ppo-anchor`):

    `≼ ≜ X² ∩ (⊑-path ∩ (⋃_{j ∈ J} ≼^{P_j ∧ ψ_δ, P_j}_δ ∩ W_j² ∪
    (remap_δ(ppo_sync) ∪ ppo_loc^{P_m}_δ) ∩ A))⁺`,

    with `W_j = {e | e ⊑ w_j ∨ e = w_j}` (`Win`), `A` the pairs at or
    `⊑`-below one event of the path, `A = ⋃_{e ∈ X ∪ X_F} {c | c ⊑ e ∨ c = e}²`
    (`Anchored`), `P_m` MoRDor's `p_combined` (`Pm`), the templates of
    `Smrd.PpoMordor`, and the path `X ∪ X_F`.

    Differences from Definition `def:freeze` (and sMRD Def. 4.9, the same
    union):

    1. `≼_sync` and `≼_loc` are cut, after remapping, to `A` instead of to the
       windows `W_j²`: sMRD's window mechanism anchored at every event of the
       path instead of only at the justified writes. The pairs after a
       thread's last justified write are kept (MoRDor's DEPARTURES F1: the
       thread's tail, which CoRR and MP need), while the pairs remapping moves
       across threads are dropped, since parallel composition has no join and
       no event of the path lies `⊑`-above events of two threads.
    2. The union is restricted to the path and closed transitively; the paper's
       is neither. The closure runs through fences, whose pairs are in
       `ppo_sync`, before `≼` is restricted to `X`.
    3. The templates are MoRDor's (`Smrd.PpoMordor`): `ppo_sync` has no
       fence-crossing summand and keeps fence endpoints; locations equal
       outright are ordered whatever the predicate; `ppo_loc` filters again by
       aliasing.
    4. Alias queries are under `P_j ∧ ψ_δ` (as sMRD's `≼^δ_P` has `ψ_δ`), and
       `ppo_loc`'s under `p_combined`, which adds the value restrictions of the
       path. The paper's are under `P_j`.
    5. Every part is remapped under the shared context `δ` (MoRDor's
       justifications carry the shared `fwd`/`we` by `remap_just`).

    Before the cut (MoRDor commit 6dd8521) the uncut parts were remapped
    across threads: an initialising write `⊑`-before every thread, elided by
    one thread's write, moved its pairs with the other threads onto that
    write (`x := 0; (x := 1 ∥ x := 2)`, `Smrd.PpoNecessity.ppo_cross_thread`,
    now the positive result), and `SB+sc` with both initialising writes
    elided had a cyclic `≼`. With the cut every step of `≼` relates
    `⊑`-comparable events, and without forwarding it lies in `⊑` where no
    elision crosses an event (`Smrd.PpoTail`, `ppoStep_po_we`).

    MoRDor's parts that have no counterpart here: the `Init` event `0` and the
    `Terminal` events with `ppo_init` (`0` before, and the terminal events
    after, every event of the path) -- a source and sinks of the relation
    closed, so they add no pair between other events; the value restrictions
    `path.p` carries only through fences or terminal events (a branch at the
    end of a thread with no event after it); and `statex`, the allocation
    disjointness MoRDor conjoins to `p_combined` (here allocation disjointness
    is in `φ_rf`, which depends on `≼` through `nta`, and cannot be conjoined
    to the predicate `≼` is computed under). -/
def ppo : Rel := fun a b => x.X a ∧ x.X b ∧ Relation.TransGen (x.ppoStep es) a b

/-- MoRDor's `ppoStep` cut to the justification windows. -/
def ppoWinStep : Rel := fun a b =>
  x.XwF es a ∧ x.XwF es b ∧
    (x.ppoJ es a b ∨ ((es.ppoSyncRM x.δ a b ∨ es.ppoLocM (x.Pm es) x.δ a b) ∧ x.InWin es a b))

/-- MoRDor's `ppo` with every part cut to the justification windows
    (MoRDor's experiment mode `MORDOR_PPO_TRUNC=paper`, branch
    `ppo-trunc-experiment`), the analogue of the paper's truncation over
    MoRDor's templates. -/
def ppoWin : Rel := fun a b => x.X a ∧ x.X b ∧ Relation.TransGen (x.ppoWinStep es) a b

/-- The intra-thread dependency order `≼ ∪ DP`. -/
def dep : Rel := (x.ppo es).union (x.DP)

/-- `nta ≜ (DP ∪ ≼ ∪ rf)⁺` -/
def nta : Rel := Rel.plus ((x.dep es).union x.rf)

/-- A deallocation `d ∈ X` frees the location `f α` of an allocation. -/
def Frees (f : Valuation) (d : EventId) (α : Sym) : Prop :=
  ∃ ed l, x.X d ∧ es.ev d = some ed ∧ ed.kind = .dealloc l ∧ l.eval f = some (f α)

/-- A deallocation `d` of the location of an allocation (symbol `α`) is
    *intermediate* for it and a second allocation `a'` if it is not ordered
    after `a'`, `(a', d) ∉ (DP ∪ ≼ ∪ rf)⁺`. The condition is negative: an
    allocator may hand a released region back to another thread without the
    program ordering the deallocation before the allocation (C11 7.22.3p2). -/
def Intermediate (f : Valuation) (d : EventId) (α : Sym) (a' : EventId) : Prop :=
  x.Frees es f d α ∧ ¬ x.nta es a' d

/-- Disjointness of memory locations: the location an allocation introduces is
    not a global, and differs from that of any other allocation unless `X`
    contains a deallocation of one of the two locations that is intermediate
    for it and the other.

    Not yet in the paper, nor here: the synchronisation edge `(d, a')` of the
    allocator, which would enter `SW`, and so `HB`, where `a'` reuses the
    location `d` frees. -/
def allocDisjoint : Pred := fun f =>
  (∀ a e α sz, x.X a → es.ev a = some e → e.kind = .alloc α sz →
      ∀ y o, f α ≠ .loc ⟨.global y, o⟩) ∧
  (∀ a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂, x.X a₁ → x.X a₂ → a₁ ≠ a₂ →
    es.ev a₁ = some e₁ → es.ev a₂ = some e₂ →
    e₁.kind = .alloc α₁ s₁ → e₂.kind = .alloc α₂ s₂ →
    (¬ ∃ d, x.Intermediate es f d α₁ a₂ ∨ x.Intermediate es f d α₂ a₁) →
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

/-- `No-Thin-Air`: `DP ∪ ≼ ∪ rf` is acyclic. -/
def NoThinAir : Prop := Rel.Acyclic ((x.dep es).union x.rf)

/-- Two events at the same location under the execution's own constraints,
    the frozen `P` together with `φ_rf`: their locations evaluate alike, to
    one value or to none, under every model of `P ∧ φ_rf`.

    Deviations from the paper, whose `⊑|loc` compares under `≡_P`: the
    constraints include `φ_rf`, which equates the locations along `rf` (as
    use-after-free compares under `φ`), so `rf ⊆ sameLoc`
    (`Execution.rfLoc`); and the locations are compared as partial values,
    `⟦loc(a)⟧_f = ⟦loc(b)⟧_f`, rather than by `EquivUnder`, which holds
    vacuously where either side fails to evaluate. So `sameLoc` is symmetric
    and transitive outright (`Execution.sameLoc_trans`); where the locations
    evaluate under every model the two agree (`sameLoc_iff_equivUnder`). -/
def sameLoc (a b : EventId) : Prop :=
  ∃ ea eb la lb, es.ev a = some ea ∧ es.ev b = some eb ∧
    ea.loc = some la ∧ eb.loc = some lb ∧
    ∀ f, x.P es f → x.phiRf es f → la.eval f = lb.eval f

/-- A coherence order: a strict order on the writes of `X`, total on the writes
    to each location. -/
structure CoherenceOrder (co : Rel) : Prop where
  writes : ∀ a b, co a b → x.X a ∧ x.X b ∧ es.cls Event.isWrite a ∧ es.cls Event.isWrite b
  irrefl : ∀ a, ¬ co a a
  trans  : ∀ a b c, co a b → co b c → co a c
  total  : ∀ a b, x.X a → x.X b → es.cls Event.isWrite a → es.cls Event.isWrite b →
    a ≠ b → x.sameLoc es a b → co a b ∨ co b a

/-- `FR ≜ rf⁻¹ ; CO` -/
def fr (co : Rel) : Rel := fun r w' => ∃ w, x.rf w r ∧ co w w'

/-- `ECO ≜ (rf ∪ CO ∪ FR)⁺` -/
def eco (co : Rel) : Rel := Rel.plus ((x.rf.union co).union (x.fr co))

/-- `⊑` within `X ∪ X_F`. -/
def poX : Rel := fun a b => x.XwF es a ∧ x.XwF es b ∧ es.poR a b

/-- `⊑|loc ≜ {(e₁, e₂) ∈ ⊑ | loc(e₁) ≡_P loc(e₂)}`, with `≡` as `sameLoc`
    (under `P ∧ φ_rf`). -/
def poloc : Rel := fun a b => x.poX es a b ∧ x.sameLoc es a b

/-- `rmw ≜ {(e_r, e_w) ∈ X × X | (e_r, c, e_w) ∈ ⊑ʳᵐʷ ∧ c ≡_P ⊤}`: the read
    and the write of each read-modify-write operation that writes in the
    execution, every `FADD` and a `CAS` on its succeeding branch, with `P` the
    frozen predicate. -/
def rmwRel : Rel := fun r w =>
  x.X r ∧ x.X w ∧ ∃ ent ∈ es.rmw, ent.r = r ∧ ent.w = w ∧ EquivUnder (x.P es) ent.cond Expr.tt

/-- `rf ; rmw`: from a write to the write of an RMW that reads from it. -/
def rfRmw : Rel := fun a b => ∃ r, x.rf a r ∧ x.rmwRel es r b

/-- `RS ≜ [W] ; ⊑|loc? ; [W_rlx,rel,sc] ; (rf ; rmw)*`. Every write is atomic
    here, as the fragment has no non-atomic accesses. -/
def rs : Rel := fun w w' =>
  es.cls Event.isWrite w ∧ ∃ w₀, (w₀ = w ∨ x.poloc es w w₀) ∧
    es.cls Event.isWrite w₀ ∧ (w' = w₀ ∨ Rel.plus (x.rfRmw es) w₀ w')

/-- `SW ≜ [W_rel,sc ∪ F_rel,sc] ; ([F] ; ⊑)? ; RS ; rf ; [R_rlx,acq,sc] ;
    (⊑ ; [F])? ; [R_acq,sc ∪ F_acq,sc]`, RC11's synchronises-with. -/
def sw : Rel := fun a b =>
  (es.cls Event.isRelW a ∨ es.cls Event.isRelF a) ∧
  ∃ w w' r, (w = a ∨ (es.cls Event.isFence a ∧ x.poX es a w)) ∧ x.rs es w w' ∧
    x.rf w' r ∧ es.cls Event.isRead r ∧
    (b = r ∨ (x.poX es r b ∧ es.cls Event.isFence b)) ∧
    (es.cls Event.isAcqR b ∨ es.cls Event.isAcqF b)

/-- `HB ≜ (⊑ ∪ SW)⁺`, RC11's happens-before. -/
def hb : Rel := Rel.plus ((x.poX es).union (x.sw es))

/-- The `Coherence` axiom for a coherence order: `HB ; ECO?` is irreflexive,
    RC11's coherence axiom (Axiom `def:mem-model-axiom:co`). It asks for
    coherence per location relative to `HB`, and not that `ECO ∪ HB` be
    acyclic, which would make the model multi-copy atomic. -/
def Coherence (co : Rel) : Prop :=
  ∀ a, ¬ ∃ b, x.hb es a b ∧ (b = a ∨ x.eco co b a)

/-- `HB|loc ≜ HB ∩ L`: `HB` restricted to pairs at the same location, where `L`
    relates events at the same location. -/
def hbLoc (L : Rel) : Rel := fun a b => x.hb es a b ∧ L a b

/-- If `L` is symmetric and transitive and contains `rf` and `CO`, then each
    `rf ∪ CO ∪ FR` edge `(a, b)` is matched by `L b a`. -/
theorem eco1_loc {co L : Rel} (symm : ∀ a b, L a b → L b a)
    (trans : ∀ a b c, L a b → L b c → L a c)
    (hrf : ∀ a b, x.rf a b → L a b) (hco : ∀ a b, co a b → L a b) :
    ∀ a b, ((x.rf.union co).union (x.fr co)) a b → L b a := by
  rintro a b ((h | h) | ⟨w, hw, hc⟩)
  · exact symm _ _ (hrf _ _ h)
  · exact symm _ _ (hco _ _ h)
  · exact trans _ _ _ (symm _ _ (hco _ _ hc)) (hrf _ _ hw)

/-- `HB ; (rf ∪ CO ∪ FR)` is irreflexive iff `HB|loc ; (rf ∪ CO ∪ FR)` is, as
    long as `rf ∪ CO ∪ FR` relates only events at the same location (for
    example, by `eco1_loc`). -/
theorem hb_eco1_irrefl_iff_hbLoc {co L : Rel}
    (hL : ∀ a b, ((x.rf.union co).union (x.fr co)) a b → L b a) :
    (∀ a, ¬ ∃ b, x.hb es a b ∧ ((x.rf.union co).union (x.fr co)) b a) ↔
    (∀ a, ¬ ∃ b, x.hbLoc es L a b ∧ ((x.rf.union co).union (x.fr co)) b a) := by
  constructor
  · rintro h a ⟨b, ⟨hab, _⟩, hba⟩
    exact h a ⟨b, hab, hba⟩
  · rintro h a ⟨b, hab, hba⟩
    exact h a ⟨b, ⟨hab, hL b a hba⟩, hba⟩

/-- The `Atomicity` axiom for a coherence order: `rmw ∩ (FR ; CO) = ∅`. No
    write to the location falls `CO`-between the write the read of an RMW
    takes and the write of the same RMW. -/
def Atomicity (co : Rel) : Prop :=
  ∀ r w, x.rmwRel es r w → ¬ ∃ w', x.fr co r w' ∧ co w' w

/-- `Coherence` and `Atomicity` under one coherence order. -/
def Coherent : Prop :=
  ∃ co, x.CoherenceOrder es co ∧ x.Coherence es co ∧ x.Atomicity es co

/-- A consistent execution of MRD+C11. -/
def Consistent (Ω : Pred) : Prop :=
  x.IsExecution es Ω ∧ x.phi es ∧ x.NoThinAir es ∧ x.Coherent es

/-! ## Use-after-free (Definition `def:uaf`) -/

/-- RC11's order for use-after-free, `(⊑ ∪ rf)⁺`, with `⊑` within `X ∪ X_F`.
    RC11's no-load-buffering axiom makes `⊑ ∪ rf` acyclic, so an access is
    ordered before a deallocation exactly when this order relates them; it
    takes the place of sMRD's `nta` in `UseAfterFree` when the verdict is
    RC11's. -/
def ntaRC11 : Rel := Rel.plus ((x.poX es).union x.rf)

/-- RC11's no-thin-air axiom (its "no load buffering"): `⊑ ∪ rf` is acyclic,
    with `⊑` within `X ∪ X_F`. sMRD replaces `⊑` by `DP ∪ ≼` (`NoThinAir`), which
    is what admits load buffering. -/
def NoThinAirRC11 : Prop := Rel.Acyclic ((x.poX es).union x.rf)

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
