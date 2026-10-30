import Smrd.Types
import Smrd.Forwardingcontext
import Smrd.Ppo
import Smrd.Conjuncts

/-!
# Justifications (Appendix A.3–A.5)

Justifications `j : (P, D) ⊢^δ w` of effectful events (Definition `def:justs`),
the forwarding relations (`def:fwd-rels`), closed relabel-equivalence
(`def:rel-eq`), and the generation of the justification set `𝕁` from
pre-justifications by the elaborations Value Assignment, Strengthening,
Forwarding, Write Elision, Lifting and Weakening (`def:gen-just`).

The stages `𝕁₀ ⊆ 𝕁₁ ⊆ …` of the paper are collapsed into one inductive
predicate `Generated`, whose derivations are the elements of `⋃ᵢ 𝕁ᵢ`.

## Representation choices

* The justified event `w` is a *copy* of an event of `𝔼`, carrying its own
  location and value expressions. The paper matches a copy to its event by
  control label; since elaborations change neither, we match it by the event
  id, which the copy keeps.
* `D` and the symbols of a set of events coincide, as symbols are the ids of
  the events introducing them (`symbols(D) = D` on symbol-introducing events).
* The environment `g = [val(e₂) ↦ val(e₁)]` of Forwarding replaces the
  expression `val(e₂)`, which for store-store forwarding is the value written
  and not a symbol (`Expr.replace`).
* The origins `e ∈ S` of Strengthening are required to be `⊑`-before `w`
  strictly: a reflexive reading would put `(w, w)` into `DP` for an allocation
  constraining its own symbol.

## Deviations from the paper

* Strengthening introduces origins `⊑`-before the justified write only,
  `e ⊑ w ∧ w ⋠ e`, the reading of sMRD's prose (Richards et al., §4.7: "We
  restrict P′ to predicates where all symbols are visible to the justified
  write"). sMRD's formal Def. 4.11, and the paper's `def:elab-str`, also admit
  `w ⊑ e`, which gives `DP` edges that run against `⊑`. Under the restriction
  every origin of a dependency precedes its write (`Smrd.DPPast`,
  `Execution.dp_po`), up to store-store forwarding from beyond the write.

* Lifting asks every symbol of the relabelled premise `⟦P₁⟧_Λ` to have its
  origin `⊑`-before the lifted write `w₂`. Closed relabel-equivalence
  constrains `Λ` on `D₁` only, so a symbol of `P₁` outside `D₁` -- a guard on
  `w₁`'s path, or a Strengthening conjunct -- may keep an origin in another
  thread than `w₂`, or `⊑`-after it, and the lifted justification then has a
  `DP` edge against `⊑`, within an execution (`Smrd.LiftCross`). The paper's
  `def:elab-lift` admits it. MoRDor's Lifting does not produce it: it lifts
  only writes in conflict, and only when `P₂` has the negation of each
  conjunct of `⟦P₁⟧_Λ` it does not share
  (`LiftElab.find_distinguishing_predicate`), so the symbols of `⟦P₁⟧_Λ` are
  symbols of `P₂`.

* Neither access of an RMW is in the elided position (`RMWAcc`, MoRDor
  `docs/DEPARTURES.md` E4): not the forwarded event `e₂` of a Forwarding
  (`fwdRel`), not the elided write `e₁` of a Write Elision (`weRel`). An RMW
  access may still be a source. Elided events leave the execution
  (`Execution.CoherenceT`, `X ∖ †`): eliding an RMW's write turns the RMW
  into a plain read and a later store, about which Atomicity says nothing
  (`Smrd.RMWElision`). Hence `Generated.not_rmwAcc_elided`. The paper's
  `def:fwd-rels` does not exclude them yet (Todoist 6hpW3hjc4W2839jX).
* Write Elision carries MoRDor's release restriction (`weNoRel`, MoRDor #207):
  a releasing write is elided only into a releasing write, and no release
  write, release or `sc` fence, or `sc` read lies `⊑`-between the two. The
  paper's Write Elision is blind to the memory order (`weRelBlind`). The
  restriction is what lets coherence leave elided writes out
  (`Execution.CoherenceT`, `Smrd.CoherenceT`).
* Forwarding carries MoRDor's acquire restriction (`fwdNoAcq`, MoRDor #210,
  `ForwardElab.forwarding_blocked` under `MORDOR_FWD_SYNC=acq`): no event that
  acquires (acquire or `sc` read or fence) lies `⊑`-between the source `e₁`
  and the forwarded event `e₂`; an acquire (`sc`) read is forwarded only from
  an acquire (`sc`) read; and an `sc` event is not forwarded across an `sc`
  event. Every kind of forwarding hoists `e₂` up to `e₁`, and an access does
  not move above an acquire (it may move above a release). The paper's
  Forwarding is blind to the memory order (`fwdRelBlind`). Without the
  restriction `CoherenceT` admits an outcome RC11 forbids
  (`Smrd.FwdAcrossAcquire`); with it, the remapped `ppo_sync` has no backward
  pair even with forwarding (`Execution.ppoSyncRM_po_T`).
* Forwarding and Write Elision carry a join restriction (`fwdNoJoin`,
  `weNoJoin`): `remap_δ` moves the forwarded event onto its source, and the
  elided write onto the eliding one, and the move must keep `⊑`-comparable
  every event comparable with the moved one where the two have a common upper
  bound (`NoJoinMove`). Forwarding does not reach across the join of a
  parallel block, from a thread (or from before the block) into the code after
  it; Write Elision does not move a write from before a parallel block into
  one of its threads when the threads join again. Without it `≼` relates
  `⊑`-incomparable events of two threads below the join
  (`Smrd.FwdAcrossJoin`). MoRDor generates neither across a join in those
  programs. Where `⊑` is a forest the restriction is vacuous
  (`Execution.fwdNoJoin_of_poForest`, `Execution.weNoJoin_of_poForest`).
-/

/-- A justification `j : (P, D) ⊢^δ w`. -/
structure Justification where
  P : Expr
  D : List EventId
  δ : FwdCtx
  w : Event
  deriving Repr

/-- A relabelling `Λ : Symbols ⇀ Symbols`. -/
abbrev Relabelling := Sym → Option Sym

/-- `⟦α⟧_Λ` -/
def Relabelling.app (Λ : Relabelling) (α : Sym) : Sym := (Λ α).getD α

/-- `Λ` is one-to-one on its domain. -/
def Relabelling.Injective (Λ : Relabelling) : Prop :=
  ∀ a b c, Λ a = some c → Λ b = some c → a = b

/-- The pre-justification of an effectful event, `𝕁₀`:
    `(valres(w), origin x ∪ origin e) ⊢^{(∅,∅)} (w : W x e)`,
    `(valres(a), origin e) ⊢^{(∅,∅)} (a : A α e)`, and
    `(valres(d), origin e) ⊢^{(∅,∅)} (d : D e)`. The symbol an allocation
    introduces is not among its dependencies. -/
def preJust (w : Event) : Option Justification :=
  match w.kind with
  | .write _ x e _ => some ⟨w.valres, x.syms ++ e.syms, .empty, w⟩
  | .alloc _ e   => some ⟨w.valres, e.syms, .empty, w⟩
  | .dealloc e   => some ⟨w.valres, e.syms, .empty, w⟩
  | _            => none

namespace Event

/-- MoRDor's `publishes` (`ForwardElab.publishes`): an event that makes the
    stores `⊑`-before it visible to a thread synchronising with it, or orders
    them in `psc` -- a write or fence of mode release or stronger, or an `sc`
    read, `W_{rel,sc} ∪ F_{rel,sc} ∪ R_sc`. (MoRDor's `Unlock` has no
    counterpart here.) -/
def publishes (e : Event) : Bool :=
  match e.kind with
  | .write o .. => o.isRelSc
  | .fence o => o.isRelSc
  | .read .sc .. => true
  | _ => false

/-- MoRDor's `acquires` (`ForwardElab.acquires`): an event that orders the
    events `⊑`-after it after what it synchronises with, a read or fence of
    mode acquire or stronger, `R_{acq,sc} ∪ F_{acq,sc}`. (MoRDor's `Lock` has
    no counterpart here.) -/
def acquires (e : Event) : Bool := e.isAcqR || e.isAcqF

/-- MoRDor's `is_sc`: an `sc` access or fence. -/
def isSc (e : Event) : Bool :=
  match e.kind with
  | .read .sc .. => true
  | .write .sc .. => true
  | .fence .sc => true
  | _ => false

/-- `R_sc` -/
def isScR (e : Event) : Bool := match e.kind with | .read .sc .. => true | _ => false

end Event

namespace EventStructure

variable (es : EventStructure)

/-- An RMW access: the read or the write of an entry of `⊑ʳᵐʷ`. -/
def RMWAcc (c : EventId) : Prop := ∃ ent ∈ es.rmw, ent.r = c ∨ ent.w = c

instance (c : EventId) : Decidable (es.RMWAcc c) :=
  inferInstanceAs (Decidable (∃ ent ∈ es.rmw, ent.r = c ∨ ent.w = c))

theorem not_rmwAcc_of_nil (h : es.rmw = []) (c : EventId) : ¬ es.RMWAcc c := by
  rintro ⟨ent, hm, -⟩; rw [h] at hm; cases hm

/-! ## Forwarding relations (Definition `def:fwd-rels`) -/

/-- `e₁ -F'_j→ e₂ ≜ e₁ ∈ pred_δ(e₂, P) ∧ e₁ ⊑ e₂ ∧ loc(e₁) ≡_{P ∧ ψ_δ} loc(e₂)`.

    `e₁ ⊑ e₂` (in the program order of the event structure, not after
    `remap_δ`) is explicit here. In sMRD as published `≼ ⊆ ⊑`, so `pred` is
    `⊑`-before and the condition is implied; here `≼` is computed after
    `remap_δ`, which can relate events of different threads (eliding `x := 0`
    into `x := 1` makes `x := 1` an immediate `≼`-predecessor of a read of `x`
    in another thread), and Forwarding and Write Elision would then forward
    across threads. MoRDor likewise cuts forwarding to the window of the
    justified write (`docs/DEPARTURES.md` E4). -/
def fwdBase (j : Justification) (e₁ e₂ : EventId) : Prop :=
  es.pred j.δ e₂ j.P.holds e₁ ∧ es.poR e₁ e₂ ∧
    ∃ ev₁ ev₂ l₁ l₂, es.ev e₁ = some ev₁ ∧ es.ev e₂ = some ev₂ ∧
      ev₁.loc = some l₁ ∧ ev₂.loc = some l₂ ∧
      EquivUnder (Pred.and j.P.holds (j.δ.psi es)) l₁ l₂

/-- The conditions of Forwarding blind to the memory order: store forwarding
    `W × R_rlx`, store-store forwarding `W × W_rlx`, and load forwarding
    `R × R`, where the forwarded event `e₂` is not a volatile access,
    `e₂ ∉ 𝒱`. -/
def fwdRelBlind (j : Justification) (e₁ e₂ : EventId) : Prop :=
  es.fwdBase j e₁ e₂ ∧
    ((es.cls Event.isWrite e₁ ∧ es.cls Event.isRlxR e₂) ∨
     (es.cls Event.isWrite e₁ ∧ es.cls Event.isRlxW e₂) ∨
     (es.cls Event.isRead e₁ ∧ es.cls Event.isRead e₂)) ∧
    ¬ es.cls Event.isVol e₂

/-- The acquire restriction on Forwarding (MoRDor #210,
    `ForwardElab.forwarding_blocked` under `MORDOR_FWD_SYNC=acq`): an acquire
    read `e₂` is forwarded only from an acquire read, an `sc` read only from an
    `sc` read, and no event that acquires lies `⊑`-between `e₁` and `e₂`, nor
    an `sc` event when `e₂` is one. Forwarding hoists `e₂` up to `e₁`, and an
    access does not move above an acquire: once forwarded events are out of
    coherence (`Execution.CoherenceT`), the events `⊑`-after the acquire
    could see a write that happens before `e₂` as coherence-later than
    `e₂`'s source (`Smrd.FwdAcrossAcquire`). Forwarding an acquire read from
    a weaker event drops the acquire. An `sc` read is not hoisted above an
    `sc` write (store buffering). -/
def fwdNoAcq (e₁ e₂ : EventId) : Prop :=
  (es.cls Event.isAcqR e₂ → es.cls Event.isAcqR e₁) ∧
    (es.cls Event.isScR e₂ → es.cls Event.isScR e₁) ∧
    ∀ c, es.poR e₁ c → es.poR c e₂ →
      ¬ es.cls Event.acquires c ∧ (es.cls Event.isSc e₂ → ¬ es.cls Event.isSc c)

/-! ### The join restriction -/

/-- `a` and `b` are `⊑`-comparable or equal. -/
def PoCmp (a b : EventId) : Prop := a = b ∨ es.poR a b ∨ es.poR b a

/-- `a` and `b` have a common upper bound in `⊑`: an event at or `⊑`-above
    both. -/
def Joinable (a b : EventId) : Prop :=
  ∃ d, (a = d ∨ es.poR a d) ∧ (b = d ∨ es.poR b d)

/-- `c` and `e` are `⊑`-comparable where they have a common upper bound.
    Where `⊑` is a forest (`Execution.PoForest`) this holds of every pair. -/
def JoinCmp (c e : EventId) : Prop := es.Joinable c e → es.PoCmp c e

/-- Moving `u` to `v` keeps joinable events comparable: every event `c` that
    is comparable with `u` where joinable with it is comparable with `v` where
    joinable with it. -/
def NoJoinMove (u v : EventId) : Prop := ∀ c, es.JoinCmp c u → es.JoinCmp c v

/-- The join restriction on Forwarding: `remap_δ` moves the forwarded event
    `e₂` onto its source `e₁` (`NoJoinMove e₂ e₁`). For `e₁ ⊑ e₂` it says
    that every event `⊑`-below `e₂` is comparable with `e₁`
    (`fwdNoJoin_below`) -- no event of another thread joins between them, as
    in `(… ∥ x := 1); r := x`, where `r := x`, after the join, would be
    forwarded from `x := 1` in one thread, `⊑`-incomparable with the events
    of the other (`Smrd.FwdAcrossJoin`) -- and, of an event `c` incomparable
    with `e₂` and without a common upper bound with it, that `c` has none
    with `e₁` either, or is comparable with it (no `N` in `⊑`; vacuous for
    the series-parallel `⊑` of `⟨P⟩_n`). Vacuous where `⊑` is a forest
    (`Execution.fwdNoJoin_of_poForest`). -/
def fwdNoJoin (e₁ e₂ : EventId) : Prop := es.NoJoinMove e₂ e₁

/-- The join restriction on Write Elision: `remap_δ` moves the elided write
    `e₁` onto the eliding write `e₂` (`NoJoinMove e₁ e₂`). For `e₁ ⊑ e₂` it
    says that every event `c ⊒ e₁` with a common upper bound with `e₂` is
    comparable with `e₂` (`weNoJoin_iff`): the elision does not move `e₁`
    from before a parallel block into one of its threads when the threads
    join again, as in `x := 0; (x := 1 ∥ r := x); κ`, where `r := x` is after
    `x := 0` but not after `x := 1`. Elision into the continuation of a join,
    `(x := 1 ∥ …); x := 2`, is not restricted. Vacuous where `⊑` is a forest
    (`Execution.weNoJoin_of_poForest`). -/
def weNoJoin (e₁ e₂ : EventId) : Prop := es.NoJoinMove e₁ e₂

theorem PoCmp.symm {a b : EventId} (h : es.PoCmp a b) : es.PoCmp b a := by
  rcases h with rfl | h | h
  · exact .inl rfl
  · exact .inr (.inr h)
  · exact .inr (.inl h)

theorem Joinable.symm {a b : EventId} (h : es.Joinable a b) : es.Joinable b a := by
  obtain ⟨d, ha, hb⟩ := h
  exact ⟨d, hb, ha⟩

theorem JoinCmp.symm {a b : EventId} (h : es.JoinCmp a b) : es.JoinCmp b a :=
  fun hj => PoCmp.symm es (h (Joinable.symm es hj))

theorem joinCmp_of_poCmp {a b : EventId} (h : es.PoCmp a b) : es.JoinCmp a b := fun _ => h

theorem joinable_of_po_of_po {a b d : EventId} (ha : a = d ∨ es.poR a d)
    (hb : b = d ∨ es.poR b d) : es.Joinable a b := ⟨d, ha, hb⟩

/-- Forwarding's join restriction: every event `⊑`-below the forwarded event
    `e₂` is comparable with the source `e₁`. -/
theorem fwdNoJoin_below {e₁ e₂ : EventId} (h : es.fwdNoJoin e₁ e₂) (h₁₂ : es.poR e₁ e₂)
    {c : EventId} (hc : es.poR c e₂) : es.PoCmp c e₁ :=
  h c (joinCmp_of_poCmp es (.inr (.inl hc))) ⟨e₂, .inr hc, .inr h₁₂⟩

/-- Write Elision's join restriction, for `e₁ ⊑ e₂`: every event `⊑`-above
    the elided write `e₁` with a common upper bound with the eliding write
    `e₂` is comparable with `e₂`. -/
theorem weNoJoin_iff (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    {e₁ e₂ : EventId} (h₁₂ : es.poR e₁ e₂) :
    es.weNoJoin e₁ e₂ ↔ ∀ c, es.poR e₁ c → es.Joinable c e₂ → es.PoCmp c e₂ := by
  constructor
  · intro h c hc hj
    exact h c (joinCmp_of_poCmp es (.inr (.inr hc))) hj
  · intro h c hc hj
    obtain ⟨d, hcd, hed⟩ := hj
    have hj₁ : es.Joinable c e₁ := ⟨d, hcd, .inr (by
      rcases hed with rfl | hed
      · exact h₁₂
      · exact hpo_trans _ _ _ h₁₂ hed)⟩
    rcases hc hj₁ with rfl | hce | hec
    · exact .inr (.inl h₁₂)
    · exact .inr (.inl (hpo_trans _ _ _ hce h₁₂))
    · exact h c hec ⟨d, hcd, hed⟩

/-- `e₁ -F_j→ e₂`: Forwarding's conditions (`fwdRelBlind`) under the acquire
    restriction (`fwdNoAcq`) and the join restriction (`fwdNoJoin`), where the
    forwarded event `e₂` is not an RMW access (a deviation from the paper,
    MoRDor E4). -/
def fwdRel (j : Justification) (e₁ e₂ : EventId) : Prop :=
  es.fwdRelBlind j e₁ e₂ ∧ es.fwdNoAcq e₁ e₂ ∧ es.fwdNoJoin e₁ e₂ ∧ ¬ es.RMWAcc e₂

/-- The conditions of Write Elision blind to the memory order:
    `e₁ -F'_j→ e₂` on a pair of writes, where the overwritten write `e₁` is not
    a volatile access, `e₁ ∉ 𝒱`. -/
def weRelBlind (j : Justification) (e₁ e₂ : EventId) : Prop :=
  es.fwdBase j e₁ e₂ ∧ es.cls Event.isWrite e₁ ∧ es.cls Event.isWrite e₂ ∧
    ¬ es.cls Event.isVol e₁

/-- The release restriction on Write Elision (MoRDor #207,
    `ForwardElab.elision_blocked`): a releasing write `e₁` is elided only into
    a releasing write, and no event that publishes lies `⊑`-between `e₁` and
    `e₂`. Eliding `e₁` sinks it to `e₂`, and a store does not sink past a
    release: an acquire reading the release happens after `e₁` but not after
    `e₂`, so once elided writes are out of coherence (`Execution.CoherenceT`)
    the acquire could read a write coherence-before `e₁`. -/
def weNoRel (e₁ e₂ : EventId) : Prop :=
  (es.cls Event.isRelW e₁ → es.cls Event.isRelW e₂) ∧
    ∀ c, es.poR e₁ c → es.poR c e₂ → ¬ es.cls Event.publishes c

/-- `e₁ -WE_j→ e₂`: Write Elision's conditions (`weRelBlind`) under the
    release restriction (`weNoRel`) and the join restriction (`weNoJoin`),
    where the elided write `e₁` is not an RMW access (a deviation from the
    paper, MoRDor E4). -/
def weRel (j : Justification) (e₁ e₂ : EventId) : Prop :=
  es.weRelBlind j e₁ e₂ ∧ es.weNoRel e₁ e₂ ∧ es.weNoJoin e₁ e₂ ∧ ¬ es.RMWAcc e₁

/-! ## Closed relabel-equivalence (Definition `def:rel-eq`) -/

/-- `P₁ : x₁ ≅^Λ_δ P₂ : x₂` on expressions:
    `∃ x. (⟦P₁ ⇒ x₁ = x⟧_Λ ∧ (P₂ ⇒ x₂ = x)) ≡_{ψ_δ} ⊤`. -/
def relabEqExpr (δ : FwdCtx) (Λ : Relabelling) (P₁ x₁ P₂ x₂ : Expr) : Prop :=
  ∃ x : Expr,
    EquivUnder (δ.psi es)
      (.and ((Expr.imp P₁ (.eq x₁ x)).rename Λ) (Expr.imp P₂ (.eq x₂ x))) Expr.tt

/-- Relabel equivalence of two events, by the shape of their actions. -/
def relabEq (δ : FwdCtx) (Λ : Relabelling) (P₁ : Expr) (e₁ : Event) (P₂ : Expr)
    (e₂ : Event) : Prop :=
  let locs := ∃ l₁ l₂, e₁.loc = some l₁ ∧ e₂.loc = some l₂ ∧ es.relabEqExpr δ Λ P₁ l₁ P₂ l₂
  let vals := ∃ v₁ v₂, e₁.val = some v₁ ∧ e₂.val = some v₂ ∧ es.relabEqExpr δ Λ P₁ v₁ P₂ v₂
  if (e₁.isRead && e₂.isRead) || (e₁.isWrite && e₂.isWrite) || (e₁.isAlloc && e₂.isAlloc) then
    locs ∧ vals
  else if e₁.isDealloc && e₂.isDealloc then locs
  else if e₁.isFence && e₂.isFence then True
  else False

/-- `P₁ : e₁ ≅^Λ_δ* P₂ : e₂`, closed through `pred_δ`. The recursion
    descends along `≼`, which is well-founded on the finite event structures
    the semantics generates, so the inductive (least) reading is the intended
    one. -/
inductive ClosedRelabEq (δ : FwdCtx) (Λ : Relabelling) : Expr → Event → Expr → Event → Prop
  | mk {P₁ P₂ : Expr} {e₁ e₂ : Event} :
      es.relabEq δ Λ P₁ e₁ P₂ e₂ →
      ((∀ x, ¬ es.pred δ e₁.id P₁.holds x) ↔ (∀ x, ¬ es.pred δ e₂.id P₂.holds x)) →
      (∀ x₁ x₂ ev₁ ev₂, es.pred δ e₁.id P₁.holds x₁ → es.pred δ e₂.id P₂.holds x₂ →
        es.ev x₁ = some ev₁ → es.ev x₂ = some ev₂ → ClosedRelabEq δ Λ P₁ ev₁ P₂ ev₂) →
      ClosedRelabEq δ Λ P₁ e₁ P₂ e₂

/-! ## Generating justifications (Definition `def:gen-just`) -/

/-- `valres(e)` of an event id, `⊤` for an id with no event. -/
def valresOf (e : EventId) : Expr := ((es.ev e).map Event.valres).getD Expr.tt

/-- The predicate Strengthening produces, `P ∧ Q ∧ ⋀_{e ∈ S} valres(e)`. -/
def strPred (P Q : Expr) (S : List EventId) : Expr :=
  .and P (.and Q (Expr.conj (S.map es.valresOf)))

theorem strPred_holds {P Q : Expr} {S : List EventId} {f : Valuation}
    (h : (es.strPred P Q S).holds f) : P.holds f :=
  ((Expr.holds_and _ _ f).1 h).1

theorem syms_strPred {P Q : Expr} {S : List EventId} :
    ∀ α ∈ P.syms, α ∈ (es.strPred P Q S).syms :=
  fun _ h => List.mem_append_left _ h

theorem conjuncts_strPred {P Q : Expr} {S : List EventId} :
    ∀ c ∈ P.conjuncts, c ∈ (es.strPred P Q S).conjuncts :=
  fun _ h => List.mem_append_left _ h

/-- `j ∈ 𝕁`, relative to the global guarantees `Ω`. Every elaboration asks
    that the predicate it produces be consistent with `Ω`,
    `P_j ∧ Ω ≢ ⊥`. -/
inductive Generated (Ω : Pred) : Justification → Prop
  /-- Pre-justifications, where the value restriction is satisfiable. -/
  | pre {w : Event} {j : Justification} :
      w ∈ es.events → preJust w = some j → Sat w.valres.holds →
      Generated Ω j
  /-- Value Assignment (Definition `def:elab-va`): substitute a value `v` with
      `α ≡_P v` in the location and value of a justified write, recomputing
      `D` and leaving `P` unchanged. -/
  | va {j₁ : Justification} {o : MemOrd} {x e : Expr} {b : Bool} {α : Sym} {v : Val} :
      Generated Ω j₁ →
      j₁.w.kind = .write o x e b →
      EquivUnder j₁.P.holds (.sym α) (.val v) →
      Sat (Pred.and j₁.P.holds Ω) →
      Generated Ω
        { P := j₁.P
          D := (x.subst α (.val v)).syms ++ (e.subst α (.val v)).syms
          δ := j₁.δ
          w := { j₁.w with kind := .write o (x.subst α (.val v)) (e.subst α (.val v)) b } }
  /-- Strengthening (Definition `def:elab-str`): conjoin a predicate `Q` and
      the value restrictions of the origins `S` it introduces,
      `P' = P ∧ Q ∧ ⋀_{e ∈ S} valres(e)`, with
      `S = origin(symbols(P')) ∖ origin(symbols(P))`. The equation for `S` is
      a fixed point, as `valres(e)` may itself bring in symbols; `S` is given
      and checked against it. `P'` is built syntactically, so
      `symbols(P') ⊇ symbols(P)` and `P'` entails `P`.

      The new origins are `⊑`-before the write, `e ⊑ w` (sMRD §4.7's prose,
      "all symbols are visible to the justified write"), not
      `e ⊑ w ∨ w ⊑ e` as in sMRD's Def. 4.11 and `def:elab-str`; see the
      module header. -/
  | str {j₁ : Justification} (Q : Expr) (S : List EventId) :
      Generated Ω j₁ →
      (∀ e, e ∈ S ↔ e ∈ (strPred es j₁.P Q S).syms ∧ e ∉ j₁.P.syms) →
      (∀ e ∈ S, j₁.δ.Remap e e) →
      (∀ e ∈ S, es.poR e j₁.w.id ∧ ¬ es.ppo j₁.P.holds j₁.δ j₁.w.id e) →
      Sat (Pred.and (strPred es j₁.P Q S).holds Ω) →
      Generated Ω { j₁ with P := strPred es j₁.P Q S }
  /-- Forwarding (Definition `def:elab-fwd`) along `e₁ -F_{j₁}→ e₂`, applying
      `g = [val(e₂) ↦ val(e₁)]` to the predicate and to the justified write.
      The extended forwarding context must be well-formed (`def:fwd-ctx`). -/
  | fwd {j₁ : Justification} {o : MemOrd} {x e : Expr} {b : Bool} {e₁ e₂ : EventId}
      {ev₁ ev₂ : Event} {v₁ v₂ : Expr} :
      Generated Ω j₁ →
      j₁.w.kind = .write o x e b →
      es.fwdRel j₁ e₁ e₂ →
      es.ev e₁ = some ev₁ → es.ev e₂ = some ev₂ →
      ev₁.val = some v₁ → ev₂.val = some v₂ →
      FwdCtx.WF { j₁.δ with f := j₁.δ.f ++ [(e₁, e₂)] } →
      Sat (Pred.and (j₁.P.replace v₂ v₁).holds Ω) →
      Generated Ω
        { P := j₁.P.replace v₂ v₁
          D := (e.replace v₂ v₁).syms ++ (x.replace v₂ v₁).syms
          δ := { j₁.δ with f := j₁.δ.f ++ [(e₁, e₂)] }
          w := { j₁.w with kind := .write o (x.replace v₂ v₁) (e.replace v₂ v₁) b } }
  /-- Write Elision (Definition `def:elab-we`), adding `(e₂, e₁)` to `WE`; the
      extended forwarding context must be well-formed (`def:fwd-ctx`). -/
  | we {j₁ : Justification} {e₁ e₂ : EventId} :
      Generated Ω j₁ →
      es.weRel j₁ e₁ e₂ →
      FwdCtx.WF { j₁.δ with we := j₁.δ.we ++ [(e₂, e₁)] } →
      Sat (Pred.and j₁.P.holds Ω) →
      Generated Ω { j₁ with δ := { j₁.δ with we := j₁.δ.we ++ [(e₂, e₁)] } }
  /-- Lifting (Definition `def:elab-lift`): `(C ∧ (⋀A₁ ∨ ⋀A₂), D₂) ⊢^δ w₂`,
      factoring the conjuncts `C` shared by `⟦P₁⟧_Λ` and `P₂` out of the
      disjunction (`Expr.liftPred`). The predicate is equivalent to SMRD's
      `⟦P₁⟧_Λ ∨ P₂` (`Expr.liftPred_holds_iff`) and has its symbols
      (`Expr.mem_syms_liftPred_iff`). Neither justified write, nor the origin
      of a dependency of either, is a volatile access.

      Every symbol of the relabelled premise `⟦P₁⟧_Λ` has its origin
      `⊑`-before `w₂`, a deviation from the paper; see the module header. -/
  | lift {j₁ j₂ : Justification} (Λ : Relabelling) :
      Generated Ω j₁ → Generated Ω j₂ →
      j₁.δ = j₂.δ →
      Λ.Injective →
      es.ClosedRelabEq j₁.δ Λ j₁.P j₁.w j₂.P j₂.w →
      (∀ e, e ∈ j₂.D ↔ ∃ α ∈ j₁.D, Λ.app α = e) →
      (∀ α ∈ j₁.D, ∃ ev₁ ev₂, es.ev α = some ev₁ ∧ es.ev (Λ.app α) = some ev₂ ∧
        es.ClosedRelabEq j₁.δ Λ j₁.P ev₁ j₂.P ev₂) →
      ¬ es.cls Event.isVol j₁.w.id → ¬ es.cls Event.isVol j₂.w.id →
      (∀ α ∈ j₁.D ++ j₂.D, ¬ es.cls Event.isVol α) →
      (∀ α ∈ (j₁.P.rename Λ).syms, es.poR α j₂.w.id) →
      Sat (Pred.and (Expr.liftPred (j₁.P.rename Λ) j₂.P).holds Ω) →
      Generated Ω { j₂ with P := Expr.liftPred (j₁.P.rename Λ) j₂.P }
  /-- Weakening (Definition `def:elab-weak`): drop a conjunct the global
      guarantees imply. Predicates are read up to their conjuncts
      (Paragraph `par:conj`), so `j₁.P` is `P' ∧ Pw` up to `ConjEq`, and any
      one conjunct can be dropped. -/
  | weak {j₁ : Justification} {P' Pw : Expr} :
      Generated Ω j₁ →
      j₁.P.ConjEq (.and P' Pw) →
      Entails Ω Pw.holds →
      Sat (Pred.and P'.holds Ω) →
      Generated Ω { j₁ with P := P' }

/-- Every generated justification has a predicate consistent with `Ω`, or is
    a pre-justification with a satisfiable value restriction. -/
theorem Generated.sat {Ω : Pred} {j : Justification} (h : es.Generated Ω j) :
    Sat j.P.holds ∨ ∃ w ∈ es.events, preJust w = some j := by
  cases h with
  | pre hw hj _ => exact Or.inr ⟨_, hw, hj⟩
  | va _ _ _ hs | fwd _ _ _ _ _ _ _ _ hs | we _ _ _ hs =>
      obtain ⟨f, hP, _⟩ := hs; exact Or.inl ⟨f, hP⟩
  | str _ _ _ _ _ _ hs | weak _ _ _ hs =>
      obtain ⟨f, hP, _⟩ := hs; exact Or.inl ⟨f, hP⟩
  | lift _ _ _ _ _ _ _ _ _ _ _ _ hs =>
      obtain ⟨f, hP, _⟩ := hs; exact Or.inl ⟨f, hP⟩

theorem δ_of_preJust {w : Event} {j : Justification} (h : preJust w = some j) : j.δ = .empty := by
  unfold preJust at h
  split at h <;> cases h <;> rfl

/-- Every Write Elision edge `(e₂, e₁)` of a generated justification was added
    by Write Elision, under its conditions (`weRel`) against a justification
    `j₀` with a satisfiable predicate, whose forwarding edges are among the
    final ones. -/
theorem Generated.we_mem {Ω : Pred} {j : Justification} (h : es.Generated Ω j) :
    ∀ p ∈ j.δ.we, ∃ j₀ : Justification, es.weRel j₀ p.2 p.1 ∧ Sat j₀.P.holds ∧
      ∀ q ∈ j₀.δ.f, q ∈ j.δ.f := by
  induction h with
  | pre _ hj _ => intro p hp; rw [δ_of_preJust hj] at hp; cases hp
  | va _ _ _ _ ih => exact ih
  | str _ _ _ _ _ _ _ ih => exact ih
  | fwd _ _ _ _ _ _ _ _ _ ih =>
      intro p hp
      obtain ⟨j₀, h₀, hs, hf⟩ := ih p hp
      exact ⟨j₀, h₀, hs, fun q hq => List.mem_append_left _ (hf q hq)⟩
  | @we j₁ e₁ e₂ _ hwe _ hs ih =>
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact ih p hp
      · simp only [List.mem_singleton] at hp
        subst hp
        obtain ⟨f, hP, -⟩ := hs
        exact ⟨j₁, hwe, ⟨f, hP⟩, fun q hq => hq⟩
  | lift _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₂ => exact ih₂
  | weak _ _ _ _ ih => exact ih

/-- Every forwarding edge `(e₁, e₂)` of a generated justification was added
    by Forwarding, under its conditions (`fwdRel`) against a justification. -/
theorem Generated.fwd_mem {Ω : Pred} {j : Justification} (h : es.Generated Ω j) :
    ∀ p ∈ j.δ.f, ∃ j₀ : Justification, es.fwdRel j₀ p.1 p.2 := by
  induction h with
  | pre _ hj _ => intro p hp; rw [δ_of_preJust hj] at hp; cases hp
  | va _ _ _ _ ih => exact ih
  | str _ _ _ _ _ _ _ ih => exact ih
  | @fwd j₁ _ _ _ _ e₁ e₂ _ _ _ _ _ _ hf _ _ _ _ _ _ ih =>
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact ih p hp
      · simp only [List.mem_singleton] at hp
        subst hp
        exact ⟨j₁, hf⟩
  | we _ _ _ _ ih => exact ih
  | lift _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₂ => exact ih₂
  | weak _ _ _ _ ih => exact ih

/-- **No RMW access is elided** (`rmw_not_elided`): in every generated
    justification, the target of each forwarding edge and the elided write of
    each Write Elision edge is not an RMW access. -/
theorem Generated.not_rmwAcc_elided {Ω : Pred} {j : Justification} (h : es.Generated Ω j) :
    ∀ p, (p ∈ j.δ.f ∨ p ∈ j.δ.we) → ¬ es.RMWAcc p.2 := by
  rintro p (hp | hp)
  · obtain ⟨j₀, -, -, -, h⟩ := Generated.fwd_mem es h p hp
    exact h
  · obtain ⟨j₀, ⟨-, -, -, h⟩, -⟩ := Generated.we_mem es h p hp
    exact h

end EventStructure
