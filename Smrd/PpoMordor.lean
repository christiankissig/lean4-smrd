import Smrd.Types
import Smrd.Forwardingcontext
import Smrd.Ppo

/-!
# MoRDor's preserved program order templates

The relations MoRDor's `freeze_ppo` (`mordor/src/executions.ml`, MoRDor commit
6dd8521) builds the frozen `≼` from, read off `mordor/src/forwarding.ml`
(`EventStructureContext.init`, `compute_ppo_sync`, `compute_ppo_loc_eq`,
`ForwardingContext.ppo`, `ppo_loc`, `ppo_sync`, `compute_ppo_rmw`, `remap_rel`).
`Execution.ppo` (`Smrd.Executions`) assembles them; the paper's templates of
Definition `def:ppo` (`Smrd.Ppo`) stay the ones justifications use (`pred_δ`).

Against Definition `def:ppo`:

* `ppoSyncM` is MoRDor's `ppo_sync`, `(E_acq × E ∪ E × E_rel) ∩ ⊑` with
  `E_acq = R_{acq,sc} ∪ F_{acq,sc}` and `E_rel = W_{rel,sc} ∪ F_{rel,sc}`. The
  paper's `≼_sync` orders across a fence (`⊑;Δ_{F_rel,sc};⊑_{∖R}`,
  `⊑_{∖W};Δ_{F_acq,sc};⊑`) and then drops every pair with a fence or branch at
  an end; MoRDor keeps the pairs into a releasing and out of an acquiring
  fence, has no fence-crossing summand, and gets the crossing pairs only by
  the transitive closure freezing takes, through a fence that both acquires
  and releases (`sc`). So across a `rel` fence alone nothing is ordered, and
  across an `sc` fence a write is ordered before a later read, which the paper
  excludes. MoRDor's lock and unlock events have no counterpart here.
* `ppoAliasM` is MoRDor's `ppo_loc_eq ∪ filter(ppo_loc_base)`: the pairs of
  `⊑` whose locations are equal outright (`Solver.exeq ~state:[]`, here
  `SemEquiv`) are kept unconditionally, the rest when the locations may be
  equal under the predicate. The two agree with the paper's `≼_alias`
  whenever the predicate is satisfiable.
* `ppoRMWM` composes with `ppoSyncM`, and does not remove `Δ_E` itself; the
  remapping step does (`remap_rel` drops self-pairs), as for `ppoM`.
* `ppoM Pa Pr δ` is `ForwardingContext.ppo`: alias queries under `Pa` (MoRDor's
  predicates with `ψ` of the context appended), RMW conditions entailed by
  `Pr` (the predicates alone, without `ψ`).
* `ppoLocM` is `ForwardingContext.ppo_loc`: `ppoM` filtered once more to the
  pairs that may alias, read on the remapped events.

MoRDor's alias queries also assume the structure's constraints (distinctness
of globals); here globals are distinct locations by evaluation.
-/

namespace Event

/-- MoRDor's `e_acq`: reads and fences that acquire, `R_{acq,sc} ∪ F_{acq,sc}`. -/
def isAcqM (e : Event) : Bool := e.isAcqR || e.isAcqF

/-- MoRDor's `e_rel`: writes and fences that release, `W_{rel,sc} ∪ F_{rel,sc}`. -/
def isRelM (e : Event) : Bool := e.isRelW || e.isRelF

end Event

namespace EventStructure

variable (es : EventStructure)

/-- MoRDor's `ppo_sync`: `(E_acq × E ∪ E × E_rel) ∩ ⊑`. -/
def ppoSyncM : Rel := fun a b =>
  es.poR a b ∧ (es.cls Event.isAcqM a ∨ es.cls Event.isRelM b)

/-- MoRDor's `ppo_rmw`: `ppo_sync ; rmwPairs ∪ rmwPairs ; ppo_sync`, with the
    conditions entailed by `P`. -/
def ppoRMWM (P : Pred) : Rel :=
  (es.ppoSyncM.comp (es.rmwPairs P)).union ((es.rmwPairs P).comp es.ppoSyncM)

/-- Locations equal outright, MoRDor's `Solver.exeq ~state:[]`. -/
def mustAlias (a b : EventId) : Prop :=
  ∃ e₁ e₂ l₁ l₂, es.ev a = some e₁ ∧ es.ev b = some e₂ ∧
    e₁.loc = some l₁ ∧ e₂.loc = some l₂ ∧ SemEquiv l₁ l₂

/-- MoRDor's `ppo_loc_eq ∪ filter_P(ppo_loc_base)`. -/
def ppoAliasM (P : Pred) : Rel := fun a b =>
  es.poR a b ∧ (es.mustAlias a b ∨ es.mayAlias P a b)

/-- The base of `ForwardingContext.ppo`, before remapping. -/
def ppoBaseM (Pa Pr : Pred) : Rel :=
  (es.ppoSyncM.union (es.ppoRMWM Pr)).union (es.ppoAliasM Pa)

/-- MoRDor's `ForwardingContext.ppo ctx p`: alias queries under `Pa = p ∧ ψ`,
    RMW conditions under `Pr = p`, remapped under `δ` with self-pairs dropped. -/
def ppoM (Pa Pr : Pred) (δ : FwdCtx) : Rel := (δ.remapRel (es.ppoBaseM Pa Pr)).offDiag

/-- MoRDor's `ForwardingContext.ppo_loc ctx p`: the pairs of `ppoM` that may
    alias under `P`, on the remapped events. (MoRDor remaps once more, which
    leaves remapped events where they are.) -/
def ppoLocM (P : Pred) (δ : FwdCtx) : Rel := fun a b => es.ppoM P P δ a b ∧ es.mayAlias P a b

/-- MoRDor's `ForwardingContext.ppo_sync ctx`: `ppo_sync` remapped. -/
def ppoSyncRM (δ : FwdCtx) : Rel := (δ.remapRel es.ppoSyncM).offDiag

theorem ppoSyncM_po {a b : EventId} (h : es.ppoSyncM a b) : es.poR a b := h.1

theorem ppoAliasM_po {P : Pred} {a b : EventId} (h : es.ppoAliasM P a b) : es.poR a b := h.1

theorem ppoAliasM_mono {P Q : Pred} (h : Entails P Q) :
    Rel.Subset (es.ppoAliasM P) (es.ppoAliasM Q) := by
  rintro a b ⟨hpo, hm | hal⟩
  · exact ⟨hpo, .inl hm⟩
  · exact ⟨hpo, .inr ((es.ppoAlias_mono h a b ⟨hpo, hal⟩).2)⟩

theorem ppoRMWM_anti {P Q : Pred} (h : Entails P Q) :
    Rel.Subset (es.ppoRMWM Q) (es.ppoRMWM P) := by
  rintro a c (⟨b, hs, hr⟩ | ⟨b, hr, hs⟩)
  · exact .inl ⟨b, hs, es.rmwPairs_anti h _ _ hr⟩
  · exact .inr ⟨b, es.rmwPairs_anti h _ _ hr, hs⟩

theorem mayAlias_mono {P Q : Pred} (h : Entails P Q) {a b : EventId}
    (hal : es.mayAlias P a b) : es.mayAlias Q a b := by
  obtain ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, hP, heq⟩ := hal
  exact ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, h f hP, heq⟩

/-- `ppoM` grows as the alias predicate weakens and the RMW predicate
    strengthens. -/
theorem ppoM_mono {Pa Qa Pr Qr : Pred} (δ : FwdCtx) (ha : Entails Pa Qa) (hr : Entails Qr Pr) :
    Rel.Subset (es.ppoM Pa Pr δ) (es.ppoM Qa Qr δ) := by
  rintro a b ⟨⟨a₀, b₀, hab, h₁, h₂⟩, hne⟩
  refine ⟨⟨a₀, b₀, ?_, h₁, h₂⟩, hne⟩
  rcases hab with (hs | hm) | hal
  · exact .inl (.inl hs)
  · exact .inl (.inr (es.ppoRMWM_anti hr _ _ hm))
  · exact .inr (es.ppoAliasM_mono ha _ _ hal)

theorem ppoSyncRM_sub_ppoM (Pa Pr : Pred) (δ : FwdCtx) :
    Rel.Subset (es.ppoSyncRM δ) (es.ppoM Pa Pr δ) := by
  rintro a b ⟨⟨a₀, b₀, hab, h₁, h₂⟩, hne⟩
  exact ⟨⟨a₀, b₀, .inl (.inl hab), h₁, h₂⟩, hne⟩

end EventStructure

namespace FwdCtx

/-- An event with no `F ∪ WE`-predecessor is its own image. -/
theorem Remap.self_of_noEdge {δ : FwdCtx} {a : EventId} (h : ∀ c, ¬ δ.edge c a) :
    δ.Remap a a := .canon h

/-- With no `F ∪ WE` edges, `remap_δ` is the identity. -/
theorem Remap.eq_of_noEdge {δ : FwdCtx} (h : ∀ a b, ¬ δ.edge a b) {a a' : EventId}
    (hr : δ.Remap a a') : a' = a := by
  cases hr with
  | canon _ => rfl
  | step he _ => exact absurd he (h _ _)

theorem remapRel_of_noEdge {δ : FwdCtx} (h : ∀ a b, ¬ δ.edge a b) {R : Rel} {a b : EventId} :
    δ.remapRel R a b ↔ R a b := by
  constructor
  · rintro ⟨a₀, b₀, hR, ha, hb⟩
    rw [Remap.eq_of_noEdge h ha, Remap.eq_of_noEdge h hb]; exact hR
  · intro hR
    exact ⟨a, b, hR, .canon (fun c => h c a), .canon (fun c => h c b)⟩

end FwdCtx
