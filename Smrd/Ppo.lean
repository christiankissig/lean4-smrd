import Smrd.Types
import Smrd.Forwardingcontext

/-!
# Preserved Program Order (Definition A.11)

Based on the appendix definitions from the paper.
-/

/-! ## Alias check -/

/-- ⟦P ∧ loc(e₁) = loc(e₂)⟧_f ≡ ⊤ for some environment f.
    We check this existentially over a supplied list of candidate environments. -/
def aliasUnderSomeEnv
    (P : BoolExpr) (loc1 loc2 : Expr) (candidates : List Env) : Bool :=
  candidates.any fun f =>
    match P.eval f, loc1.eval f, loc2.eval f with
    | some true, some v1, some v2 => v1 == v2
    | _, _, _ => false

/-! ## Preserved Program Order (Definition A.11) -/

/-- Ids of events satisfying a predicate. -/
def EventStructure.idsWhere (es : EventStructure) (p : Event → Bool) : List Nat :=
  (es.events.filter p).map (·.id)

/-- ≼_sync: the statically declared memory-order component of PPO.
    ≼_sync ≜ ( ⊑ ; Δ_{W_rel,sc}
             ∪ ⊑ ; Δ_{F_rel,sc} ; ⊑_{∖R}
             ∪ Δ_{R_acq,sc} ; ⊑
             ∪ ⊑_{∖W} ; Δ_{F_acq,sc} ; ⊑
             )_{∖(F∪B)}
-/
def EventStructure.ppoSync (es : EventStructure) : Rel :=
  let po := es.po

  -- Event id sets for each classifier
  let wRelSc   := es.idsWhere Event.isRelWrite
  let fRelSc   := es.idsWhere Event.isRelFence
  let rAcqSc   := es.idsWhere Event.isAcqRead
  let fAcqSc   := es.idsWhere Event.isAcqFence
  let reads    := es.idsWhere Event.isRead
  let writes   := es.idsWhere Event.isWrite
  let fences   := es.idsWhere Event.isFence
  let branches := es.idsWhere Event.isBranch

  -- ⊑ ; Δ_{W_rel,sc}
  let t1 := po.comp (diagonal wRelSc)
  -- ⊑ ; Δ_{F_rel,sc} ; ⊑_{∖R}
  let t2 := (po.comp (diagonal fRelSc)).comp (po.restrictExcluding reads)
  -- Δ_{R_acq,sc} ; ⊑
  let t3 := (diagonal rAcqSc).comp po
  -- ⊑_{∖W} ; Δ_{F_acq,sc} ; ⊑
  let t4 := ((po.restrictExcluding writes).comp (diagonal fAcqSc)).comp po

  -- Union, then remove pairs where either endpoint is a fence or branch
  (t1.union t2 |>.union t3 |>.union t4).restrictExcluding (fences ++ branches)

/-- ≼_rmw: atomicity of RMW operations, relative to predicate P.
    ≼_rmw ≜ ≼_sync ; {(e_w, e_r) | (e_r, c, e_w) ∈ ⊑ʳᵐʷ ∧ c ≡_P ⊤}
           ∪ {(e_w, e_r) | (e_r, c, e_w) ∈ ⊑ʳᵐʷ ∧ c ≡_P ⊤} ; ≼_sync
    where c ≡_P ⊤ is checked via supplied candidate environments.
-/
def EventStructure.ppoRMW
    (es : EventStructure) (P : BoolExpr) (envs : List Env) : Rel :=
  let sync := es.ppoSync
  -- RMW pairs (e_w, e_r) where condition c holds under P
  let rmwPairs : Rel := es.rmw.filterMap fun entry =>
    -- c ≡_P ⊤: check that P ∧ c evaluates to true under some environment
    let cHolds := envs.any fun f =>
      match (BoolExpr.and P entry.cond).eval f with
      | some true => true
      | _         => false
    if cHolds then some (entry.writeId, entry.readId) else none
  sync.comp rmwPairs |>.union (rmwPairs.comp sync)

/-- ≼_alias^P: order induced by aliased memory locations, relative to predicate P.
    ≼_alias^P ≜ {(e₁, e₂) ∈ ⊑ | ∃f. ⟦P ∧ loc(e₁) = loc(e₂)⟧_f ≡ ⊤}
-/
def EventStructure.ppoAlias
    (es : EventStructure) (P : BoolExpr) (envs : List Env) : Rel :=
  es.po.filter fun (id1, id2) =>
    match es.events.find? (·.id == id1), es.events.find? (·.id == id2) with
    | some e1, some e2 =>
        match e1.loc, e2.loc with
        | some l1, some l2 => aliasUnderSomeEnv P l1 l2 envs
        | _, _ => false
    | _, _ => false

/-- ≼^P_δ: the full preserved program order.
    ≼^P_δ ≜ remap_δ(≼_sync ∪ ≼_rmw ∪ ≼_alias)
-/
def EventStructure.ppo
    (es   : EventStructure)
    (P    : BoolExpr)
    (δ    : ForwardingContext)
    (envs : List Env)           -- candidate environments for alias/rmw checks
    : Rel :=
  let base := es.ppoSync
              |>.union (es.ppoRMW   P envs)
              |>.union (es.ppoAlias P envs)
  δ.remapRel base

/-! ## Predecessor relation (Definition A.11) -/

/-- pred_δ(e, P): immediate ≼^P_δ-predecessors of event `eId`.
    i.e. events e' such that:
      e' ≼^P_δ e  ∧  e' ≠ e  ∧
      ∀e''. e' ≼^P_δ e'' ≼^P_δ e ⟹ e' = e'' ∨ e'' = e
-/
def EventStructure.pred
    (es   : EventStructure)
    (eId  : Nat)
    (P    : BoolExpr)
    (δ    : ForwardingContext)
    (envs : List Env)
    : List Nat :=
  let ppo := es.ppo P δ envs
  -- All strict ≼-predecessors of eId
  let preds := ppo.filterMap (fun (a, b) => if b == eId && a != eId then some a else none)
  -- Keep only immediate predecessors: no other e'' sits strictly between e' and e
  preds.filter fun ePrime =>
    !preds.any fun ePP =>
      ePP != ePrime &&
      ppo.contains (ePrime, ePP) &&
      ppo.contains (ePP, eId)
