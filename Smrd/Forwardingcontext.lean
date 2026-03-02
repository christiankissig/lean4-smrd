import Smrd.Types

/-! ## Forwarding context -/

/-- A forwarding context δ = (f, we).
    - f  ⊆ E × E : forwarding relation
    - we ⊆ E × E : write elision relation -/
structure ForwardingContext : Type where
  f  : Rel   -- forwarding relation
  we : Rel   -- write elision relation
  deriving Repr

/-!
  remap_δ(e): follow forwarding/elision edges back to the canonical source.

  We compute this as: repeatedly follow the *inverse* of (f ∪ we) until
  there is no predecessor. To guarantee termination we bound the search
  by the total number of edges (which strictly decreases each step if the
  graph is acyclic, as required by the model).
-/

/-- One step of remapping: find any predecessor of `id` in `edges`. -/
private def remapStep (edges : Rel) (id : Nat) : Option Nat :=
  edges.findSome? (fun (src, tgt) => if tgt == id then some src else none)

/-- Remap `id` by following predecessor edges up to `fuel` times. -/
private def remapAux (edges : Rel) : Nat → Nat → Nat
  | 0,        id => id   -- fuel exhausted; return current id
  | fuel + 1, id =>
      match remapStep edges id with
      | none     => id             -- no predecessor: id is canonical
      | some src => remapAux edges fuel src  -- recurse toward source

/-- remap_δ(e): follow (f ∪ we)⁻¹ back to the canonical source event.
    Terminates in at most |f ∪ we| steps (assuming acyclicity). -/
def ForwardingContext.remap (δ : ForwardingContext) (id : Nat) : Nat :=
  let edges := δ.f ++ δ.we
  remapAux edges edges.length id

/-- Lift remap_δ to a relation: remap both endpoints of every pair. -/
def ForwardingContext.remapRel (δ : ForwardingContext) (r : Rel) : Rel :=
  r.map (fun (a, b) => (δ.remap a, δ.remap b))
