import Smrd.ElabDec.Closure

/-!
# Deciding `remap_δ` and well-formedness of forwarding contexts

`remap_δ` is a relation (`FwdCtx.Remap`); over a finite context it is computed
by following the unique predecessor (`FwdCtx.predOf`) at most `|F ∪ WE|`
times (`FwdCtx.remapB`, `FwdCtx.remap_iff`, for well-formed contexts), and
well-formedness (`def:fwd-ctx`) is decided by checking unique predecessors and
that every such chain ends within `|F ∪ WE|` steps (`FwdCtx.wfB_iff`). Both
rest on the pigeonhole principle: an acyclic chain visits distinct edge
targets.
-/

open Smrd.ElabDec

namespace FwdCtx

variable (δ : FwdCtx)

/-- The edges of `F ∪ WE` as one list. -/
def edges : List (EventId × EventId) := δ.f ++ δ.we

/-- The source of the first edge into `e`. -/
def predOf (e : EventId) : Option EventId := (δ.edges.find? (fun p => p.2 == e)).map Prod.fst

variable {δ}

theorem edge_iff {a e : EventId} : δ.edge a e ↔ (a, e) ∈ δ.edges := by
  simp [edge, edges, List.mem_append]

theorem edge_of_predOf {a e : EventId} (h : δ.predOf e = some a) : δ.edge a e := by
  unfold predOf at h
  cases hf : δ.edges.find? (fun p => p.2 == e) with
  | none => rw [hf] at h; cases h
  | some p =>
      rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h
      have hm := List.mem_of_find?_eq_some hf
      have he : p.2 = e := by simpa using List.find?_some hf
      rw [edge_iff, ← h, ← he]; exact hm

theorem predOf_none_iff {e : EventId} : δ.predOf e = none ↔ ∀ a, ¬ δ.edge a e := by
  unfold predOf
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  constructor
  · intro h a ha; rw [edge_iff] at ha; exact h _ ha (by simp)
  · intro h p hp hpe
    have : p.2 = e := by simpa using hpe
    exact h p.1 ((edge_iff).2 (by rw [← this]; exact hp))

theorem predOf_of_edge (huniq : ∀ a b e, δ.edge a e → δ.edge b e → a = b) {a e : EventId}
    (h : δ.edge a e) : δ.predOf e = some a := by
  cases hp : δ.predOf e with
  | none => exact absurd h ((predOf_none_iff.1 hp) a)
  | some b => rw [huniq _ _ _ (edge_of_predOf hp) h]

variable (δ)

/-- `k` steps up the chain of predecessors, staying at an event without one. -/
def up : Nat → EventId → EventId
  | 0, x => x
  | k + 1, x => (δ.predOf (up k x)).getD (up k x)

/-- `remap_δ`, computed. -/
def remapB (x : EventId) : EventId := δ.up δ.edges.length x

variable {δ}

theorem remap_of_up_remap : ∀ (k : Nat) (x z : EventId), δ.Remap (δ.up k x) z → δ.Remap x z
  | 0, _, _, h => h
  | k + 1, x, z, h => by
      apply remap_of_up_remap k x z
      simp only [up] at h
      cases hp : δ.predOf (δ.up k x) with
      | none => rw [hp] at h; exact h
      | some a => rw [hp] at h; exact Remap.step (edge_of_predOf hp) h

theorem remap_up {k : Nat} {x : EventId} (h : δ.predOf (δ.up k x) = none) : δ.Remap x (δ.up k x) :=
  remap_of_up_remap k x _ (Remap.canon (predOf_none_iff.1 h))

theorem up_stuck {k : Nat} {x : EventId} (h : δ.predOf (δ.up k x) = none) :
    ∀ m, δ.up (k + m) x = δ.up k x
  | 0 => rfl
  | m + 1 => by
      have ih := up_stuck h m
      show (δ.predOf (δ.up (k + m) x)).getD (δ.up (k + m) x) = _
      rw [ih, h]; rfl

theorem up_succ_edge {k : Nat} {x a : EventId} (h : δ.predOf (δ.up k x) = some a) :
    δ.up (k + 1) x = a ∧ δ.edge a (δ.up k x) := by
  refine ⟨?_, edge_of_predOf h⟩
  show (δ.predOf (δ.up k x)).getD (δ.up k x) = a
  rw [h]; rfl

/-- In an acyclic context every chain of predecessors ends within `|F ∪ WE|`
    steps. -/
theorem predOf_up_none (hac : Rel.Acyclic δ.edge) (x : EventId) :
    δ.predOf (δ.up δ.edges.length x) = none := by
  classical
  let n := δ.edges.length
  refine Classical.byContradiction fun hne => ?_
  -- every step up to `n` has a predecessor
  have hall : ∀ k ≤ n, ∃ a, δ.predOf (δ.up k x) = some a := by
    intro k hk
    cases hp : δ.predOf (δ.up k x) with
    | some a => exact ⟨a, rfl⟩
    | none =>
        have := up_stuck hp (n - k)
        rw [Nat.add_sub_cancel' hk] at this
        exact absurd (this ▸ hp) hne
  -- consecutive steps are edges, and so the chain is a path
  have hpath : ∀ i j, i < j → j ≤ n + 1 → Relation.TransGen δ.edge (δ.up j x) (δ.up i x) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
        obtain ⟨a, ha⟩ := hall j (by omega)
        obtain ⟨hup, hed⟩ := up_succ_edge ha
        rw [hup]
        by_cases hji : i = j
        · subst hji; exact .single hed
        · exact Rel.transGen_head hed (ih (by omega) (by omega))
  -- the chain is duplicate-free
  have hnd : ((List.range (n + 1)).map (fun k => δ.up k x)).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (List.nodup_range)
    intro i j hi hj hij heq
    have hi' := List.mem_range.1 hi
    have hj' := List.mem_range.1 hj
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact hac _ (heq ▸ hpath i j h (by omega))
    · exact hac _ (heq ▸ hpath j i h (by omega))
  have hsub : ∀ y ∈ (List.range (n + 1)).map (fun k => δ.up k x), y ∈ δ.edges.map Prod.snd := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
    obtain ⟨a, ha⟩ := hall k (by have := List.mem_range.1 hk; omega)
    exact List.mem_map.2 ⟨(a, _), (edge_iff).1 (edge_of_predOf ha), rfl⟩
  have := length_le_of_nodup_subset hnd hsub
  simp only [List.length_map, List.length_range, n] at this; omega

/-- `remap_δ` is computed by `remapB` on well-formed contexts. -/
theorem remap_iff (hwf : δ.WF) {x y : EventId} : δ.Remap x y ↔ δ.remapB x = y := by
  have hr : δ.Remap x (δ.remapB x) := remap_up (predOf_up_none hwf.acyclic x)
  constructor
  · intro h; exact Remap.functional hwf.uniq hr h
  · rintro rfl; exact hr

/-- `remap_δ(x)` is `x` or the source of an edge. -/
theorem Remap.cases {x y : EventId} (h : δ.Remap x y) : y = x ∨ y ∈ δ.edges.map Prod.fst := by
  induction h with
  | canon _ => exact Or.inl rfl
  | step hae _ ih =>
      rcases ih with rfl | h
      · exact Or.inr (List.mem_map.2 ⟨(_, _), (edge_iff).1 hae, rfl⟩)
      · exact Or.inr h

variable (δ)

/-- Every event has at most one predecessor, decided. -/
def uniqB : Bool := δ.edges.all fun p => δ.edges.all fun q => p.2 != q.2 || p.1 == q.1

/-- Well-formedness, decided. -/
def wfB : Bool := δ.uniqB && (δ.edges.map Prod.snd).all fun x => δ.predOf (δ.up δ.edges.length x) == none

variable {δ}

theorem uniqB_iff : δ.uniqB = true ↔ ∀ a b e, δ.edge a e → δ.edge b e → a = b := by
  simp only [uniqB, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  constructor
  · intro h a b e ha hb
    rw [edge_iff] at ha hb
    rcases h _ ha _ hb with h | h
    · exact absurd rfl h
    · exact h
  · intro h p hp q hq
    by_cases he : p.2 = q.2
    · right; exact h p.1 q.1 p.2 ((edge_iff).2 hp) ((edge_iff).2 (by rw [he]; exact hq))
    · left; exact he

theorem wfB_iff : δ.wfB = true ↔ δ.WF := by
  simp only [wfB, Bool.and_eq_true, uniqB_iff, List.all_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hu, hc⟩
    refine ⟨fun a hcyc => ?_, hu⟩
    -- on a cycle every event has a predecessor on the cycle
    have hstep : ∀ y, Relation.TransGen δ.edge y y → ∃ p, δ.edge p y ∧ Relation.TransGen δ.edge p p := by
      intro y hy
      cases hy with
      | single h => exact ⟨y, h, .single h⟩
      | tail h e => exact ⟨_, e, Rel.transGen_head e h⟩
    have hon : ∀ k, Relation.TransGen δ.edge (δ.up k a) (δ.up k a) := by
      intro k
      induction k with
      | zero => exact hcyc
      | succ k ih =>
          obtain ⟨p, hp, hpc⟩ := hstep _ ih
          rw [(up_succ_edge (predOf_of_edge hu hp)).1]; exact hpc
    obtain ⟨p, hp, -⟩ := hstep a hcyc
    have ha : a ∈ δ.edges.map Prod.snd := List.mem_map.2 ⟨(p, a), (edge_iff).1 hp, rfl⟩
    obtain ⟨q, hq, -⟩ := hstep _ (hon δ.edges.length)
    exact absurd (hc a ha) (by rw [predOf_of_edge hu hq]; simp)
  · intro hwf
    exact ⟨hwf.uniq, fun x _ => predOf_up_none hwf.acyclic x⟩

instance (δ : FwdCtx) : Decidable δ.WF := decidable_of_iff _ wfB_iff

end FwdCtx
