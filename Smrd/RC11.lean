import Smrd.DPPast

/-!
# RC11 as a parallel theory

RC11 (Lahav, Vafeiadis, Kang, Hur and Dreyer, *Repairing Sequential
Consistency in C/C++11*, PLDI 2017) over the executions of this library: its
four axioms, stated with the shared definitions of `Smrd.Executions`
(`rf`, `CO`, `ECO`, `SW`, `HB`, `psc`), and no others.

    ConsistentRC11 Ω ≜ IsExecution Ω ∧ φ ∧ NoElision ∧
                       NoThinAirRC11 ∧ Coherent

* **Coherence**: `HB ; ECO?` irreflexive, `HB ≜ (⊑ ∪ SW)⁺`
  (`Execution.Coherence`);
* **Atomicity**: `rmw ∩ (FR ; CO) = ∅` (`Execution.Atomicity`);
* **SC**: `psc_base ∪ psc_F` acyclic, over `⊑` and RC11's `HB`
  (`Execution.PSC`);
* **No-Thin-Air** (RC11's "no load buffering"): `⊑ ∪ rf` acyclic
  (`Execution.NoThinAirRC11`).

The last three share one coherence order with the first (`Execution.Coherent`).
sMRD's `Consistent` asks for the same `Coherent`, and differs only in
No-Thin-Air, `acyclic(DP ∪ ≼ ∪ rf)` (`Execution.NoThinAir`), and in admitting
elaborations.

## Elaborations

RC11 transforms no program: it has neither Forwarding nor Write Elision. An
RC11 execution is therefore an execution of this library whose forwarding
context moves no event, `† = ∅` (`NoElision`; implied by `δ = ∅`,
`noElision_of_δ_empty`). The justifications stay: under `† = ∅` they only
constrain the symbolic values, through `P` in `φ` and `sameLoc`, and RC11's
No-Thin-Air does not look at their dependencies. With `† = ∅` the transformed
execution `X ∖ †` is `X`, so RC11's verdict is the same whether coherence is
read over `X` (`Consistent`) or over `X ∖ †` (`ConsistentT`,
`consistentT_iff_consistent`).

## Results

* `consistent_of_consistentRC11`: RC11-consistent executions are
  sMRD-consistent where `DP ∪ ≼ ⊆ ⊑` (stated as the hypothesis `hdep`), and
  `consistentT_of_consistentRC11` for `ConsistentT`. `consistentRC11_iff`:
  under the same hypothesis RC11-consistency is sMRD-consistency together
  with `† = ∅` and RC11's No-Thin-Air.
* `dep_po_of_noElision`: `hdep` holds without elision for `RMWTight`
  executions of `SymWF` event structures with `⊑` transitive, and
  `consistent_of_consistentRC11'` uses it.
* `linearisation`: the events of an RC11-consistent execution can be listed
  without repetition so that no `(⊑ ∪ rf)⁺`-edge points backwards: a
  linearisation of `⊑ ∪ rf` (`linearise`, for any acyclic relation on a
  finite list).

Load buffering (`r1 := y; x := 1 ∥ r2 := x; y := 1` with `r1 = r2 = 1`) is
where sMRD and RC11 part: its execution is cyclic in `⊑ ∪ rf`, and acyclic in
`DP ∪ ≼ ∪ rf` where neither write depends on the read before it (not
mechanised here).
Use-after-free under RC11's verdict takes `ntaRC11 = (⊑ ∪ rf)⁺` for sMRD's
`nta` (`Execution.UseAfterFree`).
-/

namespace Smrd.RC11

open Execution

variable (es : EventStructure) (x : Execution)

/-- No event is elided: `† = ∅`. RC11 has no elaborations. -/
def NoElision : Prop := ∀ e, ¬ x.elided e

/-- **RC11-consistency** (Lahav et al., PLDI 2017): an execution without
    elaborations (`† = ∅`), with `φ`, RC11's No-Thin-Air `acyclic(⊑ ∪ rf)`, and
    RC11's coherence, atomicity and SC axioms under one coherence order. -/
def ConsistentRC11 (Ω : Pred) : Prop :=
  x.IsExecution es Ω ∧ x.phi es ∧ NoElision x ∧ x.NoThinAirRC11 es ∧ x.Coherent es

variable {es x}

/-- Without forwarding or write elision, `† = ∅`. -/
theorem noElision_of_δ_empty (h : x.δ = .empty) : NoElision x :=
  x.not_elided_of_δ_empty h

/-- Without elided events no `F ∪ WE` edge exists. -/
theorem noEdge_of_noElision (h : NoElision x) : ∀ a b, ¬ x.δ.edge a b :=
  fun _ b he => h b ((x.elided_iff b).2 ⟨_, he⟩)

/-- `DP ∪ ≼` relates events of `X` only. -/
theorem dep_X {a b : EventId} (h : x.dep es a b) : x.X a ∧ x.X b := by
  rcases h with h | h
  · exact ⟨h.1, h.2.1⟩
  · exact ⟨h.1, h.2.1⟩

/-- **RC11's No-Thin-Air implies sMRD's** where `DP ∪ ≼ ⊆ ⊑`. -/
theorem noThinAir_of_noThinAirRC11 (hdep : ∀ a b, x.dep es a b → es.poR a b)
    (h : x.NoThinAirRC11 es) : x.NoThinAir es := fun a hc =>
  h a (transGen_mono (fun c d s => by
    rcases s with s | s
    · exact .inl ⟨.inl (dep_X s).1, .inl (dep_X s).2, hdep c d s⟩
    · exact .inr s) hc)

/-- **RC11-consistency implies sMRD-consistency** where `DP ∪ ≼ ⊆ ⊑`. -/
theorem consistent_of_consistentRC11 {Ω : Pred} (hdep : ∀ a b, x.dep es a b → es.poR a b)
    (h : ConsistentRC11 es x Ω) : x.Consistent es Ω :=
  ⟨h.1, h.2.1, noThinAir_of_noThinAirRC11 hdep h.2.2.2.1, h.2.2.2.2⟩

/-- With `† = ∅`, coherence over `X` and over `X ∖ †` agree. -/
theorem consistentT_iff_consistent {Ω : Pred} (h : NoElision x) :
    x.ConsistentT es Ω ↔ x.Consistent es Ω := by
  unfold ConsistentT Consistent
  rw [coherentT_iff_coherent h]

/-- **RC11-consistency implies sMRD-consistency over `X ∖ †`** where
    `DP ∪ ≼ ⊆ ⊑`. -/
theorem consistentT_of_consistentRC11 {Ω : Pred} (hdep : ∀ a b, x.dep es a b → es.poR a b)
    (h : ConsistentRC11 es x Ω) : x.ConsistentT es Ω :=
  (consistentT_iff_consistent h.2.2.1).2 (consistent_of_consistentRC11 hdep h)

/-- **RC11-consistency is sMRD-consistency without elaborations and with
    RC11's No-Thin-Air**, where `DP ∪ ≼ ⊆ ⊑`. -/
theorem consistentRC11_iff {Ω : Pred} (hdep : ∀ a b, x.dep es a b → es.poR a b) :
    ConsistentRC11 es x Ω ↔ x.Consistent es Ω ∧ NoElision x ∧ x.NoThinAirRC11 es :=
  ⟨fun h => ⟨consistent_of_consistentRC11 hdep h, h.2.2.1, h.2.2.2.1⟩,
   fun ⟨h, hn, hr⟩ => ⟨h.1, h.2.1, hn, hr, h.2.2.2⟩⟩

/-- **`DP ∪ ≼ ⊆ ⊑` without elision**, for `RMWTight` executions of `SymWF`
    event structures whose `⊑` is transitive (`ppoStep_po`, `dp_po_noFwd`). -/
theorem dep_po_of_noElision {Ω : Pred} (hx : x.IsExecution es Ω) (h : NoElision x)
    (hT : RMWTight es x) (hwf : es.SymWF)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c) :
    ∀ a b, x.dep es a b → es.poR a b := by
  have hnoδ := noEdge_of_noElision h
  rintro a b (hp | hd)
  · exact ppo_po hpo_trans (fun _ _ s => ppoStep_po hnoδ hT s) hp
  · exact dp_po_noFwd hx hwf hpo_trans (fun p hp => hnoδ p.1 p.2 (.inl hp)) a b hd

/-- `consistent_of_consistentRC11` with `DP ∪ ≼ ⊆ ⊑` derived. -/
theorem consistent_of_consistentRC11' {Ω : Pred} (hT : RMWTight es x) (hwf : es.SymWF)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (h : ConsistentRC11 es x Ω) : x.Consistent es Ω :=
  consistent_of_consistentRC11 (dep_po_of_noElision h.1 h.2.2.1 hT hwf hpo_trans) h

/-! ## Linearisations of `⊑ ∪ rf` -/

/-- A nonempty list has an element no element of it reaches by an acyclic
    relation. -/
theorem exists_min {R : Rel} (hR : Rel.Acyclic R) :
    ∀ (S : List EventId), S ≠ [] → ∃ m ∈ S, ∀ s ∈ S, ¬ Relation.TransGen R s m
  | [], h => absurd rfl h
  | a :: S, _ => by
    by_cases hS : S = []
    · subst hS
      refine ⟨a, by simp, fun s hs => ?_⟩
      rw [List.mem_singleton] at hs
      subst hs
      exact hR s
    · obtain ⟨m, hm, hmin⟩ := exists_min hR S hS
      by_cases ham : Relation.TransGen R a m
      · refine ⟨a, by simp, fun s hs => ?_⟩
        rcases List.mem_cons.1 hs with rfl | hs
        · exact hR s
        · exact fun h => hmin s hs (transGen_trans h ham)
      · refine ⟨m, List.mem_cons_of_mem _ hm, fun s hs => ?_⟩
        rcases List.mem_cons.1 hs with rfl | hs
        · exact ham
        · exact hmin s hs

/-- **Every acyclic relation has a linearisation on a finite list**: the
    elements of `S`, without repetition, so that no `R⁺`-edge points backwards. -/
theorem linearise {R : Rel} (hR : Rel.Acyclic R) :
    ∀ (n : Nat) (S : List EventId), S.length ≤ n → ∃ l : List EventId,
      (∀ a, a ∈ l ↔ a ∈ S) ∧ l.Nodup ∧ l.Pairwise (fun a b => ¬ Relation.TransGen R b a)
  | 0, S, h => by
    have : S = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 h)
    subst this
    exact ⟨[], by simp, .nil, .nil⟩
  | n + 1, S, h => by
    by_cases hS : S = []
    · subst hS
      exact ⟨[], by simp, .nil, .nil⟩
    · obtain ⟨m, hm, hmin⟩ := exists_min hR S hS
      have hlen : (S.filter (fun a => a != m)).length ≤ n := by
        have : (S.filter (fun a => a != m)).length < S.length :=
          List.length_filter_lt_length_iff_exists.2 ⟨m, hm, by simp⟩
        omega
      obtain ⟨l, hl, hnd, hpw⟩ := linearise hR n _ hlen
      have hmem : ∀ a, a ∈ l ↔ a ∈ S ∧ a ≠ m := fun a => by
        rw [hl, List.mem_filter]; simp
      refine ⟨m :: l, fun a => ?_, ?_, ?_⟩
      · rw [List.mem_cons, hmem]
        constructor
        · rintro (rfl | ⟨h, -⟩)
          · exact hm
          · exact h
        · intro h
          by_cases e : a = m
          · exact .inl e
          · exact .inr ⟨h, e⟩
      · exact List.nodup_cons.2 ⟨fun h => ((hmem m).1 h).2 rfl, hnd⟩
      · exact List.Pairwise.cons (fun b hb => hmin b ((hmem b).1 hb).1) hpw

/-- Events of an execution are events of the event structure. -/
theorem mem_ids {Ω : Pred} (hx : x.IsExecution es Ω) {a : EventId} (h : x.X a) :
    a ∈ es.ids := by
  obtain ⟨e, he, rfl⟩ := (hx.maximal.1 a h).1
  exact List.mem_map.2 ⟨e, he, rfl⟩

open Classical in
/-- **RC11-consistent executions are linearisable**: the events of `X` can be
    listed without repetition so that no `(⊑ ∪ rf)⁺`-edge points backwards, an
    order in which a machine performing one event at a time, in program
    order and reading from earlier writes, can perform them. -/
theorem linearisation {Ω : Pred} (h : ConsistentRC11 es x Ω) :
    ∃ l : List EventId, (∀ a, a ∈ l ↔ x.X a) ∧ l.Nodup ∧
      l.Pairwise (fun a b => ¬ Relation.TransGen ((x.poX es).union x.rf) b a) := by
  obtain ⟨l, hl, hnd, hpw⟩ :=
    linearise h.2.2.2.1 _ (es.ids.filter (fun a => decide (x.X a))) (Nat.le_refl _)
  refine ⟨l, fun a => ?_, hnd, hpw⟩
  rw [hl, List.mem_filter]
  simp only [decide_eq_true_eq]
  exact ⟨fun h => h.2, fun ha => ⟨mem_ids h.1 ha, ha⟩⟩

end Smrd.RC11
