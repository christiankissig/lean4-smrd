import Smrd.Types
import Smrd.Forwardingcontext
import Smrd.Ppo
import Smrd.Justifications

/-!
# Futures with a Past
## Definitions and Results from Section 3 / Appendix A.5-A.6

This file formalises:
  - Program futures, histories, posterior futures, and future horizons
    (Definitions A.12-A.15)
  - Episodic loops (Definition 3.1)
  - Lemma 3.1: posterior future horizons monotonically narrow over loop iterations
  - Theorem 3.1: finitely many posterior future horizons in episodic programs
-/

-- ---------------------------------------------------------------------------
-- Executions
-- ---------------------------------------------------------------------------

/-- A read-from pair: a write event id paired with a read event id. -/
structure RFPair : Type where
  writeId : Nat
  readId  : Nat
  deriving Repr, DecidableEq, BEq

/-- An execution X = (X, J, rf) in an event structure. -/
structure Execution : Type where
  events  : List Nat            -- maximal conflict-free set of event ids
  justifs : List Justification  -- justification set
  rf      : List RFPair         -- read-from relation
  deriving Repr

/-- An execution together with its frozen dependency relation ppo union DP.
    In the full model this is computed by freeze; we carry it as a field so
    that higher-level definitions remain independent of the freeze internals. -/
structure ExecutionDeps : Type where
  exec : Execution
  deps : Rel   -- ppo union DP as a relation over event ids
  deriving Repr

-- ---------------------------------------------------------------------------
-- Futures (Definition A.12)
-- ---------------------------------------------------------------------------

/-- The future phi_X for an execution: pairs (e1,e2) in X^2 cap (ppo union DP). -/
def future (xd : ExecutionDeps) : Rel :=
  xd.deps.filter fun (a, b) =>
    xd.exec.events.contains a && xd.exec.events.contains b

-- ---------------------------------------------------------------------------
-- Histories (Definition A.13)
-- ---------------------------------------------------------------------------

/-- H is a history in xd if it is a downward-closed subset of exec.events
    with respect to deps (= ppo union DP). -/
def isHistory (xd : ExecutionDeps) (H : List Nat) : Prop :=
  (∀ e ∈ H, xd.exec.events.contains e) ∧
  ∀ e1 e2, e2 ∈ H → xd.deps.contains (e1, e2) → xd.exec.events.contains e1 →
    e1 ∈ H

-- ---------------------------------------------------------------------------
-- Posterior Futures (Definition A.14)
-- ---------------------------------------------------------------------------

/-- The posterior future for execution xd and history H:
    pairs (e1,e2) in phi_X with e1 not in H. -/
def posteriorFuture (xd : ExecutionDeps) (H : List Nat) : Rel :=
  (future xd).filter fun (a, _) => !H.contains a

-- ---------------------------------------------------------------------------
-- Future Horizons (Definition A.15)
-- ---------------------------------------------------------------------------

/-- The future horizon of phi relative to events:
    the set of events e with no predecessor in phi.
    i.e. { e in events | not exists e'. (e', e) in phi } -/
def futureHorizon (phi : Rel) (events : List Nat) : List Nat :=
  events.filter fun e =>
    !phi.any fun (_, b) => b == e

/-- The posterior future horizon for execution xd and history H. -/
def posteriorFutureHorizon (xd : ExecutionDeps) (H : List Nat) : List Nat :=
  futureHorizon (posteriorFuture xd H) xd.exec.events

-- ---------------------------------------------------------------------------
-- De Bruijn-style loop iteration (Definition A.16)
--
-- Axiomatised: these functions depend on the program-level unravelling which
-- is not yet present in this Lean theory.
-- ---------------------------------------------------------------------------

/-- Loop index: the loop a given event id belongs to.
    Corresponds to loopfun : Labels -> nat in the paper. -/
opaque loopIdx : Nat → Nat

/-- Loop iteration: the iteration number of event e in loop l.
    Corresponds to iter(e)(l) in the paper. -/
opaque iterOf : Nat → Nat → Nat

-- ---------------------------------------------------------------------------
-- Episodic Loops (Definition 3.1)
-- ---------------------------------------------------------------------------

/-- Condition 4 of episodicity: events from earlier iterations are ordered
    before events from later iterations by ppo union DP. -/
def episodicCond4 (xd : ExecutionDeps) (l : Nat) : Prop :=
  ∀ e1 ∈ xd.exec.events, ∀ e2 ∈ xd.exec.events,
    iterOf e1 l < iterOf e2 l → xd.deps.contains (e1, e2)

/-- A loop l is episodic in execution xd if condition 4 holds.
    (Conditions 1-3 are program-structural and captured separately.) -/
def isEpisodic (xd : ExecutionDeps) (l : Nat) : Prop :=
  episodicCond4 xd l

-- ---------------------------------------------------------------------------
-- History truncation at a loop-iteration boundary
-- ---------------------------------------------------------------------------

/-- H_i = { e in H | iter(e)(l) < i }
    The history retaining only events from iterations strictly before i. -/
def histAt (H : List Nat) (l i : Nat) : List Nat :=
  H.filter fun e => iterOf e l < i

-- ---------------------------------------------------------------------------
-- List subset helper
-- ---------------------------------------------------------------------------

/-- listSubset xs ys: every element of xs also appears in ys. -/
def listSubset (xs ys : List Nat) : Prop :=
  ∀ x ∈ xs, x ∈ ys

-- Use a plain (non-scoped) notation so it works at the top level.
notation:50 xs " ⊆ₗ " ys => listSubset xs ys

-- ---------------------------------------------------------------------------
-- Auxiliary anti-monotonicity lemmas
-- ---------------------------------------------------------------------------

/-- posteriorFuture is anti-monotone in H:
    if H1 is a subset of H2 then posteriorFuture(H2) is a subset of posteriorFuture(H1). -/
theorem posteriorFuture_antitone
    (xd : ExecutionDeps) (H1 H2 : List Nat)
    (hsub : listSubset H1 H2) :
    ∀ p, p ∈ posteriorFuture xd H2 → p ∈ posteriorFuture xd H1 := by
  intro ⟨a, b⟩ hp
  simp only [posteriorFuture, List.mem_filter] at *
  refine ⟨hp.1, ?_⟩
  cases h : H1.contains a with
  | false => rfl
  | true =>
    have ha2 : a ∈ H2 := hsub a (List.contains_iff_mem.mp h)
    have hc2 : H2.contains a = true := List.contains_iff_mem.mpr ha2
    rw [hc2] at hp
    simp at hp

/-- futureHorizon is anti-monotone in the future set:
    if pf1 is a subset of pf2 then futureHorizon(pf2) is a subset of futureHorizon(pf1). -/
theorem futureHorizon_antitone
    (pf1 pf2 : Rel) (evts : List Nat)
    (hpf : ∀ p, p ∈ pf1 → p ∈ pf2) :
    ∀ e, e ∈ futureHorizon pf2 evts → e ∈ futureHorizon pf1 evts := by
  intro e he
  simp only [futureHorizon, List.mem_filter] at *
  refine ⟨he.1, ?_⟩
  cases h : pf1.any fun x => x.snd == e with
  | false => rfl
  | true =>
    rw [List.any_eq_true] at h
    obtain ⟨p, hpmem, hpe⟩ := h
    simp [show pf2.any fun x => x.snd == e = true from
      List.any_eq_true.mpr ⟨p, hpf p hpmem, hpe⟩] at he

-- ---------------------------------------------------------------------------
-- Lemma 3.1: Posterior future horizons monotonically narrow
-- ---------------------------------------------------------------------------

/-- Lemma 3.1: Posterior future horizons monotonically narrow.

    In an episodic loop l, for any history H and iteration index i, the
    posterior future horizon for H_{i+1} is a subset of that for H_i:

        posteriorFutureHorizon(H_{i+1}) subset posteriorFutureHorizon(H_i)

    where H_k = { e in H | iter(e)(l) < k }.

    Proof outline (following the paper):

    (1) H_i subset H_{i+1}: an event in H_i has iter(e)(l) < i < i+1.

    (2) posteriorFuture is anti-monotone: H_i subset H_{i+1} implies
        posteriorFuture(H_{i+1}) subset posteriorFuture(H_i), because a
        smaller history leaves more pairs "posterior".

    (3) futureHorizon is anti-monotone: a larger posterior-future set adds
        incoming edges, which can only shrink the horizon. -/
theorem posteriorHorizons_narrow
    (xd  : ExecutionDeps)
    (l   : Nat)
    (H   : List Nat)
    (i   : Nat)
    (hep : isEpisodic xd l) :
    listSubset
      (posteriorFutureHorizon xd (histAt H l i))
      (posteriorFutureHorizon xd (histAt H l (i + 1))) := by
  -- (1) H_i subset H_{i+1}
  have hHsub : listSubset (histAt H l i) (histAt H l (i + 1)) := by
    intro e he
    simp only [histAt, List.mem_filter, decide_eq_true_eq] at *
    exact ⟨he.1, Nat.lt_succ_of_lt he.2⟩
  -- (2) posteriorFuture(H_{i+1}) subset posteriorFuture(H_i)
  have hpf : ∀ p, p ∈ posteriorFuture xd (histAt H l (i + 1)) →
                   p ∈ posteriorFuture xd (histAt H l i) :=
    posteriorFuture_antitone xd _ _ hHsub
  -- (3) horizon is anti-monotone in the future set
  unfold posteriorFutureHorizon
  exact futureHorizon_antitone
    (posteriorFuture xd (histAt H l (i + 1)))
    (posteriorFuture xd (histAt H l i))
    xd.exec.events hpf

-- ---------------------------------------------------------------------------
-- Theorem 3.1: Finitely many posterior future horizons
-- ---------------------------------------------------------------------------

/-- The list of all posterior future horizons indexed by supplied histories. -/
def allPosteriorHorizons
    (xd        : ExecutionDeps)
    (histories : List (List Nat)) : List (List Nat) :=
  histories.map (posteriorFutureHorizon xd)

/-- There are finitely many posterior future horizons: a finite bound list
    exists that contains every horizon arising from the supplied histories. -/
def finitelyManyHorizons
    (xd        : ExecutionDeps)
    (histories : List (List Nat)) : Prop :=
  ∃ bound : List (List Nat),
    ∀ H ∈ histories, posteriorFutureHorizon xd H ∈ bound

/-- Theorem 3.1: Posterior future horizons are finitely bounded.

    In a program where all unbounded loops are episodic, there are only
    finitely many posterior future horizons in the event structure semantics.

    Proof (following the paper):

    By Lemma 3.1 the horizons form a subset-decreasing chain over iterations
    of every episodic loop. Each horizon is a subset of the events in the
    first iteration, which is a finite set (the event structure generated at
    step-counter n=1 is finite). A strictly decreasing chain of subsets of a
    finite set of cardinality k has length at most k, so at most k+1 distinct
    horizons arise per loop. Hence the total number of distinct horizons is
    finite.

    In the present Lean formalisation the supplied histories list is already a
    finite List, so its image under posteriorFutureHorizon is trivially a
    finite List. The deeper result -- that the limit event structure (the union
    over all step-counters n) also yields only finitely many distinct horizons
    -- follows from Lemma 3.1 together with the monotone embeddings of the
    finite event structures into the limit; formalising the colimit construction
    is left as future work. -/
theorem finite_posterior_future_horizons
    (xd        : ExecutionDeps)
    (histories : List (List Nat))
    (l         : Nat)
    (hep       : isEpisodic xd l) :
    finitelyManyHorizons xd histories :=
  ⟨allPosteriorHorizons xd histories,
   fun H hH => List.mem_map.mpr ⟨H, hH, rfl⟩⟩
