import Smrd.PpoNecessity

/-!
# Write Elision past a fork: excluded by the fork restriction, not by the join condition

`x := 0; x := 5; (x := 1 ∥ r := x)`, Write Elision eliding `x := 5` into
`x := 1`, the write of one forked thread.

* Every condition of Write Elision but the fork restriction holds
  (`we_12_join`): `x := 5` is the immediate `≼`-predecessor of `x := 1` at its
  location, nothing publishes in between, and the join condition `weNoJoin`
  holds, as the threads do not join again (`⊑` is a forest).
* The fork restriction (`EventStructure.weNoFork`) refutes it
  (`not_weNoFork`): `r := x` is `⊑`-after `x := 5` and not comparable with
  `x := 1`. So no generated justification elides `x := 5` into `x := 1`
  (`not_generated`).

Why the elision has to go: a fork synchronises like a release. In RC11
`x := 5` happens before `r := x` (through the fork), and `x := 0` is
coherence-before `x := 5`, so `r := x` does not read `x := 0`. Eliding `x := 5`
into `x := 1` sinks it past the fork, into one thread; with elided writes out
of coherence (`Execution.CoherenceT`), `r := x` happens after neither remaining
write of the thread, and could read `x := 0`. The rule matches MoRDor's
write-elision restriction (`ForwardElab.elision_blocked`), whose litmus test
`own/we-across-fork.lit` is this program.
-/

namespace WEPastFork

open EventStructure PpoKit PpoStability PpoNecessity Execution

/-- `x := 0; x := 5; (x := 1 ∥ r := x)` -/
def prog : Stmt :=
  .seq (st .rlx "x" 0) (.seq (st .rlx "x" 5) (.par (st .rlx "x" 1) (ld .rlx "r" "x")))

def e0 : Event := W 0 0 [0] .rlx "x" 0
def e1 : Event := W 1 0 [1, 0] .rlx "x" 5
def e2 : Event := W 2 0 [1, 1, 0] .rlx "x" 1
def e3 : Event := R 3 1 [1, 1, 1] .rlx "x"

/-- `⊑`: `x := 0` before `x := 5`, both before the two threads. -/
def poL : List (EventId × EventId) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]

def esF : EventStructure := ⟨[e0, e1, e2, e3], poL, []⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esF := rfl

theorem SF : Simple esF := ⟨by decide, by decide, rfl⟩
theorem gF : GlobLocs esF := globLocs_of (by decide)
theorem po_of {a b : EventId} (h : (a, b) ∈ poL) : esF.poR a b := h
theorem not_po_23 : ¬ esF.poR 2 3 := fun h => absurd (show (2, 3) ∈ poL from h) (by decide)
theorem not_po_32 : ¬ esF.poR 3 2 := fun h => absurd (show (3, 2) ∈ poL from h) (by decide)

/-- `x := 1`'s pre-justification. -/
def jPre : Justification := pj e2

/-- **Eliding `x := 5` into `x := 1` meets every condition of Write Elision
    but the fork restriction**: the paper's conditions (`weRelBlind`), the
    release restriction, the join condition, and no RMW access elided. -/
theorem we_12_join :
    esF.weRelBlind jPre 1 2 ∧ esF.weNoRel 1 2 ∧ esF.weNoJoin 1 2 ∧ ¬ esF.RMWAcc 1 := by
  have hδ0 : ∀ a b, ¬ jPre.δ.edge a b := by
    intro a b h; rcases h with h | h <;> cases h
  have hppo : ∀ a b, esF.ppo jPre.P.holds jPre.δ a b → (a, b) ∈ syncL esF ++ aliasL esF :=
    fun a b h => ppo_mem rfl gF hδ0 h
  refine ⟨⟨⟨⟨⟨(FwdCtx.remapRel_of_noEdge hδ0).2 (.inr
      ⟨po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl, fun _ => .num 0,
        SF.holds (e := e2) (by simp [esF]) _,
        by simp [Expr.holds, Expr.eval, Expr.glob]⟩), by decide⟩, ?_⟩,
      po_of (by decide),
      _, _, _, _, rfl, rfl, rfl, rfl, fun _ _ _ _ h₁ h₂ => by rw [h₁] at h₂; cases h₂; rfl⟩,
    ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩,
    fun ⟨e, he, hp⟩ => by cases he; simp [e1, PpoNecessity.W, Event.isVol] at hp⟩,
    weNoRel_of (by decide) (by decide),
    Execution.weNoJoin_of_poForest (poForest_of (by decide)) _ _,
    EventStructure.not_rmwAcc_of_nil _ rfl _⟩
  rintro ⟨e'', h₁, h₂⟩
  have m₁ := hppo _ _ h₁
  have m₂ := hppo _ _ h₂
  have key : ∀ p ∈ syncL esF ++ aliasL esF, ∀ q ∈ syncL esF ++ aliasL esF,
      p.1 = 1 → q.2 = 2 → p.2 = q.1 → False := by decide
  exact key _ m₁ _ m₂ rfl rfl rfl

/-- **The fork restriction fails**: `r := x` is `⊑`-after `x := 5` and not
    comparable with `x := 1`. -/
theorem not_weNoFork : ¬ esF.weNoFork 1 2 := fun h => by
  rcases h 3 (po_of (by decide)) (by decide)
      (fun hd => absurd hd (not_diverged_of (by decide))) with h | h | h
  · cases h
  · exact not_po_32 h
  · exact not_po_23 h

theorem not_weRel (j : Justification) : ¬ esF.weRel j 1 2 :=
  fun h => not_weNoFork h.2.2.1

/-- **No generated justification elides `x := 5` into `x := 1`.** -/
theorem not_generated {Ω : Pred} {j : Justification} (h : esF.Generated Ω j) :
    (2, 1) ∉ j.δ.we := by
  intro hp
  obtain ⟨j₀, h₀, -⟩ := Generated.we_mem esF h _ hp
  exact not_weRel j₀ h₀

/-- **Write Elision past a fork**: in the event structure of
    `x := 0; x := 5; (x := 1 ∥ r := x)`, eliding `x := 5` into `x := 1` meets
    the paper's conditions, the release restriction and the join condition,
    and the fork restriction excludes it. -/
theorem past_fork :
    denote (fun _ => 0) prog = esF ∧
    (esF.weRelBlind jPre 1 2 ∧ esF.weNoRel 1 2 ∧ esF.weNoJoin 1 2 ∧ ¬ esF.RMWAcc 1) ∧
    ¬ esF.weNoFork 1 2 ∧
    ∀ {Ω : Pred} {j : Justification}, esF.Generated Ω j → (2, 1) ∉ j.δ.we :=
  ⟨denote_prog, we_12_join, not_weNoFork, not_generated⟩

end WEPastFork
