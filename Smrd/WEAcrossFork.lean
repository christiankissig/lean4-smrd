import Smrd.PpoNecessity
import Smrd.CoherenceT

/-!
# Write Elision into a thread that joins again: `≼` across threads without forwarding

`x := 0; (x := 1 ∥ x := 2); y := 3`, Write Elision eliding `x := 0` into
`x := 1`, with no forwarding. It is `PpoNecessity`'s `x := 0; (x := 1 ∥ x := 2)`
(N2) with code after the join.

* Every condition of Write Elision but its join restriction holds
  (`we_01_blind`): `x := 0` is the immediate `≼`-predecessor of `x := 1`, and
  nothing lies between. So does the join restriction as it reads for
  Forwarding, every event `⊑`-below the eliding write comparable with the
  elided one (`below_cmp`): only `x := 0` is below `x := 1`.
* `ppo_loc` has `(x := 0, x := 2)`, and `remap_δ` sends `x := 0` onto
  `x := 1`. Both `x := 1` and `x := 2` are `⊑`-below `y := 3`, which is on
  the path, so `≼` relates `x := 1` to `x := 2` (`ppo_12`), two events of
  different threads that `⊑` does not order: `DP ∪ ≼ ⊄ ⊑`
  (`not_dep_po`), without forwarding. Without `y := 3` the pair is not
  anchored (N2).
* Write Elision's join restriction (`EventStructure.weNoJoin`) refutes the
  elision (`not_weNoJoin`): `x := 2` is `⊑`-above `x := 0`, joinable with
  `x := 1` (at `y := 3`) and not comparable with it.

So `≼` relates `⊑`-incomparable events without forwarding, and Write
Elision needs a join restriction too, of the other shape than Forwarding's:
the elision moves `x := 0` forward past a fork, Forwarding moves its target
backward past a join. Before remapping, `≼` relates no incomparable events:
its parts are `⊑`-pairs (`Execution.ppoStep_po` without `F ∪ WE` edges).
-/

namespace WEAcrossFork

open EventStructure PpoKit PpoStability PpoNecessity Execution

/-- `x := 0; (x := 1 ∥ x := 2); y := 3` -/
def prog : Stmt :=
  .seq (st .rlx "x" 0) (.seq (.par (st .rlx "x" 1) (st .rlx "x" 2)) (st .rlx "y" 3))

def e0 : Event := W 0 0 [0] .rlx "x" 0
def e1 : Event := W 1 0 [1, 0, 0] .rlx "x" 1
def e2 : Event := W 2 1 [1, 0, 1] .rlx "x" 2
def e3 : Event := W 3 0 [1, 1] .rlx "y" 3

/-- `⊑`: `x := 0` first, the two threads unordered, both before `y := 3`. -/
def poL : List (EventId × EventId) := [(0, 1), (0, 2), (0, 3), (1, 3), (2, 3)]

def esQ : EventStructure := ⟨[e0, e1, e2, e3], poL, []⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esQ := rfl

theorem SQ : Simple esQ := ⟨by decide, by decide, rfl⟩
theorem gQ : GlobLocs esQ := globLocs_of (by decide)
theorem po_of {a b : EventId} (h : (a, b) ∈ poL) : esQ.poR a b := h
theorem not_po_12 : ¬ esQ.poR 1 2 := fun h => absurd (show (1, 2) ∈ poL from h) (by decide)
theorem not_po_21 : ¬ esQ.poR 2 1 := fun h => absurd (show (2, 1) ∈ poL from h) (by decide)

/-! ## The elision -/

/-- `x := 1`'s pre-justification. -/
def jPre : Justification := pj e1
/-- … with `x := 0` elided into it, `WE = {(1, 0)}`. -/
def jWE : Justification := { jPre with δ := { jPre.δ with we := jPre.δ.we ++ [(1, 0)] } }

/-- **Write Elision of `x := 0` into `x := 1`, under every condition but the
    join restriction.** -/
theorem we_01_blind : esQ.weRelBlind jPre 0 1 ∧ esQ.weNoRel 0 1 ∧ ¬ esQ.RMWAcc 0 := by
  have hδ0 : ∀ a b, ¬ jPre.δ.edge a b := by
    intro a b h; rcases h with h | h <;> cases h
  have hppo : ∀ a b, esQ.ppo jPre.P.holds jPre.δ a b → (a, b) ∈ syncL esQ ++ aliasL esQ :=
    fun a b h => ppo_mem rfl gQ hδ0 h
  refine ⟨⟨⟨⟨⟨(FwdCtx.remapRel_of_noEdge hδ0).2 (.inr
      ⟨po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl, fun _ => .num 0,
        SQ.holds (e := e1) (by simp [esQ]) _,
        by simp [Expr.holds, Expr.eval, Expr.glob]⟩), by decide⟩, ?_⟩,
      po_of (by decide),
      _, _, _, _, rfl, rfl, rfl, rfl, fun _ _ _ _ h₁ h₂ => by rw [h₁] at h₂; cases h₂; rfl⟩,
    ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, fun ⟨e, he, hp⟩ => by cases he; simp [e0, PpoNecessity.W, Event.isVol] at hp⟩,
    weNoRel_of (by decide) (by decide), EventStructure.not_rmwAcc_of_nil _ rfl _⟩
  rintro ⟨e'', h₁, h₂⟩
  have m₁ := hppo _ _ h₁
  have m₂ := hppo _ _ h₂
  have key : ∀ p ∈ syncL esQ ++ aliasL esQ, ∀ q ∈ syncL esQ ++ aliasL esQ,
      p.1 = 0 → q.2 = 1 → p.2 = q.1 → False := by decide
  exact key _ m₁ _ m₂ rfl rfl rfl

/-- Every event `⊑`-below the eliding write `x := 1` is comparable with the
    elided `x := 0`: the shape of Forwarding's join restriction holds. -/
theorem below_cmp : ∀ c, esQ.poR c 1 → esQ.PoCmp c 0 := fun c h => by
  have key : ∀ p ∈ poL, p.2 = 1 → p.1 = 0 := by decide
  exact .inl (key _ h rfl)

/-- **Write Elision's join restriction fails**: `x := 2` is `⊑`-above
    `x := 0`, joinable with `x := 1` at `y := 3`, and not comparable with it. -/
theorem not_weNoJoin : ¬ esQ.weNoJoin 0 1 := fun h => by
  rcases h 2 (esQ.joinCmp_of_poCmp (.inr (.inr (po_of (by decide)))))
    ⟨3, .inr (po_of (by decide)), .inr (po_of (by decide))⟩ with h | h | h
  · cases h
  · exact not_po_21 h
  · exact not_po_12 h

theorem not_weRel (j : Justification) : ¬ esQ.weRel j 0 1 :=
  fun h => not_weNoJoin h.2.2.1

/-- **No generated justification elides `x := 0` into `x := 1`.** -/
theorem not_generated {Ω : Pred} {j : Justification} (h : esQ.Generated Ω j) :
    (1, 0) ∉ j.δ.we := by
  intro hp
  obtain ⟨j₀, h₀, -⟩ := Generated.we_mem esQ h _ hp
  exact not_weRel j₀ h₀

/-! ## The execution and its `≼` -/

def JQ : List Justification := [jWE, pj e2, pj e3]
def xQ : Execution := ⟨esQ.Candidate, JQ, fun _ _ => False⟩

theorem δQ : xQ.δ = ⟨[], [(1, 0)]⟩ := rfl

theorem edge_Q {a b : EventId} (h : xQ.δ.edge a b) : a = 1 ∧ b = 0 := by
  rw [δQ] at h
  rcases h with h | h
  · cases h
  · simp at h; exact h

/-- No forwarding. -/
theorem noFwd_Q : ∀ p ∈ xQ.δ.f, False := fun p hp => by rw [δQ] at hp; cases hp

theorem X_Q {a : EventId} (h : a ∈ esQ.ids := by decide) : xQ.X a := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
  exact cand_of_mem SQ.nodup he (by revert e; decide) (by revert e; decide)

theorem canon_Q {a : EventId} (h : a ≠ 0) : xQ.δ.Remap a a :=
  .canon fun _ hc => h (edge_Q hc).2

theorem remap_01 : xQ.δ.Remap 0 1 :=
  .step (.inr (by rw [δQ]; simp)) (canon_Q (by decide))

/-- **`≼` orders `x := 1` before `x := 2`**: `ppo_loc` (in the part of
    `y := 3`'s justification) has `(x := 0, x := 2)`, `remap_δ` sends
    `x := 0` onto `x := 1`, and both ends lie in the window of `y := 3`. -/
theorem ppo_12 : xQ.ppo esQ 1 2 := by
  have must : esQ.mustAlias 0 2 :=
    ⟨e0, e2, _, _, rfl, rfl, rfl, rfl, fun _ _ _ h₁ h₂ => Option.some.inj (h₁.symm.trans h₂)⟩
  have hm : esQ.ppoM (xQ.PJ esQ (pj e3)) (pj e3).P.holds xQ.δ 1 2 :=
    ⟨⟨0, 2, .inr ⟨po_of (by decide), .inl must⟩, remap_01, canon_Q (by decide)⟩, by decide⟩
  exact ⟨X_Q, X_Q, .single ⟨.inl X_Q, .inl X_Q, .inl
    ⟨pj e3, by simp [xQ, JQ], hm, .inr (po_of (by decide)), .inr (po_of (by decide))⟩⟩⟩

/-- **`DP ∪ ≼ ⊄ ⊑`**, without forwarding. -/
theorem not_dep_po : ¬ ∀ a b, xQ.dep esQ a b → xQ.poX esQ a b :=
  fun h => not_po_12 (h 1 2 (.inl ppo_12)).2.2

/-- **Were the join restriction dropped, `xQ` would be an execution**:
    everything an execution asks holds once `jWE` is generated, as Write
    Elision would generate it from `x := 1`'s pre-justification along
    `we_01_blind`. -/
theorem isExecution_Q (gen_jWE : esQ.Generated (fun _ => True) jWE) :
    xQ.IsExecution esQ (fun _ => True) where
  maximal := ⟨fun _ h => h, fun a b _ _ ⟨ea, eb, ha, hb, hn⟩ =>
      hn ⟨fun _ => .num 0, SQ.holds (ev_inv ha).1 _, SQ.holds (ev_inv hb).1 _⟩,
    fun _ hc hn => absurd hc hn⟩
  generated j hj := by
    simp only [xQ, JQ, List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · exact gen_jWE
    · exact .pre (w := e2) (by simp [esQ]) rfl ⟨fun _ => .num 0, SQ.holds (by simp [esQ]) _⟩
    · exact .pre (w := e3) (by simp [esQ]) rfl ⟨fun _ => .num 0, SQ.holds (by simp [esQ]) _⟩
  inX j hj := by
    simp only [xQ, JQ, List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> exact X_Q
  consistent := ⟨fun _ => .num 0, fun j hj => by
      simp only [xQ, JQ, List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> simp [jWE, jPre, pj, e1, e2, e3, PpoNecessity.W, Event.valres,
        Expr.conj, Expr.holds, Expr.eval, Expr.tt],
    fun a e _ he => SQ.holds (ev_inv he).1 _⟩
  fwdWF := by
    rw [δQ]
    refine ⟨fun a ha => ?_, fun a b e ha hb => ?_⟩
    · have : ∀ c d, Relation.TransGen (FwdCtx.edge ⟨[], [(1, 0)]⟩) c d → c = 1 ∧ d = 0 := by
        intro c d h
        induction h with
        | single h => rcases h with h | h <;> simp at h; exact h
        | tail _ h ih =>
            rcases h with h | h <;> simp at h
            obtain ⟨-, rfl⟩ := ih; cases h.1
      have := this a a ha
      rw [this.1] at this; cases this.2
    · rcases ha with h | h <;> simp at h
      rcases hb with h' | h' <;> simp at h'
      rw [h.1, h'.1]
  rf_wr _ _ h := h.elim
  rf_func _ _ _ h := h.elim
  justified w hw he hn := by
    have hids : w ∈ esQ.ids := ids_of_cand hw
    have hw' : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 := by
      simp [EventStructure.ids, esQ, e0, e1, e2, e3, PpoNecessity.W] at hids; omega
    have uniq : ∀ j ∈ xQ.J, ∀ j' ∈ xQ.J, j.w.id = j'.w.id → j' = j := by
      intro j hj j' hj' h
      simp only [xQ, JQ, List.mem_cons, List.mem_nil_iff, or_false] at hj hj'
      rcases hj with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl <;>
        first | rfl | cases h
    have mk : ∀ j ∈ xQ.J, j.w.id = w →
        ∃ j ∈ xQ.J, j.w.id = w ∧ ∀ j' ∈ xQ.J, j'.w.id = w → j' = j :=
      fun j hj h => ⟨j, hj, h, fun j' hj' h' => uniq j hj j' hj' (h.trans h'.symm)⟩
    rcases hw' with rfl | rfl | rfl | rfl
    · exact absurd ⟨(1, 0), .inr (by rw [δQ]; simp), rfl⟩ hn
    · exact mk jWE (by simp [xQ, JQ]) rfl
    · exact mk (pj e2) (by simp [xQ, JQ]) rfl
    · exact mk (pj e3) (by simp [xQ, JQ]) rfl

/-- **`xQ` is not an execution**: no generated justification elides `x := 0`
    into `x := 1`. -/
theorem not_isExecution {Ω : Pred} : ¬ xQ.IsExecution esQ Ω := fun hx => by
  have hg := hx.generated jWE (by simp [xQ, JQ])
  exact not_generated hg (by simp [jWE, jPre, pj, FwdCtx.empty])

/-- **Without Write Elision's join restriction, `≼` relates `⊑`-incomparable
    events of two threads without forwarding**, in the event structure of a
    program: the elision of `x := 0` into `x := 1` meets every other
    condition of Write Elision, and the shape of Forwarding's join
    restriction (`below_cmp`); `xQ` is an execution if it is generated; and
    `≼` relates `x := 1` to `x := 2`. The join restriction refutes the
    elision. -/
theorem fork_join :
    denote (fun _ => 0) prog = esQ ∧
    (esQ.weRelBlind jPre 0 1 ∧ esQ.weNoRel 0 1 ∧ ¬ esQ.RMWAcc 0) ∧
    (∀ c, esQ.poR c 1 → esQ.PoCmp c 0) ∧
    (esQ.Generated (fun _ => True) jWE → xQ.IsExecution esQ (fun _ => True)) ∧
    (∀ p ∈ xQ.δ.f, False) ∧
    xQ.ppo esQ 1 2 ∧ ¬ esQ.poR 1 2 ∧ ¬ esQ.poR 2 1 ∧
    ¬ (∀ a b, xQ.dep esQ a b → xQ.poX esQ a b) ∧
    ¬ esQ.weNoJoin 0 1 ∧ (∀ Ω : Pred, ¬ xQ.IsExecution esQ Ω) :=
  ⟨denote_prog, we_01_blind, below_cmp, isExecution_Q, noFwd_Q, ppo_12, not_po_12, not_po_21,
    not_dep_po, not_weNoJoin, fun _ => not_isExecution⟩

end WEAcrossFork
