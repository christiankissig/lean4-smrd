import Smrd.PpoNecessity

/-!
# Write Elision into one branch of a thread that joins again

`(x := 0; r := w; if r = 0 then x := 1 else x := 2 ∥ w := 1); z := 1`,
eliding `x := 0` into `x := 1`. The branching is inside the first thread of a
parallel block, and `z := 1`, after the join, is `⊑`-above both of its
outcomes.

* `x := 2` is `⊑`-after `x := 0`, on the other outcome of the branching than
  `x := 1` (`diverged_43`), and joinable with it at `z := 1`
  (`joinable_43`).
* The fork restriction (`EventStructure.weNoFork`) refuses the elision
  (`not_weNoFork`): `x := 2` is not exempt, as it has a common upper bound
  with `x := 1`, and it is not comparable with it. So does the join condition
  (`not_weNoJoin`).
* The form of the fork restriction that exempts every diverged event, MoRDor's
  `ForwardElab.elision_blocked`, admits it (`conflictForm`). That form does not
  give the join condition here, which `weNoFork` does (`weNoFork_weNoJoin`).
* Without `z := 1` the two forms agree and the elision is admitted
  (`weNoFork_noJoin`): `x := 2` is then joinable with nothing.

A branching inside a thread with code after the join is the only shape of
`⟨P⟩_n` where the two forms differ (`weNoFork_iff_conflict`); in sequential
code the continuation of a branching is generated once per outcome
(`Smrd.WEIntoBranch`).
-/

namespace WEBranchJoin

open EventStructure PpoKit PpoStability

/-- `(x := 0; r := w; if r = 0 then x := 1 else x := 2 ∥ w := 1); z := 1` -/
def prog : Stmt :=
  .seq (.par (.seq (st .rlx "x" 0) (.seq (ld .rlx "r" "w")
      (.ite (.eq (.reg "r") (.num 0)) (st .rlx "x" 1) (st .rlx "x" 2))))
    (st .rlx "w" 1))
   (st .rlx "z" 1)

/-- The parallel block alone, without the code after the join. -/
def progNoJoin : Stmt :=
  .par (.seq (st .rlx "x" 0) (.seq (ld .rlx "r" "w")
      (.ite (.eq (.reg "r") (.num 0)) (st .rlx "x" 1) (st .rlx "x" 2))))
    (st .rlx "w" 1)

/-- The branching condition `α₁ = 0`. -/
def c : Expr := .eq (.sym 1) (Expr.num 0)
def gT : Guard := ⟨2, c, true⟩
def gF : Guard := ⟨2, c, false⟩

def e0 : Event := W 0 0 [0, 0, 0] [] [] .rlx "x" 0
def e1 : Event := R 1 0 [0, 0, 1, 0] [] [] .rlx "w"
def e2 : Event := ⟨2, .branch c, ⟨0, [0, 0, 1, 1], []⟩, []⟩
def e3 : Event := W 3 0 [0, 0, 1, 1, 0] [] [gT] .rlx "x" 1
def e4 : Event := W 4 0 [0, 0, 1, 1, 1] [] [gF] .rlx "x" 2
def e5 : Event := W 5 1 [0, 1] [] [] .rlx "w" 1
def e6 : Event := W 6 0 [1] [] [] .rlx "z" 1

/-- `⊑` of the parallel block. -/
def poP : List (EventId × EventId) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4)]

/-- … and with `z := 1` after the join. -/
def poL : List (EventId × EventId) :=
  poP ++ [(0, 6), (1, 6), (2, 6), (3, 6), (4, 6), (5, 6)]

def esJ : EventStructure := ⟨[e0, e1, e2, e3, e4, e5, e6], poL, []⟩
/-- The events of the parallel block alone: the same, with the labels of a
    top-level `∥`. -/
def p0 : Event := W 0 0 [0, 0] [] [] .rlx "x" 0
def p1 : Event := R 1 0 [0, 1, 0] [] [] .rlx "w"
def p2 : Event := ⟨2, .branch c, ⟨0, [0, 1, 1], []⟩, []⟩
def p3 : Event := W 3 0 [0, 1, 1, 0] [] [gT] .rlx "x" 1
def p4 : Event := W 4 0 [0, 1, 1, 1] [] [gF] .rlx "x" 2
def p5 : Event := W 5 1 [1] [] [] .rlx "w" 1

def esP : EventStructure := ⟨[p0, p1, p2, p3, p4, p5], poP, []⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esJ := rfl

unseal interp in
theorem denote_progNoJoin : denote (fun _ => 0) progNoJoin = esP := rfl

theorem poTrans : ∀ a b c, esJ.poR a b → esJ.poR b c → esJ.poR a c := poTrans_of (by decide)

/-- `x := 2` and `x := 1` lie on different outcomes of the branching. -/
theorem diverged_43 : esJ.Diverged 4 3 :=
  ⟨e4, e3, rfl, rfl, gF, by simp [e4, PpoStability.W], gT, by simp [e3, PpoStability.W],
    rfl, rfl, by decide⟩

/-- … and both are `⊑`-below `z := 1`. -/
theorem joinable_43 : esJ.Joinable 4 3 :=
  ⟨6, .inr (show (4, 6) ∈ poL by decide), .inr (show (3, 6) ∈ poL by decide)⟩

theorem not_cmp_43 : ¬ esJ.PoCmp 4 3 := by
  rintro (h | h | h)
  · cases h
  · exact absurd (show (4, 3) ∈ poL from h) (by decide)
  · exact absurd (show (3, 4) ∈ poL from h) (by decide)

/-- **The fork restriction refuses the elision**: `x := 2` is after `x := 0`,
    joinable with `x := 1` and not comparable with it. -/
theorem not_weNoFork : ¬ esJ.weNoFork 0 3 := fun h =>
  not_cmp_43 (h 4 (show (0, 4) ∈ poL by decide) (by decide) fun _ => joinable_43)

/-- **So does the join condition.** -/
theorem not_weNoJoin : ¬ esJ.weNoJoin 0 3 := fun h =>
  not_cmp_43 (((esJ.weNoJoin_iff poTrans (show (0, 3) ∈ poL by decide)).1 h) 4
    (show (0, 4) ∈ poL by decide) joinable_43)

/-- **The conflict form admits it**: every event after `x := 0` but `x := 1`
    is comparable with `x := 1` or diverged from it. -/
theorem conflictForm :
    ∀ c, esJ.poR 0 c → c ≠ 3 → ¬ esJ.Diverged c 3 → esJ.PoCmp c 3 := fun c hc hne hd => by
  have hc' : (0, c) ∈ poL := hc
  have key : ∀ p ∈ poL, p.1 = 0 → p.2 = 1 ∨ p.2 = 2 ∨ p.2 = 3 ∨ p.2 = 4 ∨ p.2 = 6 := by
    decide
  rcases key _ hc' rfl with h | h | h | h | h <;> simp only at h <;> subst h
  · exact .inr (.inl (show (1, 3) ∈ poL by decide))
  · exact .inr (.inl (show (2, 3) ∈ poL by decide))
  · exact absurd rfl hne
  · exact absurd diverged_43 hd
  · exact .inr (.inr (show (3, 6) ∈ poL by decide))

/-- **Without the join the elision is admitted**: `x := 2` is joinable with
    nothing. -/
theorem weNoFork_noJoin : esP.weNoFork 0 3 := fun c hc hne hj => by
  have hc' : (0, c) ∈ poP := hc
  have key : ∀ p ∈ poP, p.1 = 0 → p.2 = 1 ∨ p.2 = 2 ∨ p.2 = 3 ∨ p.2 = 4 := by decide
  rcases key _ hc' rfl with h | h | h | h <;> simp only at h <;> subst h
  · exact .inr (.inl (show (1, 3) ∈ poP by decide))
  · exact .inr (.inl (show (2, 3) ∈ poP by decide))
  · exact absurd rfl hne
  · exfalso
    obtain ⟨d, h4, h3⟩ := hj ⟨p4, p3, rfl, rfl, gF, by simp [p4, PpoStability.W], gT,
      by simp [p3, PpoStability.W], rfl, rfl, by decide⟩
    have k4 : ∀ p ∈ poP, p.1 ≠ 4 := by decide
    rcases h4 with rfl | h4
    · rcases h3 with h3 | h3
      · cases h3
      · exact absurd (show (3, 4) ∈ poP from h3) (by decide)
    · exact k4 _ h4 rfl

/-- **The two forms part on the join.** -/
theorem branch_join :
    denote (fun _ => 0) prog = esJ ∧ ¬ esJ.weNoFork 0 3 ∧ ¬ esJ.weNoJoin 0 3 ∧
      (∀ c, esJ.poR 0 c → c ≠ 3 → ¬ esJ.Diverged c 3 → esJ.PoCmp c 3) ∧
      denote (fun _ => 0) progNoJoin = esP ∧ esP.weNoFork 0 3 :=
  ⟨denote_prog, not_weNoFork, not_weNoJoin, conflictForm, denote_progNoJoin, weNoFork_noJoin⟩

end WEBranchJoin
