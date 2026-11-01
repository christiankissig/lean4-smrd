import Smrd.PpoNecessity

/-!
# Write Elision into one branch of an `if`: admitted by the fork restriction

`r := z; x := 0; if r = 1 then x := 1 else skip; y := 2`, eliding `x := 0`
into `x := 1`. The continuation `y := 2` is generated once per outcome of the
branching: `y := 2` after `x := 1` (event `4`) and `y := 2` on the `else`
outcome (event `5`).

* Event `5` is `⊑`-after `x := 0` and not comparable with `x := 1`, so the
  fork restriction without its exemption (every event after the elided write
  comparable with the eliding one) fails (`not_strong`).
* Event `5` lies on the other outcome of the branching than `x := 1`
  (`Diverged`) and has no common upper bound with it, so the fork restriction
  exempts it, and holds (`weNoFork_13`). The two never occur in one execution.
* The release restriction and the join condition hold too (`weNoRel_13`,
  `weNoJoin_13`), as in MoRDor, where the `else` copy of `y := 2` is in
  conflict with `x := 1`.

`Smrd.WEPastFork` stays refused: the sibling thread's read is not on another
outcome of a branching.
-/

namespace WEIntoBranch

open EventStructure PpoKit PpoStability Execution

/-- `r := z; x := 0; if r = 1 then x := 1 else skip; y := 2` -/
def prog : Stmt :=
  .seq (ld .rlx "r" "z") (.seq (st .rlx "x" 0)
    (.seq (.ite (.eq (.reg "r") (.num 1)) (st .rlx "x" 1) .skip) (st .rlx "y" 2)))

/-- The branching condition `α₀ = 1`. -/
def c : Expr := .eq (.sym 0) (Expr.num 1)
def gT : Guard := ⟨2, c, true⟩
def gF : Guard := ⟨2, c, false⟩

def e0 : Event := R 0 0 [0] [] [] .rlx "z"
def e1 : Event := W 1 0 [1, 0] [] [] .rlx "x" 0
def e2 : Event := ⟨2, .branch c, ⟨0, [1, 1, 0], []⟩, []⟩
def e3 : Event := W 3 0 [1, 1, 0, 0] [] [gT] .rlx "x" 1
def e4 : Event := W 4 0 [1, 1, 1] [] [gT] .rlx "y" 2
def e5 : Event := W 5 0 [1, 1, 1] [] [gF] .rlx "y" 2

def poL : List (EventId × EventId) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5),
    (3, 4)]

def esB : EventStructure := ⟨[e0, e1, e2, e3, e4, e5], poL, []⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esB := rfl

theorem po_of {a b : EventId} (h : (a, b) ∈ poL) : esB.poR a b := h
theorem poTrans : ∀ a b c, esB.poR a b → esB.poR b c → esB.poR a c := poTrans_of (by decide)

/-- The `else` copy of `y := 2` and `x := 1` lie on different outcomes of the
    branching. -/
theorem diverged_53 : esB.Diverged 5 3 :=
  ⟨e5, e3, rfl, rfl, gF, by simp [e5, PpoStability.W], gT, by simp [e3, PpoStability.W],
    rfl, rfl, by decide⟩

/-- … and have no common upper bound. -/
theorem not_joinable_53 : ¬ esB.Joinable 5 3 := by
  rintro ⟨d, h5, h3⟩
  have k5 : ∀ p ∈ poL, p.1 ≠ 5 := by decide
  rcases h5 with rfl | h5
  · rcases h3 with h3 | h3
    · cases h3
    · exact absurd (show (3, 5) ∈ poL from h3) (by decide)
  · exact k5 _ h5 rfl

/-- **The fork restriction without the exemption fails**: `y := 2` on the
    `else` outcome is after `x := 0` and not comparable with `x := 1`. -/
theorem not_strong : ¬ ∀ c, esB.poR 1 c → c ≠ 3 → esB.PoCmp c 3 := fun h => by
  rcases h 5 (po_of (by decide)) (by decide) with h | h | h
  · cases h
  · exact absurd (show (5, 3) ∈ poL from h) (by decide)
  · exact absurd (show (3, 5) ∈ poL from h) (by decide)

/-- **The fork restriction holds**: every event after `x := 0` is comparable
    with `x := 1`, but the `else` copy of `y := 2`, which is exempt. -/
theorem weNoFork_13 : esB.weNoFork 1 3 := fun c hc hne hj => by
  have hc' : (1, c) ∈ poL := hc
  have key : ∀ p ∈ poL, p.1 = 1 → p.2 = 2 ∨ p.2 = 3 ∨ p.2 = 4 ∨ p.2 = 5 := by decide
  rcases key _ hc' rfl with h | h | h | h <;> simp only at h <;> subst h
  · exact .inr (.inl (po_of (by decide)))
  · exact absurd rfl hne
  · exact .inr (.inr (po_of (by decide)))
  · exact absurd (hj diverged_53) not_joinable_53

theorem weNoRel_13 : esB.weNoRel 1 3 := weNoRel_of (by decide) (by decide)

theorem weNoJoin_13 : esB.weNoJoin 1 3 :=
  esB.weNoFork_weNoJoin poTrans weNoFork_13 (po_of (by decide))

/-- **Write Elision into one branch**: eliding `x := 0` into `x := 1` meets
    the fork restriction, the release restriction and the join condition;
    the fork restriction would fail without exempting the other outcome. -/
theorem into_branch :
    denote (fun _ => 0) prog = esB ∧ esB.weNoFork 1 3 ∧ esB.weNoRel 1 3 ∧ esB.weNoJoin 1 3 ∧
    ¬ (∀ c, esB.poR 1 c → c ≠ 3 → esB.PoCmp c 3) :=
  ⟨denote_prog, weNoFork_13, weNoRel_13, weNoJoin_13, not_strong⟩

end WEIntoBranch
