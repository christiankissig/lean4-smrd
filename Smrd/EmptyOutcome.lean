import Smrd.PpoNecessity

/-!
# An outcome without events: maximality asks for the other one

`y := 5; r := y; if (r = 0) { x := 1 } else { skip }`, all accesses relaxed. The program has one
sequential run: it reads `5`, takes the `else` outcome and stores nothing. Yet it has no execution.

The `else` outcome generates no event, so nothing on it conflicts with the store `x := 1` on the
`then` outcome. The store's value restriction, `r = 0`, is satisfiable, and so is its conjunction
with every other event's (those carry no guard). So every maximal conflict-free set contains the
store (`store_mem`), and every execution the read (`read_mem`). The read must then read from
`y := 5`, while the store's value restriction asks `r = 0`, and `φ` finds no valuation for both
(`no_execution`).

Argued, not mechanised:
* the same holds under sMRD's structural conflict `#`, since no event lies on the `else` outcome
  to be in `#` with the store: the defect is the empty outcome, not the reading of conflict;
* a loop that ends a thread and exits before its bound fails the same way, since the exit runs
  the empty continuation and maximality asks for the next iteration
  (`y := 5; r := 0; while (r = 0) { r := y }` has an execution at bound 1, none at bound 2).

MoRDor ends every run with a terminal event and takes executions to be the paths that reach one,
so its `else` outcome is not empty, and it admits the run (`r = 5`, both programs).
-/

namespace EmptyOutcome

open EventStructure PpoKit

/-- `y := 5; r := y; if (r = 0) { x := 1 } else { skip }` -/
def prog : Stmt :=
  .seq (.store .rlx "y" (.num 5) false)
    (.seq (PpoStability.ld .rlx "r" "y")
      (.ite (.eq (.reg "r") (.num 0)) (.store .rlx "x" (.num 1) false) .skip))

/-- The branch condition `r = 0`. -/
def cond : Expr := .eq (.sym 1) (.val (.num 0))

def e0 : Event := ⟨0, .write .rlx (Expr.glob "y") (.val (.num 5)) false, ⟨0, [0], []⟩, []⟩
def e1 : Event := PpoStability.R 1 0 [1, 0] [] [] .rlx "y"
def e2 : Event := ⟨2, .branch cond, ⟨0, [1, 1], []⟩, []⟩
def e3 : Event :=
  ⟨3, .write .rlx (Expr.glob "x") (.val (.num 1)) false, ⟨0, [1, 1, 0], []⟩, [⟨2, cond, true⟩]⟩

def esE : EventStructure := ⟨[e0, e1, e2, e3], [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)], []⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esE := rfl

theorem nodupE : (esE.events.map (·.id)).Nodup := by decide

theorem ev_e (e : Event) (he : e ∈ esE.events) : esE.ev e.id = some e :=
  PpoKit.ev_of_mem nodupE he

/-- `r = 0`. -/
def f₀ : Valuation := fun _ => .num 0

theorem holds_nil {e : Event} (h : e.guards = []) (f : Valuation) : e.valres.holds f := by
  rw [Event.valres, Expr.holds_conj, h]; intro _ h; cases h

/-- The store's value restriction holds exactly where the read returns `0`. -/
theorem holds_e3 (f : Valuation) : e3.valres.holds f ↔ f 1 = .num 0 := by
  rw [Event.valres, Expr.holds_conj]
  simp only [e3, cond, List.map, List.mem_singleton, forall_eq, Guard.expr, if_true, Expr.holds,
    Expr.eval]
  constructor
  · intro h; simpa using h
  · intro h; simp [h]

/-- An event of `X` other than `e₃` carries no guard. -/
theorem guards_of_X {x : Execution} (hmax : esE.MaximalConflictFree x.X) {b : EventId}
    {eb : Event} (hb : x.X b) (heb : esE.ev b = some eb) (h3 : b ≠ 3) : eb.guards = [] := by
  obtain ⟨hm, rfl⟩ := ev_inv heb
  simp only [esE, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · exact absurd ⟨e2, heb, rfl⟩ (hmax.1 _ hb).2.1
  · exact absurd rfl h3

/-- **The store of the `then` outcome is in every maximal conflict-free set**: nothing on the
    empty `else` outcome conflicts with it. -/
theorem store_mem {x : Execution} (hmax : esE.MaximalConflictFree x.X) : x.X 3 := by
  refine Classical.byContradiction fun hn => ?_
  have hc : esE.Candidate 3 := cand_of_mem nodupE (e := e3) (by decide) rfl rfl
  obtain ⟨b, hb, e₃, eb, h₃, heb, hns⟩ := hmax.2.2 3 hc hn
  have hb3 : b ≠ 3 := fun h => hn (h ▸ hb)
  rw [show (3 : EventId) = e3.id from rfl, ev_e e3 (by decide)] at h₃; cases h₃
  exact hns ⟨f₀, (holds_e3 f₀).2 rfl, holds_nil (guards_of_X hmax hb heb hb3) f₀⟩

/-- The read is in every maximal conflict-free set of a consistent execution. -/
theorem read_mem {x : Execution} {Ω : Pred} (hx : x.IsExecution esE Ω) : x.X 1 := by
  refine Classical.byContradiction fun hn => ?_
  have hc : esE.Candidate 1 := cand_of_mem nodupE (e := e1) (by decide) rfl rfl
  obtain ⟨b, hb, e₁, eb, h₁, heb, hns⟩ := hx.maximal.2.2 1 hc hn
  rw [show (1 : EventId) = e1.id from rfl, ev_e e1 (by decide)] at h₁; cases h₁
  obtain ⟨f, -, hf⟩ := hx.consistent
  exact hns ⟨f, holds_nil rfl f, hf b eb hb heb⟩

/-- **The program has no execution**, under every `Ω`: its one run, reading `5` and storing
    nothing, is not one. -/
theorem no_execution (Ω : Pred) (x : Execution) (hx : x.IsExecution esE Ω) (hphi : x.phi esE) :
    False := by
  have h3 := store_mem hx.maximal
  have h1 := read_mem hx
  obtain ⟨w, hw⟩ := (hphi.2.1 1).2 ⟨h1, ⟨e1, ev_e e1 (by decide), rfl⟩⟩
  obtain ⟨⟨ew, hew, hW⟩, -, -, -⟩ := hx.rf_wr w 1 hw
  obtain ⟨g, -, ⟨hrf, -⟩, hV⟩ := hphi.2.2
  have hg : g 1 = .num 0 := (holds_e3 g).1 (hV 3 e3 h3 (ev_e e3 (by decide)))
  obtain ⟨hm, rfl⟩ := ev_inv hew
  have h1e := ev_e e1 (by decide)
  simp only [esE, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · have := (hrf _ _ _ _ hw hew h1e).2 _ _ rfl rfl
    simp [Expr.eval, hg] at this
  · cases hW
  · cases hW
  · have := (hrf _ _ _ _ hw hew h1e).1 _ _ rfl rfl
    simp [Expr.eval, Expr.glob] at this

end EmptyOutcome
