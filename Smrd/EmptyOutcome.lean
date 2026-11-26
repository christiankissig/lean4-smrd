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

A loop that ends a thread and exits before its bound fails the same way: the exit runs the
empty continuation, and maximality asks for the next iteration. In
`y := 5; r := 0; while₁ (r = 0) { r := y }` the run that reads `5` and exits is an execution
satisfying `φ` at bound `1` (`exec_bound₁`), where the second iteration is cut off, and at bound
`2` the second iteration's read is forced (`read₂_mem`), so there is no execution at all
(`no_execution_bound₂`). The executions are not monotone in the bound.

The same holds under sMRD's structural conflict `#` (`MaxS`, maximality under `Diverged`): no
event lies on the empty outcome to be in `#` with the forced one (`no_execution_S`,
`maxS_bound₁`, `no_execution_bound₂_S`). The defect is the empty outcome, not the reading of
conflict.

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

/-! ## A loop that ends the thread and exits early -/

/-- `y := 5; r := 0; while₁ (r = 0) { r := y }` -/
def progL : Stmt :=
  .seq (.store .rlx "y" (.num 5) false)
    (.seq (.assign "r" (.num 0))
      (.while 1 (.eq (.reg "r") (.num 0)) (PpoStability.ld .rlx "r" "y")))

/-- The first head's condition, `0 = 0`, and the second's, `r = 0` on the first read. -/
def c₀ : Expr := .eq (.val (.num 0)) (.val (.num 0))
def c₁ : Expr := .eq (.sym 2) (.val (.num 0))

def l0 : Event := ⟨0, .write .rlx (Expr.glob "y") (.val (.num 5)) false, ⟨0, [0], []⟩, []⟩
def l1 : Event := ⟨1, .branch c₀, ⟨0, [1, 1], [(1, 0)]⟩, []⟩
def l2 : Event := PpoStability.R 2 0 [1, 1, 0] [(1, 0)] [⟨1, c₀, true⟩] .rlx "y"
def l3 : Event := ⟨3, .branch c₁, ⟨0, [1, 1], [(1, 1)]⟩, [⟨1, c₀, true⟩]⟩
def l4 : Event := PpoStability.R 4 0 [1, 1, 0] [(1, 1)] [⟨1, c₀, true⟩, ⟨3, c₁, true⟩] .rlx "y"

/-- `⟨progL⟩_1`: the head and the read of the first iteration; the second iteration is cut off. -/
def esL₁ : EventStructure := ⟨[l0, l1, l2], [(0, 1), (0, 2), (1, 2)], []⟩

/-- `⟨progL⟩_2`: as `⟨progL⟩_1`, with the second head and the second iteration's read. The exit at
    either head runs the empty continuation and generates nothing. -/
def esL₂ : EventStructure :=
  ⟨[l0, l1, l2, l3, l4], [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4),
    (3, 4)], []⟩

unseal interp in
theorem denote_progL₁ : denote (fun _ => 1) progL = esL₁ := rfl

unseal interp in
theorem denote_progL₂ : denote (fun _ => 2) progL = esL₂ := rfl

theorem SL₁ : Simple esL₁ := ⟨by decide, by decide, rfl⟩

/-- The run, the first read reading `y := 5`. -/
def xL₁ : Execution := simple esL₁ [(0, 2)]

/-- **At bound `1` the run that reads `5` and exits is an execution**: the read takes `y := 5`, and
    `φ` holds with the read at `5`. -/
theorem exec_bound₁ : xL₁.IsExecution esL₁ (fun _ => True) ∧ xL₁.phi esL₁ ∧ xL₁.rf 0 2 :=
  ⟨isExecution_simple SL₁ (by decide),
    phi_simple SL₁ (by decide) (by decide) (by decide)
      (fun α => if α = 2 then .num 5 else .num 0) (by decide), show (0, 2) ∈ [(0, 2)] by decide⟩

theorem nodupL₂ : (esL₂.events.map (·.id)).Nodup := by decide

theorem evL (e : Event) (he : e ∈ esL₂.events) : esL₂.ev e.id = some e :=
  PpoKit.ev_of_mem nodupL₂ he

/-- The second iteration's read holds exactly where the first read returns `0`. -/
theorem holds_l4 (f : Valuation) : l4.valres.holds f ↔ f 2 = .num 0 := by
  rw [Event.valres, Expr.holds_conj]
  simp only [l4, PpoStability.R, c₀, c₁, List.map, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Guard.expr, if_true, Expr.holds,
    Expr.eval]
  constructor
  · intro h; simpa using h.2
  · intro h; simp [h]

theorem holds_c₀ {e : Event} (h : e.guards = [] ∨ e.guards = [⟨1, c₀, true⟩]) (f : Valuation) :
    e.valres.holds f := by
  rw [Event.valres, Expr.holds_conj]
  rcases h with h | h <;> rw [h]
  · intro _ h; cases h
  · intro e he
    simp only [List.map, List.mem_singleton] at he; subst he
    simp [Guard.expr, c₀, Expr.holds, Expr.eval]

/-- An event of `X` other than the second read carries at most the first head's guard. -/
theorem guardsL_of_X {x : Execution} (hmax : esL₂.MaximalConflictFree x.X) {b : EventId}
    {eb : Event} (hb : x.X b) (heb : esL₂.ev b = some eb) (h4 : b ≠ 4) :
    eb.guards = [] ∨ eb.guards = [⟨1, c₀, true⟩] := by
  obtain ⟨hm, rfl⟩ := ev_inv heb
  simp only [esL₂, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact absurd ⟨l1, heb, rfl⟩ (hmax.1 _ hb).2.1
  · exact .inr rfl
  · exact absurd ⟨l3, heb, rfl⟩ (hmax.1 _ hb).2.1
  · exact absurd rfl h4

/-- **The second iteration's read is in every maximal conflict-free set of `⟨progL⟩_2`**: the
    exit at the second head generates nothing that could conflict with it. -/
theorem read₂_mem {x : Execution} (hmax : esL₂.MaximalConflictFree x.X) : x.X 4 := by
  refine Classical.byContradiction fun hn => ?_
  have hc : esL₂.Candidate 4 := cand_of_mem nodupL₂ (e := l4) (by decide) rfl rfl
  obtain ⟨b, hb, e₄, eb, h₄, heb, hns⟩ := hmax.2.2 4 hc hn
  have hb4 : b ≠ 4 := fun h => hn (h ▸ hb)
  rw [show (4 : EventId) = l4.id from rfl, evL l4 (by decide)] at h₄; cases h₄
  exact hns ⟨f₀, (holds_l4 f₀).2 rfl, holds_c₀ (guardsL_of_X hmax hb heb hb4) f₀⟩

/-- The first iteration's read is in every execution of `⟨progL⟩_2`. -/
theorem read₁_mem {x : Execution} {Ω : Pred} (hx : x.IsExecution esL₂ Ω) : x.X 2 := by
  refine Classical.byContradiction fun hn => ?_
  have hc : esL₂.Candidate 2 := cand_of_mem nodupL₂ (e := l2) (by decide) rfl rfl
  obtain ⟨b, hb, e₂, eb, h₂, heb, hns⟩ := hx.maximal.2.2 2 hc hn
  rw [show (2 : EventId) = l2.id from rfl, evL l2 (by decide)] at h₂; cases h₂
  obtain ⟨f, -, hf⟩ := hx.consistent
  exact hns ⟨f, holds_c₀ (.inr rfl) f, hf b eb hb heb⟩

/-- **At bound `2` no execution has the first read return `5`**, under every `Ω`: the second
    iteration's read is forced, and its value restriction asks `0`. So the run that reads `5` and
    exits is an execution at bound `1` (`exec_bound₁`) but not at bound `2`: the executions are not
    monotone in the bound. -/
theorem no_exec_bound₂ (Ω : Pred) (x : Execution) (hx : x.IsExecution esL₂ Ω)
    (hphi : x.phi esL₂) : ¬ x.rf 0 2 := by
  intro hrf0
  have h4 := read₂_mem hx.maximal
  obtain ⟨g, -, ⟨hrf, -⟩, hV⟩ := hphi.2.2
  have hg : g 2 = .num 0 := (holds_l4 g).1 (hV 4 l4 h4 (evL l4 (by decide)))
  have := (hrf 0 2 l0 l2 hrf0 (evL l0 (by decide)) (evL l2 (by decide))).2 _ _ rfl rfl
  simp [Expr.eval, hg] at this

/-- At bound `2` the first read reads `y := 5` in every execution: `y := 5` is the only write. -/
theorem rf_bound₂ (Ω : Pred) (x : Execution) (hx : x.IsExecution esL₂ Ω) (hphi : x.phi esL₂) :
    x.rf 0 2 := by
  obtain ⟨w, hw⟩ := (hphi.2.1 2).2 ⟨read₁_mem hx, ⟨l2, evL l2 (by decide), rfl⟩⟩
  obtain ⟨⟨ew, hew, hW⟩, -⟩ := hx.rf_wr w 2 hw
  obtain ⟨hm, rfl⟩ := ev_inv hew
  simp only [esL₂, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> first | exact hw | cases hW

/-- **`⟨progL⟩_2` has no execution**, under every `Ω`. -/
theorem no_execution_bound₂ (Ω : Pred) (x : Execution) (hx : x.IsExecution esL₂ Ω)
    (hphi : x.phi esL₂) : False :=
  no_exec_bound₂ Ω x hx hphi (rf_bound₂ Ω x hx hphi)

/-! ## Under sMRD's structural conflict `#`

The published structure carries a conflict relation `#`, which the coproduct of a branching's two
outcomes extends by all pairs across them (Richards et al., Definitions 4.2 and 4.4): events on
different outcomes of one branching, `Diverged`. Maximality under `#` (`MaxS`) fails the same way.
In the three structures above every guard is a `true` outcome, as nothing lies on the empty
outcomes, so nothing is in `#` (`not_diverged`) and the only `#`-maximal set is every candidate
(`maxS_all`).
-/

/-- A maximal set conflict-free under `#`. -/
def MaxS (es : EventStructure) (X : EvSet) : Prop :=
  (∀ a, X a → es.Candidate a) ∧ (∀ a b, X a → X b → ¬ es.Diverged a b) ∧
  (∀ a, es.Candidate a → ¬ X a → ∃ b, X b ∧ es.Diverged a b)

/-- Where every guard is a `true` outcome, nothing is in `#`. -/
theorem not_diverged {es : EventStructure} (h : ∀ e ∈ es.events, ∀ g ∈ e.guards, g.pos = true)
    {a b : EventId} : ¬ es.Diverged a b := by
  rintro ⟨ea, eb, ha, hb, g₁, hg₁, g₂, hg₂, -, -, hp⟩
  exact hp ((h ea (ev_inv ha).1 g₁ hg₁).trans (h eb (ev_inv hb).1 g₂ hg₂).symm)

/-- Then the only `#`-maximal set is every candidate. -/
theorem maxS_all {es : EventStructure} (h : ∀ e ∈ es.events, ∀ g ∈ e.guards, g.pos = true)
    {X : EvSet} (hX : MaxS es X) {a : EventId} (ha : es.Candidate a) : X a :=
  Classical.byContradiction fun hn => by
    obtain ⟨b, -, hd⟩ := hX.2.2 a ha hn
    exact not_diverged h hd

theorem pos_E : ∀ e ∈ esE.events, ∀ g ∈ e.guards, g.pos = true := by decide
theorem pos_L₁ : ∀ e ∈ esL₁.events, ∀ g ∈ e.guards, g.pos = true := by decide
theorem pos_L₂ : ∀ e ∈ esL₂.events, ∀ g ∈ e.guards, g.pos = true := by decide

/-- **Under `#`, `y := 5; r := y; if (r = 0) { x := 1 } else { skip }` has no execution**: every
    `#`-maximal set holds the store and the read, and `φ` fails as before. Only maximality, `rf`'s
    sources being writes, and `φ` are used. -/
theorem no_execution_S (x : Execution) (hmax : MaxS esE x.X)
    (hrfw : ∀ w r, x.rf w r → esE.cls Event.isWrite w) (hphi : x.phi esE) : False := by
  have h3 := maxS_all pos_E hmax (cand_of_mem nodupE (e := e3) (by decide) rfl rfl)
  have h1 := maxS_all pos_E hmax (cand_of_mem nodupE (e := e1) (by decide) rfl rfl)
  obtain ⟨w, hw⟩ := (hphi.2.1 1).2 ⟨h1, ⟨e1, ev_e e1 (by decide), rfl⟩⟩
  obtain ⟨ew, hew, hW⟩ := hrfw w 1 hw
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

/-- **Under `#`, the loop's run reading `5` is an execution at bound `1`**: its events, every
    candidate, are `#`-maximal. -/
theorem maxS_bound₁ : MaxS esL₁ xL₁.X :=
  ⟨fun _ h => h, fun _ _ _ _ => not_diverged pos_L₁, fun _ hc hn => absurd hc hn⟩

/-- **Under `#`, the loop has no execution at bound `2`**: every `#`-maximal set holds both reads,
    the first reads `y := 5`, and the second's value restriction asks `0`. -/
theorem no_execution_bound₂_S (x : Execution) (hmax : MaxS esL₂ x.X)
    (hrfw : ∀ w r, x.rf w r → esL₂.cls Event.isWrite w) (hphi : x.phi esL₂) : False := by
  have h4 := maxS_all pos_L₂ hmax (cand_of_mem nodupL₂ (e := l4) (by decide) rfl rfl)
  have h2 := maxS_all pos_L₂ hmax (cand_of_mem nodupL₂ (e := l2) (by decide) rfl rfl)
  obtain ⟨w, hw⟩ := (hphi.2.1 2).2 ⟨h2, ⟨l2, evL l2 (by decide), rfl⟩⟩
  obtain ⟨ew, hew, hW⟩ := hrfw w 2 hw
  obtain ⟨g, -, ⟨hrf, -⟩, hV⟩ := hphi.2.2
  have hg : g 2 = .num 0 := (holds_l4 g).1 (hV 4 l4 h4 (evL l4 (by decide)))
  obtain ⟨hm, rfl⟩ := ev_inv hew
  simp only [esL₂, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · have := (hrf _ _ _ _ hw (evL l0 (by decide)) (evL l2 (by decide))).2 _ _ rfl rfl
    simp [Expr.eval, hg] at this
  all_goals cases hW

/-! ## Under `#`, the dead iteration after a successful `CAS`

`x := 0; rb := (0 = 1); while₁ (¬ rb) { rb := CAS(x, 0, 1) }`: a thread that ends with a `CAS`
loop. After a successful `CAS` the register holds `⊤`, so the next iteration is entered under
the closed guard `¬⊤`, which no valuation satisfies: a dead copy. Read off the value
restrictions, it conflicts with everything. Under `#` it conflicts only with the other outcomes of
its branchings: the failed `CAS`, and the exit of its head. The exit runs the empty continuation,
so where the `CAS` succeeds, nothing in the set excludes the dead iteration, maximality forces its
read in, and `φ` finds no valuation for its guard. At bound `2` no `#`-maximal set in which the
`CAS` of the first iteration succeeds satisfies `φ` (`no_cas_success_S`): the run that succeeds at
once is lost. Read off the value restrictions, the dead read lies outside every conflict-free
set (`dead_incompatible`), and the run is an execution satisfying `φ` (`cas_success_exec`): its
set `{x := 0, the CAS's read, the CAS's write}` is maximal, since every other candidate lies on the
dead iteration or on the failed `CAS`'s outcome (`maximal_run`).
-/

def ffP : PExpr := .eq (.num 0) (.num 1)

/-- `x := 0; rb := (0 = 1); while₁ (¬ rb) { rb := CAS(x, 0, 1) }` -/
def progC : Stmt :=
  .seq (.store .rlx "x" (.num 0) false)
    (.seq (.assign "rb" ffP)
      (.while 1 (.not (.reg "rb")) (.cas .rlx .rlx "rb" "x" (.num 0) (.num 1))))

/-- The first head's condition `¬(0 = 1)`, the `CAS` comparisons, and the second heads'
    conditions after success, `¬⊤`, and after failure, `¬⊥`. -/
def h₀ : Expr := .not (.eq (.val (.num 0)) (.val (.num 1)))
def q (a : EventId) : Expr := .eq (.sym a) (.val (.num 0))
def hT : Expr := .not (.val (.bool true))
def hF : Expr := .not (.val (.bool false))

def wx (i : EventId) (v : Nat) (pc : List Nat) (it : List (LoopId × Nat)) (gs : List Guard) : Event :=
  ⟨i, .write .rlx (Expr.glob "x") (.val (.num v)) false, ⟨0, pc, it⟩, gs⟩
def br (i : EventId) (c : Expr) (pc : List Nat) (it : List (LoopId × Nat)) (gs : List Guard) :
    Event := ⟨i, .branch c, ⟨0, pc, it⟩, gs⟩

def G0 : List Guard := [⟨1, h₀, true⟩]
def GS : List Guard := G0 ++ [⟨3, q 2, true⟩]
def GF : List Guard := G0 ++ [⟨3, q 2, false⟩]
def GD : List Guard := GS ++ [⟨5, hT, true⟩]
def GL : List Guard := GF ++ [⟨9, hF, true⟩]

def it₀ : List (LoopId × Nat) := [(1, 0)]
def it₁ : List (LoopId × Nat) := [(1, 1)]

def esC : EventStructure :=
  ⟨[wx 0 0 [0] [] [],
    br 1 h₀ [1, 1] it₀ [],
    PpoStability.R 2 0 [1, 1, 0, 0] it₀ G0 .rlx "x",
    br 3 (q 2) [1, 1, 0, 1] it₀ G0,
    wx 4 1 [1, 1, 0, 2] it₀ GS,
    br 5 hT [1, 1] it₁ GS,
    PpoStability.R 6 0 [1, 1, 0, 0] it₁ GD .rlx "x",
    br 7 (q 6) [1, 1, 0, 1] it₁ GD,
    wx 8 1 [1, 1, 0, 2] it₁ (GD ++ [⟨7, q 6, true⟩]),
    br 9 hF [1, 1] it₁ GF,
    PpoStability.R 10 0 [1, 1, 0, 0] it₁ GL .rlx "x",
    br 11 (q 10) [1, 1, 0, 1] it₁ GL,
    wx 12 1 [1, 1, 0, 2] it₁ (GL ++ [⟨11, q 10, true⟩])],
   [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11),
    (0, 12), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11),
    (1, 12), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12),
    (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, 5), (4, 6),
    (4, 7), (4, 8), (5, 6), (5, 7), (5, 8), (6, 7), (6, 8), (7, 8), (9, 10), (9, 11), (9, 12),
    (10, 11), (10, 12), (11, 12)],
   [⟨2, q 2, 4⟩, ⟨6, q 6, 8⟩, ⟨10, q 10, 12⟩]⟩

unseal interp in
theorem denote_progC : denote (fun _ => 2) progC = esC := rfl

theorem nodupC : (esC.events.map (·.id)).Nodup := by decide

/-- The dead read: the first read of the iteration after the `CAS` succeeds. -/
def dead : Event := PpoStability.R 6 0 [1, 1, 0, 0] it₁ GD .rlx "x"

theorem dead_mem : dead ∈ esC.events := by decide

/-- No valuation satisfies the dead read's guards. -/
theorem dead_unsat (f : Valuation) : ¬ dead.valres.holds f := by
  intro h
  rw [Event.valres, Expr.holds_conj] at h
  have := h _ (List.mem_map_of_mem (f := Guard.expr) (show ⟨5, hT, true⟩ ∈ dead.guards by decide))
  simp [Guard.expr, hT, Expr.holds, Expr.eval] at this

/-- Read off the value restrictions, the dead read conflicts with every event. -/
theorem dead_incompatible (b : EventId) (eb : Event) (hb : esC.ev b = some eb) :
    esC.Conflict 6 b :=
  ⟨dead, eb, PpoKit.ev_of_mem nodupC dead_mem, hb, fun ⟨f, h, _⟩ => dead_unsat f h⟩

/-- The guards of the dead read, flipped, are carried only by the failed `CAS`'s outcome. -/
theorem div_dead {b : EventId} (h : esC.Diverged 6 b) : b ≥ 9 ∧ b ≤ 12 := by
  obtain ⟨ea, eb, ha, hb, g₁, hg₁, g₂, hg₂, hbr, hc, hp⟩ := h
  rw [show (6 : EventId) = dead.id from rfl, PpoKit.ev_of_mem nodupC dead_mem] at ha; cases ha
  obtain ⟨hm, rfl⟩ := ev_inv hb
  have key : ∀ e ∈ esC.events, (∃ g₁ ∈ dead.guards, ∃ g₂ ∈ e.guards,
      g₁.branch = g₂.branch ∧ g₁.cond = g₂.cond ∧ g₁.pos ≠ g₂.pos) → e.id ≥ 9 ∧ e.id ≤ 12 := by
    decide
  exact key eb hm ⟨g₁, hg₁, g₂, hg₂, hbr, hc, hp⟩

/-- The failed `CAS`'s outcome conflicts under `#` with the successful `CAS`'s write. -/
theorem div_write {b : EventId} (h₁ : b ≥ 9) (h₂ : b ≤ 12) (hb : esC.inE b) : esC.Diverged b 4 := by
  obtain ⟨eb, hm, rfl⟩ := hb
  have key : ∀ e ∈ esC.events, e.id ≥ 9 → e.id ≤ 12 → (⟨3, q 2, false⟩ : Guard) ∈ e.guards := by
    decide
  exact ⟨eb, wx 4 1 [1, 1, 0, 2] it₀ GS, PpoKit.ev_of_mem nodupC hm,
    PpoKit.ev_of_mem nodupC (e := wx 4 1 [1, 1, 0, 2] it₀ GS) (by decide), ⟨3, q 2, false⟩,
    key eb hm h₁ h₂, ⟨3, q 2, true⟩,
    by decide, rfl, rfl, by decide⟩

/-- **Under `#`, no `#`-maximal set in which the first `CAS` succeeds satisfies `φ`**, at bound
    `2`: the dead read is in it, and its guard `¬⊤` holds under no valuation. -/
theorem no_cas_success_S (x : Execution) (hmax : MaxS esC x.X) (h4 : x.X 4)
    (hphi : x.phi esC) : False := by
  have h6 : x.X 6 := by
    refine Classical.byContradiction fun hn => ?_
    obtain ⟨b, hb, hd⟩ := hmax.2.2 6 (cand_of_mem nodupC (e := dead) dead_mem rfl rfl) hn
    obtain ⟨l, u⟩ := div_dead hd
    exact hmax.2.1 b 4 hb h4 (div_write l u (hmax.1 b hb).1)
  obtain ⟨g, -, -, hV⟩ := hphi.2.2
  exact dead_unsat g (hV 6 dead h6 (PpoKit.ev_of_mem nodupC dead_mem))

/-! ### The run that succeeds at once is an execution, under the value restrictions -/

def wC0 : Event := wx 0 0 [0] [] []
def rC2 : Event := PpoStability.R 2 0 [1, 1, 0, 0] it₀ G0 .rlx "x"
def wC4 : Event := wx 4 1 [1, 1, 0, 2] it₀ GS

def jC0 : Justification := ⟨wC0.valres, [], .empty, wC0⟩
def jC4 : Justification := ⟨wC4.valres, [], .empty, wC4⟩

/-- The run that succeeds at once: `x := 0`, the `CAS`'s read reading it, and the `CAS`'s
    write. -/
def xC : Execution := ⟨fun a => a = 0 ∨ a = 2 ∨ a = 4, [jC0, jC4], fun w r => w = 0 ∧ r = 2⟩

def fC : Valuation := fun _ => .num 0

theorem evC {e : Event} (he : e ∈ esC.events) : esC.ev e.id = some e := PpoKit.ev_of_mem nodupC he

theorem ev0 : esC.ev 0 = some wC0 := evC (e := wC0) (by decide)
theorem ev2 : esC.ev 2 = some rC2 := evC (e := rC2) (by decide)
theorem ev4 : esC.ev 4 = some wC4 := evC (e := wC4) (by decide)

/-- The events up to the second head hold where every read returns `0`. -/
theorem holds_run : ∀ e ∈ esC.events, e.id ≤ 5 → e.valres.holds fC := by
  unfold Expr.holds; decide

theorem holds_X {a : EventId} {e : Event} (ha : xC.X a) (he : esC.ev a = some e) :
    e.valres.holds fC := by
  obtain ⟨hm, rfl⟩ := ev_inv he
  have h' : e.id = 0 ∨ e.id = 2 ∨ e.id = 4 := ha
  have h5 : e.id ≤ 5 := by rcases h' with h | h | h <;> rw [h] <;> decide
  exact holds_run e hm h5

theorem guard_holds {e : Event} {g : Guard} (hg : g ∈ e.guards) {f : Valuation}
    (h : e.valres.holds f) : g.expr.holds f := by
  rw [Event.valres, Expr.holds_conj] at h
  exact h _ (List.mem_map_of_mem hg)

theorem not_holds {c : Expr} {f : Valuation} (h : c.holds f) : ¬ (Expr.not c).holds f := by
  unfold Expr.holds at h ⊢; simp [Expr.eval, h]

/-- An event of the dead iteration holds under no valuation. -/
theorem unsat_hT {e : Event} (hg : (⟨5, hT, true⟩ : Guard) ∈ e.guards) (f : Valuation) :
    ¬ e.valres.holds f := fun h => by
  have := guard_holds hg h
  simp [Guard.expr, hT, Expr.holds, Expr.eval] at this

/-- The two outcomes of the first `CAS` are incompatible. -/
theorem unsat_flip {ea eb : Event} (ha : (⟨3, q 2, false⟩ : Guard) ∈ ea.guards)
    (hb : (⟨3, q 2, true⟩ : Guard) ∈ eb.guards) (f : Valuation) :
    ¬ (ea.valres.holds f ∧ eb.valres.holds f) := fun ⟨h₁, h₂⟩ =>
  not_holds (guard_holds hb h₂) (guard_holds ha h₁)

theorem cand_run (a : EventId) (ha : xC.X a) : esC.Candidate a := by
  rcases ha with rfl | rfl | rfl
  · exact cand_of_mem nodupC (e := wC0) (by decide) rfl rfl
  · exact cand_of_mem nodupC (e := rC2) (by decide) rfl rfl
  · exact cand_of_mem nodupC (e := wC4) (by decide) rfl rfl

theorem δC : xC.δ = .empty := rfl

/-- Every candidate off the run lies on the dead iteration or on the failed `CAS`'s outcome. -/
theorem off_run : ∀ e ∈ esC.events, e.isBranch = false → e.id ≠ 0 → e.id ≠ 2 → e.id ≠ 4 →
    (⟨5, hT, true⟩ : Guard) ∈ e.guards ∨ (⟨3, q 2, false⟩ : Guard) ∈ e.guards := by
  decide

/-- **Read off the value restrictions, the run is maximal conflict-free.** -/
theorem maximal_run : esC.MaximalConflictFree xC.X := by
  refine ⟨cand_run, fun a b ha hb ⟨ea, eb, h₁, h₂, hn⟩ => hn ⟨fC, holds_X ha h₁, holds_X hb h₂⟩,
    fun a ha hn => ?_⟩
  obtain ⟨⟨e, hm, rfl⟩, hb, -⟩ := ha
  have hbr : e.isBranch = false := by
    cases h : e.isBranch
    · rfl
    · exact absurd ⟨e, evC hm, h⟩ hb
  have hn₀ : ¬ (e.id = 0 ∨ e.id = 2 ∨ e.id = 4) := hn
  have hn' : e.id ≠ 0 ∧ e.id ≠ 2 ∧ e.id ≠ 4 :=
    ⟨fun h => hn₀ (.inl h), fun h => hn₀ (.inr (.inl h)), fun h => hn₀ (.inr (.inr h))⟩
  rcases off_run e hm hbr hn'.1 hn'.2.1 hn'.2.2 with h | h
  · exact ⟨0, Or.inl rfl, e, wC0, evC hm, ev0, fun ⟨f, h₁, _⟩ => unsat_hT h f h₁⟩
  · exact ⟨4, Or.inr (Or.inr rfl), e, wC4, evC hm, ev4,
      fun ⟨f, h₁, h₂⟩ => unsat_flip h (by decide) f ⟨h₁, h₂⟩⟩

theorem mem_JC {j : Justification} (hj : j ∈ xC.J) : j = jC0 ∨ j = jC4 := by
  simpa [xC] using hj

theorem noEffect₂ : ∀ e ∈ esC.events, e.id = 2 → e.isEffect = false := by decide
theorem noAlloc : ∀ e ∈ esC.events, e.isAlloc = false := by decide
theorem readId : ∀ e ∈ esC.events, e.isRead = true → e.id ≠ 0 ∧ e.id ≠ 4 := by decide

/-- **The run in which the first `CAS` succeeds is an execution**, the `CAS` reading `x := 0`,
    and it satisfies `φ`. -/
theorem cas_success_exec :
    xC.IsExecution esC (fun _ => True) ∧ xC.phi esC ∧ xC.X 4 ∧ xC.rf 0 2 := by
  refine ⟨⟨maximal_run, fun j hj => ?_, fun j hj => ?_, ?_, by rw [δC]; exact FwdCtx.WF.empty,
    ?_, ?_, ?_, fun j _ => xC.not_elided_of_δ_empty δC _⟩, ⟨fun e _ => xC.not_elided_of_δ_empty δC e,
    fun r => ⟨?_, ?_⟩, fC, fun j hj => ⟨?_, ?_⟩, ⟨?_, ?_⟩, fun _ _ ha he => holds_X ha he⟩,
    Or.inr (Or.inr rfl), rfl, rfl⟩
  · rcases mem_JC hj with rfl | rfl
    · exact .pre (w := wC0) (by decide) rfl ⟨fC, holds_run _ (by decide) (by decide)⟩
    · exact .pre (w := wC4) (by decide) rfl ⟨fC, holds_run _ (by decide) (by decide)⟩
  · rcases mem_JC hj with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
  · refine ⟨fC, fun j hj => ?_, fun _ _ ha he => holds_X ha he⟩
    rcases mem_JC hj with rfl | rfl
    · exact holds_run _ (by decide) (by decide)
    · exact holds_run _ (by decide) (by decide)
  · rintro w r ⟨rfl, rfl⟩
    exact ⟨⟨wC0, ev0, rfl⟩, ⟨rC2, ev2, rfl⟩, Or.inl rfl, Or.inr (Or.inl rfl)⟩
  · rintro w w' r ⟨rfl, rfl⟩ ⟨rfl, -⟩; rfl
  · rintro w hw ⟨e, he, hp⟩ -
    rcases hw with rfl | rfl | rfl
    · refine ⟨jC0, by simp [xC], rfl, fun j' hj' h => ?_⟩
      rcases mem_JC hj' with rfl | rfl
      · rfl
      · exact absurd h (by decide)
    · obtain ⟨hm, hid⟩ := ev_inv he
      rw [noEffect₂ e hm hid] at hp; cases hp
    · refine ⟨jC4, by simp [xC], rfl, fun j' hj' h => ?_⟩
      rcases mem_JC hj' with rfl | rfl
      · exact absurd h (by decide)
      · rfl
  · rintro ⟨w, -, rfl⟩
    exact ⟨Or.inr (Or.inl rfl), rC2, ev2, rfl⟩
  · rintro ⟨hX, e, he, hp⟩
    obtain ⟨hm, rfl⟩ := ev_inv he
    have := readId e hm hp
    rcases hX with h | h | h
    · exact absurd h this.1
    · exact ⟨0, rfl, h⟩
    · exact absurd h this.2
  · rcases mem_JC hj with rfl | rfl
    · exact holds_run _ (by decide) (by decide)
    · exact holds_run _ (by decide) (by decide)
  · rcases mem_JC hj with rfl | rfl <;> exact fun p hp => nomatch hp
  · rintro w r ew er ⟨rfl, rfl⟩ hw hr
    rw [ev0] at hw; rw [ev2] at hr; cases hw; cases hr
    refine ⟨fun lw lr h₁ h₂ => ?_, fun vw vr h₁ h₂ => ?_⟩
    · cases h₁; cases h₂; rfl
    · cases h₁; cases h₂; rfl
  · refine ⟨fun a e α sz _ he hk => ?_, fun _ => none,
      ⟨fun _ _ h => (nomatch h), fun _ _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩, ?_⟩
    · have := noAlloc e (ev_inv he).1
      simp [Event.isAlloc, hk] at this
    · intro a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂ _ _ _ he₁ _ hk₁
      have := noAlloc e₁ (ev_inv he₁).1
      simp [Event.isAlloc, hk₁] at this

end EmptyOutcome
