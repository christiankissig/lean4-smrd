import Smrd.DPPast
import Smrd.PpoNecessity

/-!
# Lifting drops a guard's symbol, under the unrestricted rule

`A := 0; B := 0; y := 0; (ra := A; rb := B; if ra = 0 then (if rb = 0 then y := 1) ∥ A := 1)`,
all accesses relaxed. Lifting the guarded write's pre-justification into itself under the
relabelling `Λ = [ra ↦ rb]` gives `(⊤ ∧ rb = 0 ∧ rb = 0) ∧ (⋀∅ ∨ ⋀{ra = 0})`: every conjunct of
`⟦P⟧_Λ` is a conjunct of `P`, so `A₁ = ∅` and the factored disjunction is valid. Weakening drops
it under `Ω = ⊤`, and the justification `(⊤ ∧ rb = 0 ∧ rb = 0, ∅) ⊢ y := 1` has lost the symbol
of the read the outer branch tests. A consistent execution then runs `y := 1` while `ra` reads
`1`, without `(ra, y := 1) ∈ DP`.

Every side condition of sMRD's Def. 4.16 (with the library's `⊑`-restriction) holds
(`lift_conds`, `LiftConds`): the two premises are the same generated justification (`δ`,
`D = ∅` agree), `y := 1` is closed relabel-equivalent to itself (constant location and value;
its only immediate `≼`-predecessor under either predicate is `y := 0`, related to itself; branch
events are never `≼`-predecessors), no volatile access, and the symbol `rb` of `⟦P⟧_Λ` is
`⊑`-before `y := 1`. `Λ` is `Relabelling.Injective` (one-to-one on its domain `{ra}`), but
`⟦·⟧_Λ` is not: it sends both `ra` and `rb` to `rb`.

The derivation is the reason for the restrictions on `Generated.lift` that sMRD's prose (§4.7)
states and its Def. 4.16 omits, and it is kept here in the unrestricted form: the results below
assume the lift generated (`hL`), and `gen_jL_of` shows that the restrictions are all that is
missing.

* `gen_jW_of`: the weakened justification would be generated; `jW_syms`: `ra ∉ symbols(P)`.
* `consistent_x`, `consistentT_x`: the execution taking it, with `ra` reading `A := 1` and `rb`
  reading `B := 0`, would be consistent. `IsExecution.consistent` asks a model of
  `⋀ P_j ∧ ⋀ valres(X)` (`ra = 0` there) and `φ` a model of `⋀ (P_j ∧ ψ) ∧ φ_rf` (`ra = 1`
  there); the branch condition is tied to `rf` only through `J`.
* `guard_lost`: `y := 1 ∈ X`, every model of `φ_rf` gives `ra = 1`, so the branch condition
  `ra = 0` fails, and `(ra, y := 1) ∉ DP`.

Under the restricted rule:

* `not_liftBranch`: the writes must lie on different outcomes of a branching, and no two events
  of the structure do (in particular `y := 1` and itself); `not_injOn`: `⟦·⟧_Λ` is not one-to-one.
* `guard_kept`: every generated justification of `y := 1` keeps the conjunct `ra = 0`, or has
  `ra` forwarded, under any `Ω` not implying `ra = 0`; hence `not_gen_jL`, `not_gen_jW`, and `x`
  is no execution (`not_execution`).

Variants:

* A relabelling permuting `{ra, rb}` cannot do it: `⟦P⟧_Λ` mentions `ra`, its conjunct `ra = 0`
  is shared with `P` and stays in `C` (`swap_keeps`).
* `Swap`: with a third read `rc` the relabelling can be the permutation `(ra rc)`. Strengthening
  the second premise by `rc = 0` and lifting the pre-justification into it leaves
  `rc = 0 ∧ rb = 0` after Weakening (`Swap.gen_jW_of`, `Swap.jW_syms`). `⟦·⟧_Λ` is one-to-one
  here (`Swap.injOn`); the branching restriction refuses the lift (`Swap.not_liftBranch`).
* `Free`: `free(r)` after `r := malloc(1)` in place of `y := 1`. Under the pre-justification the
  freed location may alias `A` and `B`, the reads are immediate `≼`-predecessors, and the
  all-pairs clause of closed relabel-equivalence fails; Strengthening by `r ≠ &A ∧ r ≠ &B`
  leaves the allocation as the only predecessor, and the derivation and the execution go through
  under the unrestricted rule (`Free.gen_jW_of`, `Free.guard_lost`); both restrictions refuse it
  (`Free.not_lift`).
-/

namespace GuardLoss

open EventStructure PpoKit Execution

/-- `A := 0; B := 0; y := 0; (ra := A; rb := B; if ra = 0 then (if rb = 0 then y := 1) ∥ A := 1)` -/
def prog : Stmt :=
  .seq (PpoStability.st .rlx "A" 0) (.seq (PpoStability.st .rlx "B" 0)
    (.seq (PpoStability.st .rlx "y" 0)
      (.par (.seq (PpoStability.ld .rlx "ra" "A") (.seq (PpoStability.ld .rlx "rb" "B")
          (.ite (.eq (.reg "ra") (.num 0))
            (.ite (.eq (.reg "rb") (.num 0)) (PpoStability.st .rlx "y" 1) .skip) .skip)))
        (PpoStability.st .rlx "A" 1))))

/-- `ra = 0` -/
def c3 : Expr := .eq (.sym 3) (.val (.num 0))
/-- `rb = 0` -/
def c4 : Expr := .eq (.sym 4) (.val (.num 0))

def e0 : Event := PpoStability.W 0 0 [0] [] [] .rlx "A" 0
def e1 : Event := PpoStability.W 1 0 [1, 0] [] [] .rlx "B" 0
def e2 : Event := PpoStability.W 2 0 [1, 1, 0] [] [] .rlx "y" 0
def e3 : Event := PpoStability.R 3 0 [1, 1, 1, 0, 0] [] [] .rlx "A"
def e4 : Event := PpoStability.R 4 0 [1, 1, 1, 0, 1, 0] [] [] .rlx "B"
def e5 : Event := ⟨5, .branch c3, ⟨0, [1, 1, 1, 0, 1, 1], []⟩, []⟩
def e6 : Event := ⟨6, .branch c4, ⟨0, [1, 1, 1, 0, 1, 1, 0], []⟩, [⟨5, c3, true⟩]⟩
def e7 : Event :=
  PpoStability.W 7 0 [1, 1, 1, 0, 1, 1, 0, 0] [] [⟨5, c3, true⟩, ⟨6, c4, true⟩] .rlx "y" 1
def e8 : Event := PpoStability.W 8 1 [1, 1, 1, 1] [] [] .rlx "A" 1

def poL : List (EventId × EventId) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 2), (1, 3), (1, 4),
   (1, 5), (1, 6), (1, 7), (1, 8), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 4),
   (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]

def esG : EventStructure := ⟨[e0, e1, e2, e3, e4, e5, e6, e7, e8], poL, []⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esG := rfl

theorem nodupG : (esG.events.map (·.id)).Nodup := by decide

theorem gG : GlobLocs esG := globLocs_of (by decide)

theorem poClosed : Closed esG.po := by decide

theorem po_trans : ∀ a b c, esG.poR a b → esG.poR b c → esG.poR a c := poTrans_of poClosed

/-- The valuation with every symbol `0`, under which every value restriction holds. -/
def f₀ : Valuation := fun _ => .num 0

theorem holds₀ {e : Event} (he : e ∈ esG.events) : e.valres.holds f₀ := by
  simp only [esG, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold Expr.holds <;> decide

theorem noEdge_empty : ∀ a b, ¬ FwdCtx.empty.edge a b :=
  fun _ _ h => by rcases h with h | h <;> cases h

/-- The paper's `≼^P` (no forwarding) into `y := 1` comes from `y := 0` only, whatever `P`. -/
theorem ppo_into_7 {P : Pred} {a : EventId} (h : esG.ppo P .empty a 7) : a = 2 := by
  have hm := ppo_mem rfl gG noEdge_empty h
  have key : ∀ p ∈ syncL esG ++ aliasL esG, p.2 = 7 → p.1 = 2 := by decide
  exact key _ hm rfl

/-- … and nothing is `≼^P`-before `y := 0`. -/
theorem no_ppo_into_2 {P : Pred} {a : EventId} : ¬ esG.ppo P .empty a 2 := by
  intro h
  have hm := ppo_mem rfl gG noEdge_empty h
  have key : ∀ p ∈ syncL esG ++ aliasL esG, p.2 ≠ 2 := by decide
  exact key _ hm rfl

/-! ## The generated justification -/

/-- A pre-justification with no dependencies (constant location and value). -/
def pj (w : Event) : Justification := ⟨w.valres, [], .empty, w⟩

/-- `(ra = 0 ∧ rb = 0, ∅) ⊢ y := 1` -/
def j7 : Justification := pj e7

/-- `Λ = [ra ↦ rb]`, the identity elsewhere. -/
def Λ : Relabelling := fun α => if α = 3 then some 4 else none

/-- The shared conjuncts `C = conj(⟦P⟧_Λ) ∩ conj(P)`: `⊤ ∧ rb = 0 ∧ rb = 0`. -/
def PW : Expr := Expr.conj [Expr.tt, c4, c4]
/-- The factored disjunction `⋀∅ ∨ ⋀{ra = 0}`. -/
def Pv : Expr := .or (Expr.conj []) (Expr.conj [c3])

/-- The lifted justification `(C ∧ (⋀∅ ∨ ra = 0), ∅) ⊢ y := 1`. -/
def jL : Justification := { j7 with P := Expr.liftPred (j7.P.rename Λ) j7.P }
/-- The weakened justification `(⊤ ∧ rb = 0 ∧ rb = 0, ∅) ⊢ y := 1`. -/
def jW : Justification := { j7 with P := PW }

theorem jL_P : jL.P = .and PW Pv := by decide

theorem pre7 : esG.Generated (fun _ => True) j7 :=
  .pre (w := e7) (by simp [esG]) rfl ⟨f₀, holds₀ (by simp [esG])⟩

theorem Λ_inj : Λ.Injective := by
  intro a b c ha hb
  simp only [Λ] at ha hb
  split at ha <;> split at hb <;> simp_all

/-- Constant expressions are relabel-equivalent to themselves, with themselves as witness. -/
theorem relabEqExpr_val {es : EventStructure} {L : Relabelling} {P₁ P₂ : Expr} (v : Val) :
    es.relabEqExpr .empty L P₁ (.val v) P₂ (.val v) :=
  ⟨.val v, fun _ _ _ h => h, fun _ _ _ h => h⟩

theorem relabEq_W {P₁ P₂ : Expr} (i t : Nat) (pc : List Nat) (gs₁ gs₂ : List Guard) (x : String)
    (n : Nat) :
    esG.relabEq .empty Λ P₁ (PpoStability.W i t pc [] gs₁ .rlx x n) P₂
      (PpoStability.W i t pc [] gs₂ .rlx x n) := by
  simp only [relabEq, PpoStability.W, Event.isRead, Event.isWrite, Event.isAlloc, Event.loc,
    Event.val, Bool.and_self, Bool.or_true]
  exact ⟨⟨_, _, rfl, rfl, relabEqExpr_val _⟩, ⟨_, _, rfl, rfl, relabEqExpr_val _⟩⟩

theorem cre_2 {P₁ P₂ : Expr} : esG.ClosedRelabEq .empty Λ P₁ e2 P₂ e2 :=
  .mk (relabEq_W 2 0 _ [] [] "y" 0)
    ⟨fun _ _ h => no_ppo_into_2 h.1, fun _ _ h => no_ppo_into_2 h.1⟩
    (fun _ _ _ _ h => (no_ppo_into_2 h.1).elim)

/-- **`y := 1` is closed relabel-equivalent to itself under `Λ`**: its immediate
    `≼`-predecessors under either predicate are `y := 0`, related to itself. -/
theorem cre_7 : esG.ClosedRelabEq .empty Λ j7.P e7 j7.P e7 := by
  refine .mk (relabEq_W 7 0 _ _ _ "y" 1) Iff.rfl (fun x₁ x₂ ev₁ ev₂ h₁ h₂ hv₁ hv₂ => ?_)
  have := ppo_into_7 h₁.1; subst this
  have := ppo_into_7 h₂.1; subst this
  have h2 : esG.ev 2 = some e2 := PpoKit.ev_of_mem nodupG (e := e2) (by simp [esG])
  rw [h2] at hv₁ hv₂
  cases hv₁; cases hv₂
  exact cre_2

/-- Every condition of the unrestricted Lifting holds: those of sMRD's Def. 4.16 and the paper's
    `def:elab-lift`, with the library's `⊑`-restriction and volatile condition. -/
theorem lift_conds : esG.LiftConds (fun _ => True) Λ j7 j7 := by
  refine ⟨rfl, Λ_inj, cre_7, ?_, ?_, ?_, ?_, ?_, ?_, ⟨f₀, ?_, trivial⟩⟩
  · intro e; show e ∈ ([] : List EventId) ↔ ∃ α ∈ ([] : List EventId), Λ.app α = e; simp
  · intro α h; nomatch h
  · intro h; have := cls_clsB.1 h; revert this; decide
  · intro h; have := cls_clsB.1 h; revert this; decide
  · intro α h; nomatch h
  · -- `⟦P⟧_Λ` has the symbol `rb` only, `⊑`-before `y := 1`
    intro α h
    have hs : (j7.P.rename Λ).syms = [4, 4] := by decide
    rw [hs] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at h
    subst h; show (4, 7) ∈ poL; decide
  · unfold Expr.holds; decide

theorem Pv_valid : Entails (fun _ => True) Pv.holds := by
  intro f _
  simp [Pv, Expr.holds, Expr.conj, Expr.eval, Expr.tt, c3]

/-- The two restrictions are all that stands between `lift_conds` and the lift. -/
theorem gen_jL_of (hb : esG.LiftBranch Λ j7.w.id j7.w.id) (hi : Λ.InjOn (j7.P.syms ++ j7.D)) :
    esG.Generated (fun _ => True) jL :=
  .lift' pre7 pre7 lift_conds hb hi

/-- **Were the lift generated, so would be the weakened justification**: Weakening drops the
    valid disjunction. -/
theorem gen_jW_of (hL : esG.Generated (fun _ => True) jL) : esG.Generated (fun _ => True) jW :=
  .weak (j₁ := jL) (P' := PW) (Pw := Pv) hL (by rw [jL_P]; exact Expr.ConjEq.refl _) Pv_valid
    ⟨f₀, by unfold Expr.holds; decide, trivial⟩

/-- `ra` is not a symbol of the weakened justification; `rb` is. -/
theorem jW_syms : 3 ∉ jW.P.syms ∧ 4 ∈ jW.P.syms ∧ jW.D = [] := by decide

/-- Under a relabelling swapping `ra` and `rb`, the lifted predicate keeps `ra`. -/
theorem swap_keeps :
    3 ∈ (Expr.liftPred (j7.P.rename (fun α => if α = 3 then some 4 else
      if α = 4 then some 3 else none)) j7.P).syms := by decide

/-! ## The execution -/

def rfL : List (EventId × EventId) := [(8, 3), (1, 4)]

def Jx : List Justification := [pj e0, pj e1, pj e2, jW, pj e8]

/-- `X` takes both branches; `ra` reads `A := 1`, `rb` reads `B := 0`; `y := 1` carries the
    weakened justification. -/
def x : Execution := ⟨esG.Candidate, Jx, fun w r => (w, r) ∈ rfL⟩

theorem δx : x.δ = .empty := foldr_empty (by
  intro j hj
  simp only [x, Jx, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl <;> rfl)

theorem not_elided (a : EventId) : ¬ x.elided a := not_elided_of_δ_empty _ δx a

theorem gen_Jx (hL : esG.Generated (fun _ => True) jL) :
    ∀ j ∈ Jx, esG.Generated (fun _ => True) j := by
  intro j hj
  simp only [Jx, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exact .pre (w := e0) (by simp [esG]) rfl ⟨f₀, holds₀ (by simp [esG])⟩
  · exact .pre (w := e1) (by simp [esG]) rfl ⟨f₀, holds₀ (by simp [esG])⟩
  · exact .pre (w := e2) (by simp [esG]) rfl ⟨f₀, holds₀ (by simp [esG])⟩
  · exact gen_jW_of hL
  · exact .pre (w := e8) (by simp [esG]) rfl ⟨f₀, holds₀ (by simp [esG])⟩

theorem cand_iff {a : EventId} : esG.Candidate a ↔ a ∈ [0, 1, 2, 3, 4, 7, 8] := by
  constructor
  · rintro ⟨⟨e, he, rfl⟩, hb, hf⟩
    simp only [esG, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try decide
    · exact absurd ⟨e5, PpoKit.ev_of_mem nodupG (by simp [esG]), rfl⟩ hb
    · exact absurd ⟨e6, PpoKit.ev_of_mem nodupG (by simp [esG]), rfl⟩ hb
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cand_of_mem nodupG (e := e0) (by simp [esG]) rfl rfl
    · exact cand_of_mem nodupG (e := e1) (by simp [esG]) rfl rfl
    · exact cand_of_mem nodupG (e := e2) (by simp [esG]) rfl rfl
    · exact cand_of_mem nodupG (e := e3) (by simp [esG]) rfl rfl
    · exact cand_of_mem nodupG (e := e4) (by simp [esG]) rfl rfl
    · exact cand_of_mem nodupG (e := e7) (by simp [esG]) rfl rfl
    · exact cand_of_mem nodupG (e := e8) (by simp [esG]) rfl rfl

theorem inE_of_cls {p : Event → Bool} {a : EventId} (h : esG.cls p a) :
    ∃ e ∈ esG.events, e.id = a ∧ p e = true := by
  obtain ⟨e, he, hp⟩ := h
  exact ⟨e, (ev_inv he).1, (ev_inv he).2, hp⟩

theorem inj_of_nodup {J : List Justification} (hnd : (J.map (·.w.id)).Nodup) {a b : Justification}
    (ha : a ∈ J) (hb : b ∈ J) (h : a.w.id = b.w.id) : a = b := by
  induction J with
  | nil => cases ha
  | cons c J ih =>
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
      rcases List.mem_cons.1 ha with ha | ha <;> rcases List.mem_cons.1 hb with hb | hb
      · rw [ha, hb]
      · exact absurd ⟨b, hb, by rw [← ha]; exact h.symm⟩ hnd.1
      · exact absurd ⟨a, ha, by rw [← hb]; exact h⟩ hnd.1
      · exact ih hnd.2 ha hb

theorem rf_wr_x :
    ∀ w r, x.rf w r → esG.cls Event.isWrite w ∧ esG.cls Event.isRead r ∧ x.X w ∧ x.X r := by
  intro w r h
  have key : ∀ p ∈ rfL, clsB esG Event.isWrite p.1 = true ∧ clsB esG Event.isRead p.2 = true ∧
      p.1 ∈ [0, 1, 2, 3, 4, 7, 8] ∧ p.2 ∈ [0, 1, 2, 3, 4, 7, 8] := by decide
  obtain ⟨h₁, h₂, h₃, h₄⟩ := key _ h
  exact ⟨cls_clsB.2 h₁, cls_clsB.2 h₂, cand_iff.2 h₃, cand_iff.2 h₄⟩

/-- **Were the lift generated, `x` would be an execution.** -/
theorem isExecution_x (hL : esG.Generated (fun _ => True) jL) :
    x.IsExecution esG (fun _ => True) where
  maximal := ⟨fun _ h => h, fun a b _ _ ⟨ea, eb, ha, hb, hn⟩ =>
      hn ⟨f₀, holds₀ (ev_inv ha).1, holds₀ (ev_inv hb).1⟩,
    fun _ hc hn => absurd hc hn⟩
  generated := gen_Jx hL
  inX j hj := by
    simp only [x, Jx, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> exact cand_iff.2 (by decide)
  consistent := ⟨f₀, fun j hj => by
      simp only [x, Jx, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> unfold Expr.holds <;> decide,
    fun a e _ he => holds₀ (ev_inv he).1⟩
  fwdWF := by rw [δx]; exact FwdCtx.WF.empty
  rf_wr := rf_wr_x
  rf_func w w' r h h' := by
    have key : ∀ p ∈ rfL, ∀ q ∈ rfL, p.2 = q.2 → p.1 = q.1 := by decide
    exact key _ h _ h' rfl
  justified w hw he _ := by
    obtain ⟨e, hm, rfl, hef⟩ := inE_of_cls he
    have hex : ∀ e ∈ esG.events, e.isEffect = true → ∃ j ∈ Jx, j.w.id = e.id := by decide
    obtain ⟨j, hj, hjw⟩ := hex e hm hef
    refine ⟨j, hj, hjw, fun j' hj' h => ?_⟩
    have hnd : (Jx.map (·.w.id)).Nodup := by decide
    exact inj_of_nodup hnd hj' hj (h.trans hjw.symm)
  notElided j _ := not_elided j.w.id

/-- The valuation of `φ`: `ra = 1`, every other symbol `0`. -/
def g₁ : Valuation := fun α => if α = 3 then .num 1 else .num 0

theorem P_iff {f : Valuation} : x.P esG f ↔ ∀ j ∈ Jx, j.P.holds f := by
  constructor
  · intro h j hj; exact (h j hj).1
  · intro h j hj
    refine ⟨h j hj, fun p hp => ?_⟩
    simp only [x, Jx, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> cases hp

theorem phi_x : x.phi esG := by
  refine ⟨fun e _ hel => not_elided e hel, fun r => ⟨?_, ?_⟩, g₁, P_iff.2 ?_, ?_, ?_, ?_⟩
  · rintro ⟨w, hw⟩
    exact ⟨(rf_wr_x w r hw).2.2.2, (rf_wr_x w r hw).2.1⟩
  · rintro ⟨-, hr⟩
    obtain ⟨e, hm, rfl, hp⟩ := inE_of_cls hr
    have key : ∀ e ∈ esG.events, e.isRead = true → ∃ p ∈ rfL, p.2 = e.id := by decide
    obtain ⟨p, hp', h2⟩ := key e hm hp
    exact ⟨p.1, by rw [← h2]; exact hp'⟩
  · intro j hj
    simp only [Jx, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> unfold Expr.holds <;> decide
  · intro w r ew er h hw hr
    have key : ∀ p ∈ rfL, ∀ ew ∈ esG.events, ∀ er ∈ esG.events, ew.id = p.1 → er.id = p.2 →
        ew.loc.map (·.eval g₁) = er.loc.map (·.eval g₁) ∧
        ew.val.map (·.eval g₁) = er.val.map (·.eval g₁) := by decide
    have := key (w, r) h ew (ev_inv hw).1 er (ev_inv hr).1 (ev_inv hw).2 (ev_inv hr).2
    refine ⟨fun lw lr h₁ h₂ => ?_, fun vw vr h₁ h₂ => ?_⟩
    · have := this.1; rw [h₁, h₂] at this; exact Option.some.inj this
    · have := this.2; rw [h₁, h₂] at this; exact Option.some.inj this
  · intro a e α sz _ he hk
    have key : ∀ e ∈ esG.events, e.isAlloc = false := by decide
    have := key e (ev_inv he).1
    simp [Event.isAlloc, hk] at this
  · intro a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂ _ _ _ he₁ _ hk₁
    have key : ∀ e ∈ esG.events, e.isAlloc = false := by decide
    have := key e₁ (ev_inv he₁).1
    simp [Event.isAlloc, hk₁] at this

/-- **Every model of `φ_rf` has `ra = 1`** (`ra` reads `A := 1`): the outer branch condition
    fails. -/
theorem ra_one {f : Valuation} (hφ : x.phiRf esG f) :
    f 3 = .num 1 ∧ ¬ c3.holds f := by
  have := (hφ.1 8 3 e8 e3 (by show (8, 3) ∈ rfL; decide)
    (PpoKit.ev_of_mem nodupG (e := e8) (by simp [esG]))
    (PpoKit.ev_of_mem nodupG (e := e3) (by simp [esG]))).2 _ _ rfl rfl
  simp only [Expr.num, Expr.eval] at this
  have h3 : f 3 = .num 1 := (Option.some.inj this).symm
  refine ⟨h3, fun h => ?_⟩
  simp [Expr.holds, c3, Expr.eval, h3] at h

/-! ### No-Thin-Air -/

theorem rmwTight : Execution.RMWTight esG x :=
  ⟨fun _ h => by simp [esG] at h, fun _ h => by simp [esG] at h⟩

theorem noEdge_x : ∀ a b, ¬ x.δ.edge a b := noEdge_of_noElided not_elided

/-- `DP ∪ ≼ ⊆ ⊑`. -/
theorem dep_po {a b : EventId} (h : x.dep esG a b) : esG.poR a b := by
  rcases h with hp | ⟨-, -, j, hj, rfl, hs⟩
  · exact Execution.ppo_po po_trans (fun _ _ s => Execution.ppoStep_po noEdge_x rmwTight s) hp
  · have key : ∀ j ∈ Jx, ∀ a ∈ j.P.syms ++ j.D, (a, j.w.id) ∈ poL := by decide
    exact key j hj a (List.mem_append.2 hs)

def ntaL : List (EventId × EventId) := poL ++ [(8, 3), (8, 4), (8, 5), (8, 6), (8, 7)]

theorem noThinAir_x : x.NoThinAir esG := by
  intro a h
  have hc : Closed ntaL := by decide
  have hm : (a, a) ∈ ntaL := by
    refine transGen_mem (fun c d s => ?_) hc h
    rcases s with s | s
    · exact List.mem_append.2 (.inl (dep_po s))
    · have key : ∀ p ∈ rfL, p ∈ ntaL := by decide
      exact key _ s
  have key : ∀ p ∈ ntaL, p.1 ≠ p.2 := by decide
  exact key _ hm rfl

/-! ### Coherence -/

def coL : List (EventId × EventId) := [(0, 8), (2, 7)]

theorem sameLoc_locOf {a b : EventId} (h : x.sameLoc esG a b) : locOf esG a = locOf esG b := by
  obtain ⟨ea, eb, la, lb, ha, hb, hla, hlb, hs⟩ := h
  have hgl := gG ea (ev_inv ha).1 la hla
  have hgl' := gG eb (ev_inv hb).1 lb hlb
  obtain ⟨y₁, rfl⟩ := hgl
  obtain ⟨y₂, rfl⟩ := hgl'
  obtain ⟨-, -, f, hP, hφ⟩ := phi_x
  have := hs f hP hφ
  simp only [Expr.glob, Expr.eval, Option.some.injEq, Val.loc.injEq, Loc.mk.injEq,
    LocBase.global.injEq, and_true] at this
  subst this
  simp [locOf, ha, hb, hla, hlb]

theorem coOrder : x.CoherenceOrder esG (PpoNecessity.relL coL) where
  writes a b h := by
    have key : ∀ p ∈ coL, clsB esG Event.isWrite p.1 = true ∧
        clsB esG Event.isWrite p.2 = true ∧
        p.1 ∈ [0, 1, 2, 3, 4, 7, 8] ∧ p.2 ∈ [0, 1, 2, 3, 4, 7, 8] := by decide
    obtain ⟨h₁, h₂, h₃, h₄⟩ := key _ h
    exact ⟨cand_iff.2 h₃, cand_iff.2 h₄, cls_clsB.2 h₁, cls_clsB.2 h₂⟩
  irrefl a h := by
    have key : ∀ p ∈ coL, p.1 ≠ p.2 := by decide
    exact key _ h rfl
  trans a b c h₁ h₂ := by
    have key : Closed coL := by decide
    exact key _ h₁ _ h₂ rfl
  total a b ha hb hwa hwb hne hsl := by
    have key : ∀ a ∈ [0, 1, 2, 3, 4, 7, 8], ∀ b ∈ [0, 1, 2, 3, 4, 7, 8],
        clsB esG Event.isWrite a = true → clsB esG Event.isWrite b = true → a ≠ b →
        locOf esG a = locOf esG b → (a, b) ∈ coL ∨ (b, a) ∈ coL := by decide
    exact key a (cand_iff.1 ha) b (cand_iff.1 hb) (cls_clsB.1 hwa) (cls_clsB.1 hwb) hne
      (sameLoc_locOf hsl)

theorem no_sw {a b : EventId} : ¬ x.sw esG a b := by
  intro h
  obtain ⟨ha, -⟩ := sw_cls h
  have hid : a ∈ esG.ids := by
    simp only [Bool.or_eq_true] at ha; rcases ha with h | h <;> exact clsB_id h
  have key : ∀ a ∈ esG.ids, (clsB esG Event.isRelW a || clsB esG Event.isRelF a) = false := by
    decide
  rw [key a hid] at ha; cases ha

def ecoL : List (EventId × EventId) := [(8, 3), (1, 4), (0, 8), (2, 7), (0, 3)]

theorem coherence_x : x.Coherence esG (PpoNecessity.relL coL) := by
  refine coherenceVOver_of (D := x.poX esG) (H := poL) (E := ecoL)
    (fun a b h => transGen_mem (fun _ _ s => by
      rcases s with s | s
      · exact s.2.2
      · exact (no_sw s).elim) poClosed h) (fun a b h => ?_) (by decide)
  have hE : ∀ p ∈ rfL ++ coL ++ PpoNecessity.frL rfL coL, p ∈ ecoL := by decide
  refine eco_mem (fun c d h => hE _ ?_) (fun c d h => hE _ ?_) (fun c d h => hE _ ?_)
    (by decide) h
  · exact List.mem_append.2 (.inl (List.mem_append.2 (.inl h)))
  · exact List.mem_append.2 (.inl (List.mem_append.2 (.inr h)))
  · obtain ⟨w, hrf, hco⟩ := h
    exact List.mem_append.2 (.inr (List.mem_flatMap.2 ⟨(w, c), hrf, List.mem_map.2 ⟨(w, d),
      List.mem_filter.2 ⟨hco, by simp⟩, rfl⟩⟩))

theorem atomicity_x (co : Rel) : x.Atomicity esG co := by
  rintro r w ⟨-, -, ent, hm, -⟩
  simp [esG] at hm

theorem coherent_x : x.Coherent esG :=
  ⟨PpoNecessity.relL coL, coOrder, coherence_x, atomicity_x _,
   x.psc_of_noSC esG (x.scFree_of_es esG (esG.scFree_of_all (by decide))) _⟩

/-- **Were the lift generated, the execution would be consistent.** -/
theorem consistent_x (hL : esG.Generated (fun _ => True) jL) : x.Consistent esG (fun _ => True) :=
  ⟨isExecution_x hL, phi_x, noThinAir_x, coherent_x⟩

/-- … also with coherence over `X ∖ †` (nothing is elided). -/
theorem consistentT_x (hL : esG.Generated (fun _ => True) jL) :
    x.ConsistentT esG (fun _ => True) :=
  ⟨isExecution_x hL, phi_x, noThinAir_x, (coherentT_iff_coherent not_elided).2 coherent_x⟩

/-- **The guard is lost under the unrestricted rule**: were the lift generated, a consistent
    execution would run `y := 1`, guarded by `ra = 0`, while every model of its constraints
    `P ∧ φ_rf` has `ra = 1`, and `(ra, y := 1) ∉ DP`. -/
theorem guard_lost (hL : esG.Generated (fun _ => True) jL) :
    x.Consistent esG (fun _ => True) ∧ x.X 7 ∧
    e7.valres.holds = (Expr.and (Expr.and Expr.tt c3) c4).holds ∧
    (∀ f, x.P esG f → x.phiRf esG f → f 3 = .num 1 ∧ ¬ c3.holds f) ∧
    (∃ f, x.P esG f ∧ x.phiRf esG f) ∧ ¬ x.DP 3 7 := by
  refine ⟨consistent_x hL, cand_iff.2 (by decide), rfl, fun f _ hφ => ra_one hφ, phi_x.2.2, ?_⟩
  rintro ⟨-, -, j, hj, hw, hs⟩
  have key : ∀ j ∈ Jx, j.w.id = 7 → 3 ∉ j.P.syms ++ j.D := by decide
  exact key j hj hw (List.mem_append.2 hs)

/-! ## The restricted rule

`Generated.lift` asks the lifted writes to lie on different outcomes of a branching, with `Λ`
mapping symbols of one outcome into the other (`LiftBranch`), and `⟦·⟧_Λ` to be one-to-one on
the symbols of `P₁` and `D₁` (`Relabelling.InjOn`). The lift above fails both: it lifts `y := 1`
into itself, and no event of `esG` is in conflict with any (every guard is positive); `⟦·⟧_Λ`
merges `ra` and `rb`. More: no generated justification of `y := 1` loses the conjunct `ra = 0`
unless `ra` is forwarded (`guard_kept`), so `jW` is not generated (`not_gen_jW`) and `x` is no
execution (`not_execution`). -/

/-- No two events of `esG` diverge: every guard is positive. -/
theorem not_diverged {a b : EventId} : ¬ esG.Diverged a b :=
  PpoKit.not_diverged_of_pos (by decide)

/-- **The branching restriction refuses every lift in `esG`**, in particular `y := 1` into
    itself. -/
theorem not_liftBranch (Λ' : Relabelling) (a b : EventId) : ¬ esG.LiftBranch Λ' a b :=
  fun h => not_diverged h.diverged

/-- **The one-to-one renaming refuses the lift too**: `⟦ra⟧_Λ = rb = ⟦rb⟧_Λ`. -/
theorem not_injOn : ¬ Λ.InjOn (j7.P.syms ++ j7.D) := by
  intro h
  have := h 3 (by decide) 4 (by decide) (by decide)
  cases this

/-- The values forwarding can substitute, `[v₂ ↦ v₁]`, leave `ra = 0` intact. -/
def keepsC3 (v₁ v₂ : Expr) : Bool :=
  v₂ != c3 && v₂ != .sym 3 && (v₂ != .val (.num 0) || v₁ == .val (.num 0)) &&
    (match v₂ with | .and _ _ => false | _ => true)

theorem c3_replace {v₁ v₂ : Expr} (h : keepsC3 v₁ v₂ = true) :
    c3.replace v₂ v₁ = c3 ∧ (∀ a b, v₂ ≠ .and a b) ∧ c3 ≠ v₂ := by
  simp only [keepsC3, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, (fun a b hab => by subst hab; cases h4), Ne.symm h1⟩
  unfold c3 at h1 ⊢
  rw [Expr.replace.eq_def, if_neg (Ne.symm h1)]
  simp only
  rw [Expr.replace.eq_def, if_neg (Ne.symm h2), Expr.replace.eq_def]
  by_cases h0 : Expr.val (.num 0) = v₂
  · rw [if_pos h0, (h3.resolve_left (fun h' => h' h0.symm))]
  · rw [if_neg h0]

/-- Forwarding into an event other than `ra` keeps `ra = 0`: the forwarded values are `0`, `1`
    and `rb`, and a `0` comes only from a `0`. -/
theorem fwd_keeps : ∀ ev₁ ∈ esG.events, ∀ ev₂ ∈ esG.events, (ev₁.id, ev₂.id) ∈ poL →
    ev₂.id ≠ 3 →
    (match ev₁.val, ev₂.val with | some v₁, some v₂ => keepsC3 v₁ v₂ | _, _ => true) = true := by
  decide

/-- The pre-justification of `y := 1` has the conjunct `ra = 0`. -/
theorem pre_keeps : ∀ w ∈ esG.events,
    (match preJust w with
      | some j => decide (j.w.id = 7 → c3 ∈ j.P.conjuncts)
      | none => true) = true := by
  decide

/-- **No generated justification of `y := 1` loses the guard `ra = 0`**, unless `ra` is
    forwarded: every one has `ra = 0` among its conjuncts, or a forwarding edge into `ra`. Under
    any global guarantees `Ω` that do not imply `ra = 0` (Weakening keeps the conjunct). The
    branching restriction refuses every Lifting in `esG`; Value Assignment, Write Elision and
    Strengthening keep the conjuncts; Forwarding replaces `val(e₂)`, which leaves `ra = 0`
    unless `e₂` is `ra`. -/
theorem guard_kept {Ω : Pred} (hΩ : ¬ Entails Ω c3.holds) {j : Justification}
    (h : esG.Generated Ω j) : j.w.id = 7 → c3 ∈ j.P.conjuncts ∨ ∃ e, (e, 3) ∈ j.δ.f := by
  induction h with
  | @pre w j hw hj _ =>
      intro h7; left
      have := pre_keeps w hw
      rw [hj] at this
      exact of_decide_eq_true this h7
  | va _ _ _ _ ih => exact ih
  | str Q S _ _ _ _ _ ih =>
      intro h7
      rcases ih h7 with h | h
      · exact .inl (conjuncts_strPred esG _ h)
      · exact .inr h
  | @fwd j₁ o x e b e₁ e₂ ev₁ ev₂ v₁ v₂ _ _ hf h₁ h₂ hv₁ hv₂ _ _ ih =>
      intro h7
      rcases ih h7 with h | ⟨e', he⟩
      · by_cases h3 : e₂ = 3
        · subst h3; exact .inr ⟨e₁, List.mem_append_right _ (List.mem_singleton_self _)⟩
        · left
          have hpo : (ev₁.id, ev₂.id) ∈ poL := by
            rw [(ev_inv h₁).2, (ev_inv h₂).2]; exact hf.1.1.2.1
          have hk := fwd_keeps ev₁ (ev_inv h₁).1 ev₂ (ev_inv h₂).1 hpo
            (by rw [(ev_inv h₂).2]; exact h3)
          rw [hv₁, hv₂] at hk
          obtain ⟨hr, hnand, hne⟩ := c3_replace hk
          have := Expr.mem_conjuncts_replace (q := v₁) hnand hne h
          rwa [hr] at this
      · exact .inr ⟨e', List.mem_append_left _ he⟩
  | we _ _ _ _ ih => exact ih
  | lift _ _ _ _ _ hb => exact absurd hb.diverged not_diverged
  | @weak j₁ P' Pw _ hc hE _ ih =>
      intro h7
      rcases ih h7 with h | h
      · left
        have := (hc c3).1 h
        simp only [Expr.conjuncts, List.mem_append] at this
        rcases this with h' | h'
        · exact h'
        · exact absurd (fun f hf => (Expr.holds_iff_conjuncts Pw f).1 (hE f hf) c3 h') hΩ
      · exact .inr h

theorem not_entails_c3 : ¬ Entails (fun _ => True) c3.holds :=
  fun h => absurd (h g₁ trivial) (by unfold Expr.holds; decide)

/-- **The weakened justification is not generated.** -/
theorem not_gen_jW : ¬ esG.Generated (fun _ => True) jW := by
  intro h
  rcases guard_kept not_entails_c3 h rfl with h | ⟨e, he⟩
  · revert h; decide
  · cases he

/-- **Nor is the lifted one**: `ra = 0` is no conjunct of it. -/
theorem not_gen_jL : ¬ esG.Generated (fun _ => True) jL := by
  intro h
  rcases guard_kept not_entails_c3 h rfl with h | ⟨e, he⟩
  · revert h; decide
  · cases he

/-- **`x` is no execution.** -/
theorem not_execution {Ω : Pred} (hΩ : ¬ Entails Ω c3.holds) : ¬ x.IsExecution esG Ω := by
  intro hx
  rcases guard_kept hΩ (hx.generated jW (by simp [x, Jx])) rfl with h | ⟨e, he⟩
  · revert h; decide
  · cases he

/-! ## The same with `free(r)`

`A := 0; B := 0; (r := malloc(1); ra := A; rb := B; if ra = 0 then (if rb = 0 then free(r))
∥ A := 1)`. Under the pre-justification's predicate `ra = 0 ∧ rb = 0` the location `r` of
`free(r)` may alias `A` and `B`, so the reads `ra` and `rb` are immediate `≼`-predecessors of
`free(r)`, and the all-pairs clause of closed relabel-equivalence would relate the read of `A` to
the read of `B`, which fails. Strengthening by `Q = r ≠ &A ∧ r ≠ &B` (origin: the allocation)
leaves the allocation as the only immediate predecessor, and the lift goes through as for the
write. -/

namespace Free

/-- `A := 0; B := 0; (r := malloc(1); ra := A; rb := B;
    if ra = 0 then (if rb = 0 then free(r)) ∥ A := 1)` -/
def prog : Stmt :=
  .seq (PpoStability.st .rlx "A" 0) (.seq (PpoStability.st .rlx "B" 0)
    (.par (.seq (.malloc "r" (.num 1)) (.seq (PpoStability.ld .rlx "ra" "A")
        (.seq (PpoStability.ld .rlx "rb" "B")
          (.ite (.eq (.reg "ra") (.num 0))
            (.ite (.eq (.reg "rb") (.num 0)) (.free "r") .skip) .skip))))
      (PpoStability.st .rlx "A" 1)))

def e0 : Event := PpoStability.W 0 0 [0] [] [] .rlx "A" 0
def e1 : Event := PpoStability.W 1 0 [1, 0] [] [] .rlx "B" 0
def e2 : Event := ⟨2, .alloc 2 (.val (.num 1)), ⟨0, [1, 1, 0, 0], []⟩, []⟩
def e3 : Event := PpoStability.R 3 0 [1, 1, 0, 1, 0] [] [] .rlx "A"
def e4 : Event := PpoStability.R 4 0 [1, 1, 0, 1, 1, 0] [] [] .rlx "B"
def e5 : Event := ⟨5, .branch c3, ⟨0, [1, 1, 0, 1, 1, 1], []⟩, []⟩
def e6 : Event := ⟨6, .branch c4, ⟨0, [1, 1, 0, 1, 1, 1, 0], []⟩, [⟨5, c3, true⟩]⟩
def e7 : Event :=
  ⟨7, .dealloc (.sym 2), ⟨0, [1, 1, 0, 1, 1, 1, 0, 0], []⟩, [⟨5, c3, true⟩, ⟨6, c4, true⟩]⟩
def e8 : Event := PpoStability.W 8 1 [1, 1, 1] [] [] .rlx "A" 1

def poL : List (EventId × EventId) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 2), (1, 3), (1, 4),
   (1, 5), (1, 6), (1, 7), (1, 8), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5),
   (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]

def esF : EventStructure := ⟨[e0, e1, e2, e3, e4, e5, e6, e7, e8], poL, []⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esF := rfl

theorem nodupF : (esF.events.map (·.id)).Nodup := by decide

theorem poClosed : Closed esF.po := by decide

theorem po_trans : ∀ a b c, esF.poR a b → esF.poR b c → esF.poR a c := poTrans_of poClosed

/-- The heap cell `malloc` returns in both valuations. -/
def cell : Val := .loc ⟨.heap 0, 0⟩

/-- Every symbol `0` but `r`, a heap cell. -/
def f₀ : Valuation := fun α => if α = 2 then cell else .num 0

/-- … and `ra = 1`. -/
def g₁ : Valuation := fun α => if α = 2 then cell else if α = 3 then .num 1 else .num 0

theorem holds₀ {e : Event} (he : e ∈ esF.events) : e.valres.holds f₀ := by
  simp only [esF, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold Expr.holds <;> decide

/-! ### The generated justification -/

/-- `(ra = 0 ∧ rb = 0, {r}) ⊢ free(r)` -/
def j7 : Justification := ⟨e7.valres, [2], .empty, e7⟩

/-- `r ≠ &A ∧ r ≠ &B` -/
def Q : Expr := .and (.not (.eq (.sym 2) (Expr.glob "A"))) (.not (.eq (.sym 2) (Expr.glob "B")))

/-- Strengthened by `Q`, origin the allocation. -/
def jS : Justification := { j7 with P := esF.strPred j7.P Q [2] }

/-- The shared conjuncts of `⟦P_S⟧_Λ` and `P_S`. -/
def PW : Expr :=
  Expr.conj ((jS.P.rename Λ).conjuncts.filter (fun c => decide (c ∈ jS.P.conjuncts)))

def jL : Justification := { jS with P := Expr.liftPred (jS.P.rename Λ) jS.P }
def jW : Justification := { jS with P := PW }

theorem jL_P : jL.P = .and PW Pv := by decide

theorem ev_e (e : Event) (he : e ∈ esF.events) : esF.ev e.id = some e :=
  PpoKit.ev_of_mem nodupF he

theorem ev2 : esF.ev 2 = some e2 := ev_e e2 (by simp [esF])
theorem ev7 : esF.ev 7 = some e7 := ev_e e7 (by simp [esF])

/-- Without forwarding, `≼^P` lies in `⊑`, whatever `P`. -/
theorem ppo_po_any {P : Pred} {a b : EventId} (h : esF.ppo P .empty a b) : esF.poR a b := by
  obtain ⟨hab, -⟩ := h
  rcases (FwdCtx.remapRel_of_noEdge noEdge_empty).1 hab with
    (hs | ⟨⟨x, -, hx⟩ | ⟨x, hx, -⟩, -⟩) | ⟨hpo, -⟩
  · have := ppoSync_mem hs; rw [show syncL esF = [] by decide] at this; cases this
  · exact absurd hx (not_rmwPairs rfl)
  · exact absurd hx (not_rmwPairs rfl)
  · exact hpo

theorem Q_of {f : Valuation} (h : jS.P.holds f) :
    f 2 ≠ .loc ⟨.global "A", 0⟩ ∧ f 2 ≠ .loc ⟨.global "B", 0⟩ := by
  have hQ := ((Expr.holds_and _ _ f).1 ((Expr.holds_and _ _ f).1 h).2).1
  have h' := (Expr.holds_and _ _ f).1 hQ
  constructor <;> intro he
  · have := h'.1; simp [Expr.holds, Expr.eval, Expr.glob, he] at this
  · have := h'.2; simp [Expr.holds, Expr.eval, Expr.glob, he] at this

/-- Every location other than the allocation's and the deallocation's is `A` or `B`. -/
theorem locs_glob : ∀ e ∈ esF.events, e.id ≠ 2 → e.id ≠ 7 →
    e.loc = none ∨ e.loc = some (Expr.glob "A") ∨ e.loc = some (Expr.glob "B") := by decide

theorem syncL_nil : syncL esF = [] := by decide

/-- **Under `P_S`, `≼` into `free(r)` comes from the allocation only, and nothing is
    `≼`-before the allocation.** -/
theorem ppo_into {a b : EventId} (hb : b = 7 ∨ b = 2) (h : esF.ppo jS.P.holds .empty a b) :
    a = 2 ∧ b = 7 := by
  obtain ⟨hab, -⟩ := h
  rcases (FwdCtx.remapRel_of_noEdge noEdge_empty).1 hab with
    (hs | ⟨⟨x, -, hx⟩ | ⟨x, hx, -⟩, -⟩) | ⟨hpo, hal⟩
  · have := ppoSync_mem hs; rw [syncL_nil] at this; cases this
  · exact absurd hx (not_rmwPairs rfl)
  · exact absurd hx (not_rmwPairs rfl)
  · obtain ⟨ea, eb, la, lb, ha, hb', hla, hlb, f, hP, heq⟩ := hal
    have hlb' : lb = .sym 2 := by
      rcases hb with rfl | rfl
      · rw [ev7] at hb'; cases hb'; cases hlb; rfl
      · rw [ev2] at hb'; cases hb'; cases hlb; rfl
    subst hlb'
    obtain ⟨hma, rfl⟩ := ev_inv ha
    by_cases h2 : ea.id = 2
    · rcases hb with rfl | rfl
      · exact ⟨h2, rfl⟩
      · rw [h2] at hpo; exact absurd hpo (by show (2, 2) ∉ poL; decide)
    by_cases h7 : ea.id = 7
    · rw [h7] at hpo
      rcases hb with rfl | rfl
      · exact absurd hpo (by show (7, 7) ∉ poL; decide)
      · exact absurd hpo (by show (7, 2) ∉ poL; decide)
    obtain ⟨hA, hB⟩ := Q_of hP
    rcases locs_glob ea hma h2 h7 with hl | hl | hl <;> rw [hla] at hl <;> cases hl
    · simp [Expr.holds, Expr.eval, Expr.glob] at heq; exact absurd heq.symm hA
    · simp [Expr.holds, Expr.eval, Expr.glob] at heq; exact absurd heq.symm hB

theorem holdsS₀ : jS.P.holds f₀ := by unfold Expr.holds; decide

theorem gen_jS : esF.Generated (fun _ => True) jS := by
  refine .str Q [2] (.pre (w := e7) (by simp [esF]) rfl ⟨f₀, holds₀ (by simp [esF])⟩)
    ?_ ?_ ?_ ⟨f₀, holdsS₀, trivial⟩
  · have hs : (esF.strPred j7.P Q [2]).syms = [3, 4, 2, 2] := by decide
    have hp : j7.P.syms = [3, 4] := by decide
    intro e; rw [hs, hp]; simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro rfl; decide
    · rintro ⟨h₁, h₂⟩
      rcases h₁ with h | h | h | h
      · exact absurd (.inl h) h₂
      · exact absurd (.inr h) h₂
      · exact h
      · exact h
  · intro e _; exact .canon (noEdge_empty · e)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he
    exact ⟨by show (2, 7) ∈ poL; decide,
      fun h => absurd (ppo_po_any h) (by show (7, 2) ∉ poL; decide)⟩

theorem cre_2 : esF.ClosedRelabEq .empty Λ jS.P e2 jS.P e2 := by
  refine .mk ?_ ⟨fun _ _ h => absurd (ppo_into (.inr rfl) h.1).2 (by decide),
    fun _ _ h => absurd (ppo_into (.inr rfl) h.1).2 (by decide)⟩
    (fun _ _ _ _ h => absurd (ppo_into (.inr rfl) h.1).2 (by decide))
  simp only [relabEq, e2, Event.isRead, Event.isWrite, Event.isAlloc, Event.loc, Event.val,
    Bool.and_self, Bool.or_true]
  exact ⟨⟨_, _, rfl, rfl, .sym 2, AgreesUnder.refl _ _, AgreesUnder.refl _ _⟩,
    ⟨_, _, rfl, rfl, relabEqExpr_val _⟩⟩

/-- **`free(r)` is closed relabel-equivalent to itself under `Λ`**, given `P_S`. -/
theorem cre_7 : esF.ClosedRelabEq .empty Λ jS.P e7 jS.P e7 := by
  refine .mk ?_ Iff.rfl (fun x₁ x₂ ev₁ ev₂ h₁ h₂ hv₁ hv₂ => ?_)
  · simp only [relabEq, e7, Event.isRead, Event.isWrite, Event.isAlloc, Event.isDealloc,
      Event.loc, Bool.and_self, Bool.or_false, if_true]
    exact ⟨_, _, rfl, rfl, .sym 2, AgreesUnder.refl _ _, AgreesUnder.refl _ _⟩
  · have := (ppo_into (.inl rfl) h₁.1).1; subst this
    have := (ppo_into (.inl rfl) h₂.1).1; subst this
    rw [ev2] at hv₁ hv₂
    cases hv₁; cases hv₂
    exact cre_2

/-- Every condition of the unrestricted Lifting holds. -/
theorem lift_conds : esF.LiftConds (fun _ => True) Λ jS jS := by
  refine ⟨rfl, Λ_inj, cre_7, ?_, ?_, ?_, ?_, ?_, ?_, ⟨f₀, ?_, trivial⟩⟩
  · intro e
    show e ∈ [2] ↔ ∃ α ∈ [2], Λ.app α = e
    simp [Relabelling.app, Λ, eq_comm]
  · intro α h
    simp only [jS, j7, List.mem_cons, List.not_mem_nil, or_false] at h; subst h
    exact ⟨e2, e2, ev_e e2 (by simp [esF]), ev_e e2 (by simp [esF]), cre_2⟩
  · intro h; have := cls_clsB.1 h; revert this; decide
  · intro h; have := cls_clsB.1 h; revert this; decide
  · intro α h
    have key : ∀ α ∈ jS.D ++ jS.D, clsB esF Event.isVol α = false := by decide
    intro hv; have := key α h; rw [cls_clsB.1 hv] at this; cases this
  · intro α h
    have key : ∀ α ∈ (jS.P.rename Λ).syms, (α, 7) ∈ poL := by decide
    exact key α h
  · unfold Expr.holds; decide

/-- **Were the lift generated, so would be the weakened justification of `free(r)`.** -/
theorem gen_jW_of (hL : esF.Generated (fun _ => True) jL) : esF.Generated (fun _ => True) jW :=
  .weak (j₁ := jL) (P' := PW) (Pw := Pv) hL (by rw [jL_P]; exact Expr.ConjEq.refl _)
    Pv_valid ⟨f₀, by unfold Expr.holds; decide, trivial⟩

theorem jW_syms : 3 ∉ jW.P.syms ∧ 4 ∈ jW.P.syms ∧ jW.D = [2] := by decide

/-- **The restricted rule refuses the lift**: no two events of `esF` diverge, and `⟦·⟧_Λ`
    merges `ra` and `rb`. -/
theorem not_lift (Λ' : Relabelling) (a b : EventId) :
    ¬ esF.LiftBranch Λ' a b ∧ ¬ Λ.InjOn (jS.P.syms ++ jS.D) := by
  refine ⟨fun h => PpoKit.not_diverged_of_pos (by decide) h.diverged, fun h => ?_⟩
  have := h 3 (by decide) 4 (by decide) (by decide)
  cases this

/-! ### The execution -/

def Jx : List Justification := [pj e0, pj e1, pj e2, jW, pj e8]

def x : Execution := ⟨esF.Candidate, Jx, fun w r => (w, r) ∈ rfL⟩

theorem δx : x.δ = .empty := foldr_empty (by
  intro j hj
  simp only [x, Jx, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl <;> rfl)

theorem not_elided (a : EventId) : ¬ x.elided a := not_elided_of_δ_empty _ δx a

theorem gen_Jx (hL : esF.Generated (fun _ => True) jL) :
    ∀ j ∈ Jx, esF.Generated (fun _ => True) j := by
  intro j hj
  simp only [Jx, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exact .pre (w := e0) (by simp [esF]) rfl ⟨f₀, holds₀ (by simp [esF])⟩
  · exact .pre (w := e1) (by simp [esF]) rfl ⟨f₀, holds₀ (by simp [esF])⟩
  · exact .pre (w := e2) (by simp [esF]) rfl ⟨f₀, holds₀ (by simp [esF])⟩
  · exact gen_jW_of hL
  · exact .pre (w := e8) (by simp [esF]) rfl ⟨f₀, holds₀ (by simp [esF])⟩

theorem cand_iff {a : EventId} : esF.Candidate a ↔ a ∈ [0, 1, 2, 3, 4, 7, 8] := by
  constructor
  · rintro ⟨⟨e, he, rfl⟩, hb, hf⟩
    simp only [esF, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try decide
    · exact absurd ⟨e5, ev_e e5 (by simp [esF]), rfl⟩ hb
    · exact absurd ⟨e6, ev_e e6 (by simp [esF]), rfl⟩ hb
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cand_of_mem nodupF (e := e0) (by simp [esF]) rfl rfl
    · exact cand_of_mem nodupF (e := e1) (by simp [esF]) rfl rfl
    · exact cand_of_mem nodupF (e := e2) (by simp [esF]) rfl rfl
    · exact cand_of_mem nodupF (e := e3) (by simp [esF]) rfl rfl
    · exact cand_of_mem nodupF (e := e4) (by simp [esF]) rfl rfl
    · exact cand_of_mem nodupF (e := e7) (by simp [esF]) rfl rfl
    · exact cand_of_mem nodupF (e := e8) (by simp [esF]) rfl rfl

theorem inE_of_cls {p : Event → Bool} {a : EventId} (h : esF.cls p a) :
    ∃ e ∈ esF.events, e.id = a ∧ p e = true := by
  obtain ⟨e, he, hp⟩ := h
  exact ⟨e, (ev_inv he).1, (ev_inv he).2, hp⟩

theorem rf_wr_x :
    ∀ w r, x.rf w r → esF.cls Event.isWrite w ∧ esF.cls Event.isRead r ∧ x.X w ∧ x.X r := by
  intro w r h
  have key : ∀ p ∈ rfL, clsB esF Event.isWrite p.1 = true ∧ clsB esF Event.isRead p.2 = true ∧
      p.1 ∈ [0, 1, 2, 3, 4, 7, 8] ∧ p.2 ∈ [0, 1, 2, 3, 4, 7, 8] := by decide
  obtain ⟨h₁, h₂, h₃, h₄⟩ := key _ h
  exact ⟨cls_clsB.2 h₁, cls_clsB.2 h₂, cand_iff.2 h₃, cand_iff.2 h₄⟩

theorem isExecution_x (hL : esF.Generated (fun _ => True) jL) :
    x.IsExecution esF (fun _ => True) where
  maximal := ⟨fun _ h => h, fun a b _ _ ⟨ea, eb, ha, hb, hn⟩ =>
      hn ⟨f₀, holds₀ (ev_inv ha).1, holds₀ (ev_inv hb).1⟩,
    fun _ hc hn => absurd hc hn⟩
  generated := gen_Jx hL
  inX j hj := by
    simp only [x, Jx, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> exact cand_iff.2 (by decide)
  consistent := ⟨f₀, fun j hj => by
      simp only [x, Jx, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> unfold Expr.holds <;> decide,
    fun a e _ he => holds₀ (ev_inv he).1⟩
  fwdWF := by rw [δx]; exact FwdCtx.WF.empty
  rf_wr := rf_wr_x
  rf_func w w' r h h' := by
    have key : ∀ p ∈ rfL, ∀ q ∈ rfL, p.2 = q.2 → p.1 = q.1 := by decide
    exact key _ h _ h' rfl
  justified w hw he _ := by
    obtain ⟨e, hm, rfl, hef⟩ := inE_of_cls he
    have hex : ∀ e ∈ esF.events, e.isEffect = true → ∃ j ∈ Jx, j.w.id = e.id := by decide
    obtain ⟨j, hj, hjw⟩ := hex e hm hef
    refine ⟨j, hj, hjw, fun j' hj' h => ?_⟩
    have hnd : (Jx.map (·.w.id)).Nodup := by decide
    exact inj_of_nodup hnd hj' hj (h.trans hjw.symm)
  notElided j _ := not_elided j.w.id

theorem alloc_id : ∀ e ∈ esF.events, e.isAlloc = true → e.id = 2 := by decide

theorem phi_x : x.phi esF := by
  refine ⟨fun e _ hel => not_elided e hel, fun r => ⟨?_, ?_⟩, g₁, fun j hj => ⟨?_, ?_⟩, ?_,
    ?_, ?_⟩
  · rintro ⟨w, hw⟩
    exact ⟨(rf_wr_x w r hw).2.2.2, (rf_wr_x w r hw).2.1⟩
  · rintro ⟨-, hr⟩
    obtain ⟨e, hm, rfl, hp⟩ := inE_of_cls hr
    have key : ∀ e ∈ esF.events, e.isRead = true → ∃ p ∈ rfL, p.2 = e.id := by decide
    obtain ⟨p, hp', h2⟩ := key e hm hp
    exact ⟨p.1, by rw [← h2]; exact hp'⟩
  · simp only [x, Jx, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> unfold Expr.holds <;> decide
  · intro p hp
    simp only [x, Jx, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> cases hp
  · intro w r ew er h hw hr
    have key : ∀ p ∈ rfL, ∀ ew ∈ esF.events, ∀ er ∈ esF.events, ew.id = p.1 → er.id = p.2 →
        ew.loc.map (·.eval g₁) = er.loc.map (·.eval g₁) ∧
        ew.val.map (·.eval g₁) = er.val.map (·.eval g₁) := by decide
    have := key (w, r) h ew (ev_inv hw).1 er (ev_inv hr).1 (ev_inv hw).2 (ev_inv hr).2
    refine ⟨fun lw lr h₁ h₂ => ?_, fun vw vr h₁ h₂ => ?_⟩
    · have := this.1; rw [h₁, h₂] at this; exact Option.some.inj this
    · have := this.2; rw [h₁, h₂] at this; exact Option.some.inj this
  · intro a e α sz _ he hk
    have hid := alloc_id e (ev_inv he).1 (by simp [Event.isAlloc, hk])
    rw [(ev_inv he).2] at hid; subst hid
    rw [ev2] at he; cases he
    cases hk
    intro y o h; simp [g₁, cell] at h
  · intro a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂ _ _ hne he₁ he₂ hk₁ hk₂
    have h₁ := alloc_id e₁ (ev_inv he₁).1 (by simp [Event.isAlloc, hk₁])
    have h₂ := alloc_id e₂ (ev_inv he₂).1 (by simp [Event.isAlloc, hk₂])
    rw [(ev_inv he₁).2] at h₁; rw [(ev_inv he₂).2] at h₂
    exact absurd (h₁.trans h₂.symm) hne

theorem ra_one {f : Valuation} (hφ : x.phiRf esF f) : f 3 = .num 1 ∧ ¬ c3.holds f := by
  have := (hφ.1 8 3 e8 e3 (by show (8, 3) ∈ rfL; decide) (ev_e e8 (by simp [esF]))
    (ev_e e3 (by simp [esF]))).2 _ _ rfl rfl
  simp only [Expr.num, Expr.eval] at this
  have h3 : f 3 = .num 1 := (Option.some.inj this).symm
  refine ⟨h3, fun h => ?_⟩
  simp [Expr.holds, c3, Expr.eval, h3] at h

theorem rmwTight : Execution.RMWTight esF x :=
  ⟨fun _ h => by simp [esF] at h, fun _ h => by simp [esF] at h⟩

theorem dep_po {a b : EventId} (h : x.dep esF a b) : esF.poR a b := by
  rcases h with hp | ⟨-, -, j, hj, rfl, hs⟩
  · exact Execution.ppo_po po_trans
      (fun _ _ s => Execution.ppoStep_po (noEdge_of_noElided not_elided) rmwTight s) hp
  · have key : ∀ j ∈ Jx, ∀ a ∈ j.P.syms ++ j.D, (a, j.w.id) ∈ poL := by decide
    exact key j hj a (List.mem_append.2 hs)

def ntaL : List (EventId × EventId) := poL ++ [(8, 3), (8, 4), (8, 5), (8, 6), (8, 7)]

theorem noThinAir_x : x.NoThinAir esF := by
  intro a h
  have hc : Closed ntaL := by decide
  have hm : (a, a) ∈ ntaL := by
    refine transGen_mem (fun c d s => ?_) hc h
    rcases s with s | s
    · exact List.mem_append.2 (.inl (dep_po s))
    · have key : ∀ p ∈ rfL, p ∈ ntaL := by decide
      exact key _ s
  have key : ∀ p ∈ ntaL, p.1 ≠ p.2 := by decide
  exact key _ hm rfl

def coL : List (EventId × EventId) := [(0, 8)]

theorem write_glob : ∀ e ∈ esF.events, e.isWrite = true →
    e.loc = some (Expr.glob "A") ∨ e.loc = some (Expr.glob "B") := by decide

theorem sameLoc_locOf {a b : EventId} (hwa : esF.cls Event.isWrite a)
    (hwb : esF.cls Event.isWrite b) (h : x.sameLoc esF a b) : locOf esF a = locOf esF b := by
  obtain ⟨ea, eb, la, lb, ha, hb, hla, hlb, hs⟩ := h
  have hga : ∃ y, la = Expr.glob y := by
    obtain ⟨e, he, hp⟩ := hwa; rw [ha] at he; cases he
    rcases write_glob ea (ev_inv ha).1 hp with h | h <;> rw [hla] at h <;> cases h <;>
      exact ⟨_, rfl⟩
  have hgb : ∃ y, lb = Expr.glob y := by
    obtain ⟨e, he, hp⟩ := hwb; rw [hb] at he; cases he
    rcases write_glob eb (ev_inv hb).1 hp with h | h <;> rw [hlb] at h <;> cases h <;>
      exact ⟨_, rfl⟩
  obtain ⟨y₁, rfl⟩ := hga
  obtain ⟨y₂, rfl⟩ := hgb
  obtain ⟨-, -, f, hP, hφ⟩ := phi_x
  have := hs f hP hφ
  simp only [Expr.glob, Expr.eval, Option.some.injEq, Val.loc.injEq, Loc.mk.injEq,
    LocBase.global.injEq, and_true] at this
  subst this
  simp [locOf, ha, hb, hla, hlb]

theorem coOrder : x.CoherenceOrder esF (PpoNecessity.relL coL) where
  writes a b h := by
    have key : ∀ p ∈ coL, clsB esF Event.isWrite p.1 = true ∧
        clsB esF Event.isWrite p.2 = true ∧
        p.1 ∈ [0, 1, 2, 3, 4, 7, 8] ∧ p.2 ∈ [0, 1, 2, 3, 4, 7, 8] := by decide
    obtain ⟨h₁, h₂, h₃, h₄⟩ := key _ h
    exact ⟨cand_iff.2 h₃, cand_iff.2 h₄, cls_clsB.2 h₁, cls_clsB.2 h₂⟩
  irrefl a h := by
    have key : ∀ p ∈ coL, p.1 ≠ p.2 := by decide
    exact key _ h rfl
  trans a b c h₁ h₂ := by
    have key : Closed coL := by decide
    exact key _ h₁ _ h₂ rfl
  total a b ha hb hwa hwb hne hsl := by
    have key : ∀ a ∈ [0, 1, 2, 3, 4, 7, 8], ∀ b ∈ [0, 1, 2, 3, 4, 7, 8],
        clsB esF Event.isWrite a = true → clsB esF Event.isWrite b = true → a ≠ b →
        locOf esF a = locOf esF b → (a, b) ∈ coL ∨ (b, a) ∈ coL := by decide
    exact key a (cand_iff.1 ha) b (cand_iff.1 hb) (cls_clsB.1 hwa) (cls_clsB.1 hwb) hne
      (sameLoc_locOf hwa hwb hsl)

theorem no_sw {a b : EventId} : ¬ x.sw esF a b := by
  intro h
  obtain ⟨ha, -⟩ := sw_cls h
  have hid : a ∈ esF.ids := by
    simp only [Bool.or_eq_true] at ha; rcases ha with h | h <;> exact clsB_id h
  have key : ∀ a ∈ esF.ids, (clsB esF Event.isRelW a || clsB esF Event.isRelF a) = false := by
    decide
  rw [key a hid] at ha; cases ha

def ecoL : List (EventId × EventId) := [(8, 3), (1, 4), (0, 8), (0, 3)]

theorem coherence_x : x.Coherence esF (PpoNecessity.relL coL) := by
  refine coherenceVOver_of (D := x.poX esF) (H := poL) (E := ecoL)
    (fun a b h => transGen_mem (fun _ _ s => by
      rcases s with s | s
      · exact s.2.2
      · exact (no_sw s).elim) poClosed h) (fun a b h => ?_) (by decide)
  have hE : ∀ p ∈ rfL ++ coL ++ PpoNecessity.frL rfL coL, p ∈ ecoL := by decide
  refine eco_mem (fun c d h => hE _ ?_) (fun c d h => hE _ ?_) (fun c d h => hE _ ?_)
    (by decide) h
  · exact List.mem_append.2 (.inl (List.mem_append.2 (.inl h)))
  · exact List.mem_append.2 (.inl (List.mem_append.2 (.inr h)))
  · obtain ⟨w, hrf, hco⟩ := h
    exact List.mem_append.2 (.inr (List.mem_flatMap.2 ⟨(w, c), hrf, List.mem_map.2 ⟨(w, d),
      List.mem_filter.2 ⟨hco, by simp⟩, rfl⟩⟩))

theorem atomicity_x (co : Rel) : x.Atomicity esF co := by
  rintro r w ⟨-, -, ent, hm, -⟩
  simp [esF] at hm

theorem coherent_x : x.Coherent esF :=
  ⟨PpoNecessity.relL coL, coOrder, coherence_x, atomicity_x _,
   x.psc_of_noSC esF (x.scFree_of_es esF (esF.scFree_of_all (by decide))) _⟩

theorem consistent_x (hL : esF.Generated (fun _ => True) jL) : x.Consistent esF (fun _ => True) :=
  ⟨isExecution_x hL, phi_x, noThinAir_x, coherent_x⟩

theorem consistentT_x (hL : esF.Generated (fun _ => True) jL) :
    x.ConsistentT esF (fun _ => True) :=
  ⟨isExecution_x hL, phi_x, noThinAir_x, (coherentT_iff_coherent not_elided).2 coherent_x⟩

/-- **The guard is lost with `free(r)` under the unrestricted rule**: were the lift generated,
    a consistent execution would free `r`, guarded by `ra = 0`, while every model of `φ_rf` has
    `ra = 1`, and `(ra, free(r)) ∉ DP`. -/
theorem guard_lost (hL : esF.Generated (fun _ => True) jL) :
    x.Consistent esF (fun _ => True) ∧ x.X 7 ∧
    (∀ f, x.phiRf esF f → f 3 = .num 1 ∧ ¬ c3.holds f) ∧
    (∃ f, x.P esF f ∧ x.phiRf esF f) ∧ ¬ x.DP 3 7 := by
  refine ⟨consistent_x hL, cand_iff.2 (by decide), fun f hφ => ra_one hφ, phi_x.2.2, ?_⟩
  rintro ⟨-, -, j, hj, hw, hs⟩
  have key : ∀ j ∈ Jx, j.w.id = 7 → 3 ∉ j.P.syms ++ j.D := by decide
  exact key j hj hw (List.mem_append.2 hs)

end Free

/-! ## A permutation: three reads

With a third read `rc := C` the relabelling can be a permutation, `Λ = (ra rc)`: strengthen the
second premise by `rc = 0` (origin `rc`) and lift the pre-justification into it. `⟦P⟧_Λ` is
`rc = 0 ∧ rb = 0`, both conjuncts of the strengthened predicate, so the disjunction is again
`⋀∅ ∨ ra = 0`, and Weakening leaves `rc = 0 ∧ rb = 0`. (The execution is built as for the
first program; not repeated here.) -/

namespace Swap

def prog : Stmt :=
  .seq (PpoStability.st .rlx "A" 0) (.seq (PpoStability.st .rlx "B" 0)
    (.seq (PpoStability.st .rlx "C" 0) (.seq (PpoStability.st .rlx "y" 0)
      (.par (.seq (PpoStability.ld .rlx "ra" "A") (.seq (PpoStability.ld .rlx "rb" "B")
          (.seq (PpoStability.ld .rlx "rc" "C")
            (.ite (.eq (.reg "ra") (.num 0))
              (.ite (.eq (.reg "rb") (.num 0)) (PpoStability.st .rlx "y" 1) .skip) .skip))))
        (PpoStability.st .rlx "A" 1)))))

/-- `ra = 0`, `rb = 0`, `rc = 0` -/
def ca : Expr := .eq (.sym 4) (.val (.num 0))
def cb : Expr := .eq (.sym 5) (.val (.num 0))
def cc : Expr := .eq (.sym 6) (.val (.num 0))

def esS : EventStructure :=
  ⟨[PpoStability.W 0 0 [0] [] [] .rlx "A" 0,
    PpoStability.W 1 0 [1, 0] [] [] .rlx "B" 0,
    PpoStability.W 2 0 [1, 1, 0] [] [] .rlx "C" 0,
    PpoStability.W 3 0 [1, 1, 1, 0] [] [] .rlx "y" 0,
    PpoStability.R 4 0 [1, 1, 1, 1, 0, 0] [] [] .rlx "A",
    PpoStability.R 5 0 [1, 1, 1, 1, 0, 1, 0] [] [] .rlx "B",
    PpoStability.R 6 0 [1, 1, 1, 1, 0, 1, 1, 0] [] [] .rlx "C",
    ⟨7, .branch ca, ⟨0, [1, 1, 1, 1, 0, 1, 1, 1], []⟩, []⟩,
    ⟨8, .branch cb, ⟨0, [1, 1, 1, 1, 0, 1, 1, 1, 0], []⟩, [⟨7, ca, true⟩]⟩,
    PpoStability.W 9 0 [1, 1, 1, 1, 0, 1, 1, 1, 0, 0] [] [⟨7, ca, true⟩, ⟨8, cb, true⟩]
      .rlx "y" 1,
    PpoStability.W 10 1 [1, 1, 1, 1, 1] [] [] .rlx "A" 1],
   [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, 2),
    (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, 3), (2, 4), (2, 5),
    (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9),
    (3, 10), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 6), (5, 7), (5, 8), (5, 9), (6, 7),
    (6, 8), (6, 9), (7, 8), (7, 9), (8, 9)], []⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esS := rfl

def e3 : Event := PpoStability.W 3 0 [1, 1, 1, 0] [] [] .rlx "y" 0
def e9 : Event :=
  PpoStability.W 9 0 [1, 1, 1, 1, 0, 1, 1, 1, 0, 0] [] [⟨7, ca, true⟩, ⟨8, cb, true⟩] .rlx "y" 1

theorem nodupS : (esS.events.map (·.id)).Nodup := by decide
theorem gS : GlobLocs esS := globLocs_of (by decide)
theorem ev3 : esS.ev 3 = some e3 := PpoKit.ev_of_mem nodupS (e := e3) (by simp [esS, e3])
theorem ev9 : esS.ev 9 = some e9 := PpoKit.ev_of_mem nodupS (e := e9) (by simp [esS, e9])

/-- `Λ = (ra rc)`, a permutation. -/
def Λs : Relabelling := fun α => if α = 4 then some 6 else if α = 6 then some 4 else none

theorem Λs_inj : Λs.Injective := by
  intro a b c ha hb
  simp only [Λs] at ha hb
  split at ha <;> split at hb <;> simp_all <;> split at ha <;> split at hb <;> simp_all

/-- `(ra = 0 ∧ rb = 0, ∅) ⊢ y := 1` -/
def j₁ : Justification := pj e9
/-- … strengthened by `rc = 0`. -/
def j₂ : Justification := { j₁ with P := esS.strPred j₁.P cc [6] }
def jL : Justification := { j₂ with P := Expr.liftPred (j₁.P.rename Λs) j₂.P }
/-- `⊤ ∧ rc = 0 ∧ rb = 0` -/
def PW : Expr := Expr.conj [Expr.tt, cc, cb]
def Pv : Expr := .or (Expr.conj []) (Expr.conj [ca])
def jW : Justification := { j₂ with P := PW }

theorem jL_P : jL.P = .and PW Pv := by decide

def f₀ : Valuation := fun _ => .num 0

theorem holds₀ {e : Event} (he : e ∈ esS.events) : e.valres.holds f₀ := by
  simp only [esS, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold Expr.holds <;> decide

theorem pre₁ : esS.Generated (fun _ => True) j₁ :=
  .pre (w := e9) (by simp [esS, e9]) rfl ⟨f₀, holds₀ (by simp [esS, e9])⟩

theorem gen_j₂ : esS.Generated (fun _ => True) j₂ := by
  refine .str cc [6] pre₁ ?_ ?_ ?_ ⟨f₀, by unfold Expr.holds; decide, trivial⟩
  · have hs : (esS.strPred j₁.P cc [6]).syms = [4, 5, 6] := by decide
    have hp : j₁.P.syms = [4, 5] := by decide
    intro e; rw [hs, hp]; simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro rfl; decide
    · rintro ⟨h₁, h₂⟩
      rcases h₁ with h | h | h
      · exact absurd (.inl h) h₂
      · exact absurd (.inr h) h₂
      · exact h
  · intro e _; exact .canon (noEdge_empty · e)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he; subst he
    refine ⟨by show (6, 9) ∈ esS.po; decide, fun h => ?_⟩
    have hm := ppo_mem rfl gS noEdge_empty h
    revert hm; decide

/-- `y := 0` is an immediate `≼`-predecessor of `y := 1` under every satisfiable `P`. -/
theorem pred_3 {P : Expr} (hP : Sat P.holds) : esS.pred .empty 9 P.holds 3 := by
  obtain ⟨f, hf⟩ := hP
  have hal : esS.mayAlias P.holds 3 9 :=
    ⟨e3, e9, _, _, ev3, ev9, rfl, rfl, f, hf, by simp [Expr.holds, Expr.eval, Expr.glob]⟩
  refine ⟨⟨(FwdCtx.remapRel_of_noEdge noEdge_empty).2 (.inr ⟨by show (3, 9) ∈ esS.po; decide,
    hal⟩), by decide⟩, ?_⟩
  rintro ⟨e'', h₁, h₂⟩
  have hm := ppo_mem rfl gS noEdge_empty h₁
  have key : ∀ p ∈ syncL esS ++ aliasL esS, p.1 = 3 → p.2 = 9 := by decide
  have := key _ hm rfl; subst this
  exact ppo_irrefl _ _ _ _ h₂

theorem ppo_into_9 {P : Pred} {a : EventId} (h : esS.ppo P .empty a 9) : a = 3 := by
  have hm := ppo_mem rfl gS noEdge_empty h
  have key : ∀ p ∈ syncL esS ++ aliasL esS, p.2 = 9 → p.1 = 3 := by decide
  exact key _ hm rfl

theorem no_ppo_into_3 {P : Pred} {a : EventId} : ¬ esS.ppo P .empty a 3 := by
  intro h
  have hm := ppo_mem rfl gS noEdge_empty h
  have key : ∀ p ∈ syncL esS ++ aliasL esS, p.2 ≠ 3 := by decide
  exact key _ hm rfl

theorem cre_3 {P₁ P₂ : Expr} : esS.ClosedRelabEq .empty Λs P₁ e3 P₂ e3 := by
  refine .mk ?_ ⟨fun _ _ h => no_ppo_into_3 h.1, fun _ _ h => no_ppo_into_3 h.1⟩
    (fun _ _ _ _ h => (no_ppo_into_3 h.1).elim)
  simp only [relabEq, e3, PpoStability.W, Event.isRead, Event.isWrite, Event.isAlloc, Event.loc,
    Event.val, Bool.and_self, Bool.or_true]
  exact ⟨⟨_, _, rfl, rfl, relabEqExpr_val _⟩, ⟨_, _, rfl, rfl, relabEqExpr_val _⟩⟩

theorem cre_9 : esS.ClosedRelabEq .empty Λs j₁.P e9 j₂.P e9 := by
  have s₁ : Sat j₁.P.holds := ⟨f₀, by unfold Expr.holds; decide⟩
  have s₂ : Sat j₂.P.holds := ⟨f₀, by unfold Expr.holds; decide⟩
  refine .mk ?_ ⟨fun h => absurd (pred_3 s₁) (h 3), fun h => absurd (pred_3 s₂) (h 3)⟩
    (fun x₁ x₂ ev₁ ev₂ h₁ h₂ hv₁ hv₂ => ?_)
  · simp only [relabEq, e9, PpoStability.W, Event.isRead, Event.isWrite, Event.isAlloc,
      Event.loc, Event.val, Bool.and_self, Bool.or_true]
    exact ⟨⟨_, _, rfl, rfl, relabEqExpr_val _⟩, ⟨_, _, rfl, rfl, relabEqExpr_val _⟩⟩
  · have := ppo_into_9 h₁.1; subst this
    have := ppo_into_9 h₂.1; subst this
    rw [ev3] at hv₁ hv₂
    cases hv₁; cases hv₂
    exact cre_3

/-- Every condition of the unrestricted Lifting holds. -/
theorem lift_conds : esS.LiftConds (fun _ => True) Λs j₁ j₂ := by
  refine ⟨rfl, Λs_inj, cre_9, ?_, ?_, ?_, ?_, ?_, ?_, ⟨f₀, ?_, trivial⟩⟩
  · intro e; show e ∈ ([] : List EventId) ↔ ∃ α ∈ ([] : List EventId), Λs.app α = e; simp
  · intro α h; nomatch h
  · intro h; have := cls_clsB.1 h; revert this; decide
  · intro h; have := cls_clsB.1 h; revert this; decide
  · intro α h; nomatch h
  · intro α h
    have key : ∀ α ∈ (j₁.P.rename Λs).syms, (α, 9) ∈ esS.po := by decide
    exact key α h
  · unfold Expr.holds; decide

theorem Pv_valid : Entails (fun _ => True) Pv.holds := by
  intro f _
  simp [Pv, Expr.holds, Expr.conj, Expr.eval, Expr.tt, ca]

/-- **Under a permutation the guard's symbol would be lost too**, were the lift generated. -/
theorem gen_jW_of (hL : esS.Generated (fun _ => True) jL) : esS.Generated (fun _ => True) jW :=
  .weak (j₁ := jL) (P' := PW) (Pw := Pv) hL (by rw [jL_P]; exact Expr.ConjEq.refl _)
    Pv_valid ⟨f₀, by unfold Expr.holds; decide, trivial⟩

theorem jW_syms : 4 ∉ jW.P.syms ∧ jW.P.syms = [6, 5] ∧ jW.D = [] := by decide

/-- A permutation passes the one-to-one renaming: `⟦·⟧_{(ra rc)}` is one-to-one on the symbols
    `ra`, `rb` of `P₁`. The renaming condition alone does not exclude the lift. -/
theorem injOn : Λs.InjOn (j₁.P.syms ++ j₁.D) := by unfold Relabelling.InjOn; decide

/-- **The branching restriction refuses it**: no two events of `esS` diverge. -/
theorem not_liftBranch (Λ' : Relabelling) (a b : EventId) : ¬ esS.LiftBranch Λ' a b :=
  fun h => PpoKit.not_diverged_of_pos (by decide) h.diverged

end Swap

end GuardLoss
