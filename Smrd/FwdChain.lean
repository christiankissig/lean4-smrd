import Smrd.FwdEntails
import Smrd.FwdAcrossAlias

/-!
# `FwdEntailsSrc` does not give `DP ∪ ≼ ⊆ ⊑`: a chain of forwardings

`FwdEntailsSrc` asks the entailment of every justification whose window
contains an end of the edge. A chain of two forwardings defeats it: the
reversing edge's ends are in the window, but the location equivalence of the
other edge, whose ends are not, is what lets the window's justification alias
the two events. One thread:

```
ptr := &u; ptr2 := &x; ptr3 := &x; x := 0; u := 0;
p := ptr; p2 := ptr2; p3 := ptr3;
r0 := *p2; r1 := *p; z := 1; r2 := x; r3 := *p3;
q := 1; v := r2
```

* `jA`, for `q := 1`: strengthened by `p3 = &x` (`jA1`), `r3 := *p3` forwarded
  from `r2 := x` (`F ∋ (r2, r3)`), then strengthened by `p2 = &x ∧ p ≠ &x`.
* `jB`, for `v := r2`: strengthened by `p2 = &x ∧ p ≠ &x` (`jB1`), `r2 := x`
  forwarded from `r0 := *p2` (`F ∋ (r0, r2)`), then strengthened by `p3 = &x`.
* `jZ`, for `z := 1`: strengthened by `p2 = &x ∧ p ≠ &x`.

The chain is `r3 ↦ r2 ↦ r0`. The windows containing an end of `(r2, r3)`
are `jA`'s and `jB`'s, which entail `p3 = &x`; those containing an end of
`(r0, r2)` are `jZ`'s, `jA`'s and `jB`'s, which entail `p2 = &x ∧ p ≠ &x`:
`FwdEntailsSrc` holds (`fwdEntailsSrc_P`), and so `FwdEntails`. But `jZ` does
not know `p3 = &x`: under `P_jZ ∧ ψ_δ`, `r1 := *p` and `r3 := *p3` may alias
(`p = p3 = &u`), both remapped into `jZ`'s window, `r3` onto `r0`: `≼` has
`(r1, r0)` against `⊑` (`ppo_98`). The execution is consistent.

`FwdEntailsImg` rules it out: `remap_δ(r3) = r0` is in `jZ`'s window, so `jZ`
must entail `p3 = &x` (`not_fwdEntailsImg`).
-/

set_option maxRecDepth 100000

namespace FwdChain

open EventStructure PpoKit Execution

def prog : Stmt :=
  .seq (.addrOf "a" "u") (.seq (.store .rlx "ptr" (.reg "a") false)
  (.seq (.addrOf "b" "x") (.seq (.store .rlx "ptr2" (.reg "b") false)
  (.seq (.addrOf "c" "x") (.seq (.store .rlx "ptr3" (.reg "c") false)
  (.seq (.store .rlx "x" (.num 0) false) (.seq (.store .rlx "u" (.num 0) false)
  (.seq (.load .rlx "p" "ptr" false) (.seq (.load .rlx "p2" "ptr2" false)
  (.seq (.load .rlx "p3" "ptr3" false)
  (.seq (.loadPtr .rlx "r0" (.reg "p2") false) (.seq (.loadPtr .rlx "r1" (.reg "p") false)
  (.seq (.store .rlx "z" (.num 1) false) (.seq (.load .rlx "r2" "x" false)
  (.seq (.loadPtr .rlx "r3" (.reg "p3") false)
  (.seq (.store .rlx "q" (.num 1) false)
    (.store .rlx "v" (.reg "r2") false)))))))))))))))))

def pcN (n : Nat) : List Nat := List.replicate n 1 ++ [0]

def W (i : Nat) (pc : List Nat) (x : String) (v : Expr) : Event :=
  ⟨i, .write .rlx (Expr.glob x) v false, ⟨0, pc, []⟩, []⟩
def R (i : Nat) (pc : List Nat) (l : Expr) : Event :=
  ⟨i, .read .rlx l i false, ⟨0, pc, []⟩, []⟩

def e0 : Event := W 0 (pcN 1) "ptr" (Expr.glob "u")
def e1 : Event := W 1 (pcN 3) "ptr2" (Expr.glob "x")
def e2 : Event := W 2 (pcN 5) "ptr3" (Expr.glob "x")
def e3 : Event := W 3 (pcN 6) "x" (Expr.num 0)
def e4 : Event := W 4 (pcN 7) "u" (Expr.num 0)
def e5 : Event := R 5 (pcN 8) (Expr.glob "ptr")
def e6 : Event := R 6 (pcN 9) (Expr.glob "ptr2")
def e7 : Event := R 7 (pcN 10) (Expr.glob "ptr3")
def e8 : Event := R 8 (pcN 11) (.sym 6)
def e9 : Event := R 9 (pcN 12) (.sym 5)
def e10 : Event := W 10 (pcN 13) "z" (Expr.num 1)
def e11 : Event := R 11 (pcN 14) (Expr.glob "x")
def e12 : Event := R 12 (pcN 15) (.sym 7)
def e13 : Event := W 13 (pcN 16) "q" (Expr.num 1)
def e14 : Event := W 14 (List.replicate 17 1) "v" (.sym 11)

/-- `⊑`: the total order on the fifteen events. -/
def poL : List (EventId × EventId) :=
  (List.range 15).flatMap fun i => ((List.range 15).filter (i < ·)).map (i, ·)

def esP : EventStructure :=
  ⟨[e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14], poL, []⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esP := rfl

theorem mem_poL {a b : EventId} : (a, b) ∈ poL ↔ a < b ∧ b < 15 := by
  simp only [poL, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨i, -, j, ⟨hj, hij⟩, h₁, h₂⟩; subst h₁ h₂; exact ⟨hij, hj⟩
  · rintro ⟨h₁, h₂⟩; exact ⟨a, Nat.lt_trans h₁ h₂, b, ⟨h₂, h₁⟩, rfl, rfl⟩

theorem closed_poL : Closed poL := by
  rintro ⟨a, b⟩ hp ⟨c, d⟩ hq h
  simp only at h ⊢
  rw [mem_poL] at hp hq ⊢
  subst h
  exact ⟨Nat.lt_trans hp.1 hq.1, hq.2⟩

theorem forestL_poL : ForestL poL := by
  rintro ⟨a, b⟩ hp ⟨c, d⟩ hq h
  simp only at h ⊢
  rw [mem_poL] at hp hq
  subst h
  rcases Nat.lt_trichotomy a c with h | rfl | h
  · exact .inr (.inl (mem_poL.2 ⟨h, Nat.lt_trans hq.1 hq.2⟩))
  · exact .inl rfl
  · exact .inr (.inr (mem_poL.2 ⟨h, Nat.lt_trans hp.1 hp.2⟩))

theorem SP : Simple esP := ⟨by decide, by decide, rfl⟩
theorem po_of {a b : EventId} (h : (a, b) ∈ esP.po) : esP.poR a b := h

/-! ## Predicates -/

def locX : Val := .loc ⟨.global "x", 0⟩
def locU : Val := .loc ⟨.global "u", 0⟩

/-- `p2 = &x ∧ p ≠ &x` -/
def Q2 : Expr := .and (.eq (.sym 6) (Expr.glob "x")) (.not (.eq (.sym 5) (Expr.glob "x")))
/-- `p3 = &x` -/
def Q3 : Expr := .eq (.sym 7) (Expr.glob "x")

theorem holds_Q2 (f : Valuation) : Q2.holds f ↔ f 6 = locX ∧ f 5 ≠ locX := by
  simp only [Q2, Expr.holds, Expr.eval, Expr.glob, locX]
  by_cases h6 : f 6 = .loc ⟨.global "x", 0⟩ <;> by_cases h5 : f 5 = .loc ⟨.global "x", 0⟩ <;>
    simp [h5, h6]

theorem holds_Q3 (f : Valuation) : Q3.holds f ↔ f 7 = locX := by
  simp only [Q3, Expr.holds, Expr.eval, Expr.glob, locX]
  by_cases h7 : f 7 = .loc ⟨.global "x", 0⟩ <;> simp [h7]

theorem str2 (P : Expr) (f : Valuation) :
    (esP.strPred P Q2 [5, 6]).holds f ↔ P.holds f ∧ f 6 = locX ∧ f 5 ≠ locX := by
  simp only [strPred, Expr.holds_and, holds_Q2]
  have hc : (Expr.conj ([5, 6].map esP.valresOf)).holds f := rfl
  exact ⟨fun h => ⟨h.1, h.2.1.1, h.2.1.2⟩, fun h => ⟨h.1, ⟨h.2.1, h.2.2⟩, hc⟩⟩

theorem str3 (P : Expr) (f : Valuation) :
    (esP.strPred P Q3 [7]).holds f ↔ P.holds f ∧ f 7 = locX := by
  simp only [strPred, Expr.holds_and, holds_Q3]
  have hc : (Expr.conj ([7].map esP.valresOf)).holds f := rfl
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hc⟩⟩

/-! ## Justifications -/

abbrev pj := PpoNecessity.pj

def jZ : Justification := { pj e10 with P := esP.strPred e10.valres Q2 [5, 6] }

def jA1 : Justification := { pj e13 with P := esP.strPred e13.valres Q3 [7] }
/-- `jA1` with `r3 := *p3` forwarded from `r2 := x`. -/
def jA2 : Justification :=
  { P := jA1.P.replace (.sym 12) (.sym 11)
    D := ((Expr.num 1).replace (.sym 12) (.sym 11)).syms ++
      ((Expr.glob "q").replace (.sym 12) (.sym 11)).syms
    δ := { jA1.δ with f := jA1.δ.f ++ [(11, 12)] }
    w := { jA1.w with
      kind := .write .rlx ((Expr.glob "q").replace (.sym 12) (.sym 11))
        ((Expr.num 1).replace (.sym 12) (.sym 11)) false } }
def jA : Justification := { jA2 with P := esP.strPred jA2.P Q2 [5, 6] }

def jB0 : Justification := ⟨e14.valres, [11], .empty, e14⟩
def jB1 : Justification := { jB0 with P := esP.strPred jB0.P Q2 [5, 6] }
/-- `jB1` with `r2 := x` forwarded from `r0 := *p2`. -/
def jB2 : Justification :=
  { P := jB1.P.replace (.sym 11) (.sym 8)
    D := ((Expr.sym 11).replace (.sym 11) (.sym 8)).syms ++
      ((Expr.glob "v").replace (.sym 11) (.sym 8)).syms
    δ := { jB1.δ with f := jB1.δ.f ++ [(8, 11)] }
    w := { jB1.w with
      kind := .write .rlx ((Expr.glob "v").replace (.sym 11) (.sym 8))
        ((Expr.sym 11).replace (.sym 11) (.sym 8)) false } }
def jB : Justification := { jB2 with P := esP.strPred jB2.P Q3 [7] }

theorem replace_self (q : Expr) (β : Sym) : (Expr.sym β).replace (.sym β) q = q := by
  unfold Expr.replace; simp

theorem jA2_eq : jA2 = ⟨jA1.P, [], ⟨[(11, 12)], []⟩, e13⟩ := by
  have h₁ : jA1.P.replace (.sym 12) (.sym 11) = jA1.P := Expr.replace_sym_of_not_mem (by decide)
  have h₂ : (Expr.glob "q").replace (.sym 12) (.sym 11) = Expr.glob "q" :=
    Expr.replace_sym_of_not_mem (by decide)
  have h₃ : (Expr.num 1).replace (.sym 12) (.sym 11) = Expr.num 1 :=
    Expr.replace_sym_of_not_mem (by decide)
  simp only [jA2, h₁, h₂, h₃]
  rfl

theorem jB2_eq : jB2 = ⟨jB1.P, [8], ⟨[(8, 11)], []⟩,
    { e14 with kind := .write .rlx (Expr.glob "v") (.sym 8) false }⟩ := by
  have h₁ : jB1.P.replace (.sym 11) (.sym 8) = jB1.P := Expr.replace_sym_of_not_mem (by decide)
  have h₂ : (Expr.glob "v").replace (.sym 11) (.sym 8) = Expr.glob "v" :=
    Expr.replace_sym_of_not_mem (by decide)
  simp only [jB2, h₁, h₂, replace_self]
  rfl

theorem jA_eq : jA = ⟨esP.strPred jA1.P Q2 [5, 6], [], ⟨[(11, 12)], []⟩, e13⟩ := by
  unfold jA; rw [jA2_eq]

theorem jB_eq : jB = ⟨esP.strPred jB1.P Q3 [7], [8], ⟨[(8, 11)], []⟩,
    { e14 with kind := .write .rlx (Expr.glob "v") (.sym 8) false }⟩ := by
  unfold jB; rw [jB2_eq]

theorem valres_true (e : Event) (he : e ∈ esP.events) (f : Valuation) : e.valres.holds f :=
  SP.holds he f

theorem holds_jZ (f : Valuation) : jZ.P.holds f ↔ f 6 = locX ∧ f 5 ≠ locX := by
  rw [show jZ.P = esP.strPred e10.valres Q2 [5, 6] from rfl, str2]
  simp [valres_true e10 (by simp [esP]) f]

theorem holds_jA1 (f : Valuation) : jA1.P.holds f ↔ f 7 = locX := by
  rw [show jA1.P = esP.strPred e13.valres Q3 [7] from rfl, str3]
  simp [valres_true e13 (by simp [esP]) f]

theorem holds_jB1 (f : Valuation) : jB1.P.holds f ↔ f 6 = locX ∧ f 5 ≠ locX := by
  rw [show jB1.P = esP.strPred e14.valres Q2 [5, 6] from rfl, str2]
  simp [valres_true e14 (by simp [esP]) f]

theorem holds_jA (f : Valuation) : jA.P.holds f ↔ f 7 = locX ∧ f 6 = locX ∧ f 5 ≠ locX := by
  rw [jA_eq]; simp only [str2, holds_jA1]

theorem holds_jB (f : Valuation) : jB.P.holds f ↔ (f 6 = locX ∧ f 5 ≠ locX) ∧ f 7 = locX := by
  rw [jB_eq]; simp only [str3, holds_jB1]

/-- The outcome: `p = &u`, `p2 = p3 = &x`, every other read `0`. -/
def fOut : Valuation := fun α =>
  if α = 5 then locU else if α = 6 ∨ α = 7 then locX else .num 0

theorem base_alias {P : Pred} {a b : EventId} (h : esP.ppoBase P a b) :
    esP.poR a b ∧ esP.mayAlias P a b := by
  rcases h with (hs | ⟨⟨x, -, hx⟩ | ⟨x, hx, -⟩, -⟩) | h
  · have : syncL esP = [] := by decide
    have hm := ppoSync_mem hs
    rw [this] at hm; cases hm
  · exact absurd hx (not_rmwPairs rfl)
  · exact absurd hx (not_rmwPairs rfl)
  · exact h

theorem noEdge_empty : ∀ a b, ¬ FwdCtx.empty.edge a b := by
  intro a b h; rcases h with h | h <;> cases h

theorem ppo_empty {P : Pred} {a b : EventId} (h : esP.ppo P .empty a b) :
    esP.poR a b ∧ esP.mayAlias P a b :=
  base_alias ((FwdCtx.remapRel_of_noEdge noEdge_empty).1 h.1)

/-- An event that is no source of an edge is the image of itself only. -/
theorem remap_fixed {δ : FwdCtx} {a e : EventId} (hs : ∀ c, ¬ δ.edge e c) (h : δ.Remap a e) :
    a = e := by
  induction h with
  | canon _ => rfl
  | step he _ ih => exact absurd (ih hs ▸ he) (hs _)

theorem ppo_fixed {P : Pred} {δ : FwdCtx} {a b : EventId} (ha : ∀ c, ¬ δ.edge a c)
    (hb : ∀ c, ¬ δ.edge b c) (h : esP.ppo P δ a b) : esP.poR a b := by
  obtain ⟨⟨a₀, b₀, hab, ra, rb⟩, -⟩ := h
  rw [remap_fixed ha ra, remap_fixed hb rb] at hab
  exact (base_alias hab).1

theorem wf_single {a b : EventId} (hab : a ≠ b) : FwdCtx.WF ⟨[(a, b)], []⟩ := by
  refine ⟨fun c hc => ?_, fun c d e hc hd => ?_⟩
  · have : ∀ c d, Relation.TransGen (FwdCtx.edge ⟨[(a, b)], []⟩) c d → c = a ∧ d = b := by
      intro c d h
      induction h with
      | single h => rcases h with h | h <;> simp at h; exact h
      | tail _ h ih =>
          rcases h with h | h <;> simp at h
          obtain ⟨-, rfl⟩ := ih; exact absurd h.1.symm hab
    have := this c c hc
    exact hab (this.1.symm.trans this.2)
  · rcases hc with h | h <;> simp at h
    rcases hd with h' | h' <;> simp at h'
    rw [h.1, h'.1]

/-- Under `p2 = &x ∧ p ≠ &x`, `r0 := *p2` aliases neither `r1 := *p` nor
    `z := 1`. -/
theorem not_alias_8 {P : Pred} (hP : ∀ f, P f → f 6 = locX ∧ f 5 ≠ locX) :
    ¬ esP.mayAlias P 8 9 ∧ ¬ esP.mayAlias P 8 10 := by
  constructor
  · rintro ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, hf, heq⟩
    cases h₁; cases h₂; cases hl₁; cases hl₂
    obtain ⟨h6, h5⟩ := hP f hf
    simp only [Expr.holds, Expr.eval] at heq
    have : f 6 = f 5 := by simpa using heq
    exact h5 (this ▸ h6)
  · rintro ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, hf, heq⟩
    cases h₁; cases h₂; cases hl₁; cases hl₂
    obtain ⟨h6, -⟩ := hP f hf
    simp [Expr.holds, Expr.eval, h6, locX, Expr.glob] at heq

theorem not_alias_10_11 {P : Pred} : ¬ esP.mayAlias P 10 11 := by
  rintro ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, hf, heq⟩
  cases h₁; cases h₂; cases hl₁; cases hl₂
  simp [Expr.holds, Expr.eval, Expr.glob] at heq

/-! ## Generation -/

theorem pre_P {w : Event} (hw : w ∈ esP.events) (hk : preJust w = some (pj w)) :
    esP.Generated (fun _ => True) (pj w) :=
  .pre hw hk ⟨fOut, SP.holds hw _⟩

theorem gen_jZ : esP.Generated (fun _ => True) jZ := by
  have hsyms : (esP.strPred (pj e10).P Q2 [5, 6]).syms = [6, 5] := by decide
  refine .str Q2 [5, 6] (pre_P (w := e10) (by simp [esP]) rfl) (fun e => ?_)
    (fun e _ => .canon fun a h => noEdge_empty a e h)
    (fun e he => ⟨?_, fun h => ?_⟩) ⟨fOut, (holds_jZ fOut).2 ⟨rfl, by decide⟩, trivial⟩
  · rw [hsyms]
    have : (pj e10).P.syms = [] := rfl
    rw [this]
    by_cases h5 : e = 5 <;> by_cases h6 : e = 6 <;> simp_all
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl <;> exact po_of (by decide)
  · have := (ppo_empty h).1
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl <;> exact absurd (show (_, _) ∈ poL from this) (by decide)

theorem gen_jA1 : esP.Generated (fun _ => True) jA1 := by
  have hsyms : (esP.strPred (pj e13).P Q3 [7]).syms = [7] := by decide
  refine .str Q3 [7] (pre_P (w := e13) (by simp [esP]) rfl) (fun e => ?_)
    (fun e _ => .canon fun a h => noEdge_empty a e h)
    (fun e he => ⟨?_, fun h => ?_⟩) ⟨fOut, (holds_jA1 fOut).2 rfl, trivial⟩
  · rw [hsyms]
    have : (pj e13).P.syms = [] := rfl
    rw [this]; simp
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    subst he; exact po_of (by decide)
  · have := (ppo_empty h).1
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    subst he; exact absurd (show (_, _) ∈ poL from this) (by decide)

/-- **`r3 := *p3` forwarded from `r2 := x`** under `p3 = &x`: nothing lies
    between. -/
theorem fwdA : esP.fwdRel jA1 11 12 := by
  refine ⟨⟨⟨⟨⟨(FwdCtx.remapRel_of_noEdge noEdge_empty).2 (.inr
      ⟨po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl, fOut, (holds_jA1 fOut).2 rfl,
        by simp [Expr.holds, Expr.eval, fOut, locX, Expr.glob]⟩), by decide⟩,
      ?_⟩, po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl, ?_⟩,
    .inr (.inr ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩),
    fun ⟨e, he, hp⟩ => by cases he; simp [e12, R, Event.isVol] at hp⟩,
    fwdNoAcq_of (by decide) (by decide) (by decide), not_rmwAcc_of_nil _ rfl _⟩
  · rintro ⟨e'', h₁, h₂⟩
    have p₁ := (ppo_empty h₁).1
    have p₂ := (ppo_empty h₂).1
    have key : ∀ p ∈ poL, ∀ q ∈ poL, p.1 = 11 → q.2 = 12 → p.2 = q.1 → False := by decide
    exact key _ p₁ _ p₂ rfl rfl rfl
  · intro f hf v₁ v₂ h₁ h₂
    have h7 := (holds_jA1 f).1 hf.1
    obtain rfl : locX = v₁ := Option.some.inj h₁
    obtain rfl : f 7 = v₂ := Option.some.inj h₂
    exact h7.symm

theorem gen_jA2 : esP.Generated (fun _ => True) jA2 := by
  have h₁ : jA1.P.replace (.sym 12) (.sym 11) = jA1.P := Expr.replace_sym_of_not_mem (by decide)
  exact .fwd (o := .rlx) (x := Expr.glob "q") (e := Expr.num 1) (b := false) (ev₁ := e11)
    (ev₂ := e12) (v₁ := .sym 11) (v₂ := .sym 12) gen_jA1 rfl fwdA rfl rfl rfl rfl
    (wf_single (by decide)) ⟨fOut, by rw [h₁]; exact (holds_jA1 fOut).2 rfl, trivial⟩

theorem noSrcA {a : EventId} (h : a ≠ 11) : ∀ c, ¬ jA2.δ.edge a c := by
  rw [jA2_eq]; rintro c (hc | hc) <;> simp at hc; exact h hc.1

theorem gen_jA : esP.Generated (fun _ => True) jA := by
  have hsyms : (esP.strPred jA2.P Q2 [5, 6]).syms = [7, 6, 5] := by rw [jA2_eq]; decide
  refine .str Q2 [5, 6] gen_jA2 (fun e => ?_) (fun e he => ?_) (fun e he => ⟨?_, fun h => ?_⟩)
    ⟨fOut, by rw [jA2_eq]; exact (str2 _ fOut).2 ⟨(holds_jA1 fOut).2 rfl, rfl, by decide⟩, trivial⟩
  · rw [hsyms]
    have : jA2.P.syms = [7] := by rw [jA2_eq]; decide
    rw [this]
    by_cases h5 : e = 5 <;> by_cases h6 : e = 6 <;> by_cases h7 : e = 7 <;> simp_all
  · rw [jA2_eq]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl <;> exact .canon fun a h => by rcases h with h | h <;> simp at h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rw [jA2_eq]
    rcases he with rfl | rfl <;> exact po_of (by decide)
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    have hw : jA2.w.id = 13 := by rw [jA2_eq]; rfl
    rw [hw] at h
    have := ppo_fixed (noSrcA (by decide)) (noSrcA (by rcases he with rfl | rfl <;> decide)) h
    exact absurd (show (_, _) ∈ poL from this) (by rcases he with rfl | rfl <;> decide)

theorem gen_jB1 : esP.Generated (fun _ => True) jB1 := by
  have hsyms : (esP.strPred jB0.P Q2 [5, 6]).syms = [6, 5] := by decide
  refine .str Q2 [5, 6] (.pre (w := e14) (by simp [esP]) rfl ⟨fOut, SP.holds (by simp [esP]) _⟩)
    (fun e => ?_) (fun e _ => .canon fun a h => noEdge_empty a e h)
    (fun e he => ⟨?_, fun h => ?_⟩) ⟨fOut, (holds_jB1 fOut).2 ⟨rfl, by decide⟩, trivial⟩
  · rw [hsyms]
    have : jB0.P.syms = [] := rfl
    rw [this]
    by_cases h5 : e = 5 <;> by_cases h6 : e = 6 <;> simp_all
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl <;> exact po_of (by decide)
  · have := (ppo_empty h).1
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl <;> exact absurd (show (_, _) ∈ poL from this) (by decide)

/-- **`r2 := x` forwarded from `r0 := *p2`** under `p2 = &x ∧ p ≠ &x`:
    neither `r1 := *p` nor `z := 1` is `≼`-between. -/
theorem fwdB : esP.fwdRel jB1 8 11 := by
  have hP : ∀ f, jB1.P.holds f → f 6 = locX ∧ f 5 ≠ locX := fun f hf => (holds_jB1 f).1 hf
  refine ⟨⟨⟨⟨⟨(FwdCtx.remapRel_of_noEdge noEdge_empty).2 (.inr
      ⟨po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl, fOut, (holds_jB1 fOut).2 ⟨rfl, by decide⟩,
        by simp [Expr.holds, Expr.eval, fOut, locX, Expr.glob]⟩), by decide⟩,
      ?_⟩, po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl, ?_⟩,
    .inr (.inr ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩),
    fun ⟨e, he, hp⟩ => by cases he; simp [e11, R, Event.isVol] at hp⟩,
    fwdNoAcq_of (by decide) (by decide) (by decide), not_rmwAcc_of_nil _ rfl _⟩
  · rintro ⟨e'', h₁, h₂⟩
    have p₁ := (ppo_empty h₁).1
    have p₂ := (ppo_empty h₂).1
    have key : ∀ p ∈ poL, ∀ q ∈ poL, p.1 = 8 → q.2 = 11 → p.2 = q.1 → p.2 = 9 ∨ p.2 = 10 := by
      decide
    rcases key _ p₁ _ p₂ rfl rfl rfl with h | h
    · subst h; exact (not_alias_8 hP).1 (ppo_empty h₁).2
    · subst h; exact not_alias_10_11 (ppo_empty h₂).2
  · intro f hf v₁ v₂ h₁ h₂
    have h6 := ((holds_jB1 f).1 hf.1).1
    obtain rfl : f 6 = v₁ := Option.some.inj h₁
    obtain rfl : locX = v₂ := Option.some.inj h₂
    exact h6

theorem gen_jB2 : esP.Generated (fun _ => True) jB2 := by
  have h₁ : jB1.P.replace (.sym 11) (.sym 8) = jB1.P := Expr.replace_sym_of_not_mem (by decide)
  exact .fwd (o := .rlx) (x := Expr.glob "v") (e := .sym 11) (b := false) (ev₁ := e8)
    (ev₂ := e11) (v₁ := .sym 8) (v₂ := .sym 11) gen_jB1 rfl fwdB rfl rfl rfl rfl
    (wf_single (by decide)) ⟨fOut, by rw [h₁]; exact (holds_jB1 fOut).2 ⟨rfl, by decide⟩, trivial⟩

theorem noSrcB {a : EventId} (h : a ≠ 8) : ∀ c, ¬ jB2.δ.edge a c := by
  rw [jB2_eq]; rintro c (hc | hc) <;> simp at hc; exact h hc.1

theorem gen_jB : esP.Generated (fun _ => True) jB := by
  have hsyms : (esP.strPred jB2.P Q3 [7]).syms = [6, 5, 7] := by rw [jB2_eq]; decide
  refine .str Q3 [7] gen_jB2 (fun e => ?_) (fun e he => ?_) (fun e he => ⟨?_, fun h => ?_⟩)
    ⟨fOut, by rw [jB2_eq]; exact (str3 _ fOut).2 ⟨(holds_jB1 fOut).2 ⟨rfl, by decide⟩, rfl⟩,
      trivial⟩
  · rw [hsyms]
    have : jB2.P.syms = [6, 5] := by rw [jB2_eq]; decide
    rw [this]
    by_cases h5 : e = 5 <;> by_cases h6 : e = 6 <;> by_cases h7 : e = 7 <;> simp_all
  · rw [jB2_eq]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    subst he; exact .canon fun a h => by rcases h with h | h <;> simp at h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rw [jB2_eq]; subst he; exact po_of (by decide)
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    subst he
    have hw : jB2.w.id = 14 := by rw [jB2_eq]; rfl
    rw [hw] at h
    have := ppo_fixed (noSrcB (by decide)) (noSrcB (by decide)) h
    exact absurd (show (_, _) ∈ poL from this) (by decide)

/-! ## The execution -/

def rfL : List (EventId × EventId) := [(0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (3, 11), (3, 12)]
def JP : List Justification := [pj e0, pj e1, pj e2, pj e3, pj e4, jZ, jA, jB]
def xP : Execution := ⟨esP.Candidate, JP, fun w r => (w, r) ∈ rfL⟩

theorem JP_eq : JP = [pj e0, pj e1, pj e2, pj e3, pj e4, jZ,
    ⟨esP.strPred jA1.P Q2 [5, 6], [], ⟨[(11, 12)], []⟩, e13⟩,
    ⟨esP.strPred jB1.P Q3 [7], [8], ⟨[(8, 11)], []⟩,
      { e14 with kind := .write .rlx (Expr.glob "v") (.sym 8) false }⟩] := by
  simp only [JP, jA_eq, jB_eq]

theorem δP : xP.δ = ⟨[(11, 12), (8, 11)], []⟩ := by
  simp only [xP, JP_eq, Execution.δ, List.foldr]
  rfl

theorem edge_P {a b : EventId} (h : xP.δ.edge a b) : (a = 11 ∧ b = 12) ∨ (a = 8 ∧ b = 11) := by
  rw [δP] at h
  rcases h with h | h
  · simp at h; exact h
  · cases h

theorem edge_1112 : xP.δ.edge 11 12 := .inl (by rw [δP]; simp)
theorem edge_811 : xP.δ.edge 8 11 := .inl (by rw [δP]; simp)

theorem elided_P {a : EventId} : xP.elided a ↔ a = 11 ∨ a = 12 := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := (xP.elided_iff a).1 h
    rcases edge_P hb with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact .inr rfl
    · exact .inl rfl
  · rintro (rfl | rfl)
    · exact (xP.elided_iff 11).2 ⟨8, edge_811⟩
    · exact (xP.elided_iff 12).2 ⟨11, edge_1112⟩

/-- `remap_δ`: `r2 := x` and `r3 := *p3` onto `r0 := *p2`. -/
def g (a : EventId) : EventId := if a = 11 ∨ a = 12 then 8 else a

theorem remap_P {a a' : EventId} (h : xP.δ.Remap a a') : a' = g a := by
  induction h with
  | @canon e hno =>
      unfold g
      split
      · rename_i h
        rcases h with rfl | rfl
        · exact absurd edge_811 (hno 8)
        · exact absurd edge_1112 (hno 11)
      · rfl
  | step he hr ih =>
      rcases edge_P he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [ih]; rfl
      · rw [ih]; rfl

theorem remap_canon {a : EventId} (h₁ : a ≠ 11) (h₂ : a ≠ 12) : xP.δ.Remap a a :=
  .canon fun _ hc => by rcases edge_P hc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> contradiction

theorem remap_118 : xP.δ.Remap 11 8 := .step edge_811 (remap_canon (by decide) (by decide))
theorem remap_128 : xP.δ.Remap 12 8 := .step edge_1112 remap_118

theorem X_P {a : EventId} : xP.X a ↔ a ∈ esP.ids := by
  constructor
  · exact PpoNecessity.ids_of_cand
  · intro h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    exact cand_of_mem SP.nodup he (by revert e; decide) (by revert e; decide)

theorem mem_JP {j : Justification} (hj : j ∈ JP) :
    j = pj e0 ∨ j = pj e1 ∨ j = pj e2 ∨ j = pj e3 ∨ j = pj e4 ∨ j = jZ ∨ j = jA ∨ j = jB := by
  simpa [JP] using hj

theorem jZ_mem : jZ ∈ xP.J := by simp [xP, JP]
theorem jA_mem : jA ∈ xP.J := by simp [xP, JP]
theorem jB_mem : jB ∈ xP.J := by simp [xP, JP]

theorem holds_JP {j : Justification} (hj : j ∈ JP) : j.P.holds fOut := by
  rcases mem_JP hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SP.holds (e := e0) (by simp [esP]) _
  · exact SP.holds (e := e1) (by simp [esP]) _
  · exact SP.holds (e := e2) (by simp [esP]) _
  · exact SP.holds (e := e3) (by simp [esP]) _
  · exact SP.holds (e := e4) (by simp [esP]) _
  · exact (holds_jZ fOut).2 ⟨rfl, by decide⟩
  · exact (holds_jA fOut).2 ⟨rfl, rfl, by decide⟩
  · exact (holds_jB fOut).2 ⟨⟨rfl, by decide⟩, rfl⟩

theorem psi_P (f : Valuation) (h₁ : f 8 = f 11) (h₂ : f 11 = f 12) : xP.δ.psi esP f := by
  rw [δP]
  intro p hp e₁ e₂ v₁ v₂ he₁ he₂ hv₁ hv₂
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · have h₁' : esP.ev 11 = some e11 := rfl
    have h₂' : esP.ev 12 = some e12 := rfl
    rw [h₁'] at he₁; rw [h₂'] at he₂; cases he₁; cases he₂
    cases hv₁; cases hv₂
    simp [Expr.holds, Expr.eval, h₂]
  · have h₁' : esP.ev 8 = some e8 := rfl
    have h₂' : esP.ev 11 = some e11 := rfl
    rw [h₁'] at he₁; rw [h₂'] at he₂; cases he₁; cases he₂
    cases hv₁; cases hv₂
    simp [Expr.holds, Expr.eval, h₁]

theorem psi_sub {δ : FwdCtx} (hs : ∀ p ∈ δ.f, p ∈ [(11, 12), (8, 11)]) (f : Valuation)
    (h₁ : f 8 = f 11) (h₂ : f 11 = f 12) : δ.psi esP f := fun p hp => by
  have := psi_P f h₁ h₂
  rw [δP] at this
  exact this p (hs p hp)

theorem isExecution_P : xP.IsExecution esP (fun _ => True) where
  maximal := ⟨fun _ h => h, fun a b _ _ ⟨ea, eb, ha, hb, hn⟩ =>
      hn ⟨fOut, SP.holds (ev_inv ha).1 _, SP.holds (ev_inv hb).1 _⟩,
    fun _ hc hn => absurd hc hn⟩
  generated j hj := by
    rcases mem_JP hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pre_P (by simp [esP]) rfl
    · exact pre_P (by simp [esP]) rfl
    · exact pre_P (by simp [esP]) rfl
    · exact pre_P (by simp [esP]) rfl
    · exact pre_P (by simp [esP]) rfl
    · exact gen_jZ
    · exact gen_jA
    · exact gen_jB
  inX j hj := by
    rcases mem_JP hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (try rw [jA_eq]) <;> (try rw [jB_eq]) <;> exact X_P.2 (by decide)
  consistent := ⟨fOut, fun j hj => holds_JP hj, fun a e _ he => SP.holds (ev_inv he).1 _⟩
  fwdWF := by
    rw [δP]
    have hE : ∀ c d, FwdCtx.edge ⟨[(11, 12), (8, 11)], []⟩ c d →
        (c = 11 ∧ d = 12) ∨ (c = 8 ∧ d = 11) := by
      intro c d h
      rcases h with h | h
      · simpa using h
      · cases h
    refine ⟨fun a ha => ?_, fun a b e ha hb => ?_⟩
    · have : ∀ c d, Relation.TransGen (FwdCtx.edge ⟨[(11, 12), (8, 11)], []⟩) c d → c < d := by
        intro c d h
        induction h with
        | single h => rcases hE _ _ h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
        | tail _ h ih =>
            rcases hE _ _ h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact Nat.lt_trans ih (by decide)
      exact Nat.lt_irrefl _ (this a a ha)
    · rcases hE _ _ ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hE _ _ hb with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩ <;>
        first | exact h₃.symm | exact absurd h₄ (by decide)
  rf_wr w r h := by
    have hok : ∀ p ∈ rfL, clsB esP Event.isWrite p.1 = true ∧ clsB esP Event.isRead p.2 = true := by
      decide
    obtain ⟨h₁, h₂⟩ := hok _ h
    have hw := cls_clsB.2 h₁
    have hr := cls_clsB.2 h₂
    exact ⟨hw, hr, cand_of_cls SP.nodup (fun e he => wr_nb e (.inl he)) hw,
      cand_of_cls SP.nodup (fun e he => wr_nb e (.inr he)) hr⟩
  rf_func w w' r h h' := by
    have : ∀ p ∈ rfL, ∀ q ∈ rfL, p.2 = q.2 → p.1 = q.1 := by decide
    exact this _ h _ h' rfl
  justified w hw he hn := by
    have hids : ∀ w ∈ esP.ids, clsB esP Event.isEffect w = true →
        w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 10 ∨ w = 13 ∨ w = 14 := by decide
    have hw' := hids w (X_P.1 hw) (cls_clsB.1 he)
    have hid : ∀ j ∈ JP, ∀ j' ∈ JP, j.w.id = j'.w.id → j' = j := by
      intro j hj j' hj' h
      rw [JP_eq] at hj hj'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj hj'
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | exact absurd h (by decide)
    have mk : ∀ j ∈ JP, j.w.id = w → ∃ j ∈ xP.J, j.w.id = w ∧ ∀ j' ∈ xP.J, j'.w.id = w → j' = j :=
      fun j hj h => ⟨j, hj, h, fun j' hj' h' => hid j hj j' hj' (h.trans h'.symm)⟩
    rcases hw' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mk (pj e0) (by simp [JP]) rfl
    · exact mk (pj e1) (by simp [JP]) rfl
    · exact mk (pj e2) (by simp [JP]) rfl
    · exact mk (pj e3) (by simp [JP]) rfl
    · exact mk (pj e4) (by simp [JP]) rfl
    · exact mk jZ (by simp [JP]) rfl
    · exact mk jA (by simp [JP]) (by rw [jA_eq]; rfl)
    · exact mk jB (by simp [JP]) (by rw [jB_eq]; rfl)

/-! ## `φ`, No-Thin-Air and coherence -/

def dpL : List (EventId × EventId) :=
  [(6, 10), (5, 10), (7, 13), (6, 13), (5, 13), (6, 14), (5, 14), (7, 14), (8, 14)]

theorem dp_P {a b : EventId} (h : xP.DP a b) : (a, b) ∈ dpL := by
  obtain ⟨-, -, j, hj, rfl, h⟩ := h
  have key : ∀ j ∈ JP, ∀ a ∈ j.P.syms ++ j.D, (a, j.w.id) ∈ dpL := by
    rw [JP_eq]; decide
  exact key j hj a (List.mem_append.2 h)

theorem psi_JP {j : Justification} (hj : j ∈ JP) : j.δ.psi esP fOut := by
  rcases mem_JP hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro p hp; cases hp
  · intro p hp; cases hp
  · intro p hp; cases hp
  · intro p hp; cases hp
  · intro p hp; cases hp
  · intro p hp; cases hp
  · rw [jA_eq]; exact psi_sub (by decide) fOut rfl rfl
  · rw [jB_eq]; exact psi_sub (by decide) fOut rfl rfl

theorem P_P : xP.P esP fOut := fun _ hj => ⟨holds_JP hj, psi_JP hj⟩

theorem phiRf_P : xP.phiRf esP fOut := by
  refine ⟨?_, ?_, ?_⟩
  · intro w r ew er h hw hr
    have key : ∀ p ∈ rfL, ∀ ew ∈ esP.events, ∀ er ∈ esP.events, ew.id = p.1 → er.id = p.2 →
        ew.loc.map (·.eval fOut) = er.loc.map (·.eval fOut) ∧
        ew.val.map (·.eval fOut) = er.val.map (·.eval fOut) := by decide
    have := key (w, r) h ew (ev_inv hw).1 er (ev_inv hr).1 (ev_inv hw).2 (ev_inv hr).2
    refine ⟨fun lw lr h₁ h₂ => ?_, fun vw vr h₁ h₂ => ?_⟩
    · have := this.1; rw [h₁, h₂] at this; exact Option.some.inj this
    · have := this.2; rw [h₁, h₂] at this; exact Option.some.inj this
  · intro a e α sz _ he hk
    obtain ⟨hm, -⟩ := ev_inv he
    simp only [esP, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> cases hk
  · intro a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂ _ _ _ he₁ _ hk₁
    obtain ⟨hm, -⟩ := ev_inv he₁
    simp only [esP, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> cases hk₁

theorem phi_P : xP.phi esP := by
  refine ⟨fun e h hel => ?_, fun r => ⟨?_, ?_⟩, fOut, P_P, phiRf_P⟩
  · rw [elided_P] at hel
    rcases h with ⟨r, hr⟩ | ⟨b, hb⟩
    · have : ∀ p ∈ rfL, p.1 ≠ 11 ∧ p.1 ≠ 12 := by decide
      rcases hel with rfl | rfl
      · exact (this _ hr).1 rfl
      · exact (this _ hr).2 rfl
    · have : ∀ p ∈ dpL, p.1 ≠ 11 ∧ p.1 ≠ 12 := by decide
      rcases hel with rfl | rfl
      · exact (this _ (dp_P hb)).1 rfl
      · exact (this _ (dp_P hb)).2 rfl
  · rintro ⟨w, hw⟩
    have hok : ∀ p ∈ rfL, clsB esP Event.isRead p.2 = true := by decide
    have h₂ := hok _ hw
    exact ⟨X_P.2 (clsB_id h₂), cls_clsB.2 h₂⟩
  · rintro ⟨hX, hr⟩
    have key : ∀ r ∈ esP.ids, clsB esP Event.isRead r = true → ∃ p ∈ rfL, p.2 = r := by decide
    obtain ⟨p, hp, rfl⟩ := key r (X_P.1 hX) (cls_clsB.1 hr)
    exact ⟨p.1, hp⟩

theorem not_must_89 : ¬ esP.mustAlias 8 9 := by
  rintro ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, hs⟩
  cases h₁; cases h₂; cases hl₁; cases hl₂
  have := hs (fun α => .num α) _ _ rfl rfl
  cases this

theorem not_must_810 : ¬ esP.mustAlias 8 10 := by
  rintro ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, hs⟩
  cases h₁; cases h₂; cases hl₁; cases hl₂
  have := hs (fun α => .num α) _ _ rfl rfl
  cases this

/-- A step of MoRDor's `ppoM` under `δ` is a `⊑`-pair moved by `g`, other than
    `(r0, r1)` and `(r0, z)` unless the alias predicate lets them alias. -/
theorem ppoM_bound {Pa Pr : Pred} {a b : EventId} (h : esP.ppoM Pa Pr xP.δ a b) :
    ∃ a₀ b₀, (a₀, b₀) ∈ poL ∧ ((a₀, b₀) = (8, 9) → esP.mayAlias Pa 8 9) ∧
      ((a₀, b₀) = (8, 10) → esP.mayAlias Pa 8 10) ∧ a = g a₀ ∧ b = g b₀ ∧ a ≠ b := by
  obtain ⟨⟨a₀, b₀, hb, ra, rb⟩, hne⟩ := h
  have hsync : syncML esP = [] := by decide
  refine ⟨a₀, b₀, ?_, ?_, ?_, remap_P ra, remap_P rb, hne⟩
  · rcases hb with (hs | (⟨x, -, hx⟩ | ⟨x, hx, -⟩)) | ⟨hpo, -⟩
    · have hm := ppoSyncM_mem hs
      rw [hsync] at hm; cases hm
    · exact absurd hx (not_rmwPairs rfl)
    · exact absurd hx (not_rmwPairs rfl)
    · exact hpo
  · intro he
    cases he
    rcases hb with (hs | (⟨x, -, hx⟩ | ⟨x, hx, -⟩)) | ⟨-, hm | hal⟩
    · have hm := ppoSyncM_mem hs
      rw [hsync] at hm; cases hm
    · exact absurd hx (not_rmwPairs rfl)
    · exact absurd hx (not_rmwPairs rfl)
    · exact absurd hm not_must_89
    · exact hal
  · intro he
    cases he
    rcases hb with (hs | (⟨x, -, hx⟩ | ⟨x, hx, -⟩)) | ⟨-, hm | hal⟩
    · have hm := ppoSyncM_mem hs
      rw [hsync] at hm; cases hm
    · exact absurd hx (not_rmwPairs rfl)
    · exact absurd hx (not_rmwPairs rfl)
    · exact absurd hm not_must_810
    · exact hal

/-- Every predicate of the execution whose window reaches `r0` has
    `p2 = &x ∧ p ≠ &x`. -/
theorem P_8 {j : Justification} (hj : j ∈ JP) (hw : Win esP j 8) :
    ∀ f, j.P.holds f → f 6 = locX ∧ f 5 ≠ locX := by
  rcases mem_JP hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
  · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
  · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
  · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
  · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
  · exact fun f hf => (holds_jZ f).1 hf
  · exact fun f hf => ((holds_jA f).1 hf).2
  · exact fun f hf => ((holds_jB f).1 hf).1

theorem step_bound {a b : EventId} (h : xP.ppoStep esP a b) :
    ∃ a₀ b₀, (a₀, b₀) ∈ poL ∧ (a₀, b₀) ≠ (8, 9) ∧ (a₀, b₀) ≠ (8, 10) ∧ a = g a₀ ∧ b = g b₀ ∧
      a ≠ b := by
  obtain ⟨-, -, ⟨j, hj, hp, hwa, -⟩ | ⟨hs | ⟨hp, -⟩, -⟩⟩ := h
  · obtain ⟨a₀, b₀, hpo, h89, h810, rfl, rfl, hne⟩ := ppoM_bound hp
    refine ⟨a₀, b₀, hpo, fun he => ?_, fun he => ?_, rfl, rfl, hne⟩
    · have hal := h89 he
      cases he
      exact (not_alias_8 fun f hf => P_8 hj hwa f hf.1).1 hal
    · have hal := h810 he
      cases he
      exact (not_alias_8 fun f hf => P_8 hj hwa f hf.1).2 hal
  · obtain ⟨⟨a₀, b₀, hs, -, -⟩, -⟩ := hs
    have : syncML esP = [] := by decide
    have hm := ppoSyncM_mem hs
    rw [this] at hm; cases hm
  · obtain ⟨a₀, b₀, hpo, h89, h810, rfl, rfl, hne⟩ := ppoM_bound hp
    have hPm : ∀ f, xP.Pm esP f → f 6 = locX ∧ f 5 ≠ locX :=
      fun f hf => (holds_jZ f).1 (hf.1 jZ jZ_mem)
    exact ⟨a₀, b₀, hpo, fun he => (not_alias_8 hPm).1 (h89 he),
      fun he => (not_alias_8 hPm).2 (h810 he), rfl, rfl, hne⟩

/-- `r1`, then `z`, then `r0`; otherwise program order. -/
def rk (a : EventId) : Nat := if a = 8 then 10 else if a = 9 then 8 else if a = 10 then 9 else a

theorem ntaP : xP.NoThinAir esP := by
  have hstep : ∀ a b, xP.ppoStep esP a b → rk a < rk b := by
    intro a b h
    obtain ⟨a₀, b₀, hpo, h89, h810, rfl, rfl, hne⟩ := step_bound h
    have key : ∀ p ∈ poL, p ≠ (8, 9) → p ≠ (8, 10) → g p.1 ≠ g p.2 →
        rk (g p.1) < rk (g p.2) := by decide
    exact key _ hpo h89 h810 hne
  have mono : ∀ {R : Rel}, (∀ a b, R a b → rk a < rk b) →
      ∀ a b, Relation.TransGen R a b → rk a < rk b := by
    intro R hR a b h
    induction h with
    | single h => exact hR _ _ h
    | tail _ h ih => exact Nat.lt_trans ih (hR _ _ h)
  have hedge : ∀ a b, ((xP.dep esP).union xP.rf) a b → rk a < rk b := by
    rintro a b ((⟨-, -, hp⟩ | hd) | hrf)
    · exact mono hstep a b hp
    · have key : ∀ p ∈ dpL, rk p.1 < rk p.2 := by decide
      exact key _ (dp_P hd)
    · have key : ∀ p ∈ rfL, rk p.1 < rk p.2 := by decide
      exact key _ hrf
  intro a h
  exact Nat.lt_irrefl _ (mono hedge a a h)

/-- Each location is written once in `X`, so the empty coherence order is one. -/
theorem coherentT_P : xP.CoherentT esP := by
  refine ⟨fun _ _ => False, ⟨fun _ _ h => h.elim, fun _ h => h, fun _ _ _ h => h.elim,
    fun a b ha hb hwa hwb hne hsl => ?_⟩, ?_, fun r w _ ⟨_, ⟨_, _, h⟩, _⟩ => h⟩
  · obtain ⟨ea, eb, la, lb, ha', hb', hla, hlb, heq⟩ := hsl
    have := heq fOut P_P phiRf_P
    have key : ∀ a ∈ esP.ids, ∀ b ∈ esP.ids, clsB esP Event.isWrite a = true →
        clsB esP Event.isWrite b = true → a ≠ b →
        (locOf esP a).map (·.eval fOut) ≠ (locOf esP b).map (·.eval fOut) := by decide
    exact absurd (by simp [locOf, ha', hb', hla, hlb, this])
      (key a (X_P.1 ha.1) b (X_P.1 hb.1) (cls_clsB.1 hwa) (cls_clsB.1 hwb) hne)
  · have hH : ∀ a b, xP.hbT esP a b → (a, b) ∈ poL := by
      intro a b h
      refine transGen_mem (fun c d s => ?_) closed_poL h
      rcases s with ⟨⟨-, -, hpo⟩, -⟩ | ⟨hs, -⟩
      · exact hpo
      · have : swL esP = [] := by decide
        have hm := sw_mem hs
        rw [this] at hm; cases hm
    have hE : ∀ a b, xP.eco (fun _ _ => False) a b → (a, b) ∈ rfL :=
      fun a b h => eco_mem (fun a b h => h) (fun _ _ h => h.elim)
        (fun _ _ ⟨_, _, h⟩ => h.elim) (by decide) h
    have hok : ∀ p ∈ poL, p.1 ≠ p.2 ∧ (p.2, p.1) ∉ rfL := by decide
    rintro a ⟨b, hab, rfl | hba⟩
    · exact (hok _ (hH _ _ hab)).1 rfl
    · exact (hok _ (hH _ _ hab)).2 (hE _ _ hba)

/-- **The execution is consistent**: `X ∖ †` drops `r2` and `r3`. -/
theorem consistentT_P : xP.ConsistentT esP (fun _ => True) :=
  ⟨isExecution_P, phi_P, ntaP, coherentT_P⟩

/-! ## `≼` against `⊑`, and the conditions -/

/-- `p = p3 = &u`, `p2 = &x`: a model of `P_jZ ∧ ψ_δ`. -/
def fZ : Valuation := fun α =>
  if α = 5 ∨ α = 7 then locU else if α = 6 then locX else .num 0

theorem PJ_jZ_fZ : xP.PJ esP jZ fZ :=
  ⟨(holds_jZ fZ).2 ⟨rfl, by decide⟩, psi_P fZ rfl rfl⟩

/-- `r1 := *p` and `r3 := *p3` may alias under `jZ`'s predicate. -/
theorem alias_9_12 : esP.mayAlias (xP.PJ esP jZ) 9 12 :=
  ⟨e9, e12, _, _, rfl, rfl, rfl, rfl, fZ, PJ_jZ_fZ, by simp [Expr.holds, Expr.eval, fZ]⟩

theorem ppo_98 : xP.ppo esP 9 8 := by
  have X9 : xP.X 9 := X_P.2 (by decide)
  have X8 : xP.X 8 := X_P.2 (by decide)
  exact ⟨X9, X8, .single ⟨.inl X9, .inl X8, .inl ⟨jZ, jZ_mem,
    ⟨⟨9, 12, .inr ⟨po_of (by decide), .inr alias_9_12⟩, remap_canon (by decide) (by decide),
      remap_128⟩, by decide⟩, .inr (po_of (by decide)), .inr (po_of (by decide))⟩⟩⟩

theorem not_dep_po : ¬ ∀ a b, xP.dep esP a b → xP.poX esP a b := fun h => by
  have h₁ : esP.poR 9 8 := (h 9 8 (.inl ppo_98)).2.2
  exact absurd (show (9, 8) ∈ poL from h₁) (by decide)

theorem not_noRevLoc : ¬ NoRevLoc esP xP := fun h =>
  h 9 12 9 8 (po_of (by decide)) (remap_canon (by decide) (by decide)) remap_128
    (.inr (.inr (.inl ⟨jZ, jZ_mem, alias_9_12⟩))) (po_of (by decide))

theorem rmwTightR_P : RMWTightR esP xP :=
  ⟨fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩

theorem dp_po_P : ∀ a b, xP.DP a b → esP.poR a b := fun a b h => by
  have key : ∀ p ∈ dpL, p ∈ poL := by decide
  exact key _ (dp_P h)

/-- **`FwdEntailsSrc` holds**: the windows reaching an end of `(r2, r3)` are
    `jA`'s and `jB`'s (`p3 = &x`), those reaching an end of `(r0, r2)` are
    `jZ`'s, `jA`'s and `jB`'s (`p2 = &x ∧ p ≠ &x`). -/
theorem fwdEntailsSrc_P : FwdEntailsSrc esP xP := by
  intro s t he
  rcases edge_P he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨jA1, 11, 12, ⟨.inl ⟨by rw [δP]; simp, rfl, rfl, fwdA⟩, fun p hp => (by cases hp),
      fun p hp => (by cases hp)⟩, fun j hj hw => ?_, fun f hf => ?_⟩
    · rcases mem_JP hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
      · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
      · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
      · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
      · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
      · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
      · exact fun f hf => ⟨(holds_jA1 f).2 ((holds_jA f).1 hf.1).1, fun p hp => (by cases hp)⟩
      · exact fun f hf => ⟨(holds_jA1 f).2 ((holds_jB f).1 hf.1).2, fun p hp => (by cases hp)⟩
    · exact ⟨(holds_jA1 f).2 ((holds_jA f).1 (hf.1 jA jA_mem)).1, fun p hp => (by cases hp)⟩
  · refine ⟨jB1, 8, 11, ⟨.inl ⟨by rw [δP]; simp, rfl, rfl, fwdB⟩, fun p hp => (by cases hp),
      fun p hp => (by cases hp)⟩, fun j hj hw => ?_, fun f hf => ?_⟩
    · rcases mem_JP hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
      · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
      · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
      · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
      · exact absurd hw (by simp only [Win, EventStructure.poR]; decide)
      · exact fun f hf => ⟨(holds_jB1 f).2 ((holds_jZ f).1 hf.1), fun p hp => (by cases hp)⟩
      · exact fun f hf => ⟨(holds_jB1 f).2 ((holds_jA f).1 hf.1).2, fun p hp => (by cases hp)⟩
      · exact fun f hf => ⟨(holds_jB1 f).2 ((holds_jB f).1 hf.1).1, fun p hp => (by cases hp)⟩
    · exact ⟨(holds_jB1 f).2 ((holds_jZ f).1 (hf.1 jZ jZ_mem)), fun p hp => (by cases hp)⟩

/-- **`FwdEntailsImg` fails**: `remap_δ(r3) = r0` is in `jZ`'s window, and
    `jZ` does not entail `p3 = &x`, which `fwdBase` asked of `(r2, r3)`. -/
theorem not_fwdEntailsImg : ¬ FwdEntailsImg esP xP := fun h => by
  obtain ⟨j₀, u, v, hg, hJ, -⟩ := h 11 12 edge_1112
  have hE := hJ jZ jZ_mem ⟨8, remap_128, .inr (po_of (by decide))⟩
  rcases hg.1 with ⟨-, rfl, rfl, -⟩ | ⟨hw, -⟩
  · obtain ⟨-, -, ev₁, ev₂, l₁, l₂, h₁, h₂, hl₁, hl₂, hq⟩ := hg.base
    cases h₁; cases h₂; cases hl₁; cases hl₂
    have := hq fZ (hE fZ PJ_jZ_fZ) _ _ rfl rfl
    simp [fZ, locU] at this
  · rw [δP] at hw; cases hw

/-- **`FwdEntailsSrc` does not give `DP ∪ ≼ ⊆ ⊑`**: a consistent execution
    with every hypothesis of `dep_po_T` but `NoRevLoc`, and `FwdEntailsSrc`
    (so `FwdEntails`), where `NoRevLoc` and `DP ∪ ≼ ⊆ ⊑` fail; it violates
    `FwdEntailsImg`. -/
theorem fwdEntailsSrc_insufficient :
    xP.ConsistentT esP (fun _ => True) ∧
    (∀ a b c, esP.poR a b → esP.poR b c → esP.poR a c) ∧ (∀ a, ¬ esP.poR a a) ∧
    PoForest esP ∧ RMWTightR esP xP ∧ (∀ a b, xP.DP a b → esP.poR a b) ∧
    FwdEntailsSrc esP xP ∧ FwdEntails esP xP ∧ ¬ FwdEntailsImg esP xP ∧
    ¬ NoRevLoc esP xP ∧ ¬ (∀ a b, xP.dep esP a b → xP.poX esP a b) :=
  ⟨consistentT_P, poTrans_of closed_poL,
    poIrr_of fun p hp => by
      obtain ⟨a, b⟩ := p
      have := (mem_poL.1 hp).1
      exact Nat.ne_of_lt this,
    poForest_of forestL_poL, rmwTightR_P, dp_po_P, fwdEntailsSrc_P, fwdEntailsSrc_P.fwdEntails,
    not_fwdEntailsImg, not_noRevLoc, not_dep_po⟩

end FwdChain
