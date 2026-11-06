import Smrd.RMWTightDenote
import Smrd.PpoStability

/-!
# Write Elision across a failing `CAS`

`x := 2; y := 1; rs := CAS_{rlx,rel}(x, 0, 1); y := 2`. The `CAS` reads `x`
(event `2`, symbol `α`) and branches on `α = 0` (event `3`); the success
outcome writes `x := 1` (event `4`, releasing) and `y := 2` (event `5`), the
failure outcome `y := 2` only (event `6`), under the guard `¬(α = 0)`.

The execution `X = {0, 1, 2, 6}` reads `x := 2`, so the `CAS` fails, and
elides `y := 1` into the failure copy of `y := 2`, across the `CAS`'s read and
no release. The elision is generated against `y := 2`'s pre-justification,
under its value restriction `¬(α = 0)`.

* `not_rmwTightWE`: the elision ends neither at the `CAS`'s write nor after
  it, so `RMWTightWE` -- an earlier hypothesis of `dep_po_R`, that every Write
  Elision across the read of an RMW end at its write or `⊑`-after it -- fails.
* `dep_po`: `DP ∪ ≼ ⊆ ⊑` holds all the same, by `dep_po_R`, which takes the
  failure branch into account through `RMWFailGuard`. The pair
  `(y := 1, e_r)` of `ppo_sync ; rmw` needs the `CAS`'s condition entailed
  (`rmwPairs`), and the predicate of `X` refutes it (`not_rmwPairs_P`):
  remapped to `(y := 2, e_r)`, it would be reversed.
* `consistentT`: the execution is consistent.

MoRDor generates the same execution, with the predicate `¬(α = 0) ∧ α = 2`.
-/

namespace CasFailElision

open EventStructure PpoKit PpoStability Execution

/-! ## The program -/

/-- `x := 2; y := 1; rs := CAS_{rlx,rel}(x, 0, 1); y := 2` -/
def prog : Stmt :=
  .seq (st .rlx "x" 2) (.seq (st .rlx "y" 1)
    (.seq (.cas .rlx .rel "rs" "x" (.num 0) (.num 1)) (st .rlx "y" 2)))

/-- The `CAS`'s condition `α = 0`, `α` the symbol of its read. -/
def c : Expr := .eq (.sym 2) (.val (.num 0))
def gT : Guard := ⟨3, c, true⟩
def gF : Guard := ⟨3, c, false⟩

def e0 : Event := W 0 0 [0] [] [] .rlx "x" 2
def e1 : Event := W 1 0 [1, 0] [] [] .rlx "y" 1
def e2 : Event := R 2 0 [1, 1, 0, 0] [] [] .rlx "x"
def e3 : Event := ⟨3, .branch c, ⟨0, [1, 1, 0, 1], []⟩, []⟩
def e4 : Event := W 4 0 [1, 1, 0, 2] [] [gT] .rel "x" 1
def e5 : Event := W 5 0 [1, 1, 1] [] [gT] .rlx "y" 2
def e6 : Event := W 6 0 [1, 1, 1] [] [gF] .rlx "y" 2

def poL : List (EventId × EventId) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6),
    (2, 3), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (4, 5)]

def esC : EventStructure := ⟨[e0, e1, e2, e3, e4, e5, e6], poL, [⟨2, c, 4⟩]⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esC := rfl

theorem nodupC : (esC.events.map (·.id)).Nodup := by decide

theorem po_of {a b : EventId} (h : (a, b) ∈ poL) : esC.poR a b := h

theorem poTrans : ∀ a b c, esC.poR a b → esC.poR b c → esC.poR a c := poTrans_of (by decide)

theorem poIrr : ∀ a, ¬ esC.poR a a := poIrr_of (by decide)

theorem gC : GlobLocs esC := globLocs_of (by decide)

theorem rmw24 : (⟨2, c, 4⟩ : RMWEntry) ∈ esC.rmw := by simp [esC]

theorem mem_rmw {ent : RMWEntry} (h : ent ∈ esC.rmw) : ent = ⟨2, c, 4⟩ := by
  simpa [esC] using h

theorem ev_C (a : EventId) {e : Event} (h : esC.ev a = some e) :
    e = e0 ∨ e = e1 ∨ e = e2 ∨ e = e3 ∨ e = e4 ∨ e = e5 ∨ e = e6 := by
  simpa [esC] using (ev_inv h).1

/-! ## The valuation: `α = 2` -/

/-- The outcome: the `CAS` reads `2`. -/
def fOut : Valuation := fun _ => .num 2

/-- `y := 2`'s value restriction, `¬(α = 0)`, holds where `α ≠ 0`. -/
theorem holds6 {f : Valuation} (h : f 2 ≠ .num 0) : e6.valres.holds f := by
  simp [e6, W, gF, c, Event.valres, Expr.conj, Guard.expr, Expr.holds, Expr.eval, Expr.tt, h]

/-- The `CAS`'s condition is not entailed under `¬(α = 0)`. -/
theorem not_rmwPairs_of {P : Pred} (hP : P fOut) {a b : EventId} : ¬ esC.rmwPairs P a b := by
  rintro ⟨ent, hm, -, -, h⟩
  rw [mem_rmw hm] at h
  have := h fOut hP _ _ rfl rfl
  simp [fOut] at this

/-! ## The elision -/

/-- A pre-justification. -/
def pj (w : Event) : Justification := ⟨w.valres, [], .empty, w⟩

/-- The failure copy of `y := 2`'s pre-justification. -/
def jB : Justification := pj e6
/-- … with `y := 1` elided: `WE = {(6, 1)}`. -/
def jWE : Justification := { jB with δ := { jB.δ with we := jB.δ.we ++ [(6, 1)] } }

theorem jB_holds : jB.P.holds fOut := holds6 (by simp [fOut])

/-- `≼` under `¬(α = 0)` and the empty context: `ppo_sync` and the alias
    pairs; `ppo_rmw` is empty. -/
theorem ppo_memB {δ : FwdCtx} (hδ : ∀ a b, ¬ δ.edge a b) {a b : EventId}
    (h : esC.ppo jB.P.holds δ a b) : (a, b) ∈ syncL esC ++ aliasL esC := by
  obtain ⟨hab, -⟩ := h
  rcases (FwdCtx.remapRel_of_noEdge hδ).1 hab with (hs | ⟨⟨y, -, hr⟩ | ⟨y, hr, -⟩, -⟩) | ⟨hpo, hal⟩
  · exact List.mem_append_left _ (ppoSync_mem hs)
  · exact absurd hr (not_rmwPairs_of jB_holds)
  · exact absurd hr (not_rmwPairs_of jB_holds)
  · exact List.mem_append_right _ (mayAlias_mem gC hpo hal)

/-- **Write Elision elides `y := 1` into the failure copy of `y := 2`**:
    `y := 1` is its immediate `≼`-predecessor under `¬(α = 0)`, no release lies
    between (the `CAS`'s write is on the other outcome, which the fork
    restriction exempts), and `y := 1` is no RMW access. -/
theorem we_16 : esC.weRel jB 1 6 := by
  have hδ0 : ∀ a b, ¬ jB.δ.edge a b := by
    intro a b h; rcases h with h | h <;> cases h
  refine ⟨⟨⟨⟨⟨(FwdCtx.remapRel_of_noEdge hδ0).2 (.inr
      ⟨po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl, fOut, jB_holds,
        by simp [Expr.holds, Expr.eval, Expr.glob]⟩), by decide⟩, ?_⟩,
      po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl,
      fun _ _ _ _ h₁ h₂ => by rw [h₁] at h₂; cases h₂; rfl⟩,
    ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, fun ⟨e, he, hp⟩ => by cases he; simp [e1, W, Event.isVol] at hp⟩,
    weNoRel_of (by decide) (by decide), ?_, fun ⟨ent, hm, h⟩ => by
      rw [mem_rmw hm] at h; rcases h with h | h <;> cases h⟩
  · rintro ⟨e'', h₁, h₂⟩
    have m₁ := ppo_memB hδ0 h₁
    have m₂ := ppo_memB hδ0 h₂
    have key : ∀ p ∈ syncL esC ++ aliasL esC, ∀ q ∈ syncL esC ++ aliasL esC,
        p.1 = 1 → q.2 = 6 → p.2 = q.1 → False := by decide
    exact key _ m₁ _ m₂ rfl rfl rfl
  · -- the fork restriction: `4` and `5` are on the other outcome, with no
    -- common upper bound
    intro d hd hne hj
    have hd' : (1, d) ∈ poL := hd
    have key : ∀ p ∈ poL, p.1 = 1 → p.2 = 2 ∨ p.2 = 3 ∨ p.2 = 4 ∨ p.2 = 5 ∨ p.2 = 6 := by
      decide
    have nj : ∀ d, d = 4 ∨ d = 5 → ¬ esC.Joinable d 6 := by
      rintro d hd ⟨u, h₁, h₂⟩
      have k : ∀ p ∈ poL, p.1 = 6 → False := by decide
      rcases h₂ with rfl | h₂
      · rcases h₁ with rfl | h₁
        · rcases hd with h | h <;> cases h
        · rcases hd with rfl | rfl
          · exact absurd (show (4, 6) ∈ poL from h₁) (by decide)
          · exact absurd (show (5, 6) ∈ poL from h₁) (by decide)
      · exact k _ h₂ rfl
    have dv : ∀ d, d = 4 ∨ d = 5 → esC.Diverged d 6 := by
      rintro d (rfl | rfl)
      · exact ⟨e4, e6, rfl, rfl, gT, by simp [e4, W], gF, by simp [e6, W], rfl, rfl, by decide⟩
      · exact ⟨e5, e6, rfl, rfl, gT, by simp [e5, W], gF, by simp [e6, W], rfl, rfl, by decide⟩
    rcases key _ hd' rfl with h | h | h | h | h <;> simp only at h <;> subst h
    · exact .inr (.inl (po_of (by decide)))
    · exact .inr (.inl (po_of (by decide)))
    · exact absurd (hj (dv 4 (.inl rfl))) (nj 4 (.inl rfl))
    · exact absurd (hj (dv 5 (.inr rfl))) (nj 5 (.inr rfl))
    · exact absurd rfl hne

theorem wf_we : FwdCtx.WF { jB.δ with we := jB.δ.we ++ [(6, 1)] } := by
  refine ⟨fun a ha => ?_, fun a b e ha hb => ?_⟩
  · have : ∀ c d, Relation.TransGen
        ({ jB.δ with we := jB.δ.we ++ [(6, 1)] } : FwdCtx).edge c d → c = 6 ∧ d = 1 := by
      intro c d h
      induction h with
      | single h =>
          rcases h with h | h <;> simp [jB, pj, FwdCtx.empty] at h; exact h
      | tail _ h ih =>
          rcases h with h | h <;> simp [jB, pj, FwdCtx.empty] at h
          obtain ⟨-, rfl⟩ := ih; cases h.1
    have := this a a ha
    rw [this.1] at this; cases this.2
  · rcases ha with h | h <;> simp [jB, pj, FwdCtx.empty] at h
    rcases hb with h' | h' <;> simp [jB, pj, FwdCtx.empty] at h'
    rw [h.1, h'.1]

theorem gen_jB : esC.Generated (fun _ => True) jB :=
  .pre (w := e6) (by simp [esC]) rfl ⟨fOut, jB_holds⟩

theorem gen_jWE : esC.Generated (fun _ => True) jWE :=
  .we gen_jB we_16 wf_we ⟨fOut, jB_holds, trivial⟩

/-! ## The execution -/

def XL : List EventId := [0, 1, 2, 6]
def JC : List Justification := [pj e0, jWE]
def rfC : List (EventId × EventId) := [(0, 2)]
def xC : Execution := ⟨fun a => a ∈ XL, JC, fun w r => (w, r) ∈ rfC⟩

theorem X_iff {a : EventId} : xC.X a ↔ a ∈ XL := Iff.rfl

instance (a : EventId) : Decidable (xC.X a) := inferInstanceAs (Decidable (a ∈ XL))

theorem δC : xC.δ = ⟨[], [(6, 1)]⟩ := rfl

theorem edge_C {a b : EventId} (h : xC.δ.edge a b) : a = 6 ∧ b = 1 := by
  rw [δC] at h
  rcases h with h | h
  · cases h
  · simp at h; exact h

theorem edge_61 : xC.δ.edge 6 1 := .inr (by rw [δC]; simp)

theorem we_mem : ((6, 1) : EventId × EventId) ∈ xC.δ.we := by rw [δC]; simp

theorem elided_C {a : EventId} : xC.elided a ↔ a = 1 := by
  constructor
  · intro h; obtain ⟨b, hb⟩ := (xC.elided_iff a).1 h; exact (edge_C hb).2
  · rintro rfl; exact (xC.elided_iff 1).2 ⟨6, edge_61⟩

/-- `remap_δ` moves `y := 1` to `y := 2` and fixes the rest. -/
def g (a : EventId) : EventId := if a = 1 then 6 else a

theorem remap_C {a a' : EventId} (h : xC.δ.Remap a a') : a' = g a := by
  induction h with
  | @canon e hno =>
      unfold g
      split
      · subst_vars; exact absurd edge_61 (hno 6)
      · rfl
  | step he hr ih =>
      obtain ⟨rfl, rfl⟩ := edge_C he
      cases hr with
      | canon _ => rfl
      | step he' _ => exact absurd (edge_C he').2 (by decide)

theorem remap_canon {a : EventId} (h : a ≠ 1) : xC.δ.Remap a a :=
  .canon fun _ hc => h (edge_C hc).2

theorem remap_16 : xC.δ.Remap 1 6 := .step edge_61 (remap_canon (by decide))

theorem mem_JC {j : Justification} (hj : j ∈ JC) : j = pj e0 ∨ j = jWE := by
  simpa [JC] using hj

theorem J_holds {j : Justification} (hj : j ∈ JC) : j.P.holds fOut := by
  rcases mem_JC hj with rfl | rfl
  · simp [pj, e0, W, Event.valres, Expr.conj, Expr.holds, Expr.eval, Expr.tt]
  · exact jB_holds

theorem J_psi {j : Justification} (hj : j ∈ JC) (f : Valuation) : j.δ.psi esC f := by
  rcases mem_JC hj with rfl | rfl <;>
    exact fun p hp => by simp [jWE, jB, pj, FwdCtx.empty] at hp

theorem P_C : xC.P esC fOut := fun _ hj => ⟨J_holds hj, J_psi hj fOut⟩

/-- The value restrictions of the events of `X` hold under `α = 2`. -/
theorem holdsC {a : EventId} {e : Event} (ha : xC.X a) (he : esC.ev a = some e) :
    e.valres.holds fOut := by
  have hid := (ev_inv he).2
  rcases ev_C a he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [e0, W, Event.valres, Expr.conj, Expr.holds, Expr.eval, Expr.tt]
  · simp [e1, W, Event.valres, Expr.conj, Expr.holds, Expr.eval, Expr.tt]
  · simp [e2, R, Event.valres, Expr.conj, Expr.holds, Expr.eval, Expr.tt]
  all_goals first
    | exact holds6 (by simp [fOut])
    | (subst hid; exact absurd ha (by decide))

theorem dp_C {a b : EventId} (h : xC.DP a b) : a = 2 ∧ b = 6 := by
  obtain ⟨-, -, j, hj, hw, h⟩ := h
  rcases mem_JC hj with rfl | rfl
  · simp [pj, e0, W, Event.valres, Expr.conj, Expr.syms, Expr.tt] at h
  · subst hw
    simp [jWE, jB, pj, e6, W, gF, c, Event.valres, Expr.conj, Expr.syms, Guard.expr,
      Expr.tt] at h
    exact ⟨h, rfl⟩

theorem rfOK_C : RfOK esC rfC := by decide

theorem isExecution_C : xC.IsExecution esC (fun _ => True) where
  maximal := by
    refine ⟨fun a ha => ?_, fun a b ha hb ⟨ea, eb, h₁, h₂, hn⟩ =>
      hn ⟨fOut, holdsC ha h₁, holdsC hb h₂⟩, fun a hc hn => ?_⟩
    · have k : ∀ a ∈ XL, ∀ e ∈ esC.events, e.id = a → e.isBranch = false ∧ e.isFence = false :=
        by decide
      obtain ⟨e, he, rfl⟩ : ∃ e ∈ esC.events, e.id = a := by
        have : ∀ a ∈ XL, ∃ e ∈ esC.events, e.id = a := by decide
        exact this a ha
      exact cand_of_mem nodupC he (k _ ha e he rfl).1 (k _ ha e he rfl).2
    · obtain ⟨⟨e, he, rfl⟩, hb, -⟩ := hc
      simp only [esC, List.mem_cons, List.mem_nil_iff, or_false] at he
      have c46 : ∀ e, e = e4 ∨ e = e5 → esC.Conflict e.id 6 := by
        rintro e (rfl | rfl)
        · exact ⟨e4, e6, rfl, rfl, Labels.Diverge.not_sat ⟨gT, by simp [e4, W], gF,
            by simp [e6, W], rfl, rfl, by decide⟩⟩
        · exact ⟨e5, e6, rfl, rfl, Labels.Diverge.not_sat ⟨gT, by simp [e5, W], gF,
            by simp [e6, W], rfl, rfl, by decide⟩⟩
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd (by decide) hn
      · exact absurd (by decide) hn
      · exact absurd (by decide) hn
      · exact absurd ⟨e3, rfl, rfl⟩ hb
      · exact ⟨6, by decide, c46 _ (.inl rfl)⟩
      · exact ⟨6, by decide, c46 _ (.inr rfl)⟩
      · exact absurd (by decide) hn
  generated j hj := by
    rcases mem_JC hj with rfl | rfl
    · exact .pre (w := e0) (by simp [esC]) rfl
        ⟨fOut, by simp [e0, W, Event.valres, Expr.conj, Expr.holds, Expr.eval, Expr.tt]⟩
    · exact gen_jWE
  inX j hj := by
    rcases mem_JC hj with rfl | rfl <;> decide
  notElided j hj := by
    rcases mem_JC hj with rfl | rfl <;> exact fun h => absurd (elided_C.1 h) (by decide)
  consistent := ⟨fOut, fun j hj => J_holds hj, fun a e ha he => holdsC ha he⟩
  fwdWF := by
    rw [δC]
    refine ⟨fun a ha => ?_, fun a b e ha hb => ?_⟩
    · have : ∀ c d, Relation.TransGen (FwdCtx.edge ⟨[], [(6, 1)]⟩) c d → c = 6 ∧ d = 1 := by
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
  rf_wr w r h := by
    have h' : (w, r) ∈ rfC := h
    simp only [rfC, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    exact ⟨cls_clsB.2 (by decide), cls_clsB.2 (by decide), by decide, by decide⟩
  rf_func w w' r h h' := rfOK_C.2 _ h _ h' rfl
  justified w hw he hn := by
    have hids : ∀ w ∈ XL, clsB esC Event.isEffect w = true → w ≠ 1 → w = 0 ∨ w = 6 := by
      decide
    have hw' := hids w hw (cls_clsB.1 he) (fun h => hn (elided_C.2 h))
    have uniq : ∀ j j', j ∈ JC → j' ∈ JC → j.w.id = j'.w.id → j' = j := by
      intro j j' hj hj' h
      rcases mem_JC hj with rfl | rfl <;> rcases mem_JC hj' with rfl | rfl <;>
        first | rfl | (simp [jWE, jB, pj, e0, e6, W] at h)
    rcases hw' with rfl | rfl
    · exact ⟨pj e0, by simp [xC, JC], rfl,
        fun j' hj' h => uniq _ _ (by simp [JC]) hj' h.symm⟩
    · exact ⟨jWE, by simp [xC, JC], rfl, fun j' hj' h => uniq _ _ (by simp [JC]) hj' h.symm⟩

theorem phi_C : xC.phi esC := by
  refine ⟨fun e h hel => ?_, fun r => ⟨?_, ?_⟩, fOut, P_C, ⟨?_, ?_, ?_⟩⟩
  · rw [elided_C] at hel; subst hel
    rcases h with ⟨r, hr⟩ | ⟨b, hb⟩
    · have : ∀ p ∈ rfC, p.1 ≠ 1 := by decide
      exact this _ hr rfl
    · exact absurd (dp_C hb).1 (by decide)
  · rintro ⟨w, hw⟩
    obtain ⟨-, h₂⟩ := rfOK_C.1 _ hw
    have : ∀ p ∈ rfC, p.2 ∈ XL := by decide
    exact ⟨this _ hw, cls_clsB.2 h₂⟩
  · rintro ⟨hX, hr⟩
    have key : ∀ r ∈ XL, clsB esC Event.isRead r = true → ∃ p ∈ rfC, p.2 = r := by decide
    obtain ⟨p, hp, rfl⟩ := key r hX (cls_clsB.1 hr)
    exact ⟨p.1, hp⟩
  · intro w r ew er h hw hr
    have key : ∀ p ∈ rfC, ∀ ew ∈ esC.events, ∀ er ∈ esC.events, ew.id = p.1 → er.id = p.2 →
        ew.loc.map (·.eval fOut) = er.loc.map (·.eval fOut) ∧
        ew.val.map (·.eval fOut) = er.val.map (·.eval fOut) := by decide
    have := key (w, r) h ew (ev_inv hw).1 er (ev_inv hr).1 (ev_inv hw).2 (ev_inv hr).2
    refine ⟨fun lw lr h₁ h₂ => ?_, fun vw vr h₁ h₂ => ?_⟩
    · have := this.1; rw [h₁, h₂] at this; exact Option.some.inj this
    · have := this.2; rw [h₁, h₂] at this; exact Option.some.inj this
  · intro a e α sz _ he hk
    rcases ev_C a he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hk
  · intro a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂ _ _ _ he₁ _ hk₁
    rcases ev_C _ he₁ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hk₁

/-! ## `RMWTightWE` fails -/

/-- The hypothesis `dep_po_R` took before `RMWFailGuard`: a Write Elision
    across the read of an RMW ends at its write or `⊑`-after it. -/
def RMWTightWE (es : EventStructure) (x : Execution) : Prop :=
  ∀ ent ∈ es.rmw, ∀ q p, (q, p) ∈ x.δ.we → es.poR p ent.r → es.poR ent.r q →
    q = ent.w ∨ es.poR ent.w q

/-- **`RMWTightWE` fails**: `y := 1` is elided across the `CAS`'s read into
    the failure copy of `y := 2`, which is neither its write nor after it. -/
theorem not_rmwTightWE : ¬ RMWTightWE esC xC := fun h => by
  rcases h _ rmw24 6 1 we_mem (po_of (by decide)) (po_of (by decide)) with h | h
  · cases h
  · exact absurd (show (4, 6) ∈ poL from h) (by decide)

/-- **The guarded pair is absent**: `(e_w, e_r)` is in `rmwPairs` under no
    predicate the execution's `P` satisfies with `α = 2`, in particular not
    under `P` itself, so `(y := 1, e_r)` is not in `ppo_sync ; rmw`. -/
theorem not_rmwPairs_P : ¬ esC.rmwPairs (xC.P esC) 4 2 := not_rmwPairs_of P_C

/-! ## `DP ∪ ≼ ⊆ ⊑` -/

theorem locsEval_C : LocsEval esC := fun a e l f he hl => by
  obtain ⟨x, rfl⟩ := gC e (ev_inv he).1 _ hl
  simp [Expr.glob, Expr.eval]

theorem rmwTightR_C : RMWTightR esC xC := by
  refine ⟨fun ent hm a a' ra ha' hpo => ?_, fun ent hm w' rw hw' b b' rb hb' hpo => ?_⟩ <;>
    rw [mem_rmw hm] at hpo ⊢
  · have hpo' : (a, 4) ∈ poL := hpo
    have key : ∀ p ∈ poL, p.2 = 4 → p.1 = 2 ∨ (p.1, 2) ∈ poL ∨ p.1 = 3 := by decide
    rcases key _ hpo' rfl with h | h | h
    · exact .inl h
    · exact .inr h
    · simp only at h; subst h
      rw [remap_C ra] at ha'
      rcases ha' with h | ⟨-, h, -⟩
      · exact absurd h (by decide)
      · exact absurd (cls_clsB.1 h) (by decide)
  · rw [mem_rmw hm] at rw
    rw [remap_C rw] at hw'
    rcases hw' with h | ⟨-, h, -⟩
    · exact absurd h (by decide)
    · exact absurd (cls_clsB.1 h) (by decide)

theorem fwdEntailsImg_C : FwdEntailsImg esC xC := by
  intro s t he
  obtain ⟨rfl, rfl⟩ := edge_C he
  refine ⟨jB, 1, 6, ⟨.inr ⟨we_mem, rfl, rfl, we_16⟩, fun p hp => (by cases hp),
    fun p hp => (by cases hp)⟩, fun j hj ⟨t', rt, hw⟩ f hf => ?_, fun f hf => ?_⟩
  · rw [remap_C rt] at hw
    rcases mem_JC hj with rfl | rfl
    · rcases hw with h | h
      · cases h
      · exact absurd (show (6, 0) ∈ poL from h) (by decide)
    · exact ⟨hf.1, fun p hp => by cases hp⟩
  · exact ⟨hf.1 jWE (by simp [xC, JC]), fun p hp => by cases hp⟩

/-- **`DP ∪ ≼ ⊆ ⊑`** for the execution, by `dep_po_R`. -/
theorem dep_po {a b : EventId} (h : xC.dep esC a b) : xC.poX esC a b :=
  dep_po_R isExecution_C poTrans poIrr rmwTightR_C
    (denote_prog ▸ RMWTightDenote.denote_rmwFailGuard _ prog)
    (fun a b h => by obtain ⟨rfl, rfl⟩ := dp_C h; exact po_of (by decide))
    ⟨fOut, P_C⟩ locsEval_C fwdEntailsImg_C (denote_prog ▸ RMWWFDenote.denote_rmwWF _ prog) h

/-! ## Consistency -/

theorem po_lt : ∀ p ∈ poL, p.1 < p.2 := by decide

theorem poX_lt {a b : EventId} (h : xC.poX esC a b) : a < b := po_lt (a, b) h.2.2

/-- `DP ∪ ≼ ∪ rf` increases the event id. -/
theorem nta_C : xC.NoThinAir esC := by
  have mono : ∀ {R : Rel}, (∀ a b, R a b → a < b) →
      ∀ a b, Relation.TransGen R a b → a < b := by
    intro R hR a b h
    induction h with
    | single h => exact hR _ _ h
    | tail _ h ih => exact Nat.lt_trans ih (hR _ _ h)
  have hedge : ∀ a b, ((xC.dep esC).union xC.rf) a b → a < b := by
    rintro a b (hd | hrf)
    · exact poX_lt (dep_po hd)
    · have key : ∀ p ∈ rfC, p.1 < p.2 := by decide
      exact key _ hrf
  intro a h
  exact Nat.lt_irrefl _ (mono hedge a a h)

theorem sameLoc_06 : ¬ xC.sameLoc esC 0 6 := by
  rintro ⟨ea, eb, la, lb, ha, hb, hla, hlb, heq⟩
  obtain rfl : ea = e0 := Option.some.inj (ha.symm.trans rfl)
  obtain rfl : eb = e6 := Option.some.inj (hb.symm.trans rfl)
  cases hla; cases hlb
  obtain ⟨f, hP, hrf⟩ := phi_C.2.2
  have := heq f hP hrf
  simp [Expr.glob, Expr.eval] at this

theorem coherenceOrderT_C : xC.CoherenceOrderT esC (fun _ _ => False) where
  writes _ _ h := h.elim
  irrefl _ h := h
  trans _ _ _ h := h.elim
  total a b ha hb hwa hwb hne hsl := by
    have key : ∀ a ∈ XL, a ≠ 1 → clsB esC Event.isWrite a = true → a = 0 ∨ a = 6 := by decide
    have na : a ≠ 1 := fun h => ha.2 (elided_C.2 h)
    have nb : b ≠ 1 := fun h => hb.2 (elided_C.2 h)
    rcases key a ha.1 na (cls_clsB.1 hwa) with rfl | rfl <;>
      rcases key b hb.1 nb (cls_clsB.1 hwb) with rfl | rfl
    · exact absurd rfl hne
    · exact absurd hsl sameLoc_06
    · exact absurd (sameLoc_symm hsl) sameLoc_06
    · exact absurd rfl hne
where
  sameLoc_symm {a b : EventId} (h : xC.sameLoc esC a b) : xC.sameLoc esC b a := by
    obtain ⟨ea, eb, la, lb, ha, hb, hla, hlb, heq⟩ := h
    exact ⟨eb, ea, lb, la, hb, ha, hlb, hla, fun f hP hrf => (heq f hP hrf).symm⟩

theorem coherenceT_C : xC.CoherenceT esC (fun _ _ => False) := by
  have hH : ∀ a b, xC.hbT esC a b → (a, b) ∈ esC.po := by
    intro a b h
    refine transGen_mem (fun c d s => ?_) (by decide) h
    rcases s with ⟨⟨-, -, hpo⟩, -⟩ | ⟨hs, -⟩
    · exact hpo
    · have := sw_mem hs
      have hsw : swL esC = [] := by decide
      rw [hsw] at this; cases this
  have hE : ∀ a b, xC.eco (fun _ _ => False) a b → (a, b) ∈ rfC :=
    fun a b h => eco_mem (fun a b h => h) (fun a b h => h.elim)
      (fun a b h => by obtain ⟨w, -, hco⟩ := h; exact hco.elim) (by decide) h
  have hok : ∀ p ∈ esC.po, p.1 ≠ p.2 ∧ (p.2, p.1) ∉ rfC := by decide
  rintro a ⟨b, hab, rfl | hba⟩
  · exact (hok _ (hH _ _ hab)).1 rfl
  · exact (hok _ (hH _ _ hab)).2 (hE _ _ hba)

theorem atomicity_C : xC.Atomicity esC (fun _ _ => False) := by
  rintro r w ⟨-, hw, ent, hm, rfl, rfl, -⟩
  rw [mem_rmw hm] at hw
  exact absurd hw (by decide)

theorem consistentT_C : xC.ConsistentT esC (fun _ => True) :=
  ⟨isExecution_C, phi_C, nta_C, fun _ _ => False, coherenceOrderT_C, coherenceT_C, atomicity_C,
    xC.pscT_of_es esC (esC.scFree_of_all (by decide)) _⟩

/-- **A consistent execution where `RMWTightWE` fails and `DP ∪ ≼ ⊆ ⊑`
    holds**: the event structure of the program, a consistent execution with
    `y := 1` elided across the read of a failing `CAS`, `¬ RMWTightWE`, the
    `CAS`'s pair outside `rmwPairs` under the execution's predicate, and
    `DP ∪ ≼ ⊆ ⊑`. -/
theorem cas_fail_elision :
    denote (fun _ => 0) prog = esC ∧ xC.ConsistentT esC (fun _ => True) ∧
    ((6, 1) : EventId × EventId) ∈ xC.δ.we ∧ ¬ RMWTightWE esC xC ∧
    ¬ esC.rmwPairs (xC.P esC) 4 2 ∧ (∀ a b, xC.dep esC a b → xC.poX esC a b) :=
  ⟨denote_prog, consistentT_C, we_mem, not_rmwTightWE, not_rmwPairs_P, fun _ _ h => dep_po h⟩

end CasFailElision
