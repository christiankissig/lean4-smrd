import Smrd.CoherenceT

/-!
# Deciding the axioms on finite executions

The axioms of `Smrd.Executions`, `Smrd.CoherenceRC11` and `Smrd.CoherenceT`
are stated over `Rel`-valued relations, most of which are computed from the
event structure under semantic predicates. Each axiom is, however, a function
of a few *primitive* relations and sets of an execution: `⊑` within
`X ∪ X_F`, `rf`, `rmw`, the same-location relation, `DP ∪ ≼`, the event
classes and `†`. This module

* names those primitives (`Prims`, read off an execution by `Prims.ofExec`),
  and restates the axioms over them (`Prims.NoThinAir`, `Prims.CoOrder`,
  `Prims.CohWith`, `Prims.Atomicity`); the restatements are the axioms by
  definition (`noThinAir_iff`, `coherenceT_iff`, …);
* decides the restated axioms when the primitives are finite lists
  (`PrimsL`): `PrimsL.ntaB`, `PrimsL.coOrderB`, `PrimsL.cohB`,
  `PrimsL.atomB`, each proved equal to its `Prop` (`ntaB_iff`, `coOrderB_iff`,
  `cohB_iff`, `atomB_iff`).

Transitive closures are computed by breadth-first search (`plusL`) and are
*certified*: `plusOK` checks that the computed successor sets are closed, and
the theorems assume it. It is checked when the axioms are evaluated
(`PrimsL.certB`); a closure that fails it is reported, not used.

It is what the differential test against MoRDor's executions
(`scripts/exec_diff.py`, through the `smrd-ax` executable) evaluates. The
primitives are what MoRDor exports for an execution; the test therefore checks
that MoRDor's executions satisfy the axioms, relative to MoRDor's own `≼`,
`DP`, `rf`, `rmw` and `CO`. Whether MoRDor finds every execution is not
decided: justifications (`Generated`) range over semantic predicates.
-/

namespace AxiomEval

open Execution

/-! ## The axioms over their primitives -/

/-- The primitives the axioms are functions of. -/
structure Prims where
  /-- the events of the execution -/
  X : EvSet
  W : EvSet
  R : EvSet
  F : EvSet
  RelW : EvSet
  RelF : EvSet
  AcqR : EvSet
  AcqF : EvSet
  /-- `†` -/
  el : EvSet
  /-- `⊑` within `X ∪ X_F` -/
  po : Rel
  rf : Rel
  rmw : Rel
  /-- same location -/
  sl : Rel
  /-- `DP ∪ ≼` -/
  dep : Rel
  /-- `SW_ra ≜ rf ∩ (W_rel × R_acq)`, for preserved coherence (`Execution.hbP`) -/
  swRA : Rel

namespace Prims

variable (p : Prims)

def poloc : Rel := fun a b => p.po a b ∧ p.sl a b

def rfRmw : Rel := fun a b => ∃ r, p.rf a r ∧ p.rmw r b

def rs : Rel := fun w w' =>
  p.W w ∧ ∃ w₀, (w₀ = w ∨ p.poloc w w₀) ∧ p.W w₀ ∧ (w' = w₀ ∨ Rel.plus p.rfRmw w₀ w')

def sw : Rel := fun a b =>
  (p.RelW a ∨ p.RelF a) ∧
  ∃ w w' r, (w = a ∨ (p.F a ∧ p.po a w)) ∧ p.rs w w' ∧
    p.rf w' r ∧ p.R r ∧
    (b = r ∨ (p.po r b ∧ p.F b)) ∧
    (p.AcqR b ∨ p.AcqF b)

def fr (co : Rel) : Rel := fun r w' => ∃ w, p.rf w r ∧ co w w'

def eco (co : Rel) : Rel := Rel.plus ((p.rf.union co).union (p.fr co))

/-- `H⁺ ; ECO?` is irreflexive. -/
def CohWith (H co : Rel) : Prop := ∀ a, ¬ ∃ b, Rel.plus H a b ∧ (b = a ∨ p.eco co b a)

/-- `⊑ ∪ SW`, RC11's (`Execution.hb`). -/
def hbBase : Rel := p.po.union p.sw

/-- `⊑ ∪ SW` within `(X ∖ †) ∪ X_F` (`Execution.hbT`). -/
def hbTBase : Rel :=
  Rel.union (fun a b => p.po a b ∧ ¬ p.el a ∧ ¬ p.el b) (fun a b => p.sw a b ∧ ¬ p.el a ∧ ¬ p.el b)

/-- `DP ∪ ≼ ∪ SW` (`Execution.hbV`). -/
def hbVBase : Rel := p.dep.union p.sw

/-- `DP ∪ ≼ ∪ SW_ra` (`Execution.hbP`). -/
def hbPBase : Rel := p.dep.union p.swRA

def Atomicity (co : Rel) : Prop := ∀ r w, p.rmw r w → ¬ ∃ w', p.fr co r w' ∧ co w' w

def NoThinAir : Prop := Rel.Acyclic (p.dep.union p.rf)

/-- A coherence order over the writes of `Y`. -/
def CoOrder (Y : EvSet) (co : Rel) : Prop :=
  (∀ a b, co a b → Y a ∧ Y b ∧ p.W a ∧ p.W b) ∧
  (∀ a, ¬ co a a) ∧
  (∀ a b c, co a b → co b c → co a c) ∧
  (∀ a b, Y a → Y b → p.W a → p.W b → a ≠ b → p.sl a b → co a b ∨ co b a)

/-- The primitives of an execution. -/
def ofExec (es : EventStructure) (x : Execution) : Prims where
  X := x.X
  W := es.cls Event.isWrite
  R := es.cls Event.isRead
  F := es.cls Event.isFence
  RelW := es.cls Event.isRelW
  RelF := es.cls Event.isRelF
  AcqR := es.cls Event.isAcqR
  AcqF := es.cls Event.isAcqF
  el := x.elided
  po := x.poX es
  rf := x.rf
  rmw := x.rmwRel es
  sl := x.sameLoc es
  dep := x.dep es
  swRA := x.swRA es

end Prims

/-! ### The axioms of an execution are those of its primitives -/

section OfExec

variable (es : EventStructure) (x : Execution) (co : Rel)

theorem noThinAir_iff : x.NoThinAir es ↔ (Prims.ofExec es x).NoThinAir := Iff.rfl

theorem coherence_iff : x.Coherence es co ↔ (Prims.ofExec es x).CohWith (Prims.ofExec es x).hbBase co :=
  Iff.rfl

theorem coherenceT_iff : x.CoherenceT es co ↔
    (Prims.ofExec es x).CohWith (Prims.ofExec es x).hbTBase co := Iff.rfl

theorem coherenceV_iff : x.CoherenceV es co ↔
    (Prims.ofExec es x).CohWith (Prims.ofExec es x).hbVBase co := Iff.rfl

theorem coherenceP_iff : x.CoherenceP es co ↔
    (Prims.ofExec es x).CohWith (Prims.ofExec es x).hbPBase co := Iff.rfl

theorem atomicity_iff : x.Atomicity es co ↔ (Prims.ofExec es x).Atomicity co := Iff.rfl

theorem coherenceOrder_iff : x.CoherenceOrder es co ↔ (Prims.ofExec es x).CoOrder x.X co :=
  ⟨fun h => ⟨h.writes, h.irrefl, h.trans, h.total⟩,
   fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩⟩

theorem coherenceOrderT_iff : x.CoherenceOrderT es co ↔ (Prims.ofExec es x).CoOrder (x.XT) co :=
  ⟨fun h => ⟨h.writes, h.irrefl, h.trans, h.total⟩,
   fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩⟩

end OfExec

/-! ## Finite relations -/

abbrev PairL := List (EventId × EventId)

/-- The relation a list of pairs denotes. -/
def relL (L : PairL) : Rel := fun a b => (a, b) ∈ L

/-- The elements of a list, each once. -/
def uniq : List EventId → List EventId
  | [] => []
  | a :: l => let u := uniq l; if a ∈ u then u else a :: u

theorem mem_uniq {l : List EventId} {c : EventId} : c ∈ uniq l ↔ c ∈ l := by
  induction l with
  | nil => simp [uniq]
  | cons a l ih =>
      simp only [uniq]
      split
      · rw [ih, List.mem_cons]
        constructor
        · exact .inr
        · rintro (rfl | h)
          · exact ih.1 ‹_›
          · exact h
      · rw [List.mem_cons, List.mem_cons, ih]

/-- The `R`-successors of `a`. -/
def succL (R : PairL) (a : EventId) : List EventId := (R.filter fun p => p.1 == a).map Prod.snd

theorem mem_succL {R : PairL} {a c : EventId} : c ∈ succL R a ↔ (a, c) ∈ R := by
  unfold succL
  simp only [List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨a', c'⟩, ⟨h, rfl⟩, rfl⟩; exact h
  · intro h; exact ⟨(a, c), ⟨h, rfl⟩, rfl⟩

/-- `L ; M` -/
def compose (L M : PairL) : PairL :=
  L.flatMap fun p => (succL M p.2).map fun c => (p.1, c)

theorem mem_compose {L M : PairL} {a c : EventId} :
    (a, c) ∈ compose L M ↔ ∃ b, (a, b) ∈ L ∧ (b, c) ∈ M := by
  unfold compose
  simp only [List.mem_flatMap, List.mem_map, mem_succL, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a', b⟩, h, c', hc, rfl, rfl⟩; exact ⟨b, h, hc⟩
  · rintro ⟨b, h, hc⟩; exact ⟨(a, b), h, c, hc, rfl, rfl⟩

/-- `L⁻¹` -/
def invL (L : PairL) : PairL := L.map fun p => (p.2, p.1)

theorem mem_invL {L : PairL} {a b : EventId} : (a, b) ∈ invL L ↔ (b, a) ∈ L := by
  unfold invL
  simp only [List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨b', a'⟩, h, rfl, rfl⟩; exact h
  · intro h; exact ⟨(b, a), h, rfl, rfl⟩

/-! ### Certified transitive closure -/

/-- One round of the search: add the successors of `S`. -/
def grow (R : PairL) (S : List EventId) : List EventId :=
  S ++ uniq ((S.flatMap (succL R)).filter fun c => !decide (c ∈ S))

/-- Grow `S` until it stops growing, at most `n` rounds. -/
def reach (R : PairL) : Nat → List EventId → List EventId
  | 0, S => S
  | n + 1, S =>
      let S' := grow R S
      if S'.length = S.length then S else reach R n S'

/-- The events `R⁺`-reachable from `a`, if the search ran long enough. -/
def reachFrom (R : PairL) (a : EventId) : List EventId :=
  reach R (uniq (R.map Prod.fst ++ R.map Prod.snd)).length.succ (uniq (succL R a))

/-- `S` holds the successors of `a` and is closed under successors. -/
def closedAt (R : PairL) (a : EventId) (S : List EventId) : Bool :=
  (succL R a).all (fun c => decide (c ∈ S)) && S.all fun b => (succL R b).all fun c => decide (c ∈ S)

/-- The sources of `R`. -/
def srcs (R : PairL) : List EventId := uniq (R.map Prod.fst)

/-- `R⁺`, computed. -/
def plusL (R : PairL) : PairL := (srcs R).flatMap fun a => (reachFrom R a).map fun c => (a, c)

/-- The certificate: every search reached a closed set. -/
def plusOK (R : PairL) : Bool := (srcs R).all fun a => closedAt R a (reachFrom R a)

theorem grow_sound {R : PairL} {a : EventId} {S : List EventId}
    (h : ∀ c ∈ S, Relation.TransGen (relL R) a c) : ∀ c ∈ grow R S, Relation.TransGen (relL R) a c := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · exact h c hc
  · obtain ⟨b, hb, hbc⟩ := List.mem_flatMap.1 (List.mem_filter.1 (mem_uniq.1 hc)).1
    exact .tail (h b hb) (mem_succL.1 hbc)

theorem reach_sound {R : PairL} {a : EventId} {n : Nat} {S : List EventId}
    (h : ∀ c ∈ S, Relation.TransGen (relL R) a c) : ∀ c ∈ reach R n S, Relation.TransGen (relL R) a c := by
  induction n generalizing S with
  | zero => exact h
  | succ n ih =>
      simp only [reach]
      split
      · exact h
      · exact ih (grow_sound h)

theorem reachFrom_sound {R : PairL} {a c : EventId} (h : c ∈ reachFrom R a) :
    Relation.TransGen (relL R) a c :=
  reach_sound (fun _ hc => .single (mem_succL.1 (mem_uniq.1 hc))) c h

theorem closedAt_complete {R : PairL} {a : EventId} {S : List EventId} (hc : closedAt R a S = true)
    {c : EventId} (h : Relation.TransGen (relL R) a c) : c ∈ S := by
  simp only [closedAt, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  induction h with
  | single h => exact hc.1 _ (mem_succL.2 h)
  | tail _ h ih => exact hc.2 _ ih _ (mem_succL.2 h)

theorem transGen_src {R : PairL} {a c : EventId} (h : Relation.TransGen (relL R) a c) :
    a ∈ srcs R := by
  induction h with
  | single h => exact mem_uniq.2 (List.mem_map.2 ⟨_, h, rfl⟩)
  | tail _ _ ih => exact ih

/-- **The computed closure is `R⁺`**, given the certificate. -/
theorem mem_plusL {R : PairL} (hok : plusOK R = true) {a c : EventId} :
    (a, c) ∈ plusL R ↔ Relation.TransGen (relL R) a c := by
  unfold plusL
  simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a', _, c', hc, rfl, rfl⟩
    exact reachFrom_sound hc
  · intro h
    have ha := transGen_src h
    refine ⟨a, ha, c, ?_, rfl, rfl⟩
    exact closedAt_complete (List.all_eq_true.1 hok a ha) h

theorem transGen_congr {R S : Rel} (h : ∀ a b, R a b ↔ S a b) {a b : EventId} :
    Relation.TransGen R a b ↔ Relation.TransGen S a b :=
  ⟨transGen_mono fun _ _ hab => (h _ _).1 hab, transGen_mono fun _ _ hab => (h _ _).2 hab⟩

/-- `R⁺` of a relation that a list denotes. -/
theorem plus_iff {R : Rel} {L : PairL} (hL : ∀ a b, R a b ↔ (a, b) ∈ L) (hok : plusOK L = true)
    {a b : EventId} : Rel.plus R a b ↔ (a, b) ∈ plusL L :=
  (transGen_congr hL).trans (mem_plusL hok).symm

/-! ## The axioms, decided -/

/-- Finite primitives: sets as lists of event ids, relations as lists of pairs.
    `X` lists the events of the execution, `el` those of `†`. -/
structure PrimsL where
  X : List EventId
  W : List EventId
  R : List EventId
  F : List EventId
  RelW : List EventId
  RelF : List EventId
  AcqR : List EventId
  AcqF : List EventId
  el : List EventId
  po : PairL
  rf : PairL
  rmw : PairL
  sl : PairL
  dep : PairL
  co : PairL
  deriving Repr

namespace PrimsL

variable (q : PrimsL)

/-- `SW_ra ≜ rf ∩ (W_rel × R_acq)` -/
def swRAL : PairL := q.rf.filter fun p => decide (p.1 ∈ q.RelW) && decide (p.2 ∈ q.AcqR)

/-- The primitives the lists denote. -/
def toPrims : Prims where
  X := fun a => a ∈ q.X
  W := fun a => a ∈ q.W
  R := fun a => a ∈ q.R
  F := fun a => a ∈ q.F
  RelW := fun a => a ∈ q.RelW
  RelF := fun a => a ∈ q.RelF
  AcqR := fun a => a ∈ q.AcqR
  AcqF := fun a => a ∈ q.AcqF
  el := fun a => a ∈ q.el
  po := relL q.po
  rf := relL q.rf
  rmw := relL q.rmw
  sl := relL q.sl
  dep := relL q.dep
  swRA := relL q.swRAL

/-! ### Release sequences and synchronisation -/

def polocL : PairL := q.po.filter fun p => decide (p ∈ q.sl)

def rfRmwL : PairL := compose q.rf q.rmw

/-- The heads `w` of a release sequence that `sw a _` may start at. -/
def wCands (a : EventId) : List EventId :=
  a :: (if decide (a ∈ q.F) then succL q.po a else [])

/-- The ends of the release sequences headed by `w`. -/
def rsSucc (w : EventId) : List EventId :=
  if decide (w ∈ q.W) then
    ((w :: succL q.polocL w).filter fun w₀ => decide (w₀ ∈ q.W)).flatMap
      fun w₀ => w₀ :: succL (plusL q.rfRmwL) w₀
  else []

def swB (a b : EventId) : Bool :=
  (decide (a ∈ q.RelW) || decide (a ∈ q.RelF)) && (decide (b ∈ q.AcqR) || decide (b ∈ q.AcqF)) &&
    (q.wCands a).any fun w => (q.rsSucc w).any fun w' => (succL q.rf w').any fun r =>
      decide (r ∈ q.R) && (b == r || (decide ((r, b) ∈ q.po) && decide (b ∈ q.F)))

/-- The events `sw` may relate. -/
def cand : List EventId := uniq (q.po.map Prod.fst ++ q.po.map Prod.snd ++ q.rf.map Prod.fst ++
  q.rf.map Prod.snd)

def swL : PairL := q.cand.flatMap fun a => (q.cand.filter (q.swB a)).map fun b => (a, b)

def notEl (p : EventId × EventId) : Bool := !decide (p.1 ∈ q.el) && !decide (p.2 ∈ q.el)

def hbL : PairL := q.po ++ q.swL
def hbTL : PairL := q.po.filter q.notEl ++ q.swL.filter q.notEl
def hbVL : PairL := q.dep ++ q.swL
def hbPL : PairL := q.dep ++ q.swRAL

def frL : PairL := compose (invL q.rf) q.co
def ecoL : PairL := q.rf ++ q.co ++ q.frL
def ntaL : PairL := q.dep ++ q.rf

/-- `H⁺ ; ECO?` irreflexive, `H` given as a list. -/
def cohB (H : PairL) : Bool :=
  (plusL H).all fun p => p.1 != p.2 && !decide ((p.2, p.1) ∈ plusL q.ecoL)

def atomB : Bool := q.rmw.all fun p => !(q.frL.any fun f => f.1 == p.1 && decide ((f.2, p.2) ∈ q.co))

def ntaB : Bool := (plusL q.ntaL).all fun p => p.1 != p.2

/-- A coherence order over the writes of `Ys`. -/
def coOrderB (Ys : List EventId) : Bool :=
  (q.co.all fun p => decide (p.1 ∈ Ys) && decide (p.2 ∈ Ys) && decide (p.1 ∈ q.W) &&
    decide (p.2 ∈ q.W)) &&
  (q.co.all fun p => p.1 != p.2) &&
  (q.co.all fun p => q.co.all fun p' => p.2 != p'.1 || decide ((p.1, p'.2) ∈ q.co)) &&
  (Ys.all fun a => Ys.all fun b =>
    !(decide (a ∈ q.W) && decide (b ∈ q.W) && a != b && decide ((a, b) ∈ q.sl)) ||
      decide ((a, b) ∈ q.co) || decide ((b, a) ∈ q.co))

/-- `X ∖ †` -/
def XT : List EventId := q.X.filter fun a => !decide (a ∈ q.el)

/-- The certificates of the closures computed. -/
def certB : Bool :=
  plusOK q.rfRmwL && plusOK q.hbL && plusOK q.hbTL && plusOK q.hbVL && plusOK q.hbPL &&
    plusOK q.ecoL && plusOK q.ntaL

/-! ### Correctness -/

variable {q}

theorem mem_wCands {a w : EventId} :
    w ∈ q.wCands a ↔ w = a ∨ (a ∈ q.F ∧ (a, w) ∈ q.po) := by
  unfold wCands
  rw [List.mem_cons]
  by_cases h : a ∈ q.F <;> simp [h, mem_succL]

theorem rfRmw_iff {a b : EventId} : q.toPrims.rfRmw a b ↔ (a, b) ∈ q.rfRmwL := by
  unfold Prims.rfRmw rfRmwL
  rw [mem_compose]; rfl

theorem mem_rsSucc (hok : plusOK q.rfRmwL = true) {w w' : EventId} :
    w' ∈ q.rsSucc w ↔ q.toPrims.rs w w' := by
  have hplus : ∀ a b, Rel.plus q.toPrims.rfRmw a b ↔ (a, b) ∈ plusL q.rfRmwL :=
    fun _ _ => plus_iff (fun _ _ => rfRmw_iff) hok
  unfold rsSucc Prims.rs Prims.poloc
  by_cases hw : w ∈ q.W
  · simp only [hw, decide_true, if_true, List.mem_flatMap, List.mem_filter, List.mem_cons,
      mem_succL, decide_eq_true_eq, hplus]
    simp only [polocL, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨w₀, ⟨h₀, hW⟩, h'⟩
      exact ⟨hw, w₀, h₀.imp id fun h => h, hW, h'⟩
    · rintro ⟨-, w₀, h₀, hW, h'⟩
      exact ⟨w₀, ⟨h₀.imp id fun h => h, hW⟩, h'⟩
  · simp only [hw, decide_false, Bool.false_eq_true, if_false, List.not_mem_nil, false_iff]
    exact fun h => hw h.1

theorem swB_iff (hok : plusOK q.rfRmwL = true) {a b : EventId} :
    q.swB a b = true ↔ q.toPrims.sw a b := by
  unfold swB Prims.sw
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq,
    mem_wCands, mem_rsSucc hok, mem_succL]
  constructor
  · rintro ⟨⟨hrel, hacq⟩, w, hw, w', hrs, r, hrf, hR, hb⟩
    exact ⟨hrel, w, w', r, hw, hrs, hrf, hR, hb, hacq⟩
  · rintro ⟨hrel, w, w', r, hw, hrs, hrf, hR, hb, hacq⟩
    exact ⟨⟨hrel, hacq⟩, w, hw, w', hrs, r, hrf, hR, hb⟩

theorem cand_of {a : EventId}
    (h : (∃ b, (a, b) ∈ q.po) ∨ (∃ b, (b, a) ∈ q.po) ∨ (∃ b, (a, b) ∈ q.rf) ∨ (∃ b, (b, a) ∈ q.rf)) :
    a ∈ q.cand := by
  unfold cand
  rw [mem_uniq]
  simp only [List.mem_append, List.mem_map]
  rcases h with ⟨b, h⟩ | ⟨b, h⟩ | ⟨b, h⟩ | ⟨b, h⟩
  · exact .inl (.inl (.inl ⟨(a, b), h, rfl⟩))
  · exact .inl (.inl (.inr ⟨(b, a), h, rfl⟩))
  · exact .inl (.inr ⟨(a, b), h, rfl⟩)
  · exact .inr ⟨(b, a), h, rfl⟩

theorem transGen_first {R : Rel} {a c : EventId} (h : Relation.TransGen R a c) : ∃ b, R a b := by
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ _ ih => exact ih

theorem sw_cand {a b : EventId} (h : q.toPrims.sw a b) :
    a ∈ q.cand ∧ b ∈ q.cand := by
  obtain ⟨-, w, w', r, hw, ⟨-, w₀, h₀, -, h'⟩, hrf, -, hb, -⟩ := h
  have hrf' : (w', r) ∈ q.rf := hrf
  constructor
  · rcases hw with rfl | ⟨-, hpo⟩
    · rcases h₀ with rfl | hpl
      · rcases h' with rfl | hp
        · exact cand_of (.inr (.inr (.inl ⟨_, hrf'⟩)))
        · obtain ⟨c, r', hr', -⟩ := transGen_first hp
          exact cand_of (.inr (.inr (.inl ⟨_, (hr' : (w₀, r') ∈ q.rf)⟩)))
      · exact cand_of (.inl ⟨_, hpl.1⟩)
    · exact cand_of (.inl ⟨_, hpo⟩)
  · rcases hb with rfl | ⟨hpo, -⟩
    · exact cand_of (.inr (.inr (.inr ⟨_, hrf'⟩)))
    · exact cand_of (.inr (.inl ⟨_, hpo⟩))

theorem mem_swL (hok : plusOK q.rfRmwL = true) {a b : EventId} :
    (a, b) ∈ q.swL ↔ q.toPrims.sw a b := by
  unfold swL
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨a', -, b', ⟨-, h⟩, rfl, rfl⟩
    exact (swB_iff hok).1 h
  · intro h
    have hc := sw_cand h
    exact ⟨a, hc.1, b, ⟨hc.2, (swB_iff hok).2 h⟩, rfl, rfl⟩

theorem hbBase_iff (hok : plusOK q.rfRmwL = true) {a b : EventId} :
    q.toPrims.hbBase a b ↔ (a, b) ∈ q.hbL := by
  unfold Prims.hbBase hbL Rel.union
  rw [List.mem_append, mem_swL hok]; rfl

theorem hbTBase_iff (hok : plusOK q.rfRmwL = true) {a b : EventId} :
    q.toPrims.hbTBase a b ↔ (a, b) ∈ q.hbTL := by
  unfold Prims.hbTBase hbTL Rel.union notEl
  simp only [List.mem_append, List.mem_filter, mem_swL hok, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]
  rfl

theorem hbVBase_iff (hok : plusOK q.rfRmwL = true) {a b : EventId} :
    q.toPrims.hbVBase a b ↔ (a, b) ∈ q.hbVL := by
  unfold Prims.hbVBase hbVL Rel.union
  rw [List.mem_append, mem_swL hok]; rfl

theorem hbPBase_iff {a b : EventId} : q.toPrims.hbPBase a b ↔ (a, b) ∈ q.hbPL := by
  unfold Prims.hbPBase hbPL Rel.union
  rw [List.mem_append]; rfl

theorem eco1_iff {a b : EventId} :
    ((q.toPrims.rf.union (relL q.co)).union (q.toPrims.fr (relL q.co))) a b ↔ (a, b) ∈ q.ecoL := by
  unfold ecoL Rel.union Prims.fr frL
  rw [List.mem_append, List.mem_append, mem_compose]
  simp only [mem_invL]; rfl

theorem fr_iff {a b : EventId} : q.toPrims.fr (relL q.co) a b ↔ (a, b) ∈ q.frL := by
  unfold Prims.fr frL
  rw [mem_compose]; simp only [mem_invL]; rfl

/-- **Coherence over `H`, decided.** -/
theorem cohB_iff {H : Rel} {HL : PairL} (hH : ∀ a b, H a b ↔ (a, b) ∈ HL)
    (hokH : plusOK HL = true) (hokE : plusOK q.ecoL = true) :
    q.cohB HL = true ↔ q.toPrims.CohWith H (relL q.co) := by
  have heco : ∀ a b, q.toPrims.eco (relL q.co) a b ↔ (a, b) ∈ plusL q.ecoL :=
    fun _ _ => plus_iff (fun _ _ => eco1_iff) hokE
  unfold cohB Prims.CohWith
  simp only [List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · rintro h a ⟨b, hab, hb⟩
    have := h (a, b) ((plus_iff hH hokH).1 hab)
    rcases hb with rfl | hb
    · exact this.1 rfl
    · exact this.2 ((heco _ _).1 hb)
  · rintro h ⟨a, b⟩ hab
    have hab := (plus_iff hH hokH).2 hab
    exact ⟨fun e => h a ⟨b, hab, .inl e.symm⟩, fun e => h a ⟨b, hab, .inr ((heco _ _).2 e)⟩⟩

/-- **Atomicity, decided.** -/
theorem atomB_iff : q.atomB = true ↔ q.toPrims.Atomicity (relL q.co) := by
  unfold atomB Prims.Atomicity
  simp only [List.all_eq_true, Bool.not_eq_true', List.any_eq_false, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  constructor
  · rintro h r w hrw ⟨w', hfr, hco⟩
    exact h (r, w) hrw (r, w') (fr_iff.1 hfr) ⟨rfl, hco⟩
  · rintro h ⟨r, w⟩ hrw ⟨r', w'⟩ hfr ⟨hr, hco⟩
    obtain rfl : r' = r := hr
    exact h r' w hrw ⟨w', fr_iff.2 hfr, hco⟩

/-- **No-Thin-Air, decided.** -/
theorem ntaB_iff (hok : plusOK q.ntaL = true) : q.ntaB = true ↔ q.toPrims.NoThinAir := by
  have hL : ∀ a b, (q.toPrims.dep.union q.toPrims.rf) a b ↔ (a, b) ∈ q.ntaL := by
    intro a b; unfold ntaL Rel.union; rw [List.mem_append]; rfl
  unfold ntaB Prims.NoThinAir Rel.Acyclic
  simp only [List.all_eq_true, bne_iff_ne, ne_eq]
  constructor
  · intro h a ha
    exact h (a, a) ((plus_iff hL hok).1 ha) rfl
  · rintro h ⟨a, b⟩ hab hab'
    obtain rfl : a = b := hab'
    exact h a ((plus_iff hL hok).2 hab)

/-- **A coherence order over the writes of `Ys`, decided.** -/
theorem coOrderB_iff {Ys : List EventId} :
    q.coOrderB Ys = true ↔ q.toPrims.CoOrder (fun a => a ∈ Ys) (relL q.co) := by
  unfold coOrderB Prims.CoOrder
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    bne_eq_false_iff_eq]
  constructor
  · rintro ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩
    refine ⟨fun a b hab => ?_, fun a haa => h₂ (a, a) haa rfl, fun a b c hab hbc => ?_,
      fun a b ha hb hWa hWb hne hsl => ?_⟩
    · obtain ⟨⟨⟨ha, hb⟩, hWa⟩, hWb⟩ := h₁ (a, b) hab
      exact ⟨ha, hb, hWa, hWb⟩
    · rcases h₃ (a, b) hab (b, c) hbc with h | h
      · exact absurd rfl h
      · exact h
    · rcases h₄ a ha b hb with ((((h | h) | h) | h) | h) | h
      · exact absurd hWa h
      · exact absurd hWb h
      · exact absurd h hne
      · exact absurd hsl h
      · exact .inl h
      · exact .inr h
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    refine ⟨⟨⟨fun p hp => ?_, fun p hp he => h₂ p.1 (by
      obtain ⟨a, b⟩ := p; simp only at he; subst he; exact hp)⟩, fun p hp p' hp' => ?_⟩,
      fun a ha b hb => ?_⟩
    · obtain ⟨ha, hb, hWa, hWb⟩ := h₁ p.1 p.2 hp
      exact ⟨⟨⟨ha, hb⟩, hWa⟩, hWb⟩
    · by_cases he : p.2 = p'.1
      · exact .inr (h₃ p.1 p.2 p'.2 hp (he ▸ hp'))
      · exact .inl he
    · by_cases hWa : a ∈ q.W
      · by_cases hWb : b ∈ q.W
        · by_cases hne : a = b
          · exact .inl (.inl (.inl (.inr hne)))
          · by_cases hsl : (a, b) ∈ q.sl
            · rcases h₄ a b ha hb hWa hWb hne hsl with h | h
              · exact .inl (.inr h)
              · exact .inr h
            · exact .inl (.inl (.inr hsl))
        · exact .inl (.inl (.inl (.inl (.inr hWb))))
      · exact .inl (.inl (.inl (.inl (.inl hWa))))

/-! ### The axioms of an execution, decided -/

/-- The lists are the primitives of the execution: its events, classes, `†`,
    `⊑` within `X ∪ X_F`, `rf`, `rmw`, same location, and `DP ∪ ≼`. -/
def Agrees (es : EventStructure) (x : Execution) (q : PrimsL) : Prop :=
  Prims.ofExec es x = q.toPrims

theorem agrees_of_iff {es : EventStructure} {x : Execution}
    (hX : ∀ a, x.X a ↔ a ∈ q.X)
    (hW : ∀ a, es.cls Event.isWrite a ↔ a ∈ q.W) (hR : ∀ a, es.cls Event.isRead a ↔ a ∈ q.R)
    (hF : ∀ a, es.cls Event.isFence a ↔ a ∈ q.F)
    (hRelW : ∀ a, es.cls Event.isRelW a ↔ a ∈ q.RelW)
    (hRelF : ∀ a, es.cls Event.isRelF a ↔ a ∈ q.RelF)
    (hAcqR : ∀ a, es.cls Event.isAcqR a ↔ a ∈ q.AcqR)
    (hAcqF : ∀ a, es.cls Event.isAcqF a ↔ a ∈ q.AcqF)
    (hel : ∀ a, x.elided a ↔ a ∈ q.el)
    (hpo : ∀ a b, x.poX es a b ↔ (a, b) ∈ q.po) (hrf : ∀ a b, x.rf a b ↔ (a, b) ∈ q.rf)
    (hrmw : ∀ a b, x.rmwRel es a b ↔ (a, b) ∈ q.rmw)
    (hsl : ∀ a b, x.sameLoc es a b ↔ (a, b) ∈ q.sl)
    (hdep : ∀ a b, x.dep es a b ↔ (a, b) ∈ q.dep) : Agrees es x q := by
  have hswRA : ∀ a b, x.swRA es a b ↔ (a, b) ∈ q.swRAL := by
    intro a b
    unfold swRA swRAL
    rw [List.mem_filter, hrf, hRelW, hAcqR]
    simp
  have s : ∀ {S : EvSet} {L : List EventId}, (∀ a, S a ↔ a ∈ L) → S = fun a => a ∈ L :=
    fun h => funext fun a => propext (h a)
  have r : ∀ {S : Rel} {L : PairL}, (∀ a b, S a b ↔ (a, b) ∈ L) → S = relL L :=
    fun h => funext fun a => funext fun b => propext (h a b)
  unfold Agrees Prims.ofExec toPrims
  rw [s hX, s hW, s hR, s hF, s hRelW, s hRelF, s hAcqR, s hAcqF, s hel, r hpo, r hrf, r hrmw,
    r hsl, r hdep, r hswRA]

variable {es : EventStructure} {x : Execution}

theorem noThinAir_decide (h : Agrees es x q) (hok : plusOK q.ntaL = true) :
    x.NoThinAir es ↔ q.ntaB = true := by
  rw [noThinAir_iff, h, ntaB_iff hok]

theorem coherenceT_decide (h : Agrees es x q) (hok : q.certB = true) :
    x.CoherenceT es (relL q.co) ↔ q.cohB q.hbTL = true := by
  simp only [certB, Bool.and_eq_true] at hok
  rw [coherenceT_iff, h, cohB_iff (fun _ _ => hbTBase_iff hok.1.1.1.1.1.1) hok.1.1.1.1.2 hok.1.2]

theorem coherence_decide (h : Agrees es x q) (hok : q.certB = true) :
    x.Coherence es (relL q.co) ↔ q.cohB q.hbL = true := by
  simp only [certB, Bool.and_eq_true] at hok
  rw [coherence_iff, h, cohB_iff (fun _ _ => hbBase_iff hok.1.1.1.1.1.1) hok.1.1.1.1.1.2 hok.1.2]

theorem coherenceV_decide (h : Agrees es x q) (hok : q.certB = true) :
    x.CoherenceV es (relL q.co) ↔ q.cohB q.hbVL = true := by
  simp only [certB, Bool.and_eq_true] at hok
  rw [coherenceV_iff, h, cohB_iff (fun _ _ => hbVBase_iff hok.1.1.1.1.1.1) hok.1.1.1.2 hok.1.2]

theorem coherenceP_decide (h : Agrees es x q) (hok : q.certB = true) :
    x.CoherenceP es (relL q.co) ↔ q.cohB q.hbPL = true := by
  simp only [certB, Bool.and_eq_true] at hok
  rw [coherenceP_iff, h, cohB_iff (fun _ _ => hbPBase_iff) hok.1.1.2 hok.1.2]

theorem atomicity_decide (h : Agrees es x q) :
    x.Atomicity es (relL q.co) ↔ q.atomB = true := by
  rw [atomicity_iff, h, atomB_iff]

theorem coherenceOrderT_decide (h : Agrees es x q) :
    x.CoherenceOrderT es (relL q.co) ↔ q.coOrderB q.XT = true := by
  have hXT : x.XT = fun a => a ∈ q.XT := by
    funext a
    have hX : x.X = fun a => a ∈ q.X := congrArg Prims.X h
    have hel : x.elided = fun a => a ∈ q.el := congrArg Prims.el h
    unfold Execution.XT PrimsL.XT
    rw [hX, hel]
    simp
  rw [coherenceOrderT_iff, hXT, h, coOrderB_iff]

theorem coherenceOrder_decide (h : Agrees es x q) :
    x.CoherenceOrder es (relL q.co) ↔ q.coOrderB q.X = true := by
  have hX : x.X = fun a => a ∈ q.X := congrArg Prims.X h
  rw [coherenceOrder_iff, hX, h, coOrderB_iff]

/-- **`CoherentT` and `ConsistentT`'s axioms, from a witness.** If the lists are
    the primitives of `x` and the decided checks pass for the coherence order
    `co`, then `x` satisfies No-Thin-Air and `CoherentT` (with `co` as the
    witness). -/
theorem axioms_of_checks (h : Agrees es x q) (hok : q.certB = true)
    (hnta : q.ntaB = true) (hco : q.coOrderB q.XT = true) (hcoh : q.cohB q.hbTL = true)
    (hat : q.atomB = true) : x.NoThinAir es ∧ x.CoherentT es := by
  have hok' := hok
  simp only [certB, Bool.and_eq_true] at hok'
  exact ⟨(noThinAir_decide h hok'.2).2 hnta,
    ⟨relL q.co, (coherenceOrderT_decide h).2 hco, (coherenceT_decide h hok).2 hcoh,
      (atomicity_decide h).2 hat⟩⟩

end PrimsL

end AxiomEval

/-! ## Examples -/

namespace AxiomEval.Examples

open PrimsL

/-- `x := 0; y := 0; (x := 1; y :=_rel 1 ∥ r1 :=_acq y; r2 := x)` with
    `r1 = 1 ∧ r2 = 0`: events `5: x := 0`, `6: y := 0`, `1: x := 1`,
    `2: y :=_rel 1`, `3: r1 :=_acq y`, `4: r2 := x`. -/
def mp (r2From : EventId) : PrimsL where
  X := [1, 2, 3, 4, 5, 6]
  W := [1, 2, 5, 6]
  R := [3, 4]
  F := []
  RelW := [2]
  RelF := []
  AcqR := [3]
  AcqF := []
  el := []
  po := [(5, 6), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4), (1, 2), (3, 4)]
  rf := [(2, 3), (r2From, 4)]
  rmw := []
  sl := [(1, 5), (5, 1), (2, 6), (6, 2)]
  dep := [(5, 6), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4), (1, 2), (3, 4)]
  co := [(5, 1), (6, 2)]

/-- RC11 forbids `r2 = 0` after the acquire read the release write. -/
example : (mp 5).certB = true ∧ (mp 5).cohB (mp 5).hbTL = false := by decide +kernel

/-- It allows `r2 = 1`. -/
example : (mp 1).certB = true ∧ (mp 1).cohB (mp 1).hbTL = true ∧ (mp 1).ntaB = true ∧
    (mp 1).coOrderB (mp 1).XT = true ∧ (mp 1).atomB = true := by decide +kernel

/-- A dependency cycle through `rf`: `1: r1 := x`, `2: y := r1`, `3: r2 := y`,
    `4: x := r2`, reading `1 ← 4` and `3 ← 2`. -/
def lbDep : PrimsL where
  X := [1, 2, 3, 4]
  W := [2, 4]
  R := [1, 3]
  F := []
  RelW := []
  RelF := []
  AcqR := []
  AcqF := []
  el := []
  po := [(1, 2), (3, 4)]
  rf := [(4, 1), (2, 3)]
  rmw := []
  sl := []
  dep := [(1, 2), (3, 4)]
  co := []

example : lbDep.certB = true ∧ lbDep.ntaB = false := by decide +kernel

end AxiomEval.Examples
