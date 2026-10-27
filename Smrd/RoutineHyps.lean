import Smrd.Fresh
import Smrd.PpoTail

/-!
# Routine Facts about `⟨P⟩_n` and `φ`

Facts that clients of the frozen execution (coherence through conditions (i)
and (ii), `coherenceT_of_coherenceV`) take as hypotheses, discharged here for
the event structures `denote n P` generates and for executions satisfying `φ`,
where they hold; where they do not, a counterexample.

* **Program order** (`denote_po_trans`, `denote_po_irrefl`): `⊑` of `⟨P⟩_n` is
  a strict order, for every program, with the join of parallel composition
  (`EventStructure.join`). The invariant `PoOK` is closed under the
  combinators once the ids are distinct (`denote_ids_nodup`).
* **`rf` and locations** (`Execution.rfLoc`, `Execution.sameLoc_trans`, in
  `Smrd.CoherenceRC11`): `sameLoc` compares locations under `P ∧ φ_rf` as
  partial values, so it contains `rf` and is transitive outright. Where the
  locations evaluate under every model of `P ∧ φ_rf` it is `≡_{P ∧ φ_rf}`
  (`sameLoc_iff_equivUnder`).
* **Locations that evaluate** (`denote_totalLocs`): a location expression
  that is a value or a symbol evaluates under every valuation (`Expr.Total`).
  Arithmetic may fail, on a division by zero or an ill-typed operand, under
  every model of `P ∧ φ_rf` (`*(1 / 0)`); `⟨P⟩_n` has `Total` locations where
  the program copies pointers rather than computing them (`Stmt.PtrWF`).
* **A location model** (`locModel_of_sat`, `locModel_of_totalLocs`,
  `locModel_of_denote`): the frozen `P` entails the justifications'
  predicates and `ψ_δ` of the shared context (`Pm_of_P`); a model of it, of
  the value restrictions of `X` and of `φ_rf`, under which the locations of
  `X` evaluate, is one. `φ` gives neither: its witness need not satisfy
  `valres` (`locModel_of_phi_false_valres`), and a location may evaluate under
  no valuation (`locModel_of_phi_false_loc`).
-/

namespace EventStructure

/-! ## Program order of `⟨P⟩_n` is a strict order -/

/-- `⊑` relates events of the structure, and, once the ids are distinct, is
    transitive and irreflexive. -/
def PoOK (k : EventStructure) : Prop :=
  (∀ a b, (a, b) ∈ k.po → a ∈ k.ids ∧ b ∈ k.ids) ∧
  (k.ids.Nodup → (∀ a b c, (a, b) ∈ k.po → (b, c) ∈ k.po → (a, c) ∈ k.po) ∧
    ∀ a, (a, a) ∉ k.po)

theorem mem_po_prefix {e : Event} {k : EventStructure} {a b : EventId} :
    (a, b) ∈ («prefix» e k).po ↔ (a = e.id ∧ b ∈ k.ids) ∨ (a, b) ∈ k.po := by
  simp only [«prefix», ids, List.mem_append, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro (⟨e', he', rfl, rfl⟩ | h)
    · exact .inl ⟨rfl, e', he', rfl⟩
    · exact .inr h
  · rintro (⟨rfl, e', he', rfl⟩ | h)
    · exact .inl ⟨e', he', rfl, rfl⟩
    · exact .inr h

theorem mem_po_plus {k₁ k₂ : EventStructure} {a b : EventId} :
    (a, b) ∈ (k₁.plus k₂).po ↔ (a, b) ∈ k₁.po ∨ (a, b) ∈ k₂.po := by
  simp [plus]

theorem mem_po_join {k₁ k₂ : EventStructure} {a b : EventId} :
    (a, b) ∈ (k₁.join k₂).po ↔ (a, b) ∈ k₁.po ∨ (a, b) ∈ k₂.po ∨ (a ∈ k₁.ids ∧ b ∈ k₂.ids) := by
  simp only [join, List.mem_append, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ((h | h) | ⟨a', ha', b', hb', rfl, rfl⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨ha', hb'⟩)
  · rintro (h | h | ⟨ha, hb⟩)
    · exact .inl (.inl h)
    · exact .inl (.inr h)
    · exact .inr ⟨a, ha, b, hb, rfl, rfl⟩

theorem not_mem_of_disj {l₁ l₂ : List EventId} (h : (l₁ ++ l₂).Nodup) {a : EventId}
    (h₁ : a ∈ l₁) (h₂ : a ∈ l₂) : False :=
  (List.nodup_append.1 h).2.2 a h₁ a h₂ rfl

theorem poOK_inv : _root_.ESInv PoOK where
  empty := ⟨fun _ _ h => by simp [empty] at h, fun _ => ⟨fun _ _ _ h => by simp [empty] at h,
    fun _ h => by simp [empty] at h⟩⟩
  «prefix» e k hk := by
    obtain ⟨hin, hk⟩ := hk
    refine ⟨fun a b h => ?_, fun hnd => ?_⟩
    · rcases mem_po_prefix.1 h with ⟨rfl, hb⟩ | h
      · simp [hb]
      · simp [(hin a b h).1, (hin a b h).2]
    · simp only [ids_prefix, List.nodup_cons] at hnd
      obtain ⟨hnot, hnd⟩ := hnd
      obtain ⟨htr, hirr⟩ := hk hnd
      refine ⟨fun a b c hab hbc => ?_, fun a h => ?_⟩
      · rcases mem_po_prefix.1 hab with ⟨rfl, hb⟩ | hab <;>
          rcases mem_po_prefix.1 hbc with ⟨rfl, hc⟩ | hbc
        · exact absurd hb hnot
        · exact mem_po_prefix.2 (.inl ⟨rfl, (hin _ _ hbc).2⟩)
        · exact absurd (hin _ _ hab).2 hnot
        · exact mem_po_prefix.2 (.inr (htr _ _ _ hab hbc))
      · rcases mem_po_prefix.1 h with ⟨rfl, hb⟩ | h
        · exact hnot hb
        · exact hirr a h
  plus k k' hk hk' := by
    obtain ⟨hin, hk⟩ := hk
    obtain ⟨hin', hk'⟩ := hk'
    refine ⟨fun a b h => ?_, fun hnd => ?_⟩
    · rcases mem_po_plus.1 h with h | h
      · simp [(hin a b h).1, (hin a b h).2]
      · simp [(hin' a b h).1, (hin' a b h).2]
    · rw [ids_plus] at hnd
      obtain ⟨htr, hirr⟩ := hk (List.nodup_append.1 hnd).1
      obtain ⟨htr', hirr'⟩ := hk' (List.nodup_append.1 hnd).2.1
      refine ⟨fun a b c hab hbc => ?_, fun a h => ?_⟩
      · rcases mem_po_plus.1 hab with hab | hab <;> rcases mem_po_plus.1 hbc with hbc | hbc
        · exact mem_po_plus.2 (.inl (htr _ _ _ hab hbc))
        · exact (not_mem_of_disj hnd (hin _ _ hab).2 (hin' _ _ hbc).1).elim
        · exact (not_mem_of_disj hnd (hin _ _ hbc).1 (hin' _ _ hab).2).elim
        · exact mem_po_plus.2 (.inr (htr' _ _ _ hab hbc))
      · rcases mem_po_plus.1 h with h | h
        · exact hirr a h
        · exact hirr' a h
  join k k' hk hk' := by
    obtain ⟨hin, hk⟩ := hk
    obtain ⟨hin', hk'⟩ := hk'
    refine ⟨fun a b h => ?_, fun hnd => ?_⟩
    · rcases mem_po_join.1 h with h | h | ⟨ha, hb⟩
      · simp [(hin a b h).1, (hin a b h).2]
      · simp [(hin' a b h).1, (hin' a b h).2]
      · simp [ha, hb]
    · rw [ids_join] at hnd
      obtain ⟨htr, hirr⟩ := hk (List.nodup_append.1 hnd).1
      obtain ⟨htr', hirr'⟩ := hk' (List.nodup_append.1 hnd).2.1
      have dj := fun {a : EventId} (h₁ : a ∈ k.ids) (h₂ : a ∈ k'.ids) => not_mem_of_disj hnd h₁ h₂
      refine ⟨fun a b c hab hbc => ?_, fun a h => ?_⟩
      · rcases mem_po_join.1 hab with hab | hab | ⟨ha, hb⟩ <;>
          rcases mem_po_join.1 hbc with hbc | hbc | ⟨hb', hc⟩
        · exact mem_po_join.2 (.inl (htr _ _ _ hab hbc))
        · exact (dj (hin _ _ hab).2 (hin' _ _ hbc).1).elim
        · exact mem_po_join.2 (.inr (.inr ⟨(hin _ _ hab).1, hc⟩))
        · exact (dj (hin _ _ hbc).1 (hin' _ _ hab).2).elim
        · exact mem_po_join.2 (.inr (.inl (htr' _ _ _ hab hbc)))
        · exact (dj hb' (hin' _ _ hab).2).elim
        · exact (dj (hin _ _ hbc).1 hb).elim
        · exact mem_po_join.2 (.inr (.inr ⟨ha, (hin' _ _ hbc).2⟩))
        · exact (dj hb' hb).elim
      · rcases mem_po_join.1 h with h | h | ⟨ha, ha'⟩
        · exact hirr a h
        · exact hirr' a h
        · exact dj ha ha'
  addRMW k r c w hk _ := hk

theorem denote_poOK (n : Bounds) (P : Stmt) : (denote n P).PoOK :=
  interp_inv poOK_inv _ n ⟨0, []⟩ [] P [] (fun _ _ => pure .empty) [] (Nat.lt_succ_self _)
    (fun _ _ _ => poOK_inv.empty) {}

/-- `⊑` of `⟨P⟩_n` is transitive. -/
theorem denote_po_trans (n : Bounds) (P : Stmt) :
    ∀ a b c, (denote n P).poR a b → (denote n P).poR b c → (denote n P).poR a c :=
  ((denote_poOK n P).2 (denote_ids_nodup n P)).1

/-- `⊑` of `⟨P⟩_n` is irreflexive. -/
theorem denote_po_irrefl (n : Bounds) (P : Stmt) : ∀ a, ¬ (denote n P).poR a a :=
  ((denote_poOK n P).2 (denote_ids_nodup n P)).2

/-- `⊑` of `⟨P⟩_n` relates events of `⟨P⟩_n` only. -/
theorem denote_po_inE (n : Bounds) (P : Stmt) {a b : EventId} (h : (denote n P).poR a b) :
    (denote n P).inE a ∧ (denote n P).inE b := by
  obtain ⟨ha, hb⟩ := (denote_poOK n P).1 a b h
  simp only [ids, List.mem_map] at ha hb
  exact ⟨ha, hb⟩

end EventStructure

/-! ## `EquivUnder` -/

/-- `≡_P` is transitive through an expression that evaluates under every model
    of `P`. -/
theorem EquivUnder.trans {P : Pred} {e₁ e₂ e₃ : Expr} (h₁₂ : EquivUnder P e₁ e₂)
    (h₂₃ : EquivUnder P e₂ e₃) (h₂ : ∀ f, P f → (e₂.eval f).isSome) : EquivUnder P e₁ e₃ := by
  intro f hf v₁ v₃ hv₁ hv₃
  obtain ⟨v₂, hv₂⟩ := Option.isSome_iff_exists.1 (h₂ f hf)
  exact (h₁₂ f hf v₁ v₂ hv₁ hv₂).trans (h₂₃ f hf v₂ v₃ hv₂ hv₃)

/-- Expressions without symbols evaluate alike under every valuation. -/
theorem Expr.eval_closed {e : Expr} (h : e.syms = []) (f g : Valuation) : e.eval f = e.eval g :=
  e.eval_congr f g (fun α hα => by simp [h] at hα)

/-! ## Locations that evaluate -/

/-- A location expression that evaluates under every valuation: a value or a
    symbol. Arithmetic may fail, on a division by zero or on an operand of the
    wrong type (a symbol valued `true`, say, in `α + 1`). -/
def Expr.Total : Expr → Prop
  | .val _ | .sym _ => True
  | _ => False

theorem Expr.Total.eval_isSome {e : Expr} (h : e.Total) (f : Valuation) : (e.eval f).isSome := by
  cases e <;> simp_all [Expr.Total, Expr.eval]

/-- The location of an event of this kind, if any, is `Total`. -/
def EventKind.LocTotal : EventKind → Prop
  | .read _ l _ _ | .write _ l _ _ | .dealloc l => l.Total
  | _ => True

theorem Event.loc_total {e : Event} (h : e.kind.LocTotal) {l : Expr} (hl : e.loc = some l) :
    l.Total := by
  obtain ⟨id, kind, label, guards⟩ := e
  cases kind <;> simp_all [Event.loc, EventKind.LocTotal] <;> subst hl <;> trivial

/-- Every location of `k` is `Total`. -/
def EventStructure.TotalLocs (k : EventStructure) : Prop :=
  ∀ e ∈ k.events, ∀ l, e.loc = some l → l.Total

namespace Execution

variable {es : EventStructure} {x : Execution}

/-! ## The frozen `P` and MoRDor's combined predicate -/

theorem exists_J_of_mem_δ_f {p : EventId × EventId} (hp : p ∈ x.δ.f) : ∃ j ∈ x.J, p ∈ j.δ.f := by
  obtain ⟨X, J, rf⟩ := x
  simp only [δ] at *
  induction J with
  | nil => simp [FwdCtx.empty] at hp
  | cons j J ih =>
      simp only [List.foldr_cons, FwdCtx.union, List.mem_append] at hp
      rcases hp with hp | hp
      · exact ⟨j, List.mem_cons_self, hp⟩
      · obtain ⟨j', hj', hp'⟩ := ih hp
        exact ⟨j', List.mem_cons_of_mem _ hj', hp'⟩

/-- The frozen `P` entails `ψ_δ` of the shared context. -/
theorem psi_of_P {f : Valuation} (h : x.P es f) : x.δ.psi es f := by
  intro p hp
  obtain ⟨j, hj, hpj⟩ := exists_J_of_mem_δ_f hp
  exact (h j hj).2 p hpj

/-- The frozen `P` and the value restrictions of `X` make MoRDor's combined
    predicate (the converse of `P_of_Pm` without `valres`). -/
theorem Pm_of_P {f : Valuation} (h : x.P es f) (hv : x.valresX es f) : x.Pm es f :=
  ⟨fun j hj => (h j hj).1, psi_of_P h, hv⟩

/-- The locations of the events of `S` evaluate under `f`. -/
def LocsEvalAt (es : EventStructure) (S : EvSet) (f : Valuation) : Prop :=
  ∀ a e l, S a → es.ev a = some e → e.loc = some l → (l.eval f).isSome

/-- `Total` locations evaluate under every valuation. -/
theorem locsEvalAt_of_totalLocs (ht : es.TotalLocs) (S : EvSet) (f : Valuation) :
    LocsEvalAt es S f := fun _ e l _ he hl => by
  unfold EventStructure.ev at he
  exact (ht e (List.mem_of_find?_eq_some he) l hl).eval_isSome f

/-! ## `sameLoc` against `≡` -/

/-- Where the locations of `a` and `b` evaluate under every model of
    `P ∧ φ_rf`, `sameLoc` is `≡_{P ∧ φ_rf}` (`EquivUnder`) of their
    locations. -/
theorem sameLoc_iff_equivUnder {a b : EventId} {ea eb : Event} {la lb : Expr}
    (ha : es.ev a = some ea) (hb : es.ev b = some eb) (hla : ea.loc = some la)
    (hlb : eb.loc = some lb)
    (hdef : ∀ f, x.P es f → x.phiRf es f → (la.eval f).isSome ∧ (lb.eval f).isSome) :
    x.sameLoc es a b ↔ EquivUnder (Pred.and (x.P es) (x.phiRf es)) la lb := by
  refine ⟨fun h => x.sameLoc_equivUnder es h ha hb hla hlb, fun h => ?_⟩
  refine ⟨ea, eb, la, lb, ha, hb, hla, hlb, fun f hP hrf => ?_⟩
  obtain ⟨v₁, hv₁⟩ := Option.isSome_iff_exists.1 (hdef f hP hrf).1
  obtain ⟨v₂, hv₂⟩ := Option.isSome_iff_exists.1 (hdef f hP hrf).2
  rw [hv₁, hv₂, h f ⟨hP, hrf⟩ v₁ v₂ hv₁ hv₂]

/-- `sameLoc` is transitive: the shape of `SoundHyps.locTrans`. -/
theorem sameLoc_trans_all : ∀ a b c, x.sameLoc es a b → x.sameLoc es b c → x.sameLoc es a c :=
  fun _ _ _ => x.sameLoc_trans es

/-! ## `rf` and locations -/

/-- Under `P ∧ φ_rf` the locations along `rf` are equivalent: `φ_rf` equates
    them. -/
theorem rf_equivUnder_phiRf {w r : EventId} (h : x.rf w r) {ew er : Event} {lw lr : Expr}
    (hw : es.ev w = some ew) (hr : es.ev r = some er) (hlw : ew.loc = some lw)
    (hlr : er.loc = some lr) : EquivUnder (Pred.and (x.P es) (x.phiRf es)) lw lr := by
  intro f hf v₁ v₂ h₁ h₂
  have := (hf.2.1 w r ew er h hw hr).1 lw lr hlw hlr
  rw [h₁, h₂] at this; exact Option.some.inj this

/-! ## A location model -/

/-- A model of `P`, of the value restrictions of `X` and of `φ_rf`, under
    which the locations of `X` evaluate, is a location model. -/
theorem locModel_of_sat
    (hs : ∃ f, x.P es f ∧ x.valresX es f ∧ x.phiRf es f ∧ LocsEvalAt es x.X f) :
    LocModel es x := by
  obtain ⟨f, hP, hv, hrf, hloc⟩ := hs
  exact ⟨f, Pm_of_P hP hv, hrf, hloc⟩

/-- **A location model where the locations are `Total`**: any model of
    `P ∧ valres_X ∧ φ_rf`. -/
theorem locModel_of_totalLocs (ht : es.TotalLocs)
    (hs : Sat (fun f => x.P es f ∧ x.valresX es f ∧ x.phiRf es f)) : LocModel es x := by
  obtain ⟨f, hP, hv, hrf⟩ := hs
  exact locModel_of_sat ⟨f, hP, hv, hrf, locsEvalAt_of_totalLocs ht _ f⟩

/-- **A location model from `φ`**, where the value restrictions of `X` hold
    under `P ∧ φ_rf` and the locations are `Total`. -/
theorem locModel_of_phi (hφ : x.phi es) (hval : ∀ f, x.P es f → x.phiRf es f → x.valresX es f)
    (ht : es.TotalLocs) : LocModel es x := by
  obtain ⟨f, hP, hrf⟩ := hφ.2.2
  exact locModel_of_totalLocs ht ⟨f, hP, hval f hP hrf, hrf⟩

end Execution

/-! ## Programs whose locations are `Total`

A location of `⟨P⟩_n` is a global `&x`, the symbol of an allocation, or a
program expression over the registers (`*e`, `free(r)`). It is `Total` when
the registers it reads hold values or symbols: pointers are loaded, allocated,
taken by `&x` or copied, never computed. `Stmt.PtrWF R` asks this of the
pointer registers `R`. -/

/-- A pointer expression: a register of `R`, or a constant. -/
def PExpr.Ptr (R : Reg → Prop) : PExpr → Prop
  | .reg r => R r
  | .num _ => True
  | _ => False

/-- Pointers are not computed: dereferences and `free` take a register of `R`
    (or a constant), and a register of `R` is assigned only another register of
    `R` or a constant. Loads, `malloc`, `&x`, `FADD` and `CAS` may target any
    register. -/
def Stmt.PtrWF (R : Reg → Prop) : Stmt → Prop
  | .seq s₁ s₂ | .par s₁ s₂ | .ite _ s₁ s₂ => s₁.PtrWF R ∧ s₂.PtrWF R
  | .while _ _ body => body.PtrWF R
  | .assign r e => R r → e.Ptr R
  | .loadPtr _ _ p _ => p.Ptr R
  | .storePtr _ p _ _ => p.Ptr R
  | .free r => R r
  | _ => True

namespace TotalLocsDenote

open EventStructure

/-- The registers of `R` hold values or symbols. -/
def RegsOK (R : Reg → Prop) (ρ : RegState) : Prop := ∀ r, R r → (ρ.get r).Total

theorem get_set (ρ : RegState) (r r' : Reg) (v : Expr) :
    (ρ.set r v).get r' = if r' = r then v else ρ.get r' := by
  by_cases h : r' = r
  · subst h; simp [RegState.get, RegState.set]
  · have : (r' == r) = false := by simp [h]
    simp [RegState.get, RegState.set, List.lookup, this, h]

theorem RegsOK.set {R : Reg → Prop} {ρ : RegState} (h : RegsOK R ρ) (r : Reg) {v : Expr}
    (hv : R r → v.Total) : RegsOK R (ρ.set r v) := by
  intro r' hr'
  rw [get_set]
  split
  · rename_i heq; subst heq; exact hv hr'
  · exact h r' hr'

theorem RegsOK.den {R : Reg → Prop} {ρ : RegState} (h : RegsOK R ρ) {p : PExpr} (hp : p.Ptr R) :
    (p.den ρ).Total := by
  cases p <;> simp_all [PExpr.Ptr, PExpr.den, Expr.num, Expr.Total]
  exact h _ hp

theorem totalLocs_empty : TotalLocs .empty := fun _ he => by cases he

theorem totalLocs_prefix {e : Event} {k : EventStructure} (he : e.kind.LocTotal)
    (hk : TotalLocs k) : TotalLocs («prefix» e k) := by
  intro e' he' l hl
  rcases List.mem_cons.1 he' with rfl | he'
  · exact Event.loc_total he hl
  · exact hk e' he' l hl

theorem totalLocs_plus {k k' : EventStructure} (h : TotalLocs k) (h' : TotalLocs k') :
    TotalLocs (k.plus k') := by
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact h e he
  · exact h' e he

theorem totalLocs_join {k k' : EventStructure} (h : TotalLocs k) (h' : TotalLocs k') :
    TotalLocs (k.join k') := by
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact h e he
  · exact h' e he

theorem totalLocs_addRMW {k : EventStructure} (h : TotalLocs k) (r : EventId) (c : Expr)
    (w : EventId) : TotalLocs (k.addRMW r c w) := h

theorem glob_total (x : Var) : (Expr.glob x).Total := trivial

open EventStructure in
/-- The structures `⟨s⟩` generates have `Total` locations, for a program whose
    pointers are not computed, from registers whose pointers hold values or
    symbols. -/
theorem interp_totalLocs {R : Reg → Prop} :
    ∀ (N : Nat) (n : Bounds) (ctx : Ctx) (pc : List Nat) (s : Stmt)
    (ρ : RegState) (κ : Cont) (φ : List Guard),
    sumB s.loops n + sizeOf s < N → s.PtrWF R → RegsOK R ρ →
    (∀ ρ φ, RegsOK R ρ → Gen.Holds TotalLocs (κ ρ φ)) →
    Gen.Holds TotalLocs (interp n ctx pc s ρ κ φ)
  | 0, _, _, _, _, _, _, _, hN, _, _, _ => absurd hN (Nat.not_lt_zero _)
  | N + 1, n, ctx, pc, s, ρ, κ, φ, hN, hwf, hρ, hκ => by
    have pre1 : ∀ (kind : EventId → EventKind) (m : Event → Gen EventStructure),
        (∀ i, (kind i).LocTotal) → (∀ e, Gen.Holds TotalLocs (m e)) →
        Gen.Holds TotalLocs (do let e ← mkEvent ctx pc φ kind; let k ← m e; pure («prefix» e k)) :=
      fun kind m hk hm σ => totalLocs_prefix (hk σ.nextId) (hm _ _)
    cases s with
    | skip => rw [interp.eq_def]; exact hκ _ _ hρ
    | assign r e => rw [interp.eq_def]; exact hκ _ _ (hρ.set r (fun h => hρ.den (hwf h)))
    | addrOf r x => rw [interp.eq_def]; exact hκ _ _ (hρ.set r (fun _ => glob_total x))
    | load o r x =>
        rw [interp.eq_def]
        exact pre1 _ _ (fun _ => glob_total x) (fun _ => hκ _ _ (hρ.set r (fun _ => trivial)))
    | loadPtr o r p =>
        rw [interp.eq_def]
        exact pre1 _ _ (fun _ => hρ.den hwf) (fun _ => hκ _ _ (hρ.set r (fun _ => trivial)))
    | store o x v => rw [interp.eq_def]; exact pre1 _ _ (fun _ => glob_total x) (fun _ => hκ _ _ hρ)
    | storePtr o p v =>
        rw [interp.eq_def]; exact pre1 _ _ (fun _ => hρ.den hwf) (fun _ => hκ _ _ hρ)
    | fence o => rw [interp.eq_def]; exact pre1 _ _ (fun _ => trivial) (fun _ => hκ _ _ hρ)
    | malloc r sz =>
        rw [interp.eq_def]
        exact pre1 _ _ (fun _ => trivial) (fun _ => hκ _ _ (hρ.set r (fun _ => trivial)))
    | free r => rw [interp.eq_def]; exact pre1 _ _ (fun _ => hρ r hwf) (fun _ => hκ _ _ hρ)
    | fadd or ow r x v =>
        rw [interp.eq_def]
        intro σ
        refine totalLocs_addRMW (totalLocs_prefix ?_ (totalLocs_prefix ?_
          (hκ _ _ (hρ.set r ?_) _))) _ _ _
        · exact glob_total x
        · exact glob_total x
        · exact fun _ => trivial
    | cas or ow r x e₁ e₂ =>
        rw [interp.eq_def]
        intro σ
        refine totalLocs_addRMW (totalLocs_prefix ?_ (totalLocs_prefix ?_
          (totalLocs_plus (totalLocs_prefix ?_ (hκ _ _ (hρ.set r ?_) _))
            (hκ _ _ (hρ.set r ?_) _)))) _ _ _
        · exact glob_total x
        · trivial
        · exact glob_total x
        · exact fun _ => trivial
        · exact fun _ => trivial
    | seq s₁ s₂ =>
        rw [interp.eq_def]
        simp only [Stmt.loops, sumB_append, Stmt.seq.sizeOf_spec] at hN
        exact interp_totalLocs N n ctx (pc ++ [0]) s₁ ρ _ φ (by omega) hwf.1 hρ
          (fun ρ' φ' hρ' => interp_totalLocs N n ctx (pc ++ [1]) s₂ ρ' κ φ' (by omega) hwf.2 hρ' hκ)
    | par s₁ s₂ =>
        rw [interp.eq_def]
        simp only [Stmt.loops, sumB_append, Stmt.par.sizeOf_spec] at hN
        intro σ
        exact totalLocs_join (totalLocs_plus
          (interp_totalLocs N n ctx (pc ++ [0]) s₁ ρ (fun _ _ => pure .empty) φ (by omega) hwf.1 hρ
            (fun _ _ _ _ => totalLocs_empty) _)
          (interp_totalLocs N n _ (pc ++ [1]) s₂ ρ (fun _ _ => pure .empty) φ (by omega) hwf.2 hρ
            (fun _ _ _ _ => totalLocs_empty) _))
          (hκ _ _ hρ _)
    | ite b s₁ s₂ =>
        rw [interp.eq_def]
        simp only [Stmt.loops, sumB_append, Stmt.ite.sizeOf_spec] at hN
        intro σ
        exact totalLocs_prefix trivial (totalLocs_plus
          (interp_totalLocs N n ctx _ s₁ ρ κ _ (by omega) hwf.1 hρ hκ _)
          (interp_totalLocs N n ctx _ s₂ ρ κ _ (by omega) hwf.2 hρ hκ _))
    | «while» ℓ b body =>
        rw [interp.eq_def]
        dsimp only
        split
        · exact fun _ => totalLocs_empty
        · simp only [Stmt.loops, sumB_cons, Stmt.while.sizeOf_spec] at hN
          have h₁ := sumB_dec_le body.loops n ℓ
          have h₂ := Bounds.dec_self n ℓ
          intro σ
          exact totalLocs_prefix trivial (totalLocs_plus
            (interp_totalLocs N (n.dec ℓ) _ _ body ρ _ _ (by omega) hwf hρ
              (fun ρ' φ' hρ' => interp_totalLocs N (n.dec ℓ) _ pc (.while ℓ b body) ρ' κ φ'
                (by simp only [Stmt.loops, sumB_cons, Stmt.while.sizeOf_spec]; omega) hwf hρ' hκ) _)
            (hκ _ _ hρ _))

end TotalLocsDenote

/-- **The locations of `⟨P⟩_n` are `Total`** for a program whose pointers are
    not computed (`Stmt.PtrWF`): they evaluate under every valuation. -/
theorem denote_totalLocs {R : Reg → Prop} (n : Bounds) {P : Stmt} (hwf : P.PtrWF R) :
    (denote n P).TotalLocs :=
  TotalLocsDenote.interp_totalLocs _ n ⟨0, []⟩ [] P [] (fun _ _ => pure .empty) []
    (Nat.lt_succ_self _) hwf (fun r _ => by simp [RegState.get, List.lookup, Expr.num, Expr.Total])
    (fun _ _ _ _ => TotalLocsDenote.totalLocs_empty) {}

namespace Execution

/-- **A location model in `⟨P⟩_n`** for a program whose pointers are not
    computed: any model of `P ∧ valres_X ∧ φ_rf`. -/
theorem locModel_of_denote {R : Reg → Prop} {n : Bounds} {P : Stmt} (hwf : P.PtrWF R)
    {x : Execution}
    (hs : Sat (fun f => x.P (denote n P) f ∧ x.valresX (denote n P) f ∧ x.phiRf (denote n P) f)) :
    LocModel (denote n P) x :=
  locModel_of_totalLocs (denote_totalLocs n hwf) hs

end Execution

/-! ## Counterexamples -/

namespace RoutineHyps

open Execution

private def wr (i : EventId) (l v : Expr) (pc : List Nat) (g : List Guard := []) : Event :=
  ⟨i, .write .rlx l v false, ⟨0, pc, []⟩, g⟩

/-! ### `φ` gives no location model -/

/-- `x := 1; *(1 / 0) := 2; y := 3` -/
def progDiv : Stmt := .seq (.store .rlx "x" (.num 1) false)
  (.seq (.storePtr .rlx (.bin .div (.num 1) (.num 0)) (.num 2) false) (.store .rlx "y" (.num 3) false))

def esDiv : EventStructure :=
  ⟨[wr 0 (Expr.glob "x") (.num 1) [0], wr 1 (.bin .div (.num 1) (.num 0)) (.num 2) [1, 0],
    wr 2 (Expr.glob "y") (.num 3) [1, 1]], [(0, 1), (0, 2), (1, 2)], []⟩

unseal interp in
theorem denote_progDiv : denote (fun _ => 0) progDiv = esDiv := rfl

/-- All three writes, without justifications or `rf`. -/
def xDiv : Execution := ⟨fun a => a = 0 ∨ a = 1 ∨ a = 2, [], fun _ _ => False⟩

theorem xDiv_phi : xDiv.phi esDiv := by
  refine ⟨fun e _ ⟨p, hp, _⟩ => ?_, fun r => ⟨fun ⟨_, h⟩ => h.elim, ?_⟩, ?_⟩
  · simp [xDiv, Execution.δ, FwdCtx.empty] at hp
  · rintro ⟨hX | hX | hX, e, he, hR⟩ <;> subst hX <;> cases he <;> cases hR
  · refine ⟨fun _ => .num 0, ?_⟩
    refine And.intro (fun j hj => by cases hj)
      (And.intro (fun _ _ _ _ (h : False) => h.elim) (And.intro ?_ ?_))
    · rintro a e α sz (rfl | rfl | rfl) he hk <;> cases he <;> cases hk
    · rintro a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂ (rfl | rfl | rfl) _ _ he₁ _ hk₁ <;> cases he₁ <;> cases hk₁

theorem xDiv_not_locModel : ¬ LocModel esDiv xDiv := by
  rintro ⟨f, -, -, h⟩
  have := h 1 _ _ (.inr (.inl rfl)) rfl rfl
  simp [Expr.num, Expr.eval, ArithOp.applyVal, ArithOp.apply] at this

/-- **`φ` gives no location model** in `⟨P⟩_n`: a location of `X` may
    evaluate under no valuation (`*(1 / 0)` is not `Stmt.PtrWF`). -/
theorem locModel_of_phi_false_loc : ∃ (P : Stmt) (n : Bounds) (x : Execution),
    x.phi (denote n P) ∧ ¬ LocModel (denote n P) x :=
  ⟨progDiv, _, xDiv, denote_progDiv ▸ xDiv_phi, denote_progDiv ▸ xDiv_not_locModel⟩

/-- `if 0 = 1 then x := 1` -/
def progIte : Stmt := .ite (.eq (.num 0) (.num 1)) (.store .rlx "x" (.num 1) false) .skip

def gIte : Guard := ⟨0, .eq (.num 0) (.num 1), true⟩

def esIte : EventStructure :=
  ⟨[⟨0, .branch (.eq (.num 0) (.num 1)), ⟨0, [], []⟩, []⟩,
    wr 1 (Expr.glob "x") (.num 1) [0] [gIte]], [(0, 1)], []⟩

unseal interp in
theorem denote_progIte : denote (fun _ => 0) progIte = esIte := rfl

/-- The write of the dead branch. -/
def xIte : Execution := ⟨fun a => a = 1, [], fun _ _ => False⟩

theorem xIte_phi : xIte.phi esIte := by
  refine ⟨fun e _ ⟨p, hp, _⟩ => ?_, fun r => ⟨fun ⟨_, h⟩ => h.elim, ?_⟩, ?_⟩
  · simp [xIte, Execution.δ, FwdCtx.empty] at hp
  · rintro ⟨hX, e, he, hR⟩; subst hX; cases he; cases hR
  · refine ⟨fun _ => .num 0, ?_⟩
    refine And.intro (fun j hj => by cases hj)
      (And.intro (fun _ _ _ _ (h : False) => h.elim) (And.intro ?_ ?_))
    · rintro a e α sz rfl he hk; cases he; cases hk
    · rintro a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂ rfl _ _ he₁ _ hk₁; cases he₁; cases hk₁

theorem xIte_not_locModel : ¬ LocModel esIte xIte := by
  rintro ⟨f, ⟨-, -, hv⟩, -, -⟩
  have := hv 1 _ rfl rfl
  simp [Event.valres, Expr.conj, Guard.expr, gIte, wr, Expr.holds, Expr.num, Expr.eval, Expr.tt] at this

/-- **`φ` gives no location model** in `⟨P⟩_n`: its witness need not satisfy
    the value restrictions of `X` (here `X` takes a dead branch; `IsExecution`
    excludes this one, but asks `Sat (P_J ∧ valres_X)` without `ψ_δ`). -/
theorem locModel_of_phi_false_valres : ∃ (P : Stmt) (n : Bounds) (x : Execution),
    x.phi (denote n P) ∧ ¬ LocModel (denote n P) x :=
  ⟨progIte, _, xIte, denote_progIte ▸ xIte_phi, denote_progIte ▸ xIte_not_locModel⟩

end RoutineHyps
