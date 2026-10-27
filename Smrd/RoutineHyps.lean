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
* **`rf` and locations.** `sameLoc` compares locations under the frozen `P`
  alone, while `φ` asks only that `P ∧ φ_rf` be satisfiable: `φ_rf` equates
  the locations along `rf` under its witness, not under every model of `P`.
  So `rf ⊆ sameLoc` does not follow from `φ` (`rfLoc_of_phi_false`). It
  holds under `P ∧ φ_rf` (`rf_equivUnder_phiRf`), where `P` entails `φ_rf`
  (`rfLoc_of_entails`), and where the locations along `rf` are closed
  (`rfLoc_of_phi_closed`, e.g. the globals of a program without pointers).
* **Transitivity of `sameLoc`** (`sameLoc_trans`): `EquivUnder P` is
  transitive through a middle expression that evaluates under every model of
  `P`. Without that it fails in `⟨P⟩_n`: a location `1 / 0` is `sameLoc` to
  every location (`sameLoc_trans_false`).
* **A location model** (`locModel_of_phi`, `locModel_of_sat`): the frozen `P`
  entails the justifications' predicates and `ψ_δ` of the shared context
  (`Pm_of_P`); a model of it under which the value restrictions of `X` hold
  and the locations of `X` evaluate is one. `φ` gives neither: its witness
  need not satisfy `valres` (`locModel_of_phi_false_valres`), and a location
  may evaluate under no valuation (`locModel_of_phi_false_loc`).
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

/-! ## Locations that evaluate -/

/-- The locations of the events of `S` evaluate under every model of the
    frozen `P`. -/
def LocsEval (es : EventStructure) (x : Execution) (S : EvSet) : Prop :=
  ∀ f, x.P es f → ∀ a e l, S a → es.ev a = some e → e.loc = some l → (l.eval f).isSome

/-- Closed locations that evaluate at all evaluate everywhere: e.g. the
    globals `&x` of a program without pointers. -/
theorem locsEval_of_closed {S : EvSet}
    (h : ∀ a e l, S a → es.ev a = some e → e.loc = some l → l.syms = [] ∧ ∃ g, (l.eval g).isSome) :
    LocsEval es x S := by
  intro f _ a e l ha he hl
  obtain ⟨hs, g, hg⟩ := h a e l ha he hl
  rw [Expr.eval_closed hs f g]; exact hg

/-! ## Transitivity of `sameLoc` -/

/-- `sameLoc` is transitive through an event whose location evaluates under
    every model of `P`. -/
theorem sameLoc_trans {a b c : EventId}
    (hb : ∀ f, x.P es f → ∀ e l, es.ev b = some e → e.loc = some l → (l.eval f).isSome)
    (hab : x.sameLoc es a b) (hbc : x.sameLoc es b c) : x.sameLoc es a c := by
  obtain ⟨ea, eb, la, lb, hea, heb, hla, hlb, h₁⟩ := hab
  obtain ⟨eb', ec, lb', lc, heb', hec, hlb', hlc, h₂⟩ := hbc
  rw [heb] at heb'; cases heb'
  rw [hlb] at hlb'; cases hlb'
  exact ⟨ea, ec, la, lc, hea, hec, hla, hlc,
    EquivUnder.trans h₁ h₂ (fun f hf => hb f hf eb lb heb hlb)⟩

/-- `sameLoc` is transitive through the events of `S`, where their locations
    evaluate under every model of `P`. -/
theorem sameLoc_trans_of_locsEval {S : EvSet} (hS : LocsEval es x S) {a b c : EventId} (hSb : S b)
    (hab : x.sameLoc es a b) (hbc : x.sameLoc es b c) : x.sameLoc es a c :=
  sameLoc_trans (fun f hf e l he hl => hS f hf b e l hSb he hl) hab hbc

/-- `sameLoc` is transitive where every location evaluates under every model
    of `P`: the shape of `SoundHyps.locTrans`. -/
theorem sameLoc_trans_all (hS : LocsEval es x (fun _ => True)) :
    ∀ a b c, x.sameLoc es a b → x.sameLoc es b c → x.sameLoc es a c :=
  fun _ _ _ => sameLoc_trans_of_locsEval hS trivial

/-! ## `rf` and locations -/

theorem isWrite_loc {e : Event} (h : e.isWrite = true) : ∃ l, e.loc = some l := by
  obtain ⟨id, kind, label, guards⟩ := e
  cases kind <;> simp_all [Event.isWrite, Event.loc]

theorem isRead_loc {e : Event} (h : e.isRead = true) : ∃ l, e.loc = some l := by
  obtain ⟨id, kind, label, guards⟩ := e
  cases kind <;> simp_all [Event.isRead, Event.loc]

/-- Under `P ∧ φ_rf` the locations along `rf` are equivalent: `φ_rf` equates
    them. -/
theorem rf_equivUnder_phiRf {w r : EventId} (h : x.rf w r) {ew er : Event} {lw lr : Expr}
    (hw : es.ev w = some ew) (hr : es.ev r = some er) (hlw : ew.loc = some lw)
    (hlr : er.loc = some lr) : EquivUnder (Pred.and (x.P es) (x.phiRf es)) lw lr := by
  intro f hf v₁ v₂ h₁ h₂
  have := (hf.2.1 w r ew er h hw hr).1 lw lr hlw hlr
  rw [h₁, h₂] at this; exact Option.some.inj this

/-- `rf ⊆ sameLoc` where `P` entails `φ_rf`, for an `rf` from writes to reads
    (`IsExecution.rf_wr`). -/
theorem rfLoc_of_entails (hE : ∀ f, x.P es f → x.phiRf es f)
    (hrfw : ∀ w r, x.rf w r → es.cls Event.isWrite w ∧ es.cls Event.isRead r)
    {w r : EventId} (h : x.rf w r) : x.sameLoc es w r := by
  obtain ⟨⟨ew, hw, hW⟩, ⟨er, hr, hR⟩⟩ := hrfw w r h
  obtain ⟨lw, hlw⟩ := isWrite_loc hW
  obtain ⟨lr, hlr⟩ := isRead_loc hR
  exact ⟨ew, er, lw, lr, hw, hr, hlw, hlr, fun f hf =>
    rf_equivUnder_phiRf h hw hr hlw hlr f ⟨hf, hE f hf⟩⟩

/-- `rf ⊆ sameLoc` from `φ` where the locations along `rf` are closed: the
    witness of `P ∧ φ_rf` equates them, and closed expressions evaluate alike
    everywhere. -/
theorem rfLoc_of_phi_closed (hφ : x.phi es)
    (hrfw : ∀ w r, x.rf w r → es.cls Event.isWrite w ∧ es.cls Event.isRead r)
    (hcl : ∀ w r ew er lw lr, x.rf w r → es.ev w = some ew → es.ev r = some er →
      ew.loc = some lw → er.loc = some lr → lw.syms = [] ∧ lr.syms = [])
    {w r : EventId} (h : x.rf w r) : x.sameLoc es w r := by
  obtain ⟨⟨ew, hw, hW⟩, ⟨er, hr, hR⟩⟩ := hrfw w r h
  obtain ⟨lw, hlw⟩ := isWrite_loc hW
  obtain ⟨lr, hlr⟩ := isRead_loc hR
  obtain ⟨g, -, hg⟩ := hφ.2.2
  have heq := (hg.1 w r ew er h hw hr).1 lw lr hlw hlr
  obtain ⟨hsw, hsr⟩ := hcl w r ew er lw lr h hw hr hlw hlr
  refine ⟨ew, er, lw, lr, hw, hr, hlw, hlr, fun f _ v₁ v₂ h₁ h₂ => ?_⟩
  rw [Expr.eval_closed hsw f g, heq, ← Expr.eval_closed hsr f g, h₂] at h₁
  exact (Option.some.inj h₁).symm

/-! ## A location model -/

/-- A model of `P` and the value restrictions of `X`, with the locations of
    `X` evaluating under every model of `P`, is a location model. -/
theorem locModel_of_sat (hs : Sat (Pred.and (x.P es) (x.valresX es))) (hloc : LocsEval es x x.X) :
    LocModel es x := by
  obtain ⟨f, hP, hv⟩ := hs
  exact ⟨f, Pm_of_P hP hv, fun a e l ha he hl => hloc f hP a e l ha he hl⟩

/-- **A location model from `φ`**, where the value restrictions of `X` hold
    under `P ∧ φ_rf` and the locations of `X` evaluate under `P`. -/
theorem locModel_of_phi (hφ : x.phi es) (hval : ∀ f, x.P es f → x.phiRf es f → x.valresX es f)
    (hloc : LocsEval es x x.X) : LocModel es x := by
  obtain ⟨f, hP, hrf⟩ := hφ.2.2
  exact locModel_of_sat ⟨f, hP, hval f hP hrf⟩ hloc

end Execution

/-! ## Counterexamples -/

namespace RoutineHyps

open Execution

private def rd (i : EventId) (x : Var) (pc : List Nat) : Event :=
  ⟨i, .read .rlx (Expr.glob x) i false, ⟨0, pc, []⟩, []⟩
private def wr (i : EventId) (l v : Expr) (pc : List Nat) (g : List Guard := []) : Event :=
  ⟨i, .write .rlx l v false, ⟨0, pc, []⟩, g⟩

/-! ### `rf ⊆ sameLoc` does not follow from `φ` -/

/-- `r := y; *r := 1; s := x` -/
def progRf : Stmt := .seq (.load .rlx "r" "y" false)
  (.seq (.storePtr .rlx (.reg "r") (.num 1) false) (.load .rlx "s" "x" false))

def esRf : EventStructure :=
  ⟨[rd 0 "y" [0], wr 1 (.sym 0) (.num 1) [1, 0], rd 2 "x" [1, 1]], [(0, 1), (0, 2), (1, 2)], []⟩

unseal interp in
theorem denote_progRf : denote (fun _ => 0) progRf = esRf := rfl

/-- `*r := 1` read by `s := x`, without justifications: `P = ⊤`. -/
def xRf : Execution := ⟨fun a => a = 1 ∨ a = 2, [], fun w r => w = 1 ∧ r = 2⟩

theorem xRf_phi : xRf.phi esRf := by
  refine ⟨fun e _ ⟨p, hp, _⟩ => ?_, fun r => ⟨?_, ?_⟩, ?_⟩
  · simp [xRf, Execution.δ, FwdCtx.empty] at hp
  · rintro ⟨w, rfl, rfl⟩
    exact ⟨.inr rfl, _, rfl, rfl⟩
  · rintro ⟨hX | hX, e, he, hR⟩ <;> subst hX
    · cases he; cases hR
    · exact ⟨1, rfl, rfl⟩
  · refine ⟨fun α => if α = 0 then .loc ⟨.global "x", 0⟩ else .num 1, ?_⟩
    refine And.intro (fun j hj => by cases hj) (And.intro ?_ (And.intro ?_ ?_))
    · rintro w r ew er ⟨rfl, rfl⟩ hw hr
      cases hw; cases hr
      refine ⟨fun lw lr hlw hlr => ?_, fun vw vr hvw hvr => ?_⟩
      · cases hlw; cases hlr; rfl
      · cases hvw; cases hvr; rfl
    · rintro a e α sz (rfl | rfl) he hk <;> cases he <;> cases hk
    · rintro a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂ (rfl | rfl) _ _ he₁ _ hk₁ <;> cases he₁ <;> cases hk₁

/-- The write and the read are not `sameLoc`: `P = ⊤` leaves `r` free. -/
theorem xRf_not_sameLoc : ¬ xRf.sameLoc esRf 1 2 := by
  rintro ⟨ea, eb, la, lb, ha, hb, hla, hlb, h⟩
  cases ha; cases hb; cases hla; cases hlb
  have := h (fun _ => .num 0) (fun j hj => by cases hj) _ _ rfl rfl
  cases this

/-- **`rf ⊆ sameLoc` does not follow from `φ`**, in `⟨P⟩_n`. -/
theorem rfLoc_of_phi_false : ∃ (P : Stmt) (n : Bounds) (x : Execution),
    x.phi (denote n P) ∧ ∃ w r, x.rf w r ∧ ¬ x.sameLoc (denote n P) w r :=
  ⟨progRf, _, xRf, denote_progRf ▸ xRf_phi, 1, 2, ⟨rfl, rfl⟩,
    denote_progRf ▸ xRf_not_sameLoc⟩

/-! ### `sameLoc` is not transitive, and `φ` gives no location model -/

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

theorem xDiv_sameLoc_01 : xDiv.sameLoc esDiv 0 1 :=
  ⟨_, _, _, _, rfl, rfl, rfl, rfl, fun _ _ _ _ _ h => by cases h⟩

theorem xDiv_sameLoc_12 : xDiv.sameLoc esDiv 1 2 :=
  ⟨_, _, _, _, rfl, rfl, rfl, rfl, fun _ _ _ _ h _ => by cases h⟩

theorem xDiv_not_sameLoc_02 : ¬ xDiv.sameLoc esDiv 0 2 := by
  rintro ⟨ea, eb, la, lb, ha, hb, hla, hlb, h⟩
  cases ha; cases hb; cases hla; cases hlb
  have := h (fun _ => .num 0) (fun j hj => by cases hj) _ _ rfl rfl
  exact absurd this (by decide)

/-- **`sameLoc` is not transitive** in `⟨P⟩_n`: `1 / 0` evaluates nowhere. -/
theorem sameLoc_trans_false : ∃ (P : Stmt) (n : Bounds) (x : Execution) (a b c : EventId),
    x.sameLoc (denote n P) a b ∧ x.sameLoc (denote n P) b c ∧ ¬ x.sameLoc (denote n P) a c :=
  ⟨progDiv, _, xDiv, 0, 1, 2, denote_progDiv ▸ xDiv_sameLoc_01, denote_progDiv ▸ xDiv_sameLoc_12,
    denote_progDiv ▸ xDiv_not_sameLoc_02⟩

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
  rintro ⟨f, -, h⟩
  have := h 1 _ _ (.inr (.inl rfl)) rfl rfl
  simp [Expr.num, Expr.eval, ArithOp.applyVal, ArithOp.apply] at this

/-- **`φ` gives no location model** in `⟨P⟩_n`: a location of `X` may
    evaluate under no valuation. -/
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
  rintro ⟨f, ⟨-, -, hv⟩, -⟩
  have := hv 1 _ rfl rfl
  simp [Event.valres, Expr.conj, Guard.expr, gIte, wr, Expr.holds, Expr.num, Expr.eval, Expr.tt] at this

/-- **`φ` gives no location model** in `⟨P⟩_n`: its witness need not satisfy
    the value restrictions of `X` (here `X` takes a dead branch; `IsExecution`
    excludes this one, but asks `Sat (P_J ∧ valres_X)` without `ψ_δ`). -/
theorem locModel_of_phi_false_valres : ∃ (P : Stmt) (n : Bounds) (x : Execution),
    x.phi (denote n P) ∧ ¬ LocModel (denote n P) x :=
  ⟨progIte, _, xIte, denote_progIte ▸ xIte_phi, denote_progIte ▸ xIte_not_locModel⟩

end RoutineHyps
