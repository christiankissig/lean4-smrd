import Smrd.ElabDec.Fragment

/-!
# The elaboration closure is finite up to propositional equivalence

`GenR Ω Qs wk` is `Generated Ω` (`def:gen-just`) with two restrictions:

* **Strengthening conjoins a predicate from a finite list `Qs`** (Condition
  C2). MoRDor strengthens only with equations `val(e₁) = val(e₂)` between the
  values of two events of the structure (`mordorQs`). The paper's
  Condition `a:locations.2` asks only that `Q` be bounded, which does not give
  finiteness: `α = n` for each numeral `n` is bounded, and these are pairwise
  inequivalent (`strengthening_infinite`).
* **Weakening is admitted only when `wk = true`.** The paper sets Weakening
  aside (Definition `def:elab-weak`). The finiteness theorem holds either way;
  the decision procedure (`Smrd.ElabDec.Saturate`) needs `wk = false`.

`GenR` is contained in `Generated` (`GenR.generated`).

Two justifications are *equivalent*, `JEq`, when their predicates are
propositionally equivalent (`Expr.PEq`: same atoms, same three-valued
combination, hence same denotation and same symbols), their dependencies have
the same members, and their forwarding contexts and justified writes are equal.

## Invariants (`GenR.inv`)

Every justification of `GenR`
* has a well-formed forwarding context whose edges have pairwise distinct
  targets and endpoints among the events (`Inv.nodupT`, `Inv.ends`): each new
  edge of Forwarding or Write Elision ends at an event `remap_δ` fixes, which
  no earlier edge targets (`fwdBase_canon`). So `|F| + |WE| ≤ |E|`.
* has dependencies `D` with the symbols of its write's location and value
  (`Inv.dmem`), the paper's invariant stated at `def:elab-va`.

## Finiteness (`GenR.finite`)

Under `ValsAtomic` (no event's value is headed by a connective, implied by
Condition C1) the atoms of every predicate are of size at most `K^(|F|+1)`
for a constant `K` of the structure, with symbols among those of the
structure and values among its own (`GenR.atoms_small`): Forwarding is the only
elaboration that changes atoms, by replacing `val(e₂)` with `val(e₁)`, which
multiplies sizes by at most `K`, and it adds an edge to `F`; Lifting renames
atoms onto symbols `⊑`-before its write. The written expressions of the
justified writes are bounded the same way, with the values Value Assignment
substitutes, each determined by a predicate's equivalence class and a symbol
(`GenR.w_small`). The predicates fall into finitely many classes (truth tables
over the finitely many atoms), and so do `D`, `δ` and `w`: there is a finite
list `U` of justifications such that every justification of `GenR` is
equivalent to one of `U`.
-/

open Expr Smrd.ElabDec

namespace EventStructure

variable (es : EventStructure)

/-- The elaboration closure with Strengthening restricted to the predicates
    `Qs` and Weakening to `wk = true`. -/
inductive GenR (Ω : Pred) (Qs : List Expr) (wk : Bool) : Justification → Prop
  | pre {w : Event} {j : Justification} :
      w ∈ es.events → preJust w = some j → Sat w.valres.holds →
      GenR Ω Qs wk j
  | va {j₁ : Justification} {o : MemOrd} {x e : Expr} {b : Bool} {α : Sym} {v : Val} :
      GenR Ω Qs wk j₁ →
      j₁.w.kind = .write o x e b →
      EquivUnder j₁.P.holds (.sym α) (.val v) →
      Sat (Pred.and j₁.P.holds Ω) →
      GenR Ω Qs wk
        { P := j₁.P
          D := (x.subst α (.val v)).syms ++ (e.subst α (.val v)).syms
          δ := j₁.δ
          w := { j₁.w with kind := .write o (x.subst α (.val v)) (e.subst α (.val v)) b } }
  | str {j₁ : Justification} (Q : Expr) (S : List EventId) :
      Q ∈ Qs →
      GenR Ω Qs wk j₁ →
      (∀ e, e ∈ S ↔ e ∈ (strPred es j₁.P Q S).syms ∧ e ∉ j₁.P.syms) →
      (∀ e ∈ S, j₁.δ.Remap e e) →
      (∀ e ∈ S, es.poR e j₁.w.id ∧ ¬ es.ppo j₁.P.holds j₁.δ j₁.w.id e) →
      Sat (Pred.and (strPred es j₁.P Q S).holds Ω) →
      GenR Ω Qs wk { j₁ with P := strPred es j₁.P Q S }
  | fwd {j₁ : Justification} {o : MemOrd} {x e : Expr} {b : Bool} {e₁ e₂ : EventId}
      {ev₁ ev₂ : Event} {v₁ v₂ : Expr} :
      GenR Ω Qs wk j₁ →
      j₁.w.kind = .write o x e b →
      es.fwdRel j₁ e₁ e₂ →
      es.ev e₁ = some ev₁ → es.ev e₂ = some ev₂ →
      ev₁.val = some v₁ → ev₂.val = some v₂ →
      FwdCtx.WF { j₁.δ with f := j₁.δ.f ++ [(e₁, e₂)] } →
      Sat (Pred.and (j₁.P.replace v₂ v₁).holds Ω) →
      GenR Ω Qs wk
        { P := j₁.P.replace v₂ v₁
          D := (e.replace v₂ v₁).syms ++ (x.replace v₂ v₁).syms
          δ := { j₁.δ with f := j₁.δ.f ++ [(e₁, e₂)] }
          w := { j₁.w with kind := .write o (x.replace v₂ v₁) (e.replace v₂ v₁) b } }
  | we {j₁ : Justification} {e₁ e₂ : EventId} :
      GenR Ω Qs wk j₁ →
      es.weRel j₁ e₁ e₂ →
      FwdCtx.WF { j₁.δ with we := j₁.δ.we ++ [(e₂, e₁)] } →
      Sat (Pred.and j₁.P.holds Ω) →
      GenR Ω Qs wk { j₁ with δ := { j₁.δ with we := j₁.δ.we ++ [(e₂, e₁)] } }
  | lift {j₁ j₂ : Justification} (Λ : Relabelling) :
      GenR Ω Qs wk j₁ → GenR Ω Qs wk j₂ →
      j₁.δ = j₂.δ →
      Λ.Injective →
      es.ClosedRelabEq j₁.δ Λ j₁.P j₁.w j₂.P j₂.w →
      (∀ e, e ∈ j₂.D ↔ ∃ α ∈ j₁.D, Λ.app α = e) →
      (∀ α ∈ j₁.D, ∃ ev₁ ev₂, es.ev α = some ev₁ ∧ es.ev (Λ.app α) = some ev₂ ∧
        es.ClosedRelabEq j₁.δ Λ j₁.P ev₁ j₂.P ev₂) →
      ¬ es.cls Event.isVol j₁.w.id → ¬ es.cls Event.isVol j₂.w.id →
      (∀ α ∈ j₁.D ++ j₂.D, ¬ es.cls Event.isVol α) →
      (∀ α ∈ (j₁.P.rename Λ).syms, es.poR α j₂.w.id) →
      Sat (Pred.and (Expr.liftPred (j₁.P.rename Λ) j₂.P).holds Ω) →
      GenR Ω Qs wk { j₂ with P := Expr.liftPred (j₁.P.rename Λ) j₂.P }
  | weak {j₁ : Justification} {P' Pw : Expr} :
      wk = true →
      GenR Ω Qs wk j₁ →
      j₁.P.ConjEq (.and P' Pw) →
      Entails Ω Pw.holds →
      Sat (Pred.and P'.holds Ω) →
      GenR Ω Qs wk { j₁ with P := P' }

variable {es}

theorem GenR.generated {Ω : Pred} {Qs : List Expr} {wk : Bool} {j : Justification}
    (h : es.GenR Ω Qs wk j) : es.Generated Ω j := by
  induction h with
  | pre hw hj hs => exact .pre hw hj hs
  | va _ hk he hs ih => exact .va ih hk he hs
  | str Q S _ _ h1 h2 h3 h4 ih => exact .str Q S ih h1 h2 h3 h4
  | fwd _ hk hf h1 h2 h3 h4 hwf hs ih => exact .fwd ih hk hf h1 h2 h3 h4 hwf hs
  | we _ hw hwf hs ih => exact .we ih hw hwf hs
  | lift Λ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ih₁ ih₂ =>
      exact .lift Λ ih₁ ih₂ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  | weak _ _ h1 h2 h3 ih => exact .weak ih h1 h2 h3

variable (es)

/-- MoRDor's Strengthening predicates: equations `val(e₁) = val(e₂)` between
    the values of two events of the structure. -/
def mordorQs : List Expr :=
  es.events.flatMap fun e₁ => es.events.filterMap fun e₂ =>
    match e₁.val, e₂.val with
    | some v₁, some v₂ => some (.eq v₁ v₂)
    | _, _ => none

/-! ## Invariants -/

/-- The symbols of the location and value of an effectful event. -/
def _root_.Event.effSyms (e : Event) : List Sym :=
  match e.kind with
  | .write _ x v _ => x.syms ++ v.syms
  | .alloc _ s => s.syms
  | .dealloc l => l.syms
  | _ => []

/-- The targets of the edges of a forwarding context. -/
def _root_.FwdCtx.tgts (δ : FwdCtx) : List EventId := δ.f.map Prod.snd ++ δ.we.map Prod.snd

/-- The invariants of `GenR` used by the decision procedure. -/
structure Inv (j : Justification) : Prop where
  wf : j.δ.WF
  nodupT : j.δ.tgts.Nodup
  ends : ∀ p ∈ j.δ.f ++ j.δ.we, p.1 ∈ es.ids ∧ p.2 ∈ es.ids
  dmem : ∀ a, a ∈ j.D ↔ a ∈ j.w.effSyms

variable {es}

theorem _root_.FwdCtx.Remap.canon_end {δ : FwdCtx} {x y : EventId} (h : δ.Remap x y) :
    ∀ a, ¬ δ.edge a y := by
  induction h with
  | canon h => exact h
  | step _ _ ih => exact ih

theorem mem_ids_of_ev {e : EventId} {ev : Event} (h : es.ev e = some ev) : e ∈ es.ids := by
  have hm := List.mem_of_find?_eq_some h
  have hid : ev.id = e := by simpa using List.find?_some h
  exact List.mem_map.2 ⟨ev, hm, hid⟩

theorem mem_events_of_ev {e : EventId} {ev : Event} (h : es.ev e = some ev) : ev ∈ es.events :=
  List.mem_of_find?_eq_some h

theorem ev_id_of_ev {e : EventId} {ev : Event} (h : es.ev e = some ev) : ev.id = e := by
  simpa using List.find?_some h

/-- The ends of a Forwarding or Write Elision pair are fixed by `remap_δ` and
    are events. -/
theorem fwdBase_canon {j : Justification} {e₁ e₂ : EventId} (h : es.fwdBase j e₁ e₂) :
    (∀ a, ¬ j.δ.edge a e₁) ∧ (∀ a, ¬ j.δ.edge a e₂) ∧ e₁ ∈ es.ids ∧ e₂ ∈ es.ids := by
  obtain ⟨⟨⟨⟨a, b, -, ha, hb⟩, -⟩, -⟩, -, ev₁, ev₂, -, -, h₁, h₂, -⟩ := h
  exact ⟨ha.canon_end, hb.canon_end, mem_ids_of_ev h₁, mem_ids_of_ev h₂⟩

theorem not_mem_tgts {δ : FwdCtx} {t : EventId} (h : ∀ a, ¬ δ.edge a t) : t ∉ δ.tgts := by
  intro ht
  simp only [FwdCtx.tgts, List.mem_append, List.mem_map] at ht
  rcases ht with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact h p.1 (Or.inl hp)
  · exact h p.1 (Or.inr hp)

theorem nodup_insert {l m : List EventId} {x : EventId} (h : (l ++ m).Nodup) (hx : x ∉ l ++ m) :
    (l ++ [x] ++ m).Nodup := by
  have : l ++ [x] ++ m = l ++ x :: m := by simp
  rw [this, List.perm_middle.nodup_iff, List.nodup_cons]; exact ⟨hx, h⟩

theorem preJust_D {w : Event} {j : Justification} (h : preJust w = some j) :
    j.w = w ∧ j.δ = .empty ∧ j.P = w.valres ∧ ∀ a, a ∈ j.D ↔ a ∈ w.effSyms := by
  unfold preJust at h
  split at h <;> cases h <;> simp_all [Event.effSyms]

theorem GenR.inv {Ω : Pred} {Qs : List Expr} {wk : Bool} {j : Justification}
    (h : es.GenR Ω Qs wk j) : es.Inv j := by
  induction h with
  | pre _ hj _ =>
      obtain ⟨hw, hδ, -, hD⟩ := preJust_D hj
      refine ⟨hδ ▸ FwdCtx.WF.empty, by rw [hδ]; exact List.nodup_nil, ?_, by rw [hw]; exact hD⟩
      rw [hδ]; intro p hp; cases hp
  | va _ hk _ _ ih =>
      refine ⟨ih.wf, ih.nodupT, ih.ends, fun a => ?_⟩
      simp [Event.effSyms]
  | str _ _ _ _ _ _ _ _ ih => exact ⟨ih.wf, ih.nodupT, ih.ends, ih.dmem⟩
  | @fwd j₁ o x e b e₁ e₂ ev₁ ev₂ v₁ v₂ _ hk hf _ _ _ _ hwf _ ih =>
      have hb := fwdBase_canon hf.1.1
      refine ⟨hwf, ?_, ?_, fun a => ?_⟩
      · have := nodup_insert ih.nodupT (not_mem_tgts hb.2.1)
        simpa [FwdCtx.tgts] using this
      · intro p hp
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with (hp | rfl) | hp
        · exact ih.ends p (List.mem_append_left _ hp)
        · exact ⟨hb.2.2.1, hb.2.2.2⟩
        · exact ih.ends p (List.mem_append_right _ hp)
      · simp only [Event.effSyms, List.mem_append]; exact or_comm
  | @we j₁ e₁ e₂ _ hw hwf _ ih =>
      have hb := fwdBase_canon hw.1.1
      refine ⟨hwf, ?_, ?_, ih.dmem⟩
      · have := nodup_insert (m := []) (by simpa using ih.nodupT) (by simpa using not_mem_tgts hb.1)
        simpa [FwdCtx.tgts] using this
      · intro p hp
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | hp | rfl
        · exact ih.ends p (List.mem_append_left _ hp)
        · exact ih.ends p (List.mem_append_right _ hp)
        · exact ⟨hb.2.2.2, hb.2.2.1⟩
  | lift _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₂ => exact ⟨ih₂.wf, ih₂.nodupT, ih₂.ends, ih₂.dmem⟩
  | weak _ _ _ _ _ ih => exact ⟨ih.wf, ih.nodupT, ih.ends, ih.dmem⟩

/-- The forwarding context of a justification of `GenR` has at most `|E|`
    edges in each of its relations. -/
theorem Inv.length_le {j : Justification} (h : es.Inv j) :
    j.δ.f.length ≤ es.events.length ∧ j.δ.we.length ≤ es.events.length := by
  have hle := length_le_of_nodup_subset h.nodupT (L := es.ids) (fun t ht => by
    simp only [FwdCtx.tgts, List.mem_append, List.mem_map] at ht
    rcases ht with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · exact (h.ends p (List.mem_append_left _ hp)).2
    · exact (h.ends p (List.mem_append_right _ hp)).2)
  simp only [FwdCtx.tgts, List.length_append, List.length_map, ids] at hle
  omega

/-! ## Equivalence of justifications -/

/-- Equivalent justifications. -/
def JEq (j j' : Justification) : Prop :=
  j.P.PEq j'.P ∧ (∀ a, a ∈ j.D ↔ a ∈ j'.D) ∧ j.δ = j'.δ ∧ j.w = j'.w

theorem JEq.refl (j : Justification) : JEq j j := ⟨PEq.refl _, fun _ => Iff.rfl, rfl, rfl⟩
theorem JEq.symm {j j' : Justification} (h : JEq j j') : JEq j' j :=
  ⟨h.1.symm, fun a => (h.2.1 a).symm, h.2.2.1.symm, h.2.2.2.symm⟩
theorem JEq.trans {j₁ j₂ j₃ : Justification} (h : JEq j₁ j₂) (h' : JEq j₂ j₃) : JEq j₁ j₃ :=
  ⟨h.1.trans h'.1, fun a => (h.2.1 a).trans (h'.2.1 a), h.2.2.1.trans h'.2.2.1,
    h.2.2.2.trans h'.2.2.2⟩

/-- `JEq`, decided. -/
def jeqB (j j' : Justification) : Bool :=
  peqB j.P j'.P && j.D.all (· ∈ j'.D) && j'.D.all (· ∈ j.D) && j.δ == j'.δ &&
    decide (j.w = j'.w)

theorem jeqB_iff (j j' : Justification) : jeqB j j' = true ↔ JEq j j' := by
  simp only [jeqB, Bool.and_eq_true, peqB_iff, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    JEq]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩; exact ⟨h1, fun a => ⟨h2 a, h3 a⟩, h4, h5⟩
  · rintro ⟨h1, h2, h4, h5⟩; exact ⟨⟨⟨⟨h1, fun a => (h2 a).1⟩, fun a => (h2 a).2⟩, h4⟩, h5⟩

instance (j j' : Justification) : Decidable (JEq j j') := decidable_of_iff _ (jeqB_iff j j')

/-! ## Finiteness -/

variable (es)

/-- No event's value is headed by a connective; implied by Condition C1. -/
def ValsAtomic : Prop := ∀ e ∈ es.events, ∀ v, e.val = some v → v.IsConn = false

/-- The expressions the closure starts from: `⊤`, the predicates `Qs`, and the
    guards, locations and values of the events. -/
def baseExprs (Qs : List Expr) : List Expr :=
  Expr.tt :: Qs ++ es.events.flatMap fun e => e.guards.map Guard.expr ++ e.loc.toList ++ e.val.toList

/-- A bound on the sizes of the base expressions. -/
def sizeK (Qs : List Expr) : Nat := (es.baseExprs Qs).foldl (fun m e => max m e.size) 1

/-- The symbols the closure can mention: those of the base expressions and the
    sources of `⊑`. -/
def symU (Qs : List Expr) : List Sym := (es.baseExprs Qs).flatMap Expr.syms ++ es.po.map Prod.fst

/-- The values of the base expressions. -/
def valU (Qs : List Expr) : List Val := (es.baseExprs Qs).flatMap Expr.vals

variable {es}

theorem le_foldl_max (L : List Expr) : ∀ (m : Nat) (e : Expr), e ∈ L →
    e.size ≤ L.foldl (fun m e => max m e.size) m ∧ m ≤ L.foldl (fun m e => max m e.size) m := by
  induction L with
  | nil => intro m e h; cases h
  | cons a L ih =>
      intro m e h
      simp only [List.foldl_cons]
      rcases List.mem_cons.1 h with rfl | h
      · by_cases hL : L = []
        · subst hL; simp; omega
        · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil L hL
          have := (ih (max m e.size) x hx).2; omega
      · have := ih (max m a.size) e h; omega

theorem foldl_max_ge (L : List Expr) : ∀ m : Nat, m ≤ L.foldl (fun m e => max m e.size) m := by
  induction L with
  | nil => intro m; exact Nat.le_refl _
  | cons a L ih => intro m; simp only [List.foldl_cons]; have := ih (max m a.size); omega

theorem size_le_sizeK {Qs : List Expr} {e : Expr} (h : e ∈ es.baseExprs Qs) :
    e.size ≤ es.sizeK Qs := (le_foldl_max _ 1 e h).1

theorem one_le_sizeK (Qs : List Expr) : 1 ≤ es.sizeK Qs := foldl_max_ge _ 1

theorem size_le_of_mem_atoms {a : Expr} : ∀ {e : Expr}, a ∈ e.atoms → a.size ≤ e.size
  | .not x, h => by have := size_le_of_mem_atoms (e := x) h; simp [size]; omega
  | .and x y, h | .or x y, h => by
      simp only [atoms, List.mem_append] at h
      rcases h with h | h
      · have := size_le_of_mem_atoms h; simp [size]; omega
      · have := size_le_of_mem_atoms h; simp [size]; omega
  | .val _, h | .sym _, h | .bin _ _ _, h | .eq _ _, h | .le _ _, h => by
      simp only [atoms, List.mem_singleton] at h; subst h; exact Nat.le_refl _

theorem vals_of_mem_atoms {a : Expr} : ∀ {e : Expr}, a ∈ e.atoms → ∀ v ∈ a.vals, v ∈ e.vals
  | .not x, h, v, hv => vals_of_mem_atoms (e := x) h v hv
  | .and x y, h, v, hv | .or x y, h, v, hv => by
      simp only [atoms, List.mem_append] at h; simp only [vals, List.mem_append]
      exact h.imp (fun h => vals_of_mem_atoms h v hv) (fun h => vals_of_mem_atoms h v hv)
  | .val _, h, v, hv | .sym _, h, v, hv | .bin _ _ _, h, v, hv | .eq _ _, h, v, hv
  | .le _ _, h, v, hv => by simp only [atoms, List.mem_singleton] at h; subst h; exact hv

theorem syms_of_mem_atoms {a e : Expr} (h : a ∈ e.atoms) : ∀ α ∈ a.syms, α ∈ e.syms :=
  fun α hα => (mem_syms_iff_atoms e α).2 ⟨a, h, hα⟩

/-- An atom of a base expression is small. -/
theorem small_of_base {Qs : List Expr} {e a : Expr} (he : e ∈ es.baseExprs Qs) (ha : a ∈ e.atoms)
    (k : Nat) : Small (es.symU Qs) (fun v => v ∈ es.valU Qs) (es.sizeK Qs ^ (k + 1)) a := by
  refine ⟨?_, fun α hα => ?_, fun v hv => ?_⟩
  · have h1 := size_le_of_mem_atoms ha
    have h2 := size_le_sizeK he
    have h3 : es.sizeK Qs ≤ es.sizeK Qs ^ (k + 1) :=
      Nat.le_self_pow (by omega) _
    omega
  · exact List.mem_append_left _ (List.mem_flatMap.2 ⟨e, he, syms_of_mem_atoms ha α hα⟩)
  · exact List.mem_flatMap.2 ⟨e, he, vals_of_mem_atoms ha v hv⟩

theorem atoms_conjunct {P c : Expr} (h : c ∈ P.conjuncts) : ∀ a ∈ c.atoms, a ∈ P.atoms := by
  induction P with
  | and x y ihx ihy =>
      simp only [conjuncts, List.mem_append] at h
      intro a ha; simp only [atoms, List.mem_append]
      exact h.elim (fun h => Or.inl (ihx h a ha)) (fun h => Or.inr (ihy h a ha))
  | _ => simp only [conjuncts, List.mem_singleton] at h; subst h; exact fun _ h => h

theorem atoms_foldl_and {a : Expr} :
    ∀ (L : List Expr) (acc : Expr), a ∈ (L.foldl .and acc).atoms → a ∈ acc.atoms ∨ ∃ e ∈ L, a ∈ e.atoms
  | [], _, h => Or.inl h
  | e :: L, acc, h => by
      rcases atoms_foldl_and L _ h with h | ⟨x, hx, h⟩
      · simp only [atoms, List.mem_append] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨e, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, h⟩

theorem atoms_conj {a : Expr} {L : List Expr} (h : a ∈ (Expr.conj L).atoms) :
    a = Expr.tt ∨ ∃ e ∈ L, a ∈ e.atoms := by
  rcases atoms_foldl_and L _ h with h | h
  · left; simpa [tt, atoms] using h
  · exact Or.inr h

theorem atoms_liftPred {a A B : Expr} (h : a ∈ (Expr.liftPred A B).atoms) :
    a = Expr.tt ∨ a ∈ A.atoms ∨ a ∈ B.atoms := by
  simp only [liftPred, atoms, List.mem_append] at h
  rcases h with h | h | h <;> rcases atoms_conj h with h | ⟨c, hc, ha⟩
  all_goals first
    | exact Or.inl h
    | (simp only [List.mem_filter] at hc
       first
        | exact Or.inr (Or.inl (atoms_conjunct hc.1 a ha))
        | exact Or.inr (Or.inr (atoms_conjunct hc.1 a ha)))

theorem atoms_of_conjEq {P P' Pw : Expr} (h : P.ConjEq (.and P' Pw)) :
    ∀ a ∈ P'.atoms, a ∈ P.atoms := by
  intro a ha
  have : ∀ c ∈ P'.conjuncts, c ∈ P.conjuncts := fun c hc =>
    (h c).2 (by simp only [conjuncts, List.mem_append]; exact Or.inl hc)
  -- an atom of `P'` is an atom of one of its conjuncts
  have key : ∀ Q : Expr, a ∈ Q.atoms → ∃ c ∈ Q.conjuncts, a ∈ c.atoms := by
    intro Q
    induction Q with
    | and x y ihx ihy =>
        intro hq; simp only [atoms, List.mem_append] at hq
        rcases hq with hq | hq
        · obtain ⟨c, hc, h'⟩ := ihx hq; exact ⟨c, by simp [conjuncts, hc], h'⟩
        · obtain ⟨c, hc, h'⟩ := ihy hq; exact ⟨c, by simp [conjuncts, hc], h'⟩
    | _ => intro hq; exact ⟨_, List.mem_singleton_self _, hq⟩
  obtain ⟨c, hc, h'⟩ := key P' ha
  exact atoms_conjunct (this c hc) a h'

theorem valresOf_atoms {Qs : List Expr} {e : EventId} {a : Expr} (h : a ∈ (es.valresOf e).atoms) :
    ∃ x ∈ es.baseExprs Qs, a ∈ x.atoms := by
  unfold valresOf at h
  cases hev : es.ev e with
  | none => rw [hev] at h; exact ⟨Expr.tt, List.mem_cons_self .., h⟩
  | some ev =>
      rw [hev] at h
      simp only [Option.map_some, Option.getD_some, Event.valres] at h
      rcases atoms_conj h with rfl | ⟨g, hg, ha⟩
      · exact ⟨Expr.tt, List.mem_cons_self .., by simp [tt, atoms]⟩
      · obtain ⟨gd, hgd, rfl⟩ := List.mem_map.1 hg
        refine ⟨gd.expr, ?_, ha⟩
        simp only [baseExprs, List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap]
        exact Or.inr (Or.inr ⟨ev, mem_events_of_ev hev, Or.inl (Or.inl (List.mem_map_of_mem hgd))⟩)

theorem base_of_val {Qs : List Expr} {ev : Event} {v : Expr} (hev : ev ∈ es.events)
    (hv : ev.val = some v) : v ∈ es.baseExprs Qs := by
  simp only [baseExprs, List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap]
  exact Or.inr (Or.inr ⟨ev, hev, Or.inr (by simp [hv])⟩)

theorem base_of_loc {Qs : List Expr} {ev : Event} {l : Expr} (hev : ev ∈ es.events)
    (hl : ev.loc = some l) : l ∈ es.baseExprs Qs := by
  simp only [baseExprs, List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap]
  exact Or.inr (Or.inr ⟨ev, hev, Or.inl (Or.inr (by simp [hl]))⟩)

theorem small_mono {SU : List Sym} {VP : Val → Prop} {n m : Nat} {e : Expr} (h : n ≤ m)
    (hs : Small SU VP n e) : Small SU VP m e := ⟨Nat.le_trans hs.1 h, hs.2⟩

theorem pow_mono_succ {K k : Nat} (hK : 1 ≤ K) : K ^ (k + 1) ≤ K ^ (k + 1 + 1) :=
  Nat.pow_le_pow_right hK (by omega)

theorem valres_atoms {Qs : List Expr} {w : Event} (hw : w ∈ es.events) {a : Expr}
    (h : a ∈ w.valres.atoms) : ∃ x ∈ es.baseExprs Qs, a ∈ x.atoms := by
  rcases atoms_conj h with rfl | ⟨g, hg, ha⟩
  · exact ⟨Expr.tt, List.mem_cons_self .., by simp [tt, atoms]⟩
  · obtain ⟨gd, hgd, rfl⟩ := List.mem_map.1 hg
    refine ⟨gd.expr, ?_, ha⟩
    simp only [baseExprs, List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap]
    exact Or.inr (Or.inr ⟨w, hw, Or.inl (Or.inl (List.mem_map_of_mem hgd))⟩)

theorem base_of_Q {Qs : List Expr} {Q : Expr} (h : Q ∈ Qs) : Q ∈ es.baseExprs Qs := by
  simp [baseExprs, h]

theorem small_replace {SU : List Sym} {VP : Val → Prop} {n K : Nat} {a p q : Expr}
    (ha : Small SU VP n a) (hq : Small SU VP K q) : Small SU VP (n * K) (a.replace p q) := by
  refine ⟨?_, fun α hα => ?_, fun v hv => ?_⟩
  · have := size_replace p q a
    exact Nat.le_trans this (Nat.mul_le_mul ha.1 hq.1)
  · rcases syms_replace p q a α hα with h | h
    · exact ha.2.1 α h
    · exact hq.2.1 α h
  · rcases vals_replace p q a v hv with h | h
    · exact ha.2.2 v h
    · exact hq.2.2 v h

/-- **The atoms of every predicate are small**: of size at most
    `K^(|F|+1)`, with symbols and values from the structure. -/
theorem GenR.atoms_small {Ω : Pred} {Qs : List Expr} {wk : Bool} (hva : es.ValsAtomic)
    {j : Justification} (h : es.GenR Ω Qs wk j) :
    ∀ a ∈ j.P.atoms, Small (es.symU Qs) (fun v => v ∈ es.valU Qs) (es.sizeK Qs ^ (j.δ.f.length + 1)) a := by
  induction h with
  | pre hw hj _ =>
      obtain ⟨-, hδ, hP, -⟩ := preJust_D hj
      intro a ha; rw [hP] at ha
      obtain ⟨x, hx, hax⟩ := valres_atoms (Qs := Qs) hw ha
      exact small_of_base hx hax _
  | va _ _ _ _ ih => exact ih
  | str Q S hQ _ _ _ _ _ ih =>
      intro a ha
      simp only [strPred, atoms, List.mem_append] at ha
      rcases ha with ha | ha | ha
      · exact ih a ha
      · exact small_of_base (base_of_Q hQ) ha _
      · rcases atoms_conj ha with rfl | ⟨e, he, hae⟩
        · exact small_of_base (List.mem_cons_self ..) (by simp [tt, atoms]) _
        · obtain ⟨x, -, rfl⟩ := List.mem_map.1 he
          obtain ⟨y, hy, hay⟩ := valresOf_atoms (Qs := Qs) hae
          exact small_of_base hy hay _
  | @fwd j₁ o x e b e₁ e₂ ev₁ ev₂ v₁ v₂ _ _ _ h₁ h₂ hv₁ hv₂ _ _ ih =>
      have m₁ := mem_events_of_ev h₁
      have m₂ := mem_events_of_ev h₂
      intro a ha
      simp only [List.length_append, List.length_singleton]
      rw [atoms_replace (hva ev₂ m₂ v₂ hv₂) (hva ev₁ m₁ v₁ hv₁)] at ha
      obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.1 ha
      have hs := small_replace (p := v₂) (ih a₀ ha₀)
        (show Small (es.symU Qs) (fun v => v ∈ es.valU Qs) (es.sizeK Qs) v₁ from
          ⟨size_le_sizeK (base_of_val m₁ hv₁),
           fun α hα => List.mem_append_left _ (List.mem_flatMap.2 ⟨v₁, base_of_val m₁ hv₁, hα⟩),
           fun v hv => List.mem_flatMap.2 ⟨v₁, base_of_val m₁ hv₁, hv⟩⟩)
      rw [← Nat.pow_succ] at hs
      exact hs
  | we _ _ _ _ ih => exact ih
  | @lift j₁ j₂ Λ _ _ hδ _ _ _ _ _ _ _ hpo _ ih₁ ih₂ =>
      intro a ha
      rcases atoms_liftPred ha with rfl | ha | ha
      · exact small_of_base (List.mem_cons_self ..) (by simp [tt, atoms]) _
      · have hsyms : ∀ α ∈ a.syms, α ∈ (j₁.P.rename Λ).syms := syms_of_mem_atoms ha
        rw [atoms_rename] at ha
        obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.1 ha
        have h0 := ih₁ a₀ ha₀
        rw [hδ] at h0
        refine ⟨by rw [size_rename]; exact h0.1, fun α hα => ?_, fun v hv => ?_⟩
        · exact List.mem_append_right _ (List.mem_map.2 ⟨_, hpo α (hsyms α hα), rfl⟩)
        · rw [vals_rename] at hv; exact h0.2.2 v hv
      · exact ih₂ a ha
  | weak _ _ hc _ _ ih => exact fun a ha => ih a (atoms_of_conjEq hc a ha)


/-! ## The justified writes -/

variable (es)

/-- The values Value Assignment can substitute for a symbol of the structure:
    determined by a predicate of the closure. -/
def InV (Ω : Pred) (Qs : List Expr) (wk : Bool) (v : Val) : Prop :=
  ∃ j₁, es.GenR Ω Qs wk j₁ ∧ ∃ α ∈ es.symU Qs, Sat j₁.P.holds ∧
    EquivUnder j₁.P.holds (.sym α) (.val v)

/-- The justified write is a copy of an event, with the same expressions or,
    for a write, with small ones. -/
def WShape (Ω : Pred) (Qs : List Expr) (wk : Bool) (j : Justification) : Prop :=
  ∃ ev ∈ es.events, j.w = { ev with kind := j.w.kind } ∧
    (j.w.kind = ev.kind ∨ ∃ o x e b x' e', ev.kind = .write o x e b ∧ j.w.kind = .write o x' e' b ∧
      Small (es.symU Qs) (fun v => v ∈ es.valU Qs ∨ es.InV Ω Qs wk v)
        (es.sizeK Qs ^ (j.δ.f.length + 1)) x' ∧
      Small (es.symU Qs) (fun v => v ∈ es.valU Qs ∨ es.InV Ω Qs wk v)
        (es.sizeK Qs ^ (j.δ.f.length + 1)) e')

variable {es}

theorem small_base_W {Qs : List Expr} {VP : Val → Prop} {x : Expr} (hx : x ∈ es.baseExprs Qs)
    (hVP : ∀ v, v ∈ es.valU Qs → VP v) (k : Nat) :
    Small (es.symU Qs) VP (es.sizeK Qs ^ (k + 1)) x :=
  ⟨Nat.le_trans (size_le_sizeK hx) (Nat.le_self_pow (by omega) _),
   fun α hα => List.mem_append_left _ (List.mem_flatMap.2 ⟨x, hx, hα⟩),
   fun v hv => hVP v (List.mem_flatMap.2 ⟨x, hx, hv⟩)⟩

/-- From the shape of a justified write `W o x e b`: its event and the
    smallness of `x` and `e`. -/
theorem WShape.write {Ω : Pred} {Qs : List Expr} {wk : Bool} {j : Justification}
    (h : es.WShape Ω Qs wk j) {o : MemOrd} {x e : Expr} {b : Bool}
    (hk : j.w.kind = .write o x e b) :
    ∃ ev ∈ es.events, j.w = { ev with kind := j.w.kind } ∧ (∃ x₀ e₀, ev.kind = .write o x₀ e₀ b) ∧
      Small (es.symU Qs) (fun v => v ∈ es.valU Qs ∨ es.InV Ω Qs wk v)
        (es.sizeK Qs ^ (j.δ.f.length + 1)) x ∧
      Small (es.symU Qs) (fun v => v ∈ es.valU Qs ∨ es.InV Ω Qs wk v)
        (es.sizeK Qs ^ (j.δ.f.length + 1)) e := by
  obtain ⟨ev, hev, hw, hc | ⟨o', x₀, e₀, b', x', e', hk₀, hk', hx, he⟩⟩ := h
  · rw [hk] at hc
    have hl : ev.loc = some x := by simp [Event.loc, ← hc]
    have hv : ev.val = some e := by simp [Event.val, ← hc]
    exact ⟨ev, hev, hw, ⟨x, e, hc.symm⟩, small_base_W (base_of_loc hev hl) (fun v h => Or.inl h) _,
      small_base_W (base_of_val hev hv) (fun v h => Or.inl h) _⟩
  · rw [hk] at hk'; cases hk'
    exact ⟨ev, hev, hw, ⟨x₀, e₀, hk₀⟩, hx, he⟩

theorem small_subst {SU : List Sym} {VP : Val → Prop} {n : Nat} {x : Expr} {α : Sym} {v : Val}
    (hx : Small SU VP n x) (hv : α ∈ x.syms → VP v) : Small SU VP n (x.subst α (.val v)) := by
  by_cases hα : α ∈ x.syms
  · refine ⟨by rw [size_subst_val]; exact hx.1, fun β hβ => hx.2.1 β (syms_subst_val α v x β hβ),
      fun w hw => ?_⟩
    rcases vals_subst_val α v x w hw with h | rfl
    · exact hx.2.2 w h
    · exact hv hα
  · rw [subst_of_not_mem x hα]; exact hx

theorem GenR.wshape {Ω : Pred} {Qs : List Expr} {wk : Bool}
    {j : Justification} (h : es.GenR Ω Qs wk j) : es.WShape Ω Qs wk j := by
  induction h with
  | @pre w j hw hj _ =>
      obtain ⟨hjw, -, -, -⟩ := preJust_D hj
      exact ⟨w, hw, by rw [hjw], Or.inl (by rw [hjw])⟩
  | @va j₁ o x e b α v hg hk he hs ih =>
      obtain ⟨ev, hev, hw, ⟨x₀, e₀, hk₀⟩, hx, hex⟩ := ih.write hk
      have hV : α ∈ x.syms ∨ α ∈ e.syms → es.InV Ω Qs wk v := fun hα => by
        obtain ⟨f, hf, -⟩ := hs
        refine ⟨j₁, hg, α, ?_, ⟨f, hf⟩, he⟩
        rcases hα with hα | hα
        · exact hx.2.1 α hα
        · exact hex.2.1 α hα
      refine ⟨ev, hev, ?_, Or.inr ⟨o, x₀, e₀, b, _, _, hk₀, rfl,
        small_subst hx (fun h => Or.inr (hV (Or.inl h))),
        small_subst hex (fun h => Or.inr (hV (Or.inr h)))⟩⟩
      simp only; rw [hw]
  | str _ _ _ _ _ _ _ _ ih => exact ih
  | @fwd j₁ o x e b e₁ e₂ ev₁ ev₂ v₁ v₂ _ hk _ h₁ _ hv₁ _ _ _ ih =>
      obtain ⟨ev, hev, hw, ⟨x₀, e₀, hk₀⟩, hx, hex⟩ := ih.write hk
      have m₁ := mem_events_of_ev h₁
      have hq : Small (es.symU Qs) (fun v => v ∈ es.valU Qs ∨ es.InV Ω Qs wk v) (es.sizeK Qs) v₁ :=
        ⟨size_le_sizeK (base_of_val m₁ hv₁),
         fun α hα => List.mem_append_left _ (List.mem_flatMap.2 ⟨v₁, base_of_val m₁ hv₁, hα⟩),
         fun v hv => Or.inl (List.mem_flatMap.2 ⟨v₁, base_of_val m₁ hv₁, hv⟩)⟩
      have sx := small_replace (p := v₂) hx hq
      have se := small_replace (p := v₂) hex hq
      rw [← Nat.pow_succ] at sx se
      refine ⟨ev, hev, ?_, Or.inr ⟨o, x₀, e₀, b, _, _, hk₀, rfl, ?_, ?_⟩⟩
      · simp only; rw [hw]
      · simpa using sx
      · simpa using se
  | we _ _ _ _ ih =>
      obtain ⟨ev, hev, hw, hc⟩ := ih
      exact ⟨ev, hev, hw, hc⟩
  | lift _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₂ => exact ih₂
  | weak _ _ _ _ _ ih => exact ih

theorem effSyms_base {Qs : List Expr} {ev : Event} (hev : ev ∈ es.events) :
    ∀ α ∈ ev.effSyms, α ∈ es.symU Qs := by
  intro α hα
  apply List.mem_append_left
  unfold Event.effSyms at hα
  split at hα
  · rename_i o x v b hk
    rcases List.mem_append.1 hα with h | h
    · exact List.mem_flatMap.2 ⟨x, base_of_loc hev (by simp [Event.loc, hk]), h⟩
    · exact List.mem_flatMap.2 ⟨v, base_of_val hev (by simp [Event.val, hk]), h⟩
  · rename_i a s hk
    exact List.mem_flatMap.2 ⟨s, base_of_val hev (by simp [Event.val, hk]), hα⟩
  · rename_i l hk
    exact List.mem_flatMap.2 ⟨l, base_of_loc hev (by simp [Event.loc, hk]), hα⟩
  · cases hα

/-- The dependencies are symbols of the structure. -/
theorem GenR.D_sub {Ω : Pred} {Qs : List Expr} {wk : Bool}
    {j : Justification} (h : es.GenR Ω Qs wk j) : ∀ a ∈ j.D, a ∈ es.symU Qs := by
  intro a ha
  rw [h.inv.dmem] at ha
  obtain ⟨ev, hev, hw, hc | ⟨o, x, e, b, x', e', hk₀, hk, hx, he⟩⟩ := h.wshape
  · have : j.w.effSyms = ev.effSyms := by simp [Event.effSyms, hc]
    rw [this] at ha; exact effSyms_base hev a ha
  · simp only [Event.effSyms, hk, List.mem_append] at ha
    exact ha.elim (hx.2.1 a) (he.2.1 a)

/-! ## Truth tables and the finiteness theorem -/

/-- The truth table of a predicate over a list of atoms. -/
def tableOf (A : List Expr) (P : Expr) : List (Option Bool) :=
  (allFuns A tvals).map fun l => kval (assignOf l) P

theorem peq_of_table {A : List Expr} {P P' : Expr} (hP : ∀ a ∈ P.atoms, a ∈ A)
    (hP' : ∀ a ∈ P'.atoms, a ∈ A) (h : tableOf A P = tableOf A P') : PEq P P' := by
  intro ρ
  have hl := map_mem_allFuns tvals ρ A (fun a _ => mem_tvals _)
  have h' := (List.map_inj_left.1 h) _ hl
  have hag : ∀ a ∈ A, assignOf (A.map fun a => (a, ρ a)) a = ρ a := fun a ha => by
    simp [assignOf, lookup_map_self ρ A a ha]
  rw [kval_congr P (fun a ha => (hag a (hP a ha)).symm),
    kval_congr P' (fun a ha => (hag a (hP' a ha)).symm)]
  exact h'

/-- Pairs from two lists. -/
def prodL {α β : Type} (L : List α) (M : List β) : List (α × β) := L.flatMap fun a => M.map (a, ·)

theorem length_prodL {α β : Type} (L : List α) (M : List β) :
    (prodL L M).length = L.length * M.length := by
  induction L with
  | nil => simp [prodL]
  | cons a L ih =>
      simp only [prodL, List.flatMap_cons, List.length_append, List.length_map] at ih ⊢
      rw [ih, List.length_cons, Nat.succ_mul]; omega

theorem mem_prodL {α β : Type} {L : List α} {M : List β} {a : α} {b : β} (ha : a ∈ L) (hb : b ∈ M) :
    (a, b) ∈ prodL L M := List.mem_flatMap.2 ⟨a, ha, List.mem_map.2 ⟨b, hb, rfl⟩⟩

variable (es)

/-- The atom universe: the small expressions at the largest exponent. -/
def atomU (Qs : List Expr) : List Expr :=
  allExprs (es.symU Qs) (es.valU Qs) (es.sizeK Qs ^ (es.events.length + 1))

/-- The truth tables over the atom universe. -/
def tableU (Qs : List Expr) : List (List (Option Bool)) :=
  allLists tvals (allFuns (es.atomU Qs) tvals).length

variable {es}

theorem atoms_mem_atomU {Ω : Pred} {Qs : List Expr} {wk : Bool} (hva : es.ValsAtomic)
    {j : Justification} (h : es.GenR Ω Qs wk j) : ∀ a ∈ j.P.atoms, a ∈ es.atomU Qs := by
  intro a ha
  have hs := h.atoms_small hva a ha
  apply mem_allExprs
  exact small_mono (Nat.pow_le_pow_right (one_le_sizeK Qs) (by have := h.inv.length_le.1; omega)) hs

theorem table_mem {A : List Expr} (P : Expr) :
    tableOf A P ∈ allLists tvals (allFuns A tvals).length := by
  have := mem_allLists (vs := tvals) (tableOf A P) (fun x _ => mem_tvals x)
  simpa [tableOf] using this

/-- The values Value Assignment substitutes are finitely many: at most one per
    truth table and symbol. -/
theorem InV_finite (Ω : Pred) (Qs : List Expr) (wk : Bool) (hva : es.ValsAtomic) :
    ∃ V : List Val, (∀ v, es.InV Ω Qs wk v → v ∈ V) ∧
      V.length ≤ (es.tableU Qs).length * (es.symU Qs).length := by
  classical
  let g : List (Option Bool) × Sym → Option Val := fun tα =>
    if h : ∃ v j₁, es.GenR Ω Qs wk j₁ ∧ tableOf (es.atomU Qs) j₁.P = tα.1 ∧ Sat j₁.P.holds ∧
        EquivUnder j₁.P.holds (.sym tα.2) (.val v) then some (Classical.choose h) else none
  refine ⟨(prodL (es.tableU Qs) (es.symU Qs)).filterMap g, fun v ⟨j₁, hg, α, hα, hs, he⟩ => ?_, ?_⟩
  · refine List.mem_filterMap.2 ⟨(tableOf (es.atomU Qs) j₁.P, α),
      mem_prodL (table_mem _) hα, ?_⟩
    have hex : ∃ v j₁', es.GenR Ω Qs wk j₁' ∧ tableOf (es.atomU Qs) j₁'.P = tableOf (es.atomU Qs) j₁.P ∧
        Sat j₁'.P.holds ∧ EquivUnder j₁'.P.holds (.sym α) (.val v) := ⟨v, j₁, hg, rfl, hs, he⟩
    simp only [g, dif_pos hex, Option.some.injEq]
    obtain ⟨j₁', hg', ht, -, he'⟩ := Classical.choose_spec hex
    have hpeq := peq_of_table (atoms_mem_atomU hva hg') (atoms_mem_atomU hva hg) ht
    obtain ⟨f, hf⟩ := hs
    have e1 := he f hf (f α) v rfl rfl
    have e2 := he' f ((hpeq.holds_iff f).2 hf) (f α) _ rfl rfl
    exact e2.symm.trans e1
  · exact Nat.le_trans (List.length_filterMap_le _ _) (by rw [length_prodL]; exact Nat.le_refl _)

/-! ### Keys -/

variable (es)

/-- The key of a justification: the truth table of its predicate, the
    symbols of the structure in its dependencies, its context and its write. -/
def keyOf (Qs : List Expr) (j : Justification) : List (Option Bool) × List Bool × FwdCtx × Event :=
  (tableOf (es.atomU Qs) j.P, (es.symU Qs).map (fun a => decide (a ∈ j.D)), j.δ, j.w)

/-- The candidate forwarding contexts. -/
def ctxU : List FwdCtx :=
  (prodL (allListsUpTo (prodL es.ids es.ids) es.events.length)
    (allListsUpTo (prodL es.ids es.ids) es.events.length)).map fun fw => ({ f := fw.1, we := fw.2 } : FwdCtx)

/-- The candidate written expressions, over the values `V`. -/
def exprU (Qs : List Expr) (V : List Val) : List Expr :=
  allExprs (es.symU Qs) (es.valU Qs ++ V) (es.sizeK Qs ^ (es.events.length + 1))

/-- The candidate justified writes. -/
def writeU (Qs : List Expr) (V : List Val) : List Event :=
  es.events.flatMap fun ev => ev ::
    match ev.kind with
    | .write o _ _ b => (es.exprU Qs V).flatMap fun x' => (es.exprU Qs V).map fun e' =>
        { ev with kind := .write o x' e' b }
    | _ => []

/-- The candidate keys. -/
def keyU (Qs : List Expr) (V : List Val) : List (List (Option Bool) × List Bool × FwdCtx × Event) :=
  prodL (es.tableU Qs) (prodL (allLists [true, false] (es.symU Qs).length)
    (prodL es.ctxU (es.writeU Qs V)))

/-- The number of expressions of size at most `n` over `s` symbols and `v`
    values. -/
def cntE (s v : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => v + s + cntE s v n + 11 * (cntE s v n * cntE s v n)

/-- A computable bound on the number of pairwise inequivalent justifications of
    the closure. -/
def boundB (Qs : List Expr) : Nat :=
  let c := cntE (es.symU Qs).length ((es.valU Qs).length + (es.tableU Qs).length * (es.symU Qs).length)
    (es.sizeK Qs ^ (es.events.length + 1))
  (es.tableU Qs).length * ((allLists [true, false] (es.symU Qs).length).length *
    (es.ctxU.length * (es.events.length * (1 + c * c))))

variable {es}

theorem length_flatMap_eq {α β : Type} {f : α → List β} {k : Nat} (h : ∀ a, (f a).length = k) :
    ∀ l : List α, (l.flatMap f).length = l.length * k
  | [] => by simp
  | a :: l => by
      rw [List.flatMap_cons, List.length_append, h a, length_flatMap_eq h l, List.length_cons,
        Nat.succ_mul]; omega

theorem length_flatMap_le {α β : Type} {f : α → List β} {k : Nat} (h : ∀ a, (f a).length ≤ k) :
    ∀ l : List α, (l.flatMap f).length ≤ l.length * k
  | [] => by simp
  | a :: l => by
      rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
      have := h a; have := length_flatMap_le h l; omega

theorem length_allExprs (SU : List Sym) (VU : List Val) :
    ∀ n, (allExprs SU VU n).length = cntE SU.length VU.length n
  | 0 => rfl
  | n + 1 => by
      simp only [allExprs, cntE, List.length_append, List.length_map]
      rw [length_flatMap_eq (k := 11) (fun _ => rfl), length_flatMap_eq (k := (allExprs SU VU n).length)
        (fun _ => by simp), length_allExprs SU VU n]
      omega

theorem cntE_mono {s v v' : Nat} (h : v ≤ v') : ∀ n, cntE s v n ≤ cntE s v' n
  | 0 => Nat.le_refl _
  | n + 1 => by
      have ih := cntE_mono (s := s) h n
      have := Nat.mul_le_mul ih ih
      simp only [cntE]; omega

theorem keyOf_mem {Ω : Pred} {Qs : List Expr} {wk : Bool} {V : List Val}
    (hV : ∀ v, es.InV Ω Qs wk v → v ∈ V) {j : Justification} (hj : es.GenR Ω Qs wk j) :
    es.keyOf Qs j ∈ es.keyU Qs V := by
  have hinv := hj.inv
  refine mem_prodL (table_mem _) (mem_prodL ?_ (mem_prodL ?_ ?_))
  · have := mem_allLists (vs := [true, false]) ((es.symU Qs).map fun a => decide (a ∈ j.D))
      (fun x _ => by cases x <;> simp)
    simpa using this
  · obtain ⟨hf, hw⟩ := hinv.length_le
    have hp : ∀ p ∈ j.δ.f ++ j.δ.we, p ∈ prodL es.ids es.ids := fun p hp => by
      obtain ⟨h1, h2⟩ := hinv.ends p hp; exact mem_prodL h1 h2
    refine List.mem_map.2 ⟨(j.δ.f, j.δ.we), mem_prodL ?_ ?_, rfl⟩
    · exact mem_allListsUpTo (fun p h => hp p (List.mem_append_left _ h)) hf
    · exact mem_allListsUpTo (fun p h => hp p (List.mem_append_right _ h)) hw
  · obtain ⟨ev, hev, hw, hc | ⟨o, x, e, b, x', e', hk₀, hk, hx, he⟩⟩ := hj.wshape
    · refine List.mem_flatMap.2 ⟨ev, hev, List.mem_cons.2 (Or.inl ?_)⟩
      rw [hw, hc]
    · refine List.mem_flatMap.2 ⟨ev, hev, List.mem_cons_of_mem _ ?_⟩
      have hmono : es.sizeK Qs ^ (j.δ.f.length + 1) ≤ es.sizeK Qs ^ (es.events.length + 1) :=
        Nat.pow_le_pow_right (one_le_sizeK Qs) (by have := hinv.length_le.1; omega)
      have up : ∀ y, Small (es.symU Qs) (fun v => v ∈ es.valU Qs ∨ es.InV Ω Qs wk v)
          (es.sizeK Qs ^ (j.δ.f.length + 1)) y → y ∈ es.exprU Qs V := fun y hy =>
        mem_allExprs _ _ ⟨Nat.le_trans hy.1 hmono, hy.2.1, fun v hv =>
          (hy.2.2 v hv).elim (fun h => List.mem_append_left _ h)
            (fun h => List.mem_append_right _ (hV v h))⟩
      simp only [hk₀]
      exact List.mem_flatMap.2 ⟨x', up x' hx, List.mem_map.2 ⟨e', up e' he, by rw [hw, hk]⟩⟩

theorem jeq_of_keyOf {Ω : Pred} {Qs : List Expr} {wk : Bool} (hva : es.ValsAtomic)
    {j j' : Justification} (hj : es.GenR Ω Qs wk j) (hj' : es.GenR Ω Qs wk j')
    (hk : es.keyOf Qs j = es.keyOf Qs j') : JEq j j' := by
  simp only [keyOf, Prod.mk.injEq] at hk
  obtain ⟨ht, hd, hδ, hw⟩ := hk
  refine ⟨peq_of_table (atoms_mem_atomU hva hj) (atoms_mem_atomU hva hj') ht, fun a => ?_, hδ, hw⟩
  by_cases ha : a ∈ es.symU Qs
  · have := (List.map_inj_left.1 hd) a ha
    simpa using this
  · exact ⟨fun h => absurd (hj.D_sub a h) ha, fun h => absurd (hj'.D_sub a h) ha⟩

theorem length_keyU_le {Qs : List Expr} {V : List Val}
    (hV : V.length ≤ (es.tableU Qs).length * (es.symU Qs).length) :
    (es.keyU Qs V).length ≤ es.boundB Qs := by
  unfold keyU boundB
  simp only [length_prodL]
  apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left
  unfold writeU
  have hx : (es.exprU Qs V).length ≤ cntE (es.symU Qs).length ((es.valU Qs).length +
      (es.tableU Qs).length * (es.symU Qs).length) (es.sizeK Qs ^ (es.events.length + 1)) := by
    unfold exprU; rw [length_allExprs, List.length_append]
    exact cntE_mono (by omega) _
  refine length_flatMap_le (fun ev => ?_) _
  rw [List.length_cons]
  have hxx := Nat.mul_le_mul hx hx
  split
  · rw [length_flatMap_eq (k := (es.exprU Qs V).length) (fun _ => by simp)]; omega
  · simp

/-- **The elaboration closure is finite up to equivalence.** Under
    `ValsAtomic` (Condition C1) and with Strengthening restricted to a finite
    list `Qs` (Condition C2), there is a finite list `U` of justifications of
    the closure such that every justification of the closure is equivalent to
    one of `U`: equal forwarding context and justified write, dependencies with
    the same members, and propositionally equivalent predicates. With or
    without Weakening. -/
theorem GenR.finite (Ω : Pred) (Qs : List Expr) (wk : Bool) (hva : es.ValsAtomic) :
    ∃ U : List Justification, ∀ j, es.GenR Ω Qs wk j → ∃ u ∈ U, es.GenR Ω Qs wk u ∧ JEq j u := by
  classical
  obtain ⟨V, hV, -⟩ := InV_finite Ω Qs wk hva
  let g : List (Option Bool) × List Bool × FwdCtx × Event → Option Justification := fun k =>
    if h : ∃ j, es.GenR Ω Qs wk j ∧ es.keyOf Qs j = k then some (Classical.choose h) else none
  refine ⟨(es.keyU Qs V).filterMap g, fun j hj => ?_⟩
  have hex : ∃ j', es.GenR Ω Qs wk j' ∧ es.keyOf Qs j' = es.keyOf Qs j := ⟨j, hj, rfl⟩
  obtain ⟨hg', hk'⟩ := Classical.choose_spec hex
  refine ⟨Classical.choose hex, List.mem_filterMap.2 ⟨es.keyOf Qs j, keyOf_mem hV hj,
    by simp [g, dif_pos hex]⟩, hg', (jeq_of_keyOf hva hg' hj hk').symm⟩

/-- **A computable bound**: a list of pairwise inequivalent justifications of
    the closure is no longer than `boundB`. -/
theorem GenR.bound {Ω : Pred} {Qs : List Expr} {wk : Bool} (hva : es.ValsAtomic)
    (L : List Justification) (hL : ∀ j ∈ L, es.GenR Ω Qs wk j)
    (hp : L.Pairwise (fun a b => ¬ JEq a b)) : L.length ≤ es.boundB Qs := by
  classical
  obtain ⟨V, hV, hVl⟩ := InV_finite Ω Qs wk hva
  refine Nat.le_trans (length_le_of_map_nodup (es.keyOf Qs) ?_ (fun j hj => keyOf_mem hV (hL j hj)))
    (length_keyU_le hVl)
  rw [List.Nodup, List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ hp
  intro a b ha hb hab heq
  exact hab (jeq_of_keyOf hva (hL a ha) (hL b hb) heq)

/-- Condition `a:locations.2` alone (a bounded `Q`) does not bound the
    closure: the bounded predicates `α = n` are pairwise inequivalent. -/
theorem strengthening_infinite (α : Sym) {n m : Nat} (h : n ≠ m) :
    ¬ ∀ f, (Expr.eq (.sym α) (.num n)).holds f ↔ (Expr.eq (.sym α) (.num m)).holds f := by
  intro hall
  have := (hall (fun _ => .num n)).1 (by simp [Expr.holds, Expr.eval, Expr.num])
  simp [Expr.holds, Expr.eval, Expr.num] at this
  exact h this

end EventStructure
