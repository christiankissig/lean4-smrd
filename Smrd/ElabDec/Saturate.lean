import Smrd.ElabDec.Deciders

/-!
# Deciding the elaboration closure by saturation

For a finite event structure `es` meeting `Bounded es Qs M` (Conditions C1–C3),
global guarantees given by a bounded predicate `ΩE`, an `Oracle` for bounded
arithmetic and a `RelSplit` for the event-only conditions of Forwarding and
Write Elision, membership in the Weakening-free closure `GenR ΩE.holds Qs false`
is decidable up to equivalence (`JEq`):

* `step L` applies every elaboration to the justifications of `L` with every
  relevant choice of its parameters, keeping the applications whose side
  conditions the deciders accept. The parameters range over finite lists: the
  pre-justifications; the symbols of the write for Value Assignment, with the
  value the oracle's witness gives (`α ≡_P v` fixes `v` on a satisfiable `P`);
  `Qs` and the sublists of the `⊑`-sources for Strengthening (only the members
  of `S` matter); pairs of events for Forwarding and Write Elision; pairs of
  justifications and relabellings of the premise's symbols and dependencies
  onto the `⊑`-sources and the other dependencies for Lifting (only `Λ` on
  those matters, and closed relabel equivalence does not depend on `Λ`).
* Every elaboration respects `JEq` in its premises (`step_complete`), so a
  list closed under `step` up to `JEq` contains a representative of every
  justification of the closure.
* `stage k` adds the new classes of `step` to a list of pairwise inequivalent
  justifications. A stage that adds nothing is closed. Each stage that adds
  something is longer, and lists of pairwise inequivalent justifications of the
  closure are no longer than `boundB` (`GenR.bound`), so `stage (boundB + 1)`
  is closed (`stage_closed`).

`decideJ j` searches the final stage (`decideJ_iff`). Weakening is excluded:
it can drop a conjunct of one predicate but not of a propositionally
equivalent one with a different conjunct structure (`weak_not_congr`), so the
classes of `JEq` do not determine what Weakening generates.
-/

open Expr Smrd.ElabDec

namespace EventStructure

variable (es : EventStructure) (O : Oracle) (ΩE : Expr) (Qs : List Expr) (sp : es.RelSplit)

/-- The relabelling an association list describes. -/
def relOf (l : List (Sym × Option Sym)) : Relabelling := fun α => (l.lookup α).getD none

def preC : List Justification :=
  es.events.filterMap fun w =>
    match preJust w with
    | some j => if O.sat w.valres then some j else none
    | none => none

def vaOne (r : Justification) (α : Sym) : Option Justification :=
  let v := O.witness r.P α
  match r.w.kind with
  | .write o x e b =>
      if O.equivB r.P (.sym α) (.val v) && O.satAnd r.P ΩE then
        some ⟨r.P, (x.subst α (.val v)).syms ++ (e.subst α (.val v)).syms, r.δ,
          { r.w with kind := .write o (x.subst α (.val v)) (e.subst α (.val v)) b }⟩
      else none
  | _ => none

def strOK (r : Justification) (Q : Expr) (S : List EventId) : Bool :=
  S.all (fun e => decide (e ∈ (es.strPred r.P Q S).syms) && !decide (e ∈ r.P.syms)) &&
  (es.strPred r.P Q S).syms.all (fun e => decide (e ∈ r.P.syms) || decide (e ∈ S)) &&
  S.all (fun e => r.δ.remapB e == e) &&
  S.all (fun e => decide (es.poR e r.w.id) && !es.ppoB O r.P r.δ r.w.id e) &&
  O.satAnd (es.strPred r.P Q S) ΩE

def strOne (r : Justification) (Q : Expr) (S : List EventId) : Option Justification :=
  if es.strOK O ΩE r Q S then some { r with P := es.strPred r.P Q S } else none

def fwdOne (r : Justification) (p : EventId × EventId) : Option Justification :=
  match r.w.kind, es.ev p.1, es.ev p.2 with
  | .write o x e b, some ev₁, some ev₂ =>
      match ev₁.val, ev₂.val with
      | some v₁, some v₂ =>
          if es.fwdBaseB O r p.1 p.2 && sp.fwdR p.1 p.2 &&
              ({ r.δ with f := r.δ.f ++ [p] } : FwdCtx).wfB && O.satAnd (r.P.replace v₂ v₁) ΩE then
            some { P := r.P.replace v₂ v₁
                   D := (e.replace v₂ v₁).syms ++ (x.replace v₂ v₁).syms
                   δ := { r.δ with f := r.δ.f ++ [p] }
                   w := { r.w with kind := .write o (x.replace v₂ v₁) (e.replace v₂ v₁) b } }
          else none
      | _, _ => none
  | _, _, _ => none

def weOne (r : Justification) (p : EventId × EventId) : Option Justification :=
  if es.fwdBaseB O r p.1 p.2 && sp.weR p.1 p.2 &&
      ({ r.δ with we := r.δ.we ++ [(p.2, p.1)] } : FwdCtx).wfB && O.satAnd r.P ΩE then
    some { r with δ := { r.δ with we := r.δ.we ++ [(p.2, p.1)] } }
  else none

def liftOK (r₁ r₂ : Justification) (Λ : Relabelling) (dom : List Sym) : Bool :=
  dom.all (fun a => dom.all fun b => (Λ a).isNone || Λ a != Λ b || a == b) &&
  es.crB O r₁.P r₂.P r₁.δ r₁.w r₂.w &&
  r₂.D.all (fun e => r₁.D.any fun α => Λ.app α == e) &&
  r₁.D.all (fun α => decide (Λ.app α ∈ r₂.D)) &&
  r₁.D.all (fun α => match es.ev α, es.ev (Λ.app α) with
    | some ev₁, some ev₂ => es.crB O r₁.P r₂.P r₁.δ ev₁ ev₂
    | _, _ => false) &&
  !decide (es.cls Event.isVol r₁.w.id) && !decide (es.cls Event.isVol r₂.w.id) &&
  (r₁.D ++ r₂.D).all (fun α => !decide (es.cls Event.isVol α)) &&
  (r₁.P.rename Λ).syms.all (fun α => decide (es.poR α r₂.w.id)) &&
  O.satAnd (Expr.liftPred (r₁.P.rename Λ) r₂.P) ΩE

def liftOne (r₁ r₂ : Justification) (l : List (Sym × Option Sym)) : Option Justification :=
  if r₁.δ == r₂.δ && es.liftOK O ΩE r₁ r₂ (relOf l) (r₁.P.syms ++ r₁.D) then
    some { r₂ with P := Expr.liftPred (r₁.P.rename (relOf l)) r₂.P }
  else none

/-- The relabellings Lifting is tried with. -/
def liftDom (r₁ r₂ : Justification) : List (List (Sym × Option Sym)) :=
  allFuns (r₁.P.syms ++ r₁.D) (none :: (es.po.map Prod.fst ++ r₂.D).map some)

/-- One round of elaborations. -/
def step (L : List Justification) : List Justification :=
  es.preC O ++
  L.flatMap (fun r =>
    r.w.effSyms.filterMap (vaOne O ΩE r) ++
    Qs.flatMap (fun Q => (subs (es.po.map Prod.fst)).filterMap (es.strOne O ΩE r Q)) ++
    (prodL es.ids es.ids).filterMap (es.fwdOne O ΩE sp r) ++
    (prodL es.ids es.ids).filterMap (es.weOne O ΩE sp r)) ++
  (prodL L L).flatMap (fun p => (es.liftDom p.1 p.2).filterMap (es.liftOne O ΩE p.1 p.2))

/-- Add the members of `M` not equivalent to one already kept. -/
def addNew (L M : List Justification) : List Justification :=
  M.foldl (fun acc j => if acc.any (fun r => jeqB r j) then acc else acc ++ [j]) L

def stage : Nat → List Justification
  | 0 => []
  | k + 1 => addNew (stage k) (es.step O ΩE Qs sp (stage k))

/-- **The decision procedure**: is `j` equivalent to a justification of the
    Weakening-free closure? -/
def decideJ (j : Justification) : Bool :=
  (es.stage O ΩE Qs sp (es.boundB Qs + 1)).any fun r => jeqB r j

/-! ## `addNew` -/

theorem addNew_foldl (M : List Justification) :
    ∀ L, (∃ E, M.foldl (fun acc j => if acc.any (fun r => jeqB r j) then acc else acc ++ [j]) L = L ++ E ∧
      ∀ x ∈ E, x ∈ M) ∧
    (∀ m ∈ M, ∃ r ∈ M.foldl (fun acc j => if acc.any (fun r => jeqB r j) then acc else acc ++ [j]) L,
      JEq r m) ∧
    (L.Pairwise (fun a b => ¬ JEq a b) →
      (M.foldl (fun acc j => if acc.any (fun r => jeqB r j) then acc else acc ++ [j]) L).Pairwise
        (fun a b => ¬ JEq a b)) := by
  induction M with
  | nil => intro L; exact ⟨⟨[], by simp, by simp⟩, by simp, id⟩
  | cons m M ih =>
      intro L
      simp only [List.foldl_cons]
      by_cases hm : L.any (fun r => jeqB r m) = true
      · rw [if_pos hm]
        obtain ⟨⟨E, hE, hEM⟩, hcov, hpw⟩ := ih L
        refine ⟨⟨E, hE, fun x hx => List.mem_cons_of_mem _ (hEM x hx)⟩, ?_, hpw⟩
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · obtain ⟨r, hr, hj⟩ := List.any_eq_true.1 hm
          exact ⟨r, by rw [hE]; exact List.mem_append_left _ hr, (jeqB_iff _ _).1 hj⟩
        · exact hcov x hx
      · rw [if_neg hm]
        obtain ⟨⟨E, hE, hEM⟩, hcov, hpw⟩ := ih (L ++ [m])
        refine ⟨⟨[m] ++ E, by rw [hE, List.append_assoc], fun x hx => ?_⟩, ?_, fun hL => hpw ?_⟩
        · rcases List.mem_append.1 hx with hx | hx
          · simp at hx; subst hx; exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (hEM x hx)
        · intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact ⟨x, by rw [hE]; simp, JEq.refl _⟩
          · exact hcov x hx
        · rw [List.pairwise_append]
          refine ⟨hL, by simp, fun a ha b hb hab => ?_⟩
          simp at hb; subst hb
          exact hm (List.any_eq_true.2 ⟨a, ha, (jeqB_iff _ _).2 hab⟩)

theorem addNew_ext (L M : List Justification) :
    ∃ E, addNew L M = L ++ E ∧ ∀ x ∈ E, x ∈ M := (addNew_foldl M L).1

theorem addNew_cover {L M : List Justification} : ∀ m ∈ M, ∃ r ∈ addNew L M, JEq r m :=
  (addNew_foldl M L).2.1

theorem addNew_pairwise {L M : List Justification} (h : L.Pairwise (fun a b => ¬ JEq a b)) :
    (addNew L M).Pairwise (fun a b => ¬ JEq a b) := (addNew_foldl M L).2.2 h

theorem addNew_grow {L M : List Justification} {m : Justification} (hm : m ∈ M)
    (hn : ∀ r ∈ L, ¬ JEq r m) : L.length < (addNew L M).length := by
  obtain ⟨E, hE, -⟩ := addNew_ext L M
  rw [hE, List.length_append]
  cases E with
  | nil =>
      obtain ⟨r, hr, hj⟩ := addNew_cover (L := L) m hm
      rw [hE, List.append_nil] at hr
      exact absurd hj (hn r hr)
  | cons _ _ => simp

theorem addNew_same {L M : List Justification} (h : ∀ m ∈ M, ∃ r ∈ L, JEq r m) : addNew L M = L := by
  obtain ⟨E, hE, hEM⟩ := addNew_ext L M
  have hp := addNew_pairwise (L := []) (M := M) List.Pairwise.nil
  -- every member of `E` is equivalent to a member of `L`, and the fold keeps none such
  cases E with
  | nil => simpa using hE
  | cons x E =>
      exfalso
      unfold addNew at hE
      -- the first element added was not equivalent to any element of `L`
      have key : ∀ (M : List Justification) (L : List Justification), (∀ m ∈ M, ∃ r ∈ L, JEq r m) →
          M.foldl (fun acc j => if acc.any (fun r => jeqB r j) then acc else acc ++ [j]) L = L := by
        intro M
        induction M with
        | nil => intro L _; rfl
        | cons m M ih =>
            intro L hML
            simp only [List.foldl_cons]
            obtain ⟨r, hr, hj⟩ := hML m (List.mem_cons_self ..)
            rw [if_pos (show (L.any fun r => jeqB r m) = true from
              List.any_eq_true.2 ⟨r, hr, (jeqB_iff r m).2 hj⟩)]
            exact ih L (fun m' hm' => hML m' (List.mem_cons_of_mem _ hm'))
      rw [key M L h] at hE
      simp at hE

/-! ## Soundness of `step` -/

theorem relOf_dom {l : List (Sym × Option Sym)} {dom : List Sym} {vs : List (Option Sym)}
    (hl : l ∈ allFuns dom vs) {a : Sym} {c : Sym} (h : relOf l a = some c) : a ∈ dom := by
  unfold relOf at h
  cases hlk : l.lookup a with
  | none => rw [hlk] at h; cases h
  | some v => exact (lookup_mem_of_mem_allFuns hl a v hlk).1


section sound

variable {es O ΩE Qs sp} {M : List Nat} (hb : es.Bounded Qs M) (hΩ : isBPred M ΩE = true)
include hb hΩ

omit hΩ in
theorem preC_sound {j : Justification} (h : j ∈ es.preC O) : es.GenR ΩE.holds Qs false j := by
  obtain ⟨w, hw, hj⟩ := List.mem_filterMap.1 h
  revert hj
  cases hp : preJust w with
  | none => simp
  | some j' =>
      simp only
      split
      · rename_i hs; intro he; cases he
        exact .pre hw hp ((O.sat_iff M _ (hb.valres hw)).1 hs)
      · simp

theorem vaOne_sound {r j : Justification} {α : Sym} (hr : es.GenR ΩE.holds Qs false r)
    (h : vaOne O ΩE r α = some j) : es.GenR ΩE.holds Qs false j := by
  have hP := hr.bpred hb
  unfold vaOne at h
  split at h
  · rename_i o x e b hk
    dsimp only at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      exact .va hr hk ((O.equivB_iff hP (isBPred_eq_term rfl rfl)).1 hc.1)
        ((O.satAnd_iff hP hΩ).1 hc.2)
    · cases h
  · cases h

theorem strOne_sound {r j : Justification} {Q : Expr} {S : List EventId} (hQ : Q ∈ Qs)
    (hr : es.GenR ΩE.holds Qs false r) (h : es.strOne O ΩE r Q S = some j) :
    es.GenR ΩE.holds Qs false j := by
  have hP := hr.bpred hb
  have hwf := hr.inv.wf
  unfold strOne at h
  split at h
  · rename_i hc
    cases h
    unfold strOK at hc
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not, Bool.or_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
    refine .str Q S hQ hr (fun e => ⟨fun he => h1 e he, fun ⟨he, hn⟩ => (h2 e he).resolve_left hn⟩)
      (fun e he => (FwdCtx.remap_iff hwf).2 (h3 e he)) (fun e he => ⟨(h4 e he).1, fun hp => ?_⟩)
      ((O.satAnd_iff (isBPred_strPred hb hP hQ S) hΩ).1 h5)
    have := (h4 e he).2
    rw [(ppoB_iff hb hP hwf).2 hp] at this; cases this
  · cases h

theorem fwdOne_sound {r j : Justification} {p : EventId × EventId}
    (hr : es.GenR ΩE.holds Qs false r) (h : es.fwdOne O ΩE sp r p = some j) :
    es.GenR ΩE.holds Qs false j := by
  have hP := hr.bpred hb
  have hwf := hr.inv.wf
  unfold fwdOne at h
  split at h
  · rename_i o x e b ev₁ ev₂ hk h₁ h₂
    split at h
    · rename_i v₁ v₂ hv₁ hv₂
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true] at hc
        obtain ⟨⟨⟨hfb, hfr⟩, hw⟩, hs⟩ := hc
        have hf : es.fwdRel r p.1 p.2 := (sp.fwd_iff r p.1 p.2).2 ⟨(fwdBaseB_iff hb hP hwf).1 hfb, hfr⟩
        exact .fwd hr hk hf h₁ h₂ hv₁ hv₂ (FwdCtx.wfB_iff.1 hw)
          ((O.satAnd_iff (isBPred_fwd_replace hb hP hf h₁ h₂ hv₁ hv₂) hΩ).1 hs)
      · cases h
    · cases h
  · cases h

theorem weOne_sound {r j : Justification} {p : EventId × EventId}
    (hr : es.GenR ΩE.holds Qs false r) (h : es.weOne O ΩE sp r p = some j) :
    es.GenR ΩE.holds Qs false j := by
  have hP := hr.bpred hb
  have hwf := hr.inv.wf
  unfold weOne at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨hfb, hfr⟩, hw⟩, hs⟩ := hc
    exact .we hr ((sp.we_iff r p.1 p.2).2 ⟨(fwdBaseB_iff hb hP hwf).1 hfb, hfr⟩)
      (FwdCtx.wfB_iff.1 hw) ((O.satAnd_iff hP hΩ).1 hs)
  · cases h

theorem liftOne_sound {r₁ r₂ j : Justification} {l : List (Sym × Option Sym)}
    (hl : l ∈ es.liftDom r₁ r₂)
    (hr₁ : es.GenR ΩE.holds Qs false r₁) (hr₂ : es.GenR ΩE.holds Qs false r₂)
    (h : es.liftOne O ΩE r₁ r₂ l = some j) : es.GenR ΩE.holds Qs false j := by
  have hP₁ := hr₁.bpred hb
  have hP₂ := hr₂.bpred hb
  have hwf := hr₁.inv.wf
  unfold liftOne at h
  split at h
  · rename_i hc
    cases h
    simp only [liftOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not] at hc
    obtain ⟨hδ, ⟨⟨⟨⟨⟨⟨⟨⟨⟨hinj, hcr⟩, hD1⟩, hD2⟩, hDcr⟩, hv1⟩, hv2⟩, hv3⟩, hpo⟩, hs⟩⟩ := hc
    refine .lift (relOf l) hr₁ hr₂ hδ ?_ ((crB_iff hb hP₁ hP₂ hwf _).1 hcr) ?_ ?_ hv1 hv2 hv3 hpo
      ((O.satAnd_iff (isBPred_liftPred (by rw [isBPred_rename]; exact hP₁) hP₂) hΩ).1 hs)
    · intro a b c ha hb'
      have hda := relOf_dom hl ha
      have hdb := relOf_dom hl hb'
      rcases hinj a hda b hdb with (h | h) | h
      · rw [ha] at h; cases h
      · exact absurd (ha.trans hb'.symm) (by simpa using h)
      · simpa using h
    · intro e
      exact ⟨fun he => by obtain ⟨α, hα, h⟩ := hD1 e he; exact ⟨α, hα, by simpa using h⟩,
        fun ⟨α, hα, h⟩ => h ▸ hD2 α hα⟩
    · intro α hα
      have := hDcr α hα
      revert this
      cases h₁ : es.ev α with
      | none => simp
      | some ev₁ =>
        cases h₂ : es.ev (Relabelling.app (relOf l) α) with
        | none => simp
        | some ev₂ =>
          intro hc
          exact ⟨ev₁, ev₂, rfl, rfl, (crB_iff hb hP₁ hP₂ hwf _).1 hc⟩
  · cases h

theorem step_sound {L : List Justification} (hL : ∀ r ∈ L, es.GenR ΩE.holds Qs false r) :
    ∀ j ∈ es.step O ΩE Qs sp L, es.GenR ΩE.holds Qs false j := by
  intro j hj
  simp only [step, List.mem_append, List.mem_flatMap, List.mem_filterMap] at hj
  rcases hj with (h | ⟨r, hr, (((⟨α, -, h⟩ | ⟨Q, hQ, S, -, h⟩) | ⟨p, -, h⟩) | ⟨p, -, h⟩)⟩) |
      ⟨⟨r₁, r₂⟩, hp, l, hl, h⟩
  · exact preC_sound hb h
  · exact vaOne_sound hb hΩ (hL r hr) h
  · exact strOne_sound hb hΩ hQ (hL r hr) h
  · exact fwdOne_sound hb hΩ (hL r hr) h
  · exact weOne_sound hb hΩ (hL r hr) h
  · simp only [prodL, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at hp
    obtain ⟨a, ha, b, hb', rfl, rfl⟩ := hp
    exact liftOne_sound hb hΩ hl (hL a ha) (hL b hb') h

end sound

/-! ## Completeness of `step` -/

theorem holds_eq_of_peq {P P' : Expr} (h : P.PEq P') : P.holds = P'.holds :=
  funext fun f => propext (h.holds_iff f)

theorem mem_syms_strPred {P Q : Expr} {S : List EventId} {α : Sym} :
    α ∈ (es.strPred P Q S).syms ↔ α ∈ P.syms ∨ α ∈ Q.syms ∨ ∃ e ∈ S, α ∈ (es.valresOf e).syms := by
  simp only [strPred, syms, List.mem_append, mem_syms_conj, List.mem_map]
  constructor
  · rintro (h | h | ⟨x, ⟨e, he, rfl⟩, hx⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨e, he, hx⟩)
  · rintro (h | h | ⟨e, he, hx⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨_, ⟨e, he, rfl⟩, hx⟩)

theorem syms_rename_mem {Λ : Relabelling} {P : Expr} {α : Sym} :
    α ∈ (P.rename Λ).syms ↔ ∃ β ∈ P.syms, Λ.app β = α := by
  rw [syms_rename, List.mem_map]; rfl

section complete

variable {es O ΩE Qs sp} {M : List Nat} (hb : es.Bounded Qs M) (hΩ : isBPred M ΩE = true)
include hb hΩ

theorem step_complete {L : List Justification} (hL : ∀ r ∈ L, es.GenR ΩE.holds Qs false r)
    (hcl : ∀ k ∈ es.step O ΩE Qs sp L, ∃ r ∈ L, JEq k r) :
    ∀ j, es.GenR ΩE.holds Qs false j → ∃ r ∈ L, JEq j r := by
  have hva := hb.valsAtomic
  have close : ∀ {j k : Justification}, k ∈ es.step O ΩE Qs sp L → JEq j k → ∃ r ∈ L, JEq j r :=
    fun hk hjk => by obtain ⟨r, hr, h⟩ := hcl _ hk; exact ⟨r, hr, hjk.trans h⟩
  have inPer : ∀ {r k : Justification}, r ∈ L →
      (k ∈ r.w.effSyms.filterMap (vaOne O ΩE r) ∨
        k ∈ Qs.flatMap (fun Q => (subs (es.po.map Prod.fst)).filterMap (es.strOne O ΩE r Q)) ∨
        k ∈ (prodL es.ids es.ids).filterMap (es.fwdOne O ΩE sp r) ∨
        k ∈ (prodL es.ids es.ids).filterMap (es.weOne O ΩE sp r)) →
      k ∈ es.step O ΩE Qs sp L := fun hr hk => by
    unfold step
    refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨_, hr, ?_⟩))
    rcases hk with h | h | h | h
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
    · exact List.mem_append_left _ (List.mem_append_right _ h)
    · exact List.mem_append_right _ h
  intro j hj
  induction hj with
  | @pre w j hw hj hs =>
      refine close (k := j) ?_ (JEq.refl _)
      simp only [step, List.mem_append]
      refine Or.inl (Or.inl (List.mem_filterMap.2 ⟨w, hw, ?_⟩))
      simp only [hj]
      rw [if_pos ((O.sat_iff M _ (hb.valres hw)).2 hs)]
  | @va j₁ o x e b α v hg₁ hk he hs ih =>
      obtain ⟨r₁, hr₁, hpeq, hD, hδ, hw⟩ := ih
      have hh := holds_eq_of_peq hpeq
      have hP := (hL r₁ hr₁).bpred hb
      have hk' : r₁.w.kind = .write o x e b := by rw [← hw]; exact hk
      by_cases hα : α ∈ x.syms ++ e.syms
      · -- the oracle's witness is the assigned value
        have hwit : O.witness r₁.P α = v := by
          obtain ⟨f, hf, -⟩ := hs
          obtain ⟨g, hg, hgα⟩ := O.witness_spec M r₁.P α hP ⟨f, by rw [← hh]; exact hf⟩
          rw [← hgα]; exact he g (by rw [hh]; exact hg) _ _ rfl rfl
        refine close (k := ⟨r₁.P, (x.subst α (.val v)).syms ++ (e.subst α (.val v)).syms, r₁.δ,
          { r₁.w with kind := .write o (x.subst α (.val v)) (e.subst α (.val v)) b }⟩)
          (inPer hr₁ (Or.inl (List.mem_filterMap.2 ⟨α, by simpa [Event.effSyms, hk'] using hα, ?_⟩)))
          ⟨hpeq, fun _ => Iff.rfl, hδ, by simp only; rw [hw]⟩
        unfold vaOne
        simp only [hk', hwit]
        rw [if_pos]
        simp only [Bool.and_eq_true]
        exact ⟨(O.equivB_iff hP (isBPred_eq_term rfl rfl)).2 (by rw [← hh]; exact he),
          (O.satAnd_iff hP hΩ).2 (by rw [← hh]; exact hs)⟩
      · have hαx : α ∉ x.syms := fun h => hα (List.mem_append_left _ h)
        have hαe : α ∉ e.syms := fun h => hα (List.mem_append_right _ h)
        refine ⟨r₁, hr₁, JEq.trans ?_ ⟨hpeq, hD, hδ, hw⟩⟩
        refine ⟨PEq.refl _, fun a => ?_, rfl, ?_⟩
        · simp only [subst_of_not_mem x hαx, subst_of_not_mem e hαe]
          rw [hg₁.inv.dmem a]; simp [Event.effSyms, hk]
        · simp only [subst_of_not_mem x hαx, subst_of_not_mem e hαe]
          rw [← hk]
  | @str j₁ Q S hQ hg₁ hS hrm hpo hs ih =>
      obtain ⟨r₁, hr₁, hpeq, hD, hδ, hw⟩ := ih
      have hh := holds_eq_of_peq hpeq
      have hP := (hL r₁ hr₁).bpred hb
      have hwf := (hL r₁ hr₁).inv.wf
      let S' := (es.po.map Prod.fst).filter (fun e => decide (e ∈ S))
      have hS' : ∀ e, e ∈ S' ↔ e ∈ S := fun e => by
        simp only [S', List.mem_filter, decide_eq_true_eq]
        exact ⟨fun h => h.2, fun h => ⟨List.mem_map.2 ⟨(e, j₁.w.id), (hpo e h).1, rfl⟩, h⟩⟩
      have hpe : (es.strPred j₁.P Q S).PEq (es.strPred r₁.P Q S') := by
        unfold strPred
        refine PEq.and hpeq (PEq.and (PEq.refl Q) (fun ρ => kval_conj_congr (fun x => ?_) ρ))
        simp only [List.mem_map, hS']
      have hsy : ∀ α, α ∈ (es.strPred r₁.P Q S').syms ↔ α ∈ (es.strPred j₁.P Q S).syms :=
        fun α => ⟨hpe.symm.mem_syms, hpe.mem_syms⟩
      have hPs : ∀ α, α ∈ r₁.P.syms ↔ α ∈ j₁.P.syms := fun α => ⟨hpeq.symm.mem_syms, hpeq.mem_syms⟩
      refine close (k := { r₁ with P := es.strPred r₁.P Q S' })
        (inPer hr₁ (Or.inr (Or.inl (List.mem_flatMap.2 ⟨Q, hQ, List.mem_filterMap.2
          ⟨S', filter_mem_subs _ _, ?_⟩⟩)))) ⟨hpe, hD, hδ, hw⟩
      unfold strOne
      rw [if_pos]
      unfold strOK
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', decide_eq_true_eq,
        decide_eq_false_iff_not, Bool.or_eq_true, beq_iff_eq]
      refine ⟨⟨⟨⟨fun e he => ?_, fun e he => ?_⟩, fun e he => ?_⟩, fun e he => ?_⟩, ?_⟩
      · rw [hS'] at he; rw [hsy, hPs]; exact (hS e).1 he
      · rw [hsy] at he; rw [hPs, hS']
        by_cases h : e ∈ j₁.P.syms
        · exact Or.inl h
        · exact Or.inr ((hS e).2 ⟨he, h⟩)
      · rw [hS'] at he; rw [← FwdCtx.remap_iff hwf, ← hδ]; exact hrm e he
      · rw [hS'] at he
        refine ⟨by rw [← hw]; exact (hpo e he).1, ?_⟩
        cases hc : es.ppoB O r₁.P r₁.δ r₁.w.id e
        · rfl
        · exact absurd (by rw [hh, hδ, hw]; exact (ppoB_iff hb hP hwf).1 hc) (hpo e he).2
      · rw [O.satAnd_iff (isBPred_strPred hb hP hQ S') hΩ, ← holds_eq_of_peq hpe]; exact hs
  | @fwd j₁ o x e b e₁ e₂ ev₁ ev₂ v₁ v₂ hg₁ hk hf h₁ h₂ hv₁ hv₂ hwf' hs ih =>
      obtain ⟨r₁, hr₁, hpeq, hD, hδ, hw⟩ := ih
      have hh := holds_eq_of_peq hpeq
      have hP := (hL r₁ hr₁).bpred hb
      have hwf := (hL r₁ hr₁).inv.wf
      have hk' : r₁.w.kind = .write o x e b := by rw [← hw]; exact hk
      have m₁ := mem_events_of_ev h₁
      have m₂ := mem_events_of_ev h₂
      have hpr := PEq.replace (p := v₂) (q := v₁) (hva ev₂ m₂ v₂ hv₂) (hva ev₁ m₁ v₁ hv₁) hpeq
      obtain ⟨hfb, hfr⟩ := (sp.fwd_iff j₁ e₁ e₂).1 hf
      have hfb' : es.fwdBase r₁ e₁ e₂ := (fwdBase_congr hh hδ).1 hfb
      have hc := fwdBase_canon hfb
      refine close (k := ⟨r₁.P.replace v₂ v₁, (e.replace v₂ v₁).syms ++ (x.replace v₂ v₁).syms,
          { r₁.δ with f := r₁.δ.f ++ [(e₁, e₂)] },
          { r₁.w with kind := .write o (x.replace v₂ v₁) (e.replace v₂ v₁) b }⟩)
        (inPer hr₁ (Or.inr (Or.inr (Or.inl (List.mem_filterMap.2
          ⟨(e₁, e₂), mem_prodL hc.2.2.1 hc.2.2.2, ?_⟩)))))
        ⟨hpr, fun _ => Iff.rfl, by rw [hδ], by simp only; rw [hw]⟩
      unfold fwdOne
      simp only [hk', h₁, h₂, hv₁, hv₂]
      rw [if_pos]
      simp only [Bool.and_eq_true]
      refine ⟨⟨⟨(fwdBaseB_iff hb hP hwf).2 hfb', hfr⟩, FwdCtx.wfB_iff.2 (by rw [← hδ]; exact hwf')⟩, ?_⟩
      rw [O.satAnd_iff (isBPred_fwd_replace hb hP ((sp.fwd_iff r₁ e₁ e₂).2 ⟨hfb', hfr⟩) h₁ h₂ hv₁ hv₂) hΩ,
        ← holds_eq_of_peq hpr]
      exact hs
  | @we j₁ e₁ e₂ hg₁ hwe hwf' hs ih =>
      obtain ⟨r₁, hr₁, hpeq, hD, hδ, hw⟩ := ih
      have hh := holds_eq_of_peq hpeq
      have hP := (hL r₁ hr₁).bpred hb
      have hwf := (hL r₁ hr₁).inv.wf
      obtain ⟨hfb, hfr⟩ := (sp.we_iff j₁ e₁ e₂).1 hwe
      have hfb' : es.fwdBase r₁ e₁ e₂ := (fwdBase_congr hh hδ).1 hfb
      have hc := fwdBase_canon hfb
      refine close (k := { r₁ with δ := { r₁.δ with we := r₁.δ.we ++ [(e₂, e₁)] } })
        (inPer hr₁ (Or.inr (Or.inr (Or.inr (List.mem_filterMap.2
          ⟨(e₁, e₂), mem_prodL hc.2.2.1 hc.2.2.2, ?_⟩)))))
        ⟨hpeq, hD, by simp only; rw [hδ], hw⟩
      unfold weOne
      rw [if_pos]
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨(fwdBaseB_iff hb hP hwf).2 hfb', hfr⟩, FwdCtx.wfB_iff.2 (by rw [← hδ]; exact hwf')⟩,
        (O.satAnd_iff hP hΩ).2 (by rw [← hh]; exact hs)⟩
  | @lift j₁ j₂ Λ hg₁ hg₂ hδ12 hinj hcr hD12 hDcr hv1 hv2 hv3 hpo hs ih₁ ih₂ =>
      obtain ⟨r₁, hr₁, hpeq₁, hD₁, hδ₁, hw₁⟩ := ih₁
      obtain ⟨r₂, hr₂, hpeq₂, hD₂, hδ₂, hw₂⟩ := ih₂
      have hh₁ := holds_eq_of_peq hpeq₁
      have hh₂ := holds_eq_of_peq hpeq₂
      have hP₁ := (hL r₁ hr₁).bpred hb
      have hP₂ := (hL r₂ hr₂).bpred hb
      have hwf := (hL r₁ hr₁).inv.wf
      let dom := r₁.P.syms ++ r₁.D
      let l := dom.map fun a => (a, Λ a)
      have hagree : ∀ a ∈ dom, relOf l a = Λ a := fun a ha => by
        simp [relOf, l, lookup_map_self Λ dom a ha]
      have happ : ∀ a ∈ dom, (relOf l).app a = Λ.app a := fun a ha => by
        simp only [Relabelling.app, hagree a ha]
      have hPs : ∀ α, α ∈ r₁.P.syms ↔ α ∈ j₁.P.syms := fun α => ⟨hpeq₁.symm.mem_syms, hpeq₁.mem_syms⟩
      have hren : r₁.P.rename (relOf l) = r₁.P.rename Λ :=
        rename_congr _ (fun α hα => happ α (List.mem_append_left _ hα))
      have hrsy : ∀ α, α ∈ (r₁.P.rename Λ).syms ↔ α ∈ (j₁.P.rename Λ).syms := fun α => by
        rw [syms_rename_mem, syms_rename_mem]
        exact ⟨fun ⟨β, hβ, h⟩ => ⟨β, (hPs β).1 hβ, h⟩, fun ⟨β, hβ, h⟩ => ⟨β, (hPs β).2 hβ, h⟩⟩
      have hpl : (Expr.liftPred (j₁.P.rename Λ) j₂.P).PEq (Expr.liftPred (r₁.P.rename (relOf l)) r₂.P) := by
        rw [hren]; exact PEq.liftPred (PEq.rename Λ hpeq₁) hpeq₂
      have hl : l ∈ es.liftDom r₁ r₂ := by
        apply map_mem_allFuns
        intro a ha
        cases hΛ : Λ a with
        | none => exact List.mem_cons_self ..
        | some c =>
            refine List.mem_cons_of_mem _ (List.mem_map.2 ⟨c, ?_, rfl⟩)
            have hc : Λ.app a = c := by simp [Relabelling.app, hΛ]
            rcases List.mem_append.1 ha with ha | ha
            · refine List.mem_append_left _ (List.mem_map.2 ⟨(c, j₂.w.id), hpo c ?_, rfl⟩)
              rw [syms_rename_mem]; exact ⟨a, (hPs a).1 ha, hc⟩
            · exact List.mem_append_right _ ((hD₂ c).1 ((hD12 c).2 ⟨a, (hD₁ a).2 ha, hc⟩))
      refine close (k := { r₂ with P := Expr.liftPred (r₁.P.rename (relOf l)) r₂.P }) ?_
        ⟨hpl, hD₂, hδ₂, hw₂⟩
      simp only [step, List.mem_append, List.mem_flatMap]
      refine Or.inr ⟨(r₁, r₂), mem_prodL hr₁ hr₂, List.mem_filterMap.2 ⟨l, hl, ?_⟩⟩
      have hcr' : ∀ {a₁ a₂ : Event}, es.ClosedRelabEq j₁.δ Λ j₁.P a₁ j₂.P a₂ →
          es.crB O r₁.P r₂.P r₁.δ a₁ a₂ = true := fun h =>
        (crB_iff hb hP₁ hP₂ hwf Λ).2 (by rw [← hδ₁]; exact ClosedRelabEq.congr hh₁ hh₂ h)
      unfold liftOne
      rw [if_pos]
      simp only [liftOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true,
        Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
      refine ⟨by rw [← hδ₁, ← hδ₂]; exact hδ12, ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩⟩
      · intro a ha b hb'
        rw [hagree a ha, hagree b hb']
        cases hΛa : Λ a with
        | none => exact Or.inl (Or.inl rfl)
        | some c =>
            by_cases hab : Λ a = Λ b
            · right; rw [hΛa] at hab; simpa using hinj a b c hΛa hab.symm
            · exact Or.inl (Or.inr (by rw [hΛa] at hab; simpa using hab))
      · rw [← hw₁, ← hw₂]; exact hcr' hcr
      · intro e he
        obtain ⟨α, hα, h⟩ := (hD12 e).1 ((hD₂ e).2 he)
        exact ⟨α, (hD₁ α).1 hα, by rw [happ α (List.mem_append_right _ ((hD₁ α).1 hα))]; simpa using h⟩
      · intro α hα
        rw [happ α (List.mem_append_right _ hα)]
        exact (hD₂ _).1 ((hD12 _).2 ⟨α, (hD₁ α).2 hα, rfl⟩)
      · intro α hα
        rw [happ α (List.mem_append_right _ hα)]
        obtain ⟨ev₁, ev₂, he₁, he₂, hc⟩ := hDcr α ((hD₁ α).2 hα)
        simp only [he₁, he₂]; exact hcr' hc
      · rw [← hw₁]; exact hv1
      · rw [← hw₂]; exact hv2
      · intro α hα
        rcases List.mem_append.1 hα with h | h
        · exact hv3 α (List.mem_append_left _ ((hD₁ α).2 h))
        · exact hv3 α (List.mem_append_right _ ((hD₂ α).2 h))
      · intro α hα
        rw [hren, hrsy] at hα; rw [← hw₂]; exact hpo α hα
      · rw [O.satAnd_iff (isBPred_liftPred (by rw [isBPred_rename]; exact hP₁) hP₂) hΩ,
          ← holds_eq_of_peq hpl]
        exact hs
  | weak hwk => cases hwk

end complete

/-! ## Saturation -/

section saturation

variable {es O ΩE Qs sp} {M : List Nat} (hb : es.Bounded Qs M) (hΩ : isBPred M ΩE = true)
include hb hΩ

theorem stage_sound : ∀ k, ∀ r ∈ es.stage O ΩE Qs sp k, es.GenR ΩE.holds Qs false r
  | 0, r, h => by cases h
  | k + 1, r, h => by
      obtain ⟨E, hE, hEM⟩ := addNew_ext (es.stage O ΩE Qs sp k) (es.step O ΩE Qs sp (es.stage O ΩE Qs sp k))
      simp only [stage] at h
      rw [hE] at h
      rcases List.mem_append.1 h with h | h
      · exact stage_sound k r h
      · exact step_sound hb hΩ (stage_sound k) r (hEM r h)

omit hb hΩ in
theorem stage_pairwise : ∀ k, (es.stage O ΩE Qs sp k).Pairwise (fun a b => ¬ JEq a b)
  | 0 => List.Pairwise.nil
  | k + 1 => addNew_pairwise (stage_pairwise k)

/-- The stage `boundB + 1` is closed under `step` up to equivalence. -/
theorem stage_closed :
    ∀ m ∈ es.step O ΩE Qs sp (es.stage O ΩE Qs sp (es.boundB Qs + 1)),
      ∃ r ∈ es.stage O ΩE Qs sp (es.boundB Qs + 1), JEq m r := by
  let st := es.stage O ΩE Qs sp
  let Cl : Nat → Prop := fun k => ∀ m ∈ es.step O ΩE Qs sp (st k), ∃ r ∈ st k, JEq m r
  have same : ∀ k, Cl k → st (k + 1) = st k := fun k h => by
    show addNew (st k) _ = st k
    exact addNew_same (fun m hm => by obtain ⟨r, hr, h⟩ := h m hm; exact ⟨r, hr, h.symm⟩)
  have stay : ∀ k, Cl k → ∀ n, st (k + n) = st k := by
    intro k h n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [← Nat.add_assoc, same (k + n) (by intro m hm; rw [ih] at hm ⊢; exact h m hm), ih]
  have grow : ∀ k, ¬ Cl k → (st k).length < (st (k + 1)).length := fun k h => by
    have ⟨m, hm, hn⟩ : ∃ m ∈ es.step O ΩE Qs sp (st k), ∀ r ∈ st k, ¬ JEq r m :=
      Classical.byContradiction fun h' => h fun m hm => Classical.byContradiction fun hr =>
        h' ⟨m, hm, fun r hr' hj => hr ⟨r, hr', hj.symm⟩⟩
    exact addNew_grow hm hn
  have bnd : ∀ k, (st k).length ≤ es.boundB Qs := fun k =>
    GenR.bound hb.valsAtomic _ (stage_sound hb hΩ k) (stage_pairwise k)
  have hex : ∃ k ≤ es.boundB Qs, Cl k := by
    refine Classical.byContradiction fun hne => ?_
    have : ∀ k ≤ es.boundB Qs + 1, k ≤ (st k).length := by
      intro k
      induction k with
      | zero => intro _; exact Nat.zero_le _
      | succ k ih =>
          intro hk
          have := grow k (fun h => hne ⟨k, by omega, h⟩)
          have := ih (by omega); omega
    have := this _ (Nat.le_refl _)
    have := bnd (es.boundB Qs + 1)
    omega
  obtain ⟨k, hk, hc⟩ := hex
  have := stay k hc (es.boundB Qs + 1 - k)
  rw [Nat.add_sub_cancel' (by omega)] at this
  intro m hm
  change m ∈ es.step O ΩE Qs sp (es.stage O ΩE Qs sp (es.boundB Qs + 1)) at hm
  change ∃ r ∈ es.stage O ΩE Qs sp (es.boundB Qs + 1), JEq m r
  change es.stage O ΩE Qs sp (es.boundB Qs + 1) = es.stage O ΩE Qs sp k at this
  rw [this] at hm ⊢
  exact hc m hm

/-- **Decidability of the Weakening-free elaboration closure.** For a finite
    event structure meeting Conditions C1–C3 (`Bounded`), global guarantees
    given by a bounded predicate, and Strengthening from `Qs`, `decideJ`
    decides, relative to the oracle, whether a justification is equivalent to
    one of the closure. -/
theorem decideJ_iff (j : Justification) :
    es.decideJ O ΩE Qs sp j = true ↔ ∃ j', es.GenR ΩE.holds Qs false j' ∧ JEq j' j := by
  unfold decideJ
  rw [List.any_eq_true]
  constructor
  · rintro ⟨r, hr, hj⟩
    exact ⟨r, stage_sound hb hΩ _ r hr, (jeqB_iff _ _).1 hj⟩
  · rintro ⟨j', hj', he⟩
    obtain ⟨r, hr, hjr⟩ := step_complete hb hΩ (stage_sound hb hΩ _) (stage_closed hb hΩ) j' hj'
    exact ⟨r, hr, (jeqB_iff _ _).2 (hjr.symm.trans he)⟩

end saturation

/-! ## Weakening does not respect propositional equivalence -/

theorem conjuncts_ne_nil : ∀ P : Expr, P.conjuncts ≠ []
  | .and a _ => by simp [conjuncts, conjuncts_ne_nil a]
  | .not _ | .or _ _ | .val _ | .sym _ | .bin _ _ _ | .eq _ _ | .le _ _ => by simp [conjuncts]

/-- `(α = α) ∧ (β = 0)` and `¬(¬(α = α) ∨ ¬(β = 0))` are propositionally
    equivalent. Weakening under `Ω = ⊤` drops the valid conjunct `α = α` of the
    first, leaving a predicate without `α`; the second has a single conjunct,
    which is not valid, and Weakening does not apply to it. -/
theorem weak_not_congr :
    let P : Expr := .and (.eq (.sym 0) (.sym 0)) (.eq (.sym 1) (.num 0))
    let P' : Expr := .not (.or (.not (.eq (.sym 0) (.sym 0))) (.not (.eq (.sym 1) (.num 0))))
    P.PEq P' ∧
      (∃ P'' Pw, P.ConjEq (.and P'' Pw) ∧ Entails Pred.top Pw.holds ∧ 0 ∉ P''.syms) ∧
      ∀ P'' Pw, P'.ConjEq (.and P'' Pw) → ¬ Entails Pred.top Pw.holds := by
  intro P P'
  refine ⟨fun ρ => ?_, ⟨.eq (.sym 1) (.num 0), .eq (.sym 0) (.sym 0), ?_, ?_, by simp [syms, num]⟩, ?_⟩
  · simp only [P, P', kval]
    cases ρ (.eq (.sym 0) (.sym 0)) with
    | none => rfl
    | some a =>
      cases ρ (.eq (.sym 1) (.num 0)) with
      | none => cases a <;> rfl
      | some b => cases a <;> cases b <;> rfl
  · intro c; simp only [P, conjuncts, List.mem_append, List.mem_singleton]; exact or_comm
  · intro f _; simp [Expr.holds, Expr.eval]
  · intro P'' Pw hc hent
    obtain ⟨c, hcw⟩ := List.exists_mem_of_ne_nil _ (conjuncts_ne_nil Pw)
    have hcP : c ∈ P'.conjuncts := (hc c).2 (by simp [conjuncts, hcw])
    simp only [P', conjuncts, List.mem_singleton] at hcP
    have hw := (holds_iff_conjuncts Pw (fun _ => .num 1)).1 (hent _ trivial) c hcw
    rw [hcP] at hw
    simp [Expr.holds, Expr.eval, Expr.num] at hw

end EventStructure
