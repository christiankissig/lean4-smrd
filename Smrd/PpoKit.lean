import Smrd.PpoTail
import Smrd.Monotonicity

/-!
# A kit for concrete executions

Tools for the examples of `Smrd.PpoStability` and `Smrd.PpoNecessity`: event
structures computed by `denote`, their executions without forwarding or
elision, and decidable over-approximations of the relations freezing builds,
so that a relation's pairs can be bounded by a list and checked by `decide`.

* `simple es rf`: the execution with `X` the candidates, `J` the
  pre-justifications, and `rf` a list; `isExecution_simple`, `phi_simple`
  prove it an execution with `φ` from decidable side conditions (`Simple`).
* `syncL`, `aliasL` (the paper's `≼_sync`, `≼_alias` on global locations, as
  lists), `syncML` (MoRDor's `ppo_sync`); `ppo_mem`,
  `ppoStep_mem` bound the paper's `≼^P_δ` and MoRDor's steps by them, without
  forwarding or elision.
* `transGen_mem`: a transitive closure stays in a list closed under the step.
* `hbOver`, `CoherenceVOver`: `HB_v`-coherence over any dependency relation.
-/

namespace PpoKit

open EventStructure

/-! ## Events -/

theorem ev_inv {es : EventStructure} {c : EventId} {e : Event} (h : es.ev c = some e) :
    e ∈ es.events ∧ e.id = c :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

def clsB (es : EventStructure) (p : Event → Bool) (c : EventId) : Bool :=
  match es.ev c with
  | some e => p e
  | none => false

theorem cls_clsB {es : EventStructure} {p : Event → Bool} {c : EventId} :
    es.cls p c ↔ clsB es p c = true := by
  unfold clsB EventStructure.cls
  cases h : es.ev c <;> simp

theorem find_id {L : List Event} (hnd : (L.map (·.id)).Nodup) {e : Event} (he : e ∈ L) :
    L.find? (·.id == e.id) = some e := by
  induction L with
  | nil => cases he
  | cons a L ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.1 he with rfl | he
      · simp
      · have hne : a.id ≠ e.id := fun h => hnd.1 (h ▸ List.mem_map_of_mem he)
        have hb : (a.id == e.id) = false := by simp [hne]
        simp [List.find?, hb, ih hnd.2 he]

theorem ev_of_mem {es : EventStructure} (hnd : (es.events.map (·.id)).Nodup) {e : Event}
    (he : e ∈ es.events) : es.ev e.id = some e := find_id hnd he

/-! ## Simple executions -/

/-- A structure whose value restrictions are constant truths and whose ids are
    distinct. -/
structure Simple (es : EventStructure) : Prop where
  nodup  : (es.events.map (·.id)).Nodup
  valres : ∀ e ∈ es.events, e.valres.syms = [] ∧ e.valres.eval (fun _ => .num 0) = some (.bool true)
  normw  : es.rmw = []

theorem Simple.holds {es : EventStructure} (S : Simple es) {e : Event} (he : e ∈ es.events)
    (f : Valuation) : e.valres.holds f := by
  have h := S.valres e he
  unfold Expr.holds
  rw [Expr.eval_congr _ f (fun _ => .num 0) (fun α hα => by rw [h.1] at hα; cases hα)]
  exact h.2

/-- All pre-justifications. -/
def preJs (es : EventStructure) : List Justification := es.events.filterMap preJust

theorem preJust_spec {w : Event} {j : Justification} (h : preJust w = some j) :
    j.w = w ∧ j.δ = .empty ∧ j.P = w.valres ∧ w.isEffect = true := by
  unfold preJust at h
  split at h <;> cases h <;> simp_all [Event.isEffect, Event.isWrite, Event.isAlloc,
    Event.isDealloc]

theorem mem_preJs {es : EventStructure} {j : Justification} :
    j ∈ preJs es ↔ ∃ w ∈ es.events, preJust w = some j := by
  simp [preJs, List.mem_filterMap]

/-- The execution of all candidates, pre-justifications and the `rf` of a list. -/
def simple (es : EventStructure) (rf : List (EventId × EventId)) : Execution :=
  ⟨es.Candidate, preJs es, fun w r => (w, r) ∈ rf⟩

theorem foldr_empty {J : List Justification} (h : ∀ j ∈ J, j.δ = .empty) :
    J.foldr (fun j δ => j.δ.union δ) .empty = .empty := by
  induction J with
  | nil => rfl
  | cons j J ih =>
      simp only [List.foldr_cons]
      rw [ih (fun j' hj' => h j' (List.mem_cons_of_mem _ hj')), h j (List.mem_cons_self ..)]
      rfl

theorem δ_simple (es : EventStructure) (rf : List (EventId × EventId)) :
    (simple es rf).δ = .empty :=
  foldr_empty (fun j hj => by
    obtain ⟨w, -, hw⟩ := mem_preJs.1 hj
    exact (preJust_spec hw).2.1)

theorem noEdge_simple (es : EventStructure) (rf : List (EventId × EventId)) :
    ∀ a b, ¬ (simple es rf).δ.edge a b := by
  intro a b h; rw [δ_simple] at h; rcases h with h | h <;> cases h

theorem not_elided_simple (es : EventStructure) (rf : List (EventId × EventId)) (a : EventId) :
    ¬ (simple es rf).elided a := by
  rintro ⟨p, hp, -⟩; rw [δ_simple] at hp; rcases hp with hp | hp <;> cases hp

theorem cand_of_mem {es : EventStructure} (hnd : (es.events.map (·.id)).Nodup) {e : Event}
    (he : e ∈ es.events) (hb : e.isBranch = false) (hf : e.isFence = false) :
    es.Candidate e.id := by
  refine ⟨⟨e, he, rfl⟩, ?_, ?_⟩
  · rintro ⟨e', he', hp⟩; rw [ev_of_mem hnd he] at he'; cases he'; rw [hb] at hp; cases hp
  · rintro ⟨e', he', hp⟩; rw [ev_of_mem hnd he] at he'; cases he'; rw [hf] at hp; cases hp

theorem effect_nb {e : Event} (h : e.isEffect = true) : e.isBranch = false ∧ e.isFence = false := by
  obtain ⟨id, k, l, g⟩ := e
  cases k <;> simp_all [Event.isEffect, Event.isWrite, Event.isAlloc, Event.isDealloc,
    Event.isBranch, Event.isFence]

/-- Side conditions on the `rf` list: writes into reads, functional. -/
def RfOK (es : EventStructure) (rf : List (EventId × EventId)) : Prop :=
  (∀ p ∈ rf, clsB es Event.isWrite p.1 = true ∧ clsB es Event.isRead p.2 = true) ∧
  (∀ p ∈ rf, ∀ q ∈ rf, p.2 = q.2 → p.1 = q.1)

instance (es : EventStructure) (rf : List (EventId × EventId)) : Decidable (RfOK es rf) := by
  unfold RfOK; infer_instance

theorem cand_of_cls {es : EventStructure} (hnd : (es.events.map (·.id)).Nodup) {p : Event → Bool}
    (hp : ∀ e, p e = true → e.isBranch = false ∧ e.isFence = false) {c : EventId}
    (h : es.cls p c) : es.Candidate c := by
  obtain ⟨e, he, hpe⟩ := h
  obtain ⟨hm, rfl⟩ := ev_inv he
  exact cand_of_mem hnd hm (hp e hpe).1 (hp e hpe).2

theorem wr_nb (e : Event) (h : e.isWrite = true ∨ e.isRead = true) :
    e.isBranch = false ∧ e.isFence = false := by
  obtain ⟨id, k, l, g⟩ := e
  cases k <;> simp_all [Event.isWrite, Event.isRead, Event.isBranch, Event.isFence]

theorem isExecution_simple {es : EventStructure} (S : Simple es) {rf : List (EventId × EventId)}
    (hrf : RfOK es rf) : (simple es rf).IsExecution es (fun _ => True) where
  maximal := ⟨fun _ h => h, fun a b _ _ ⟨ea, eb, ha, hb, hn⟩ =>
      hn ⟨fun _ => .num 0, S.holds (ev_inv ha).1 _, S.holds (ev_inv hb).1 _⟩,
    fun _ hc hn => absurd hc hn⟩
  generated j hj := by
    obtain ⟨w, hw, hj'⟩ := mem_preJs.1 hj
    exact .pre hw hj' ⟨fun _ => .num 0, S.holds hw _⟩
  inX j hj := by
    obtain ⟨w, hw, hj'⟩ := mem_preJs.1 hj
    obtain ⟨hjw, -, -, he⟩ := preJust_spec hj'
    rw [hjw]
    exact cand_of_mem S.nodup hw (effect_nb he).1 (effect_nb he).2
  consistent := ⟨fun _ => .num 0, fun j hj => by
      obtain ⟨w, hw, hj'⟩ := mem_preJs.1 hj
      rw [(preJust_spec hj').2.2.1]; exact S.holds hw _,
    fun a e _ he => S.holds (ev_inv he).1 _⟩
  fwdWF := by rw [δ_simple]; exact FwdCtx.WF.empty
  rf_wr w r h := by
    obtain ⟨h₁, h₂⟩ := hrf.1 _ h
    have hw := cls_clsB.2 h₁
    have hr := cls_clsB.2 h₂
    exact ⟨hw, hr, cand_of_cls S.nodup (fun e he => wr_nb e (.inl he)) hw,
      cand_of_cls S.nodup (fun e he => wr_nb e (.inr he)) hr⟩
  rf_func w w' r h h' := hrf.2 _ h _ h' rfl
  justified w hw he _ := by
    obtain ⟨e, hev, hef⟩ := he
    obtain ⟨hm, rfl⟩ := ev_inv hev
    have hpj : ∃ j, preJust e = some j := by
      unfold preJust
      obtain ⟨id, k, l, g⟩ := e
      cases k <;> simp_all [Event.isEffect, Event.isWrite, Event.isAlloc, Event.isDealloc]
    obtain ⟨j, hj⟩ := hpj
    refine ⟨j, mem_preJs.2 ⟨e, hm, hj⟩, by rw [(preJust_spec hj).1], fun j' hj' hw' => ?_⟩
    obtain ⟨e', hm', hj''⟩ := mem_preJs.1 hj'
    have h1 := (preJust_spec hj'').1
    have : e' = e := by
      have h₁ := ev_of_mem S.nodup hm'
      rw [← h1, hw', hev] at h₁
      rw [← h1]; exact (Option.some.inj h₁).symm
    subst this
    rw [hj] at hj''; exact (Option.some.inj hj'').symm

/-- `φ` for a simple execution, with a valuation `f` that makes each `rf`
    edge agree on locations and values, every read reading, and no
    allocations. -/
theorem phi_simple {es : EventStructure} (S : Simple es) {rf : List (EventId × EventId)}
    (hrf : RfOK es rf) (hreads : ∀ e ∈ es.events, e.isRead = true → ∃ p ∈ rf, p.2 = e.id)
    (hnoalloc : ∀ e ∈ es.events, e.isAlloc = false) (f : Valuation)
    (hf : ∀ p ∈ rf, ∀ ew ∈ es.events, ∀ er ∈ es.events, ew.id = p.1 → er.id = p.2 →
      ew.loc.map (·.eval f) = er.loc.map (·.eval f) ∧
      ew.val.map (·.eval f) = er.val.map (·.eval f)) :
    (simple es rf).phi es := by
  have hx := isExecution_simple S hrf
  refine ⟨fun e _ hel => not_elided_simple es rf e hel, fun r => ⟨?_, ?_⟩, f, ?_, ?_, ?_, ?_⟩
  · rintro ⟨w, hw⟩
    exact ⟨(hx.rf_wr w r hw).2.2.2, (hx.rf_wr w r hw).2.1⟩
  · rintro ⟨-, e, he, hp⟩
    obtain ⟨hm, rfl⟩ := ev_inv he
    obtain ⟨p, hp', h2⟩ := hreads e hm hp
    exact ⟨p.1, by rw [← h2]; exact hp'⟩
  · intro j hj
    obtain ⟨w, hw, hj'⟩ := mem_preJs.1 hj
    obtain ⟨-, hδ, hP, -⟩ := preJust_spec hj'
    exact ⟨by rw [hP]; exact S.holds hw f, fun p hp => by rw [hδ] at hp; cases hp⟩
  · intro w r ew er h hw hr
    have := hf (w, r) h ew (ev_inv hw).1 er (ev_inv hr).1 (ev_inv hw).2 (ev_inv hr).2
    refine ⟨fun lw lr h₁ h₂ => ?_, fun vw vr h₁ h₂ => ?_⟩
    · have := this.1; rw [h₁, h₂] at this; exact Option.some.inj this
    · have := this.2; rw [h₁, h₂] at this; exact Option.some.inj this
  · intro a e α sz _ he hk
    have := hnoalloc e (ev_inv he).1
    simp [Event.isAlloc, hk] at this
  · intro a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂ _ _ _ he₁ _ hk₁
    have := hnoalloc e₁ (ev_inv he₁).1
    simp [Event.isAlloc, hk₁] at this

/-! ## Decidable bounds on the relations -/

/-- The paper's four summands of `≼_sync`, with fences and branches removed. -/
def syncL (es : EventStructure) : List (EventId × EventId) :=
  let po := es.po
  let c := clsB es
  let t₁ := po.filter (fun p => c Event.isRelW p.2)
  let t₂ := po.flatMap (fun p => if c Event.isRelF p.2 then
    (po.filter (fun q => q.1 == p.2 && !c Event.isRead q.2)).map (fun q => (p.1, q.2)) else [])
  let t₃ := po.filter (fun p => c Event.isAcqR p.1)
  let t₄ := po.flatMap (fun p => if c Event.isAcqF p.2 && !c Event.isWrite p.1 then
    (po.filter (fun q => q.1 == p.2)).map (fun q => (p.1, q.2)) else [])
  ((t₁ ++ t₂) ++ (t₃ ++ t₄)).filter (fun p => !c Event.isFence p.1 && !c Event.isBranch p.1 &&
    !c Event.isFence p.2 && !c Event.isBranch p.2)

/-- MoRDor's `ppo_sync`. -/
def syncML (es : EventStructure) : List (EventId × EventId) :=
  es.po.filter (fun p => clsB es Event.isAcqM p.1 || clsB es Event.isRelM p.2)

def locOf (es : EventStructure) (c : EventId) : Option Expr := (es.ev c).bind Event.loc

/-- `⊑`-pairs whose locations are the same expression. -/
def aliasL (es : EventStructure) : List (EventId × EventId) :=
  es.po.filter (fun p => match locOf es p.1, locOf es p.2 with
    | some l₁, some l₂ => decide (l₁ = l₂)
    | _, _ => false)

/-- Every location is a global, or absent. -/
def GlobLocs (es : EventStructure) : Prop :=
  ∀ e ∈ es.events, ∀ l, e.loc = some l → ∃ x, l = Expr.glob x

def globB (e : Event) : Bool :=
  match e.loc with
  | some (.val (.loc ⟨.global _, 0⟩)) => true
  | none => true
  | _ => false

theorem globLocs_of {es : EventStructure} (h : ∀ e ∈ es.events, globB e = true) : GlobLocs es := by
  intro e he l hl
  have := h e he
  unfold globB at this
  rw [hl] at this
  split at this
  · next x hx => cases hx; exact ⟨x, rfl⟩
  · simp_all
  · simp_all

theorem ppoSync_mem {es : EventStructure} {a b : EventId} (h : es.ppoSync a b) :
    (a, b) ∈ syncL es := by
  simp only [EventStructure.ppoSync, Rel.excl, Rel.union, Rel.comp, diag] at h
  obtain ⟨h, hna, hnb⟩ := h
  have hex : (!clsB es Event.isFence a && !clsB es Event.isBranch a &&
      !clsB es Event.isFence b && !clsB es Event.isBranch b) = true := by
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;>
      first
      | exact Bool.eq_false_iff.2 (fun h => hna (Or.inl (cls_clsB.2 h)))
      | exact Bool.eq_false_iff.2 (fun h => hna (Or.inr (cls_clsB.2 h)))
      | exact Bool.eq_false_iff.2 (fun h => hnb (Or.inl (cls_clsB.2 h)))
      | exact Bool.eq_false_iff.2 (fun h => hnb (Or.inr (cls_clsB.2 h)))
  simp only [syncL, List.mem_filter, List.mem_append, List.mem_flatMap]
  refine ⟨?_, hex⟩
  rcases h with (⟨x, hax, rfl, hx⟩ | ⟨y, ⟨x, hax, rfl, hx⟩, ⟨hyb, -, hb⟩⟩) |
    (⟨x, ⟨rfl, hx⟩, hab⟩ | ⟨y, ⟨x, ⟨hax, hnw, -⟩, rfl, hy⟩, hyb⟩)
  · exact Or.inl (Or.inl ⟨hax, cls_clsB.1 hx⟩)
  · refine Or.inl (Or.inr ⟨(a, x), hax, ?_⟩)
    rw [if_pos (cls_clsB.1 hx)]
    exact List.mem_map.2 ⟨(x, b), List.mem_filter.2 ⟨hyb, by
      simp only [beq_self_eq_true, Bool.true_and, Bool.not_eq_true']
      exact Bool.eq_false_iff.2 (fun h => hb (cls_clsB.2 h))⟩, rfl⟩
  · exact Or.inr (Or.inl ⟨hab, cls_clsB.1 hx⟩)
  · refine Or.inr (Or.inr ⟨(a, x), hax, ?_⟩)
    rw [if_pos (by
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨cls_clsB.1 hy, Bool.eq_false_iff.2 (fun h => hnw (cls_clsB.2 h))⟩)]
    exact List.mem_map.2 ⟨(x, b), List.mem_filter.2 ⟨hyb, by simp⟩, rfl⟩

theorem ppoSyncM_mem {es : EventStructure} {a b : EventId} (h : es.ppoSyncM a b) :
    (a, b) ∈ syncML es := by
  obtain ⟨hpo, ha | hb⟩ := h
  · exact List.mem_filter.2 ⟨hpo, by simp [cls_clsB.1 ha]⟩
  · exact List.mem_filter.2 ⟨hpo, by simp [cls_clsB.1 hb]⟩

theorem glob_inj {x y : Var} {f : Valuation} {v₁ v₂ : Val} (h₁ : (Expr.glob x).eval f = some v₁)
    (h₂ : (Expr.glob y).eval f = some v₂) (h : v₁ = v₂) : x = y := by
  simp [Expr.glob, Expr.eval] at h₁ h₂
  subst h₁ h₂; cases h; rfl

theorem alias_mem {es : EventStructure} (hg : GlobLocs es) {a b : EventId} (hpo : es.poR a b)
    (h : ∃ e₁ e₂ l₁ l₂, es.ev a = some e₁ ∧ es.ev b = some e₂ ∧ e₁.loc = some l₁ ∧
      e₂.loc = some l₂ ∧ ∃ f, (Expr.eq l₁ l₂).holds f) :
    (a, b) ∈ aliasL es := by
  obtain ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, hf⟩ := h
  obtain ⟨x, rfl⟩ := hg e₁ (ev_inv h₁).1 _ hl₁
  obtain ⟨y, rfl⟩ := hg e₂ (ev_inv h₂).1 _ hl₂
  have : x = y := by
    simp [Expr.holds, Expr.eval, Expr.glob] at hf; exact hf
  subst this
  refine List.mem_filter.2 ⟨hpo, ?_⟩
  simp [locOf, h₁, h₂, hl₁, hl₂]

theorem mayAlias_mem {es : EventStructure} (hg : GlobLocs es) {P : Pred} {a b : EventId}
    (hpo : es.poR a b) (h : es.mayAlias P a b) : (a, b) ∈ aliasL es := by
  obtain ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, -, hf⟩ := h
  exact alias_mem hg hpo ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, hf⟩

theorem mustAlias_mem {es : EventStructure} (hg : GlobLocs es) {a b : EventId}
    (hpo : es.poR a b) (h : es.mustAlias a b) : (a, b) ∈ aliasL es := by
  obtain ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, hs⟩ := h
  obtain ⟨x, rfl⟩ := hg e₁ (ev_inv h₁).1 _ hl₁
  obtain ⟨y, rfl⟩ := hg e₂ (ev_inv h₂).1 _ hl₂
  have hxy := hs (fun _ => .num 0) _ _ rfl rfl
  cases hxy
  exact alias_mem hg hpo ⟨e₁, e₂, _, _, h₁, h₂, hl₁, hl₂, fun _ => .num 0,
    by simp [Expr.holds, Expr.eval, Expr.glob]⟩

theorem not_rmwPairs {es : EventStructure} (h : es.rmw = []) {P : Pred} {a b : EventId} :
    ¬ es.rmwPairs P a b := by
  rintro ⟨ent, hm, -⟩; rw [h] at hm; cases hm

/-- The paper's `≼^P_δ` with `δ` empty, bounded. -/
theorem ppo_mem {es : EventStructure} (hr : es.rmw = []) (hg : GlobLocs es) {P : Pred}
    {δ : FwdCtx} (hδ : ∀ a b, ¬ δ.edge a b) {a b : EventId} (h : es.ppo P δ a b) :
    (a, b) ∈ syncL es ++ aliasL es := by
  obtain ⟨hab, -⟩ := h
  rcases (FwdCtx.remapRel_of_noEdge hδ).1 hab with (hs | ⟨⟨x, -, hx⟩ | ⟨x, hx, -⟩, -⟩) | ⟨hpo, hal⟩
  · exact List.mem_append.2 (.inl (ppoSync_mem hs))
  · exact absurd hx (not_rmwPairs hr)
  · exact absurd hx (not_rmwPairs hr)
  · exact List.mem_append.2 (.inr (mayAlias_mem hg hpo hal))

/-- MoRDor's `ppoM` with `δ` empty, bounded. -/
theorem ppoM_mem {es : EventStructure} (hr : es.rmw = []) (hg : GlobLocs es) {Pa Pr : Pred}
    {δ : FwdCtx} (hδ : ∀ a b, ¬ δ.edge a b) {a b : EventId} (h : es.ppoM Pa Pr δ a b) :
    (a, b) ∈ syncML es ++ aliasL es := by
  obtain ⟨hab, -⟩ := h
  rcases (FwdCtx.remapRel_of_noEdge hδ).1 hab with (hs | (⟨x, -, hx⟩ | ⟨x, hx, -⟩)) | ⟨hpo, hm | hal⟩
  · exact List.mem_append.2 (.inl (ppoSyncM_mem hs))
  · exact absurd hx (not_rmwPairs hr)
  · exact absurd hx (not_rmwPairs hr)
  · exact List.mem_append.2 (.inr (mustAlias_mem hg hpo hm))
  · exact List.mem_append.2 (.inr (mayAlias_mem hg hpo hal))

theorem ppoStep_mem {es : EventStructure} {x : Execution} (hr : es.rmw = []) (hg : GlobLocs es)
    (hδ : ∀ a b, ¬ x.δ.edge a b) {a b : EventId} (h : x.ppoStep es a b) :
    (a, b) ∈ syncML es ++ aliasL es := by
  obtain ⟨-, -, ⟨j, -, hp, -⟩ | hs | ⟨hp, -⟩⟩ := h
  · exact ppoM_mem hr hg hδ hp
  · exact ppoM_mem hr hg hδ (es.ppoSyncRM_sub_ppoM (x.Pm es) (x.Pm es) x.δ _ _ hs)
  · exact ppoM_mem hr hg hδ hp

/-- A list closed under composition. -/
def Closed (L : List (EventId × EventId)) : Prop :=
  ∀ p ∈ L, ∀ q ∈ L, p.2 = q.1 → (p.1, q.2) ∈ L

instance (L : List (EventId × EventId)) : Decidable (Closed L) := by unfold Closed; infer_instance

/-- `TransGen R` stays in a list closed under appending an `R`-step. -/
theorem transGen_mem {R : Rel} {L : List (EventId × EventId)} (hR : ∀ a b, R a b → (a, b) ∈ L)
    (hL : Closed L) {a b : EventId} (h : Relation.TransGen R a b) : (a, b) ∈ L := by
  induction h with
  | single h => exact hR _ _ h
  | tail _ h ih => exact hL _ ih _ (hR _ _ h) rfl

/-- The transitive closure of a list, by `n` rounds of composition. -/
def closeL : Nat → List (EventId × EventId) → List (EventId × EventId)
  | 0, L => L
  | n + 1, L =>
      let L' := L ++ (L.flatMap fun p => (L.filter (fun q => q.1 == p.2)).map fun q => (p.1, q.2))
      closeL n (L'.eraseDups)

theorem pair_eta (p : EventId × EventId) : (p.1, p.2) = p := rfl

/-! ## Coherence over a dependency relation -/

/-- `HB` over a dependency relation `D`: `(D ∪ SW)⁺`. -/
def hbOver (es : EventStructure) (x : Execution) (D : Rel) : Rel := Rel.plus (D.union (x.sw es))

/-- `HB_D ; ECO?` irreflexive. -/
def CoherenceVOver (es : EventStructure) (x : Execution) (D : Rel) (co : Rel) : Prop :=
  ∀ a, ¬ ∃ b, hbOver es x D a b ∧ (b = a ∨ x.eco co b a)

theorem coherenceV_iff_over {es : EventStructure} {x : Execution} {co : Rel} :
    x.CoherenceV es co ↔ CoherenceVOver es x (x.dep es) co := Iff.rfl

/-- `SW` relates a releasing write or fence to an acquiring read or fence. -/
theorem sw_cls {es : EventStructure} {x : Execution} {a b : EventId} (h : x.sw es a b) :
    (clsB es Event.isRelW a || clsB es Event.isRelF a) = true ∧
    (clsB es Event.isAcqR b || clsB es Event.isAcqF b) = true := by
  obtain ⟨ha, -, -, -, -, -, -, -, -, hb⟩ := h
  constructor
  · rcases ha with h | h <;> simp [cls_clsB.1 h]
  · rcases hb with h | h <;> simp [cls_clsB.1 h]

/-- `SW` stays among the releasing and acquiring events. -/
def swL (es : EventStructure) : List (EventId × EventId) :=
  (es.ids.flatMap fun a => es.ids.map fun b => (a, b)).filter fun p =>
    (clsB es Event.isRelW p.1 || clsB es Event.isRelF p.1) &&
    (clsB es Event.isAcqR p.2 || clsB es Event.isAcqF p.2)

theorem clsB_id {es : EventStructure} {p : Event → Bool} {c : EventId} (h : clsB es p c = true) :
    c ∈ es.ids := by
  unfold clsB at h
  split at h
  · next e he => obtain ⟨hm, rfl⟩ := ev_inv he; exact List.mem_map_of_mem hm
  · cases h

theorem sw_mem {es : EventStructure} {x : Execution} {a b : EventId} (h : x.sw es a b) :
    (a, b) ∈ swL es := by
  obtain ⟨ha, hb⟩ := sw_cls h
  have ia : a ∈ es.ids := by
    simp only [Bool.or_eq_true] at ha; rcases ha with h | h <;> exact clsB_id h
  have ib : b ∈ es.ids := by
    simp only [Bool.or_eq_true] at hb; rcases hb with h | h <;> exact clsB_id h
  exact List.mem_filter.2 ⟨List.mem_flatMap.2 ⟨a, ia, List.mem_map.2 ⟨b, ib, rfl⟩⟩,
    by simp only [ha, hb, Bool.and_self]⟩

/-- `ECO` over list-given `rf` and `co`, bounded by a closed list. -/
theorem eco_mem {x : Execution} {co : Rel} {L : List (EventId × EventId)}
    (hrf : ∀ a b, x.rf a b → (a, b) ∈ L) (hco : ∀ a b, co a b → (a, b) ∈ L)
    (hfr : ∀ a b, x.fr co a b → (a, b) ∈ L) (hL : Closed L) {a b : EventId}
    (h : x.eco co a b) : (a, b) ∈ L :=
  transGen_mem (fun a b h => by
    rcases h with (h | h) | h
    · exact hrf a b h
    · exact hco a b h
    · exact hfr a b h) hL h

/-- `HB_D`-coherence from list bounds: `HB_D ⊆ H`, `ECO ⊆ E`, and no pair of
    `H` reflexive or reversed in `E`. -/
theorem coherenceVOver_of {es : EventStructure} {x : Execution} {D co : Rel}
    {H E : List (EventId × EventId)} (hH : ∀ a b, hbOver es x D a b → (a, b) ∈ H)
    (hE : ∀ a b, x.eco co a b → (a, b) ∈ E)
    (hok : ∀ p ∈ H, p.1 ≠ p.2 ∧ (p.2, p.1) ∉ E) : CoherenceVOver es x D co := by
  rintro a ⟨b, hab, rfl | hba⟩
  · exact (hok _ (hH _ _ hab)).1 rfl
  · exact (hok _ (hH _ _ hab)).2 (hE _ _ hba)

/-! ## Generated justifications justify events -/

/-- Every generated justification is of an effectful event of the structure. -/
theorem Generated.w_mem {es : EventStructure} {Ω : Pred} {j : Justification}
    (h : es.Generated Ω j) : ∃ e ∈ es.events, e.id = j.w.id ∧ e.isEffect = true := by
  induction h with
  | pre hw hj _ =>
      obtain ⟨h1, -, -, he⟩ := preJust_spec hj
      exact ⟨_, hw, by rw [h1], he⟩
  | va _ hk _ _ ih =>
      obtain ⟨e, he, hid, hef⟩ := ih; exact ⟨e, he, hid, hef⟩
  | str _ _ _ _ _ _ _ ih => exact ih
  | fwd _ _ _ _ _ _ _ _ _ ih =>
      obtain ⟨e, he, hid, hef⟩ := ih; exact ⟨e, he, hid, hef⟩
  | we _ _ _ _ ih => exact ih
  | lift _ _ _ _ _ _ _ _ _ _ _ _ _ ih₂ => exact ih₂
  | weak _ _ _ _ ih => exact ih

/-- Without guards that can fail, an execution contains every candidate. -/
theorem all_in_X {es : EventStructure} {x : Execution} {Ω : Pred} (hX : x.IsExecution es Ω)
    (S : Simple es) {a : EventId} (hc : es.Candidate a) : x.X a := by
  apply Classical.byContradiction
  intro hn
  obtain ⟨b, -, ea, eb, ha, hb, hns⟩ := hX.maximal.2.2 a hc hn
  exact hns ⟨fun _ => .num 0, S.holds (ev_inv ha).1 _, S.holds (ev_inv hb).1 _⟩

theorem noEdge_of_noElided {x : Execution} (h : ∀ a, ¬ x.elided a) : ∀ a b, ¬ x.δ.edge a b :=
  fun a b he => h b ((x.elided_iff b).2 ⟨a, he⟩)

/-- MoRDor's combined predicate is satisfiable in an execution without
    forwarding or elision whose value restrictions are constant truths. -/
theorem sat_Pm {es : EventStructure} {x : Execution} {Ω : Pred} (hX : x.IsExecution es Ω)
    (S : Simple es) (hδ : ∀ a, ¬ x.elided a) : ∃ f, x.Pm es f := by
  obtain ⟨f, hJ, -⟩ := hX.consistent
  refine ⟨f, hJ, fun p hp => ?_, fun a e _ he => S.holds (ev_inv he).1 f⟩
  exact absurd ⟨p, .inl hp, rfl⟩ (hδ p.2)

/-- A pair at one global location `⊑`-ordered in `X ∪ X_F`, neither end
    elided, is in MoRDor's `≼` (through `ppo_loc`), under a satisfiable
    combined predicate. -/
theorem ppo_of_alias {es : EventStructure} {x : Execution} (hδ : ∀ a, ¬ x.elided a)
    {f : Valuation} (hf : x.Pm es f) {a b : EventId} {ea eb : Event} {y : Var}
    (ha : es.ev a = some ea) (hb : es.ev b = some eb) (hla : ea.loc = some (Expr.glob y))
    (hlb : eb.loc = some (Expr.glob y)) (hpo : es.poR a b) (hne : a ≠ b) (hXa : x.X a)
    (hXb : x.X b) : x.ppo es a b := by
  have hal : es.mayAlias (x.Pm es) a b :=
    ⟨ea, eb, _, _, ha, hb, hla, hlb, f, hf, by simp [Expr.holds, Expr.eval, Expr.glob]⟩
  refine ⟨hXa, hXb, .single ⟨.inl hXa, .inl hXb, .inr (.inr ⟨⟨?_, hne⟩, hal⟩)⟩⟩
  exact (FwdCtx.remapRel_of_noEdge (noEdge_of_noElided hδ)).2 (.inr ⟨hpo, .inr hal⟩)

end PpoKit
