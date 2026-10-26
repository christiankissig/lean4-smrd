import Smrd.PpoTail

/-!
# Coherence over the transformed execution `X ∖ †`

sMRD's elaborations transform the program: Write Elision drops the earlier of
two writes, Forwarding the forwarded event. The transformed execution is
`X ∖ †`, with `† = π₂(F ∪ WE)` (`Execution.elided`), and sMRD's coherence axiom
is RC11's over it (`CoherenceT`): a coherence order over the writes of
`X ∖ †` (`CoherenceOrderT`), and `HB_T ; ECO?` irreflexive with
`HB_T ≜ (⊑ ∪ SW)⁺` restricted to `(X ∖ †) ∪ X_F` (`hbT`). RC11 itself does not
elide; `Execution.Coherence` is its axiom over `X`.

Leaving elided writes out of coherence is sound only if no elision crosses a
release: in `x := 1; flag :rel= 1; x := 2 ∥ r1 :acq= flag; r2 := x`, eliding
`x := 1` into `x := 2` drops the `HB`-edge from `x := 1` to `r2`, and `HB_T`
admits `r1 = 1 ∧ r2 = 0`, which RC11 forbids (`Smrd.WEAcrossRelease`). Write
Elision therefore carries MoRDor's release restriction
(`EventStructure.weNoRel`, MoRDor #207).

## Results

* `rmw_not_elided`, `rmwRel_XT`, `atomicityT_iff`: no RMW access is elided
  (Forwarding and Write Elision exclude it, `EventStructure.RMWAcc`), so every
  `rmw` pair lies in `X ∖ †` and Atomicity over `X ∖ †` is RC11's.
* `coherentT_iff_coherent`: without elided events, `CoherentT` is RC11's
  `Coherent`.
* `remap_cross_pub`: under the restriction, an elision crosses no event that
  publishes (release write, release or `sc` fence, `sc` read) unless that
  event is elided into the same write.
* `ppoSyncRM_po_T`: hence the remapped `ppo_sync` has no backward pair: every
  anchored pair of it on the path lies in `⊑`, without further hypotheses
  (beyond no forwarding and `⊑` a forest). The backward pair
  `(x := 2, flag :rel= 1)` that made MoRDor's sMRD forbid the outcome above is
  not generated, and not needed.
* `dep_po_T`: `DP ∪ ≼ ⊆ ⊑` without forwarding, where no elision crosses an
  event that may alias the elided write or is an RMW access (`NoCrossLoc`);
  that no RMW access is elided is derived (`rmw_not_elided`). This replaces `NoCross` of `Smrd.PpoTail`: crossings
  of publishing events are excluded by the restriction, and the remaining
  ones are those MoRDor's `pred` condition (the elided write is the
  immediate `ppo_loc`-predecessor) is meant to exclude, which is not derived
  here.
* `coherenceV_of_coherenceT`, `coherenceT_of_coherenceV`,
  `coherenceT_iff_coherenceV`: `HB_v`-coherence (`HB_v = (DP ∪ ≼ ∪ SW)⁺`, the
  operational semantics' happens-before) and `CoherenceT` coincide for one
  coherence order over `X ∖ †`. Against `coherenceV_iff_coherence_we`, the
  hypothesis that no event of the path is elided is gone (the transformed
  execution leaves them out), `NoCross` is weakened to `NoCrossLoc`, and the
  execution justifies no elided write (`hJ`). That elisions point `⊑`-forward
  is derived (`we_po`: Write Elision asks `e₁ ⊑ e₂`, `EventStructure.fwdBase`),
  so `WEForward` reduces to no forwarding (`weForward_of_noFwd`), which is
  still assumed: a forwarded event is in `†` too, it is remapped `⊑`-backward
  to its source, and Forwarding across an
  acquire is not restricted. That is a real gap, not only of the proof:
  forwarding a store into a later one across an acquire,
  `x := 1; r0 :acq= flag; x := 1`, makes `CoherenceT` admit an outcome RC11
  and `HB_v`-coherence forbid (`Smrd.FwdAcrossAcquire`). Forwarding needs the
  dual restriction (no acquire `⊑`-between), or the remapped backward pair
  of `ppo_sync` stays necessary there.
-/

namespace Event

theorem publishes_of_isRelM {e : Event} (h : e.isRelM = true) : e.publishes = true := by
  obtain ⟨id, k, l, g⟩ := e
  cases k <;> simp_all [Event.isRelM, Event.isRelW, Event.isRelF,
    Event.publishes]

theorem not_write_of_isAcqM {e : Event} (h : e.isAcqM = true) : e.isWrite = false := by
  obtain ⟨id, k, l, g⟩ := e
  cases k <;> simp_all [Event.isAcqM, Event.isAcqR, Event.isAcqF, Event.isWrite]

theorem not_write_of_isRead {e : Event} (h : e.isRead = true) : e.isWrite = false := by
  obtain ⟨id, k, l, g⟩ := e
  cases k <;> simp_all [Event.isRead, Event.isWrite]

theorem not_write_of_isFence {e : Event} (h : e.isFence = true) : e.isWrite = false := by
  obtain ⟨id, k, l, g⟩ := e
  cases k <;> simp_all [Event.isFence, Event.isWrite]

end Event

namespace Execution

variable (es : EventStructure) (x : Execution)

/-! ## The axiom -/

/-- The transformed execution `X ∖ †`. -/
def XT : EvSet := fun a => x.X a ∧ ¬ x.elided a

/-- `⊑` within `(X ∖ †) ∪ X_F`. -/
def poXT : Rel := fun a b => x.poX es a b ∧ ¬ x.elided a ∧ ¬ x.elided b

/-- RC11's `SW` between events of `(X ∖ †) ∪ X_F`. The writes of a release
    sequence after its head are read from, so not elided (`φ`). -/
def swT : Rel := fun a b => x.sw es a b ∧ ¬ x.elided a ∧ ¬ x.elided b

/-- `HB_T ≜ (⊑ ∪ SW)⁺` over `(X ∖ †) ∪ X_F`. -/
def hbT : Rel := Rel.plus ((x.poXT es).union (x.swT es))

/-- A coherence order of the transformed execution: a strict order on the
    writes of `X ∖ †`, total on the writes to each location. -/
structure CoherenceOrderT (co : Rel) : Prop where
  writes : ∀ a b, co a b → x.XT a ∧ x.XT b ∧ es.cls Event.isWrite a ∧ es.cls Event.isWrite b
  irrefl : ∀ a, ¬ co a a
  trans  : ∀ a b c, co a b → co b c → co a c
  total  : ∀ a b, x.XT a → x.XT b → es.cls Event.isWrite a → es.cls Event.isWrite b →
    a ≠ b → x.sameLoc es a b → co a b ∨ co b a

/-- **sMRD's `Coherence` axiom, over the transformed execution**: `HB_T ; ECO?`
    is irreflexive. -/
def CoherenceT (co : Rel) : Prop :=
  ∀ a, ¬ ∃ b, x.hbT es a b ∧ (b = a ∨ x.eco co b a)

/-- `CoherenceT` and `Atomicity` under one coherence order of `X ∖ †`. -/
def CoherentT : Prop :=
  ∃ co, x.CoherenceOrderT es co ∧ x.CoherenceT es co ∧ x.Atomicity es co

/-- A consistent execution of sMRD, coherence checked over `X ∖ †`. -/
def ConsistentT (Ω : Pred) : Prop :=
  x.IsExecution es Ω ∧ x.phi es ∧ x.NoThinAir es ∧ x.CoherentT es

/-! ## Without elided events, RC11's axiom -/

section NoElided

variable {es x}

theorem hbT_iff_hb (h : ∀ a, ¬ x.elided a) {a b : EventId} : x.hbT es a b ↔ x.hb es a b := by
  constructor
  · intro hab
    exact transGen_mono (fun _ _ s => by
      rcases s with s | s
      · exact .inl s.1
      · exact .inr s.1) hab
  · intro hab
    exact transGen_mono (fun c d s => by
      rcases s with s | s
      · exact .inl ⟨s, h c, h d⟩
      · exact .inr ⟨s, h c, h d⟩) hab

theorem coherenceOrderT_iff (h : ∀ a, ¬ x.elided a) {co : Rel} :
    x.CoherenceOrderT es co ↔ x.CoherenceOrder es co := by
  constructor
  · intro hc
    exact ⟨fun a b hab => by
        obtain ⟨ha, hb, hwa, hwb⟩ := hc.writes a b hab
        exact ⟨ha.1, hb.1, hwa, hwb⟩,
      hc.irrefl, hc.trans,
      fun a b ha hb => hc.total a b ⟨ha, h a⟩ ⟨hb, h b⟩⟩
  · intro hc
    exact ⟨fun a b hab => by
        obtain ⟨ha, hb, hwa, hwb⟩ := hc.writes a b hab
        exact ⟨⟨ha, h a⟩, ⟨hb, h b⟩, hwa, hwb⟩,
      hc.irrefl, hc.trans,
      fun a b ha hb => hc.total a b ha.1 hb.1⟩

/-- **Without elided events, `CoherentT` is RC11's `Coherent`.** -/
theorem coherentT_iff_coherent (h : ∀ a, ¬ x.elided a) : x.CoherentT es ↔ x.Coherent es := by
  have hcoh : ∀ co, x.CoherenceT es co ↔ x.Coherence es co := fun co => by
    unfold CoherenceT Coherence
    simp only [hbT_iff_hb h]
  constructor
  · rintro ⟨co, ho, hc, ha⟩
    exact ⟨co, (coherenceOrderT_iff h).1 ho, (hcoh co).1 hc, ha⟩
  · rintro ⟨co, ho, hc, ha⟩
    exact ⟨co, (coherenceOrderT_iff h).2 ho, (hcoh co).2 hc, ha⟩

end NoElided

/-! ## Elided events -/

section Elided

variable {es x}

/-- An edge of `WE` in the shared context is one of a justification. -/
theorem mem_δ_we_inv {p : EventId × EventId} (hp : p ∈ x.δ.we) : ∃ j ∈ x.J, p ∈ j.δ.we := by
  obtain ⟨X, J, rf⟩ := x
  simp only [δ] at *
  induction J with
  | nil => cases hp
  | cons j J ih =>
      simp only [FwdCtx.union, List.foldr_cons] at hp
      rcases List.mem_append.1 hp with hp | hp
      · exact ⟨j, List.mem_cons_self .., hp⟩
      · obtain ⟨j', hj', hp'⟩ := ih hp
        exact ⟨j', List.mem_cons_of_mem _ hj', hp'⟩

/-- **Every elision of an execution was generated under Write Elision's
    conditions**, against a justification with a satisfiable predicate whose
    forwarding edges are among the execution's. -/
theorem we_edge {Ω : Pred} (hx : x.IsExecution es Ω) {p : EventId × EventId} (hp : p ∈ x.δ.we) :
    ∃ j₀ : Justification, es.weRel j₀ p.2 p.1 ∧ Sat j₀.P.holds ∧ ∀ q ∈ j₀.δ.f, q ∈ x.δ.f := by
  obtain ⟨j, hj, hpj⟩ := mem_δ_we_inv hp
  obtain ⟨j₀, h₀, hs, hf⟩ := EventStructure.Generated.we_mem es (hx.generated j hj) p hpj
  exact ⟨j₀, h₀, hs, fun q hq => mem_δ_f hj (hf q hq)⟩

/-- **Every elision of an execution is `⊑`-forward**, `e₁ ⊑ e₂` for
    `(e₂, e₁) ∈ WE`: Write Elision asks it of the pair (`fwdBase`). -/
theorem we_po {Ω : Pred} (hx : x.IsExecution es Ω) : ∀ p ∈ x.δ.we, es.poR p.2 p.1 :=
  fun _ hp => by
    obtain ⟨j₀, ⟨⟨⟨-, hpo, -⟩, -⟩, -⟩, -⟩ := we_edge hx hp
    exact hpo

/-- **`WEForward` holds of every execution without forwarding**: its second
    half, elisions `⊑`-forward, is `we_po`. Its first half, no forwarding, is
    not derived: Forwarding remaps the forwarded event `⊑`-backward, to its
    source, so `remap_fwd` fails with it, and forwarding across an acquire is
    a real gap of `CoherenceT` (`Smrd.FwdAcrossAcquire`). -/
theorem weForward_of_noFwd {Ω : Pred} (hx : x.IsExecution es Ω) (hnoF : ∀ p ∈ x.δ.f, False) :
    WEForward es x :=
  ⟨hnoF, we_po hx⟩

/-- Without forwarding, an elided event is the earlier write of an elision. -/
theorem elided_we (hW : WEForward es x) {e : EventId} (h : x.elided e) :
    ∃ e₂, (e₂, e) ∈ x.δ.we := by
  obtain ⟨p, hp | hp, rfl⟩ := h
  · exact (hW.1 p hp).elim
  · exact ⟨p.1, hp⟩

/-- Without forwarding, only writes are elided. -/
theorem elided_write {Ω : Pred} (hx : x.IsExecution es Ω) (hW : WEForward es x) {e : EventId}
    (h : x.elided e) : es.cls Event.isWrite e := by
  obtain ⟨e₂, he⟩ := elided_we hW h
  obtain ⟨j₀, ⟨⟨-, hw, -⟩, -⟩, -⟩ := we_edge hx he
  exact hw

theorem not_elided_of_not_write {Ω : Pred} (hx : x.IsExecution es Ω) (hW : WEForward es x)
    {e : EventId} {p : Event → Bool} (hp : ∀ e, p e = true → e.isWrite = false)
    (h : es.cls p e) : ¬ x.elided e := by
  intro hel
  obtain ⟨ev, hev, hpe⟩ := elided_write hx hW hel
  obtain ⟨ev', hev', hpe'⟩ := h
  rw [hev] at hev'; cases hev'
  rw [hp _ hpe'] at hpe; cases hpe

/-- The image of `remap_δ` is not elided. -/
theorem remap_not_elided {a a' : EventId} (h : x.δ.Remap a a') : ¬ x.elided a' := by
  induction h with
  | canon hno =>
      intro hel
      obtain ⟨c, hc⟩ := (x.elided_iff _).1 hel
      exact hno c hc
  | step _ _ ih => exact ih

/-- An event `remap_δ` moves is elided. -/
theorem elided_of_remap_ne {a a' : EventId} (h : x.δ.Remap a a') (hne : a ≠ a') : x.elided a := by
  cases h with
  | canon _ => exact absurd rfl hne
  | step he _ => exact (x.elided_iff _).2 ⟨_, he⟩

/-- **Under the release restriction, an elision crosses no event that
    publishes**, unless that event is elided into the same write: for
    `remap_δ(a) = a'` and `a ⊑ c ⊑ a'`, `remap_δ(c) = a'` or `c` does not
    publish. By induction along the chain of elisions `a ↦ … ↦ a'`: `c` is a
    link of the chain, or lies strictly between two consecutive links, where
    `weNoRel` excludes a publishing event. -/
theorem remap_cross_pub {Ω : Pred} (hx : x.IsExecution es Ω) (hW : WEForward es x)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) {a a' : EventId} (h : x.δ.Remap a a') :
    ∀ c, es.poR a c → es.poR c a' → x.δ.Remap c a' ∨ ¬ es.cls Event.publishes c := by
  induction h with
  | canon _ => intro c h₁ h₂; exact absurd (hpo_trans _ _ _ h₁ h₂) (hirr _)
  | @step b e e' he hr ih =>
      intro c h₁ h₂
      -- `e` is elided into `b`
      have hwe : (b, e) ∈ x.δ.we := by
        rcases he with hf | hw
        · exact (hW.1 _ hf).elim
        · exact hw
      obtain ⟨j₀, ⟨-, ⟨-, hnr⟩, -⟩, -⟩ := we_edge hx hwe
      have hb : b = e' ∨ es.poR b e' := remap_fwd hW hpo_trans hr
      rcases hF c b e' (.inr h₂) (hb.elim (fun h => .inl h) .inr) with rfl | hcb | hbc
      · exact .inl hr
      · exact .inr (hnr c h₁ hcb)
      · exact ih c hbc h₂

/-! ## RMWs are not elided

Neither access of an RMW is in the elided position (`EventStructure.fwdRel`,
`EventStructure.weRel`, MoRDor E4), so every pair of `rmw` lies in `X ∖ †`,
and Atomicity over `X ∖ †` is RC11's on those pairs: the transformation
removes no RMW access and splits no RMW. -/

/-- A forwarding edge in the shared context is one of a justification. -/
theorem mem_δ_f_inv {p : EventId × EventId} (hp : p ∈ x.δ.f) : ∃ j ∈ x.J, p ∈ j.δ.f := by
  obtain ⟨X, J, rf⟩ := x
  simp only [δ] at *
  induction J with
  | nil => cases hp
  | cons j J ih =>
      simp only [FwdCtx.union, List.foldr_cons] at hp
      rcases List.mem_append.1 hp with hp | hp
      · exact ⟨j, List.mem_cons_self .., hp⟩
      · obtain ⟨j', hj', hp'⟩ := ih hp
        exact ⟨j', List.mem_cons_of_mem _ hj', hp'⟩

/-- **No RMW access of an execution is elided** (`rmw_not_elided`). -/
theorem rmw_not_elided {Ω : Pred} (hx : x.IsExecution es Ω) {e : EventId} (h : x.elided e) :
    ¬ es.RMWAcc e := by
  obtain ⟨p, hp, rfl⟩ := h
  rcases hp with hp | hp
  · obtain ⟨j, hj, hpj⟩ := mem_δ_f_inv hp
    exact EventStructure.Generated.not_rmwAcc_elided es (hx.generated j hj) p (.inl hpj)
  · obtain ⟨j, hj, hpj⟩ := mem_δ_we_inv hp
    exact EventStructure.Generated.not_rmwAcc_elided es (hx.generated j hj) p (.inr hpj)

/-- `remap_δ` fixes RMW accesses. -/
theorem remap_rmwAcc {Ω : Pred} (hx : x.IsExecution es Ω) {e e' : EventId} (h : x.δ.Remap e e')
    (hr : es.RMWAcc e) : e = e' :=
  Classical.byContradiction fun hne => rmw_not_elided hx (elided_of_remap_ne h hne) hr

/-- **Every `rmw` pair of an execution lies in `X ∖ †`.** -/
theorem rmwRel_XT {Ω : Pred} (hx : x.IsExecution es Ω) {r w : EventId} (h : x.rmwRel es r w) :
    x.XT r ∧ x.XT w := by
  obtain ⟨hr, hw, ent, hm, rfl, rfl, -⟩ := h
  exact ⟨⟨hr, fun hel => rmw_not_elided hx hel ⟨ent, hm, .inl rfl⟩⟩,
    ⟨hw, fun hel => rmw_not_elided hx hel ⟨ent, hm, .inr rfl⟩⟩⟩

/-- `rmw` of the transformed execution: the pairs of `rmw` within `X ∖ †`. -/
def rmwRelT (es : EventStructure) (x : Execution) : Rel := fun r w =>
  x.rmwRel es r w ∧ x.XT r ∧ x.XT w

/-- **`rmw` of `X ∖ †` is `rmw` of `X`.** -/
theorem rmwRelT_iff {Ω : Pred} (hx : x.IsExecution es Ω) {r w : EventId} :
    x.rmwRelT es r w ↔ x.rmwRel es r w :=
  ⟨fun h => h.1, fun h => ⟨h, rmwRel_XT hx h⟩⟩

/-- Atomicity over `X ∖ †`: `rmw_T ∩ (FR ; CO) = ∅`. -/
def AtomicityT (es : EventStructure) (x : Execution) (co : Rel) : Prop :=
  ∀ r w, x.rmwRelT es r w → ¬ ∃ w', x.fr co r w' ∧ co w' w

/-- **Atomicity over `X ∖ †` is RC11's `Atomicity`**: no RMW pair is dropped
    by the transformation. -/
theorem atomicityT_iff {Ω : Pred} (hx : x.IsExecution es Ω) {co : Rel} :
    x.AtomicityT es co ↔ x.Atomicity es co :=
  ⟨fun h r w hrw => h r w ((rmwRelT_iff hx).2 hrw),
   fun h r w hrw => h r w ((rmwRelT_iff hx).1 hrw)⟩

/-! ## `≼` within `⊑` -/

/-- The crossings the release restriction leaves: no elision of `a` into
    `remap_δ(a) = a'` crosses an event `c`, `a ⊑ c ⊑ a'`, that may alias `a`
    (under a justification's alias predicate `P_j ∧ ψ_δ` or the combined
    predicate), unless `c` is elided into `a'` too; nor one where `c` is an
    RMW access. MoRDor's Write Elision asks the elided write to be the
    immediate `ppo_loc`-predecessor of the eliding one (`fprime`), which an
    aliasing `c` in between would refute; that is not derived here. That `a`
    is no RMW access is (`rmw_not_elided`); crossing one is not excluded:
    `x := 1; FADD_rel(x, 1)` may elide `x := 1` into the FADD's write, across
    its read. `pred` is taken
    in the eliding justification `j₀` (its `P` and `δ`), while the alias
    queries here are under the execution's predicates: a justification of
    `x` whose predicate Strengthening never made distinguish `c` from `a`
    (e.g. `x := 1; *p := 2; x := 3`, elided under `p ≠ &x` and `*p := 2`
    justified under `⊤`) may alias them, and `c` may already be remapped by
    `j₀.δ`, so that it is not `≼`-between in `j₀`. -/
def NoCrossLoc (es : EventStructure) (x : Execution) : Prop :=
  ∀ a a' c, x.δ.Remap a a' → es.poR a c → es.poR c a' →
    (es.mustAlias a c ∨ es.mayAlias (x.Pm es) a c ∨ (∃ j ∈ x.J, es.mayAlias (x.PJ es j) a c) ∨
      es.RMWAcc c) →
    x.δ.Remap c a'

/-- Where `δ` has no edge, `NoCrossLoc` holds. -/
theorem noCrossLoc_of_noEdge (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hnoδ : ∀ a b, ¬ x.δ.edge a b) : NoCrossLoc es x :=
  fun a a' c hr h₁ h₂ _ => noCross_of_noEdge hpo_trans hirr hnoδ a a' c hr h₁ h₂

/-- `NoCross` implies `NoCrossLoc`. -/
theorem noCrossLoc_of_noCross (h : NoCross es x) : NoCrossLoc es x :=
  fun a a' c hr h₁ h₂ _ => h a a' c hr h₁ h₂

/-- The common part of the backward case: a base pair `a ⊑ b` whose images
    are reversed, `b' ⊑ a'`, has `b ⊑ a'`. -/
theorem backward_cross (hW : WEForward es x)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    {b a' b' : EventId} (rb : x.δ.Remap b b') (hb'a' : es.poR b' a') :
    es.poR b a' := by
  rcases remap_fwd hW hpo_trans rb with rfl | hbb
  · exact hb'a'
  · exact hpo_trans _ _ _ hbb hb'a'

/-- **A step of `ppoM`, anchored and on the path, lies in `⊑`** without
    forwarding, under the release restriction and `NoCrossLoc`. -/
theorem ppoM_po_T {Ω : Pred} (hx : x.IsExecution es Ω) (hW : WEForward es x)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hL : NoCrossLoc es x) (hT : RMWTightR es x)
    {Pa Pr : Pred}
    (hPa : ∀ a c, es.mayAlias Pa a c →
      es.mayAlias (x.Pm es) a c ∨ ∃ j ∈ x.J, es.mayAlias (x.PJ es j) a c)
    {a' b' : EventId} (ha' : x.XwF es a') (hb' : x.XwF es b')
    (hA : x.Anchored es a' b') (h : es.ppoM Pa Pr x.δ a' b') : es.poR a' b' := by
  obtain ⟨⟨a, b, hab, ra, rb⟩, hne⟩ := h
  have hu := hx.fwdWF.uniq
  have hfun := fun {e e₁ e₂ : EventId} => @FwdCtx.Remap.functional x.δ hu e e₁ e₂
  -- the base pair is `⊑`-forward
  have hbase : es.poR a b := by
    rcases hab with (hs | (⟨w, hs, ent, hm, hw, hr', -⟩ | ⟨r, ⟨ent, hm, hw, hr', -⟩, hs⟩)) | hal
    · exact hs.1
    · subst hw hr'
      rcases hT.1 ent hm a a' ra ha' hs.1 with rfl | h
      · exact absurd (hfun ra rb) hne
      · exact h
    · subst hw hr'
      rcases hT.2 ent hm b b' rb hb' hs.1 with rfl | h
      · exact absurd (hfun ra rb) hne
      · exact h
    · exact hal.1
  rcases anchored_cmp hF hA with h | h | h
  · exact absurd h hne
  · exact h
  · -- backward: `b ⊑ a'`, and `b` is shown to be elided into `a'`
    have hba' := backward_cross hW hpo_trans rb h
    have hcross : x.δ.Remap b a' := by
      rcases hab with (hs | (⟨w, hs, ent, hm, hw, hr', -⟩ | ⟨r, ⟨ent, hm, hw, hr', -⟩, hs⟩)) | hal
      · rcases hs.2 with hacq | hrel
        · -- an acquiring read or fence is not elided, so `a = a'`
          have hna : ¬ x.elided a := not_elided_of_not_write hx hW
            (fun _ h => Event.not_write_of_isAcqM h) hacq
          have haa : a = a' := Classical.byContradiction fun hne' =>
            hna (elided_of_remap_ne ra hne')
          subst haa
          exact absurd (hpo_trans _ _ _ hbase hba') (hirr _)
        · rcases remap_cross_pub hx hW hpo_trans hirr hF ra b hbase hba' with h' | h'
          · exact h'
          · exact absurd (cls_mono es (fun _ h => Event.publishes_of_isRelM h) hrel) h'
      · exact hL a a' b ra hbase hba' (.inr (.inr (.inr ⟨ent, hm, .inl hr'⟩)))
      · -- `a` is the RMW's write, which is not elided, so `a = a'`
        have haa : a = a' := remap_rmwAcc hx ra ⟨ent, hm, .inr hw⟩
        subst haa
        exact absurd (hpo_trans _ _ _ hbase hba') (hirr _)
      · rcases hal.2 with hm | hm
        · exact hL a a' b ra hbase hba' (.inl hm)
        · rcases hPa a b hm with h' | h'
          · exact hL a a' b ra hbase hba' (.inr (.inl h'))
          · exact hL a a' b ra hbase hba' (.inr (.inr (.inl h')))
    exact absurd (hfun rb hcross) (fun h => hne h.symm)

/-- **The remapped `ppo_sync` has no backward pair under the release
    restriction**: without forwarding, every anchored pair of it on the path
    lies in `⊑`, with no hypothesis on crossings. -/
theorem ppoSyncRM_po_T {Ω : Pred} (hx : x.IsExecution es Ω) (hW : WEForward es x)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es)
    {a' b' : EventId} (hA : x.Anchored es a' b') (h : es.ppoSyncRM x.δ a' b') : es.poR a' b' := by
  obtain ⟨⟨a, b, hs, ra, rb⟩, hne⟩ := h
  have hfun := fun {e e₁ e₂ : EventId} => @FwdCtx.Remap.functional x.δ hx.fwdWF.uniq e e₁ e₂
  rcases anchored_cmp hF hA with h | h | h
  · exact absurd h hne
  · exact h
  · have hba' := backward_cross hW hpo_trans rb h
    rcases hs.2 with hacq | hrel
    · have hna : ¬ x.elided a := not_elided_of_not_write hx hW
        (fun _ h => Event.not_write_of_isAcqM h) hacq
      have haa : a = a' := Classical.byContradiction fun hne' =>
        hna (elided_of_remap_ne ra hne')
      subst haa
      exact absurd (hpo_trans _ _ _ hs.1 hba') (hirr _)
    · rcases remap_cross_pub hx hW hpo_trans hirr hF ra b hs.1 hba' with h' | h'
      · exact absurd (hfun rb h') (fun h => hne h.symm)
      · exact absurd (cls_mono es (fun _ h => Event.publishes_of_isRelM h) hrel) h'

theorem mayAlias_Pm_or_PJ {Pa : Pred} (hPa : Pa = x.Pm es ∨ ∃ j ∈ x.J, Pa = x.PJ es j)
    {a c : EventId} (h : es.mayAlias Pa a c) :
    es.mayAlias (x.Pm es) a c ∨ ∃ j ∈ x.J, es.mayAlias (x.PJ es j) a c := by
  rcases hPa with rfl | ⟨j, hj, rfl⟩
  · exact .inl h
  · exact .inr ⟨j, hj, h⟩

/-- **Without forwarding, each step of `≼` lies in `⊑`**, under the release
    restriction and `NoCrossLoc`. -/
theorem ppoStep_po_T {Ω : Pred} (hx : x.IsExecution es Ω) (hW : WEForward es x)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hL : NoCrossLoc es x) (hT : RMWTightR es x)
    {a b : EventId} (h : x.ppoStep es a b) : es.poR a b := by
  obtain ⟨ha, hb, ⟨j, hj, hp, hwa, hwb⟩ | ⟨hs | ⟨hp, -⟩, hA⟩⟩ := h
  · exact ppoM_po_T hx hW hpo_trans hirr hF hL hT
      (fun _ _ h => mayAlias_Pm_or_PJ (.inr ⟨j, hj, rfl⟩) h) ha hb
      (anchored_of_inWin hx.inX ⟨j, hj, hwa, hwb⟩) hp
  · exact ppoSyncRM_po_T hx hW hpo_trans hirr hF hA hs
  · exact ppoM_po_T hx hW hpo_trans hirr hF hL hT
      (fun _ _ h => mayAlias_Pm_or_PJ (.inl rfl) h) ha hb hA hp

/-- **`DP ∪ ≼ ⊆ ⊑` without forwarding**, under the release restriction and
    `NoCrossLoc`. -/
theorem dep_po_T {Ω : Pred} (hx : x.IsExecution es Ω) (hW : WEForward es x)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hL : NoCrossLoc es x) (hT : RMWTightR es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b) {a b : EventId} (h : x.dep es a b) :
    x.poX es a b := by
  rcases h with hp | hd
  · exact ⟨.inl hp.1, .inl hp.2.1,
      ppo_po hpo_trans (fun _ _ h => ppoStep_po_T hx hW hpo_trans hirr hF hL hT h) hp⟩
  · exact ⟨.inl hd.1, .inl hd.2.1, hDP a b hd⟩

end Elided

/-! ## `HB_v`-coherence and `CoherenceT` -/

section Equiv

variable {es x}

/-- No step of `DP ∪ ≼ ∪ SW` ends at an elided event, where no elided write is
    justified in the execution. -/
theorem step_tgt {Ω : Pred} (hx : x.IsExecution es Ω) (hW : WEForward es x)
    (hJ : ∀ j ∈ x.J, ¬ x.elided j.w.id) {c d : EventId}
    (h : ((x.dep es).union (x.sw es)) c d) : ¬ x.elided d := by
  rcases h with (hp | hd) | hs
  · -- the last step of `≼` ends at an image of `remap_δ`
    obtain ⟨-, -, hp⟩ := hp
    have last : ∀ c d, x.ppoStep es c d → ¬ x.elided d := by
      rintro c d ⟨-, -, ⟨j, -, ⟨⟨_, _, _, -, rb⟩, -⟩, -⟩ | ⟨⟨⟨_, _, _, -, rb⟩, -⟩ |
        ⟨⟨⟨_, _, _, -, rb⟩, -⟩, -⟩, -⟩⟩ <;> exact remap_not_elided rb
    cases hp with
    | single h => exact last _ _ h
    | tail _ h => exact last _ _ h
  · obtain ⟨-, -, j, hj, rfl, -⟩ := hd
    exact hJ j hj
  · obtain ⟨-, -, -, -, -, -, -, -, -, hacq⟩ := hs
    rcases hacq with h | h
    · exact not_elided_of_not_write hx hW
        (fun _ h => Event.not_write_of_isRead (isRead_of_isAcqR h)) h
    · exact not_elided_of_not_write hx hW
        (fun _ h => Event.not_write_of_isFence (isFence_of_isAcqF h)) h

/-- A step of `DP ∪ ≼ ∪ SW` from an event that is not elided is a step of
    `⊑ ∪ SW` over `X ∖ †`. -/
theorem step_T {Ω : Pred} (hx : x.IsExecution es Ω) (hW : WEForward es x)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hL : NoCrossLoc es x) (hT : RMWTightR es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b) (hJ : ∀ j ∈ x.J, ¬ x.elided j.w.id)
    {c d : EventId} (hc : ¬ x.elided c) (h : ((x.dep es).union (x.sw es)) c d) :
    ((x.poXT es).union (x.swT es)) c d := by
  have hd := step_tgt hx hW hJ h
  rcases h with hdep | hs
  · exact .inl ⟨dep_po_T hx hW hpo_trans hirr hF hL hT hDP hdep, hc, hd⟩
  · exact .inr ⟨hs, hc, hd⟩

/-- No `ECO` edge ends at an elided event, for a coherence order of `X ∖ †`. -/
theorem eco_tgt {Ω : Pred} (hx : x.IsExecution es Ω) (hW : WEForward es x) {co : Rel}
    (hco : x.CoherenceOrderT es co) {a b : EventId} (h : x.eco co b a) : ¬ x.elided a := by
  have one : ∀ c d, ((x.rf.union co).union (x.fr co)) c d → ¬ x.elided d := by
    rintro c d ((h | h) | ⟨w, -, h⟩)
    · exact not_elided_of_not_write hx hW (fun _ h => Event.not_write_of_isRead h)
        (hx.rf_wr c d h).2.1
    · exact (hco.writes c d h).2.1.2
    · exact (hco.writes w d h).2.1.2
  cases h with
  | single h => exact one _ _ h
  | tail _ h => exact one _ _ h

/-- **`CoherenceT` implies `HB_v`-coherence**, for one coherence order of
    `X ∖ †`: without forwarding, under the release restriction, `NoCrossLoc`,
    `RMWTightR`, `DP ⊆ ⊑`, and no justification of an elided write. No
    `NoCross`, and no hypothesis that the path has no elided event. -/
theorem coherenceV_of_coherenceT {Ω : Pred} {co : Rel} (hx : x.IsExecution es Ω)
    (hnoF : ∀ p ∈ x.δ.f, False)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hL : NoCrossLoc es x) (hT : RMWTightR es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b) (hJ : ∀ j ∈ x.J, ¬ x.elided j.w.id)
    (hco : x.CoherenceOrderT es co) (h : x.CoherenceT es co) : x.CoherenceV es co := by
  have hW := weForward_of_noFwd hx hnoF
  rintro a ⟨b, hab, hba⟩
  have ha : ¬ x.elided a := by
    rcases hba with rfl | heco
    · cases hab with
      | single s => exact step_tgt hx hW hJ s
      | tail _ s => exact step_tgt hx hW hJ s
    · exact eco_tgt hx hW hco heco
  -- the path stays among events that are not elided
  have path : ∀ c, x.hbV es a c → x.hbT es a c ∧ ¬ x.elided c := by
    intro c hc
    induction hc with
    | single s =>
        exact ⟨.single (step_T hx hW hpo_trans hirr hF hL hT hDP hJ ha s), step_tgt hx hW hJ s⟩
    | tail _ s ih =>
        exact ⟨.tail ih.1 (step_T hx hW hpo_trans hirr hF hL hT hDP hJ ih.2 s),
          step_tgt hx hW hJ s⟩
  exact h a ⟨b, (path b hab).1, hba⟩

/-- An `HB_T` path is an `HB_v` path or a single `⊑` edge of `X ∖ †`. -/
theorem hbT_cases (hnf : x.FenceFree es)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a)
    {a b : EventId} (h : x.hbT es a b) : x.hbV es a b ∨ x.poXT es a b := by
  have potr : ∀ a b c, x.poXT es a b → x.poXT es b c → x.poXT es a c :=
    fun _ _ _ ⟨⟨ha, _, h₁⟩, hna, _⟩ ⟨⟨_, hc, h₂⟩, _, hnc⟩ =>
      ⟨⟨ha, hc, hpo_trans _ _ _ h₁ h₂⟩, hna, hnc⟩
  have hrel : ∀ a w, x.poXT es a w → es.cls Event.isRelW w → x.dep es a w :=
    fun _ _ ⟨hp, hna, hnw⟩ hw => rel_dep_ne hnf hirr hna hnw hp hw
  have hacq : ∀ r b, es.cls Event.isAcqR r → x.poXT es r b → x.dep es r b :=
    fun _ _ hr ⟨hp, hnr, hnb⟩ => acq_dep_ne hnf hirr hnr hnb hr hp
  have inv : x.poXT es a b ∨ ∃ r, x.hbV es a r ∧ es.cls Event.isAcqR r ∧
      (r = b ∨ x.poXT es r b) := by
    induction h with
    | single h =>
      rcases h with hp | hs
      · exact .inl hp
      · exact .inr ⟨_, .single (.inr hs.1), sw_acq hnf hs.1, .inl rfl⟩
    | tail _ h ih =>
      rcases h with hp | hs
      · rcases ih with hpo | ⟨r, hr, hacqr, rfl | hpo⟩
        · exact .inl (potr _ _ _ hpo hp)
        · exact .inr ⟨r, hr, hacqr, .inr hp⟩
        · exact .inr ⟨r, hr, hacqr, .inr (potr _ _ _ hpo hp)⟩
      · have hc : x.hbV es _ _ := .single (.inr hs.1)
        refine .inr ⟨_, ?_, sw_acq hnf hs.1, .inl rfl⟩
        rcases ih with hpo | ⟨r, hr, hacqr, rfl | hpo⟩
        · exact transGen_trans (.single (.inl (hrel _ _ hpo (x.sw_shape es hnf hs.1).1))) hc
        · exact transGen_trans hr hc
        · exact transGen_trans (transGen_trans hr (.single (.inl (hacq _ _ hacqr hpo)))) hc
  rcases inv with hpo | ⟨r, hr, hacqr, rfl | hpo⟩
  · exact .inr hpo
  · exact .inl hr
  · exact .inl (transGen_trans hr (.single (.inl (hacq _ _ hacqr hpo))))

/-- **`HB_v`-coherence implies `CoherenceT`**, for fence-free executions with
    a location model, whatever `δ`: conditions (i) and (ii) hold between events
    that are not elided, and `HB_T` relates only those. -/
theorem coherenceT_of_coherenceV {co : Rel} (hnf : x.FenceFree es)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a)
    (hLtrans : ∀ a b c, x.sameLoc es a b → x.sameLoc es b c → x.sameLoc es a c)
    (hrfL : ∀ a b, x.rf a b → x.sameLoc es a b)
    (hcoL : ∀ a b, co a b → x.sameLoc es a b) (hm : LocModel es x)
    (h : x.CoherenceV es co) : x.CoherenceT es co := by
  rintro a ⟨b, hab, hba⟩
  rcases hbT_cases hnf hpo_trans hirr hab with hp | ⟨hpo, hna, hnb⟩
  · exact h a ⟨b, hp, hba⟩
  · rcases hba with rfl | heco
    · exact hirr _ hpo.2.2
    · have hl := x.eco_loc es hLtrans hrfL hcoL heco
      exact h a ⟨b, .single (.inl (poloc_dep_ne hnf hirr hm hna hnb ⟨hpo, hl⟩)), .inr heco⟩

/-- **`HB_v`-coherence and `CoherenceT` coincide** for a coherence order of
    `X ∖ †`, for fence-free executions with a location model, without
    forwarding, under the release restriction, `NoCrossLoc`, `RMWTightR`,
    `DP ⊆ ⊑`, and no justification of an elided write. -/
theorem coherenceT_iff_coherenceV {Ω : Pred} {co : Rel} (hx : x.IsExecution es Ω)
    (hnf : x.FenceFree es) (hnoF : ∀ p ∈ x.δ.f, False)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hL : NoCrossLoc es x) (hT : RMWTightR es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b) (hJ : ∀ j ∈ x.J, ¬ x.elided j.w.id)
    (hLtrans : ∀ a b c, x.sameLoc es a b → x.sameLoc es b c → x.sameLoc es a c)
    (hrfL : ∀ a b, x.rf a b → x.sameLoc es a b)
    (hco : x.CoherenceOrderT es co) (hcoL : ∀ a b, co a b → x.sameLoc es a b)
    (hm : LocModel es x) :
    x.CoherenceT es co ↔ x.CoherenceV es co :=
  ⟨coherenceV_of_coherenceT hx hnoF hpo_trans hirr hF hL hT hDP hJ hco,
   coherenceT_of_coherenceV hnf hpo_trans hirr hLtrans hrfL hcoL hm⟩

end Equiv

end Execution
