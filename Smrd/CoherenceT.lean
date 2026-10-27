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
* `remap_cross_pub`: under the restriction, without forwarding, an elision
  crosses no event that publishes (release write, release or `sc` fence,
  `sc` read) unless that event is elided into the same write.
* Forwarding carries the dual, acquire restriction
  (`EventStructure.fwdNoAcq`, MoRDor #210): without it, forwarding a store
  into a later one across an acquire, `x := 1; r0 :acq= flag; x := 1`, makes
  `CoherenceT` admit an outcome RC11 and `HB_v`-coherence forbid
  (`Smrd.FwdAcrossAcquire`).
* `remap_stay_up`, `remap_enter_up`, `remap_acq_back`, `remap_rel_fwd`: a
  chain of `remap_δ` (Write Elision moves `⊑`-forward, Forwarding
  `⊑`-backward) leaves the up-set of an event `c` only by a Forwarding edge
  across `c`, and enters it only by a Write Elision edge across `c`; the
  chain of an acquiring event moves backward, that of a releasing event
  forward.
* `sync_not_back`, `ppoSyncRM_po_T`: hence `remap_δ` reverses no pair of
  `ppo_sync`, with forwarding and write elision, under the two restrictions
  and with no other hypothesis on `δ`: the remapped `ppo_sync` has no backward
  pair. The backward pairs `(x := 2, flag :rel= 1)` and `(r0, x := 1)` that
  made MoRDor's sMRD forbid the two outcomes are not generated, and not
  needed.
* `dep_po_T`: `DP ∪ ≼ ⊆ ⊑` with forwarding and write elision, where `remap_δ`
  reverses no `⊑`-pair of events that may alias or of which one is an RMW
  access (`NoRevLoc`), and RMWs are tight (`RMWTightR`). `NoRevLoc` is what
  MoRDor's `pred` condition (the source is the immediate `ppo_loc`-predecessor)
  is meant to give, but it does not follow from the restrictions: in a
  consistent execution, a justification that never distinguished two pointers
  orders an event before a forwarded read that another justification forwarded
  across it, and `≼ ⊄ ⊑` (`Smrd.FwdAcrossAlias`). Without forwarding it follows
  from `NoCrossLoc` (`noRevLoc_of_noCrossLoc`), the hypothesis this replaces.
  No `WEForward`, no hypothesis that there is no forwarding.
* `coherenceV_of_coherenceT`, `coherenceT_of_coherenceV`,
  `coherenceT_iff_coherenceV`: `HB_v`-coherence (`HB_v = (DP ∪ ≼ ∪ SW)⁺`, the
  operational semantics' happens-before) and `CoherenceT` coincide for one
  coherence order over `X ∖ †`, with forwarding and write elision, under
  `NoRevLoc`, `RMWTightR`, `DP ⊆ ⊑`, `φ`, no justification of an elided write
  (`hJ`), and where no acquire read is forwarded (`hnoAcqF`). A forwarded
  acquire read is `SW`-after its release in `HB_v` but not in `HB_T`; it has
  no `HB_v`-successor, so only a cycle closing through its `FR` is at stake,
  which is not ruled out here. Elided (forwarded) reads that are `ECO`-targets
  have no `HB_v`-successor (`no_step_elided_read`, from `φ`). That elisions
  point `⊑`-forward and forwardings `⊑`-backward is derived (`we_po`,
  `fwd_po`).
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
    source, so `remap_fwd` fails with it. The results below that need
    `⊑`-forward chains (`dep_po_T`, `coherenceV_of_coherenceT`) no longer go
    through `WEForward`: they use the acquire restriction on Forwarding
    (`remap_stay_up`, `sync_not_back`). -/
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

/-- **Every forwarding edge of an execution was generated under Forwarding's
    conditions** (`fwdRel`), the acquire restriction among them. -/
theorem fwd_edge {Ω : Pred} (hx : x.IsExecution es Ω) {p : EventId × EventId} (hp : p ∈ x.δ.f) :
    ∃ j₀ : Justification, es.fwdRel j₀ p.1 p.2 := by
  obtain ⟨j, hj, hpj⟩ := mem_δ_f_inv hp
  exact EventStructure.Generated.fwd_mem es (hx.generated j hj) p hpj

/-- **Every forwarding of an execution is `⊑`-backward**, `e₁ ⊑ e₂` for
    `(e₁, e₂) ∈ F`: Forwarding asks it of the pair (`fwdBase`). -/
theorem fwd_po {Ω : Pred} (hx : x.IsExecution es Ω) : ∀ p ∈ x.δ.f, es.poR p.1 p.2 :=
  fun _ hp => by
    obtain ⟨j₀, ⟨⟨⟨-, hpo, -⟩, -⟩, -⟩⟩ := fwd_edge hx hp
    exact hpo

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

/-! ### Chains of `remap_δ` with forwarding

`remap_δ` follows a chain of `F ∪ WE` edges: a Write Elision edge moves an
event `⊑`-forward (`we_po`), a Forwarding edge `⊑`-backward (`fwd_po`). A
chain that starts at or after an event `c` and ends before it crosses `c` by a
Forwarding edge, or passes through `c` (`remap_stay_up`); one that starts
outside the up-set of `c` and ends in it crosses `c` by a Write Elision edge,
or passes through `c` (`remap_enter_up`). The release restriction excludes
the second for a publishing `c`, the acquire restriction the first for an
acquiring `c`. -/

/-- An edge of the execution's `F ∪ WE` is a Forwarding edge, `⊑`-backward,
    or a Write Elision edge, `⊑`-forward. -/
theorem edge_cases {Ω : Pred} (hx : x.IsExecution es Ω) {q p : EventId} (h : x.δ.edge q p) :
    ((q, p) ∈ x.δ.f ∧ es.poR q p) ∨ ((q, p) ∈ x.δ.we ∧ es.poR p q) := by
  rcases h with h | h
  · exact .inl ⟨h, fwd_po hx _ h⟩
  · exact .inr ⟨h, we_po hx _ h⟩

/-- **A chain from the up-set of `c` stays in it**, unless it passes through
    `c` or a Forwarding edge crosses `c`. -/
theorem remap_stay_up {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c) (hF : PoForest es)
    {c e e' : EventId} (h : x.δ.Remap e e') (hc : c = e ∨ es.poR c e) :
    (c = e' ∨ es.poR c e') ∨ x.δ.Remap c e' ∨
      ∃ q p, (q, p) ∈ x.δ.f ∧ es.poR q c ∧ es.poR c p := by
  revert hc
  induction h with
  | canon _ => exact fun hc => .inl hc
  | @step q e e' he hr ih =>
      rintro (rfl | hce)
      · exact .inr (.inl (.step he hr))
      · rcases edge_cases hx he with ⟨hf, hqe⟩ | ⟨-, heq⟩
        · rcases hF q c e (.inr hqe) (.inr hce) with rfl | hqc | hcq
          · exact .inr (.inl hr)
          · exact .inr (.inr ⟨q, e, hf, hqc, hce⟩)
          · exact ih (.inr hcq)
        · exact ih (.inr (hpo_trans _ _ _ hce heq))

/-- **A chain into the up-set of `c` from outside it** passes through `c`, or
    a Write Elision edge crosses `c`. -/
theorem remap_enter_up {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c) (hF : PoForest es)
    {c e e' : EventId} (h : x.δ.Remap e e') (hc : ¬ (c = e ∨ es.poR c e))
    (hc' : c = e' ∨ es.poR c e') :
    x.δ.Remap c e' ∨ ∃ q p, (q, p) ∈ x.δ.we ∧ es.poR p c ∧ es.poR c q := by
  revert hc
  induction h with
  | canon _ => exact fun hc => absurd hc' hc
  | @step q e e' he hr ih =>
      intro hc
      by_cases hq : c = q ∨ es.poR c q
      · rcases edge_cases hx he with ⟨-, hqe⟩ | ⟨hw, heq⟩
        · rcases hq with rfl | hcq
          · exact absurd (.inr hqe) hc
          · exact absurd (.inr (hpo_trans _ _ _ hcq hqe)) hc
        · rcases hq with rfl | hcq
          · exact .inl hr
          · rcases hF c e q (.inr hcq) (.inr heq) with rfl | hce | hec
            · exact absurd (.inl rfl) hc
            · exact absurd (.inr hce) hc
            · exact .inr ⟨q, e, hw, hec, hcq⟩
      · exact ih hc' hq

theorem isRead_of_isRlxR {e : Event} (h : e.isRlxR = true) : e.isRead = true := by
  obtain ⟨id, k, l, g⟩ := e
  cases k with
  | read o => cases o <;> simp_all [Event.isRlxR, Event.isRead]
  | _ => simp_all [Event.isRlxR]

theorem isWrite_of_isRlxW {e : Event} (h : e.isRlxW = true) : e.isWrite = true := by
  obtain ⟨id, k, l, g⟩ := e
  cases k with
  | write o => cases o <;> simp_all [Event.isRlxW, Event.isWrite]
  | _ => simp_all [Event.isRlxW]

/-- The forwarded event is a read or a write. -/
theorem fwd_tgt_rw {j : Justification} {e₁ e₂ : EventId} (h : es.fwdRelBlind j e₁ e₂) :
    es.cls (fun e => e.isRead || e.isWrite) e₂ := by
  obtain ⟨-, hk, -⟩ := h
  rcases hk with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · exact cls_mono es (fun e h => by simp [isRead_of_isRlxR h]) h
  · exact cls_mono es (fun e h => by simp [isWrite_of_isRlxW h]) h
  · exact cls_mono es (fun e h => by simp [h]) h

/-- An acquiring fence is neither forwarded nor elided. -/
theorem fence_not_rw {e : Event} (h : e.isAcqF = true) : (e.isRead || e.isWrite) = false := by
  obtain ⟨id, k, l, g⟩ := e
  cases k <;> simp_all [Event.isAcqF, Event.isRead, Event.isWrite]

theorem acquires_of_isAcqM {e : Event} (h : e.isAcqM = true) : e.acquires = true := by
  simpa [Event.acquires, Event.isAcqM] using h

/-- **The chain of an acquiring event moves `⊑`-backward**: only an acquire
    read is forwarded into an acquire read (`fwdNoAcq`), an acquire fence is
    not forwarded, and neither is elided by Write Elision. -/
theorem remap_acq_back {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    {a a' : EventId} (h : x.δ.Remap a a') (ha : es.cls Event.isAcqM a) :
    a = a' ∨ es.poR a' a := by
  induction h with
  | canon _ => exact .inl rfl
  | @step q e e' he hr ih =>
      rcases edge_cases hx he with ⟨hf, hqe⟩ | ⟨hw, -⟩
      · obtain ⟨j₀, hb, hna, -⟩ := fwd_edge hx hf
        dsimp only at hb hna
        have hacqR : es.cls Event.isAcqR e := by
          obtain ⟨ev, hev, hm⟩ := ha
          simp only [Event.isAcqM, Bool.or_eq_true] at hm
          rcases hm with hm | hm
          · exact ⟨ev, hev, hm⟩
          · obtain ⟨ev', hev', hrw⟩ := fwd_tgt_rw hb
            rw [hev] at hev'; cases hev'
            have := fence_not_rw hm
            simp only [this] at hrw; cases hrw
        have hq : es.cls Event.isAcqM q :=
          cls_mono es (fun e h => by simp [Event.isAcqM, h]) (hna.1 hacqR)
        rcases ih hq with rfl | h'
        · exact .inr hqe
        · exact .inr (hpo_trans _ _ _ h' hqe)
      · obtain ⟨j₀, ⟨⟨-, hwr, -, -⟩, -⟩, -⟩ := we_edge hx hw
        exact absurd (cls_excl es (fun e h₁ h₂ => by rw [Event.not_write_of_isAcqM h₁] at h₂; cases h₂)
          ha hwr) id

theorem relM_not_fwd {e : Event} (h : e.isRelM = true) :
    e.isRlxR = false ∧ e.isRlxW = false ∧ e.isRead = false := by
  obtain ⟨id, k, l, g⟩ := e
  cases k with
  | read o => cases o <;> simp_all [Event.isRelM, Event.isRelW, Event.isRelF]
  | write o => cases o <;> simp_all [Event.isRelM, Event.isRelW, Event.isRelF, MemOrd.isRelSc,
      Event.isRlxR, Event.isRlxW, Event.isRead]
  | fence o => cases o <;> simp_all [Event.isRelM, Event.isRelW, Event.isRelF, MemOrd.isRelSc,
      Event.isRlxR, Event.isRlxW, Event.isRead]
  | _ => simp_all [Event.isRelM, Event.isRelW, Event.isRelF]

theorem isRelM_of_isRelW {e : Event} (h : e.isRelW = true) : e.isRelM = true := by
  simp [Event.isRelM, h]

/-- **The chain of a releasing event moves `⊑`-forward**: a release write or
    fence is not forwarded, and a release write is elided only into a release
    write (`weNoRel`). -/
theorem remap_rel_fwd {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    {b b' : EventId} (h : x.δ.Remap b b') (hb : es.cls Event.isRelM b) :
    b = b' ∨ es.poR b b' := by
  induction h with
  | canon _ => exact .inl rfl
  | @step q e e' he hr ih =>
      rcases edge_cases hx he with ⟨hf, -⟩ | ⟨hw, heq⟩
      · obtain ⟨j₀, ⟨-, hk, -⟩, -, -⟩ := fwd_edge hx hf
        dsimp only at hk
        obtain ⟨ev, hev, hm⟩ := hb
        have hn := relM_not_fwd hm
        rcases hk with ⟨-, ev', hev', h'⟩ | ⟨-, ev', hev', h'⟩ | ⟨-, ev', hev', h'⟩ <;>
          (rw [hev] at hev'; cases hev') <;> simp_all
      · obtain ⟨j₀, ⟨⟨-, hwr, -, -⟩, hnr, -⟩, -⟩ := we_edge hx hw
        dsimp only at hwr hnr
        have hrelW : es.cls Event.isRelW e := by
          obtain ⟨ev, hev, hm⟩ := hb
          simp only [Event.isRelM, Bool.or_eq_true] at hm
          rcases hm with hm | hm
          · exact ⟨ev, hev, hm⟩
          · obtain ⟨ev', hev', hw'⟩ := hwr
            rw [hev] at hev'; cases hev'
            rw [Event.not_write_of_isFence (isFence_of_isRelF hm)] at hw'; cases hw'
        have hq : es.cls Event.isRelM q := cls_mono es (fun _ h => isRelM_of_isRelW h) (hnr.1 hrelW)
        rcases ih hq with rfl | h'
        · exact .inr heq
        · exact .inr (hpo_trans _ _ _ heq h')

/-- **No pair of `ppo_sync` is reversed by `remap_δ`**, with forwarding and
    write elision, under their restrictions: for an acquire source `a`, the
    chain of `a` moves backward and that of `b` stays after `a`, as no
    Forwarding edge crosses `a` (`fwdNoAcq`); for a release target `b`, the
    chain of `b` moves forward and that of `a` stays out of the up-set of `b`,
    as no Write Elision edge crosses `b` (`weNoRel`). -/
theorem sync_not_back {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es)
    {a b a' b' : EventId} (hs : es.ppoSyncM a b) (ra : x.δ.Remap a a') (rb : x.δ.Remap b b')
    (hne : a' ≠ b') : ¬ es.poR b' a' := by
  intro hba
  have hfun := fun {e e₁ e₂ : EventId} => @FwdCtx.Remap.functional x.δ hx.fwdWF.uniq e e₁ e₂
  rcases hs.2 with hacq | hrel
  · rcases remap_stay_up hx hpo_trans hF rb (c := a) (.inr hs.1) with hup | hra | ⟨q, p, hf, hqa, hap⟩
    · have hb'a : es.poR b' a := by
        rcases remap_acq_back hx hpo_trans ra hacq with rfl | h
        · exact hba
        · exact hpo_trans _ _ _ hba h
      rcases hup with rfl | h
      · exact hirr _ hb'a
      · exact hirr _ (hpo_trans _ _ _ h hb'a)
    · exact hne (hfun ra hra)
    · obtain ⟨j₀, -, hna, -⟩ := fwd_edge hx hf
      exact (hna.2.2 a hqa hap).1 (cls_mono es (fun _ h => acquires_of_isAcqM h) hacq)
  · have hup : b = a' ∨ es.poR b a' := by
      rcases remap_rel_fwd hx hpo_trans rb hrel with rfl | h
      · exact .inr hba
      · exact .inr (hpo_trans _ _ _ h hba)
    have hnot : ¬ (b = a ∨ es.poR b a) := by
      rintro (rfl | h)
      · exact hirr _ hs.1
      · exact hirr _ (hpo_trans _ _ _ hs.1 h)
    rcases remap_enter_up hx hpo_trans hF ra hnot hup with hrb | ⟨q, p, hw, hpb, hbq⟩
    · exact hne (hfun hrb rb)
    · obtain ⟨j₀, ⟨-, hnr, -⟩, -⟩ := we_edge hx hw
      exact hnr.2 b hpb hbq (cls_mono es (fun _ h => Event.publishes_of_isRelM h) hrel)

/-! ### `≼ ⊆ ⊑` with forwarding -/

/-- The base pairs of `ppo_loc` and `ppo_rmw`: `a` and `b` may alias (outright,
    under the combined predicate, or under a justification's), or one is an
    RMW access. -/
def LocLinked (es : EventStructure) (x : Execution) (a b : EventId) : Prop :=
  es.mustAlias a b ∨ es.mayAlias (x.Pm es) a b ∨ (∃ j ∈ x.J, es.mayAlias (x.PJ es j) a b) ∨
    es.RMWAcc a ∨ es.RMWAcc b

/-- `remap_δ` reverses no `⊑`-ordered pair of `LocLinked` events. This is what
    MoRDor's `pred` condition (the source is an immediate `ppo_loc`-predecessor
    of the forwarded or eliding event) is meant to give. It does not follow
    from it, for the reason given at `NoCrossLoc`: `pred` is taken under the
    generating justification's `P` and `δ`, `LocLinked` under every
    justification's. `Smrd.FwdAcrossAlias` forwards `r2 := x` from
    `r0 := *p2` across `r1 := *p` under `p2 = &x ∧ p ≠ &x`, while another
    justification, strengthened by `p ≠ p2` only, lets `r1` and `r2` alias; the
    execution is consistent, satisfies every other hypothesis of `dep_po_T`,
    and violates `NoRevLoc` and `DP ∪ ≼ ⊆ ⊑`. It covers Forwarding, which
    `NoCrossLoc` does not; without forwarding `NoCrossLoc` implies it
    (`noRevLoc_of_noCrossLoc`). -/
def NoRevLoc (es : EventStructure) (x : Execution) : Prop :=
  ∀ a b a' b', es.poR a b → x.δ.Remap a a' → x.δ.Remap b b' → LocLinked es x a b →
    ¬ es.poR b' a'

/-- **Without forwarding, `NoCrossLoc` implies `NoRevLoc`.** -/
theorem noRevLoc_of_noCrossLoc {Ω : Pred} (hx : x.IsExecution es Ω) (hW : WEForward es x)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hL : NoCrossLoc es x) : NoRevLoc es x := by
  intro a b a' b' hab ra rb hl hba
  have hfun := fun {e e₁ e₂ : EventId} => @FwdCtx.Remap.functional x.δ hx.fwdWF.uniq e e₁ e₂
  have hba' := backward_cross hW hpo_trans rb hba
  have cross : x.δ.Remap b a' → False := fun h => by
    rw [hfun rb h] at hba; exact hirr _ hba
  rcases hl with hm | hm | hm | hm | hm
  · exact cross (hL a a' b ra hab hba' (.inl hm))
  · exact cross (hL a a' b ra hab hba' (.inr (.inl hm)))
  · exact cross (hL a a' b ra hab hba' (.inr (.inr (.inl hm))))
  · have haa : a = a' := remap_rmwAcc hx ra hm
    subst haa
    exact hirr _ (hpo_trans _ _ _ hab hba')
  · exact cross (hL a a' b ra hab hba' (.inr (.inr (.inr hm))))

/-- **A step of `ppoM`, anchored and on the path, lies in `⊑`**, with
    forwarding and write elision under their restrictions, and `NoRevLoc`. -/
theorem ppoM_po_T {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hL : NoRevLoc es x) (hT : RMWTightR es x)
    {Pa Pr : Pred}
    (hPa : ∀ a c, es.mayAlias Pa a c →
      es.mayAlias (x.Pm es) a c ∨ ∃ j ∈ x.J, es.mayAlias (x.PJ es j) a c)
    {a' b' : EventId} (ha' : x.XwF es a') (hb' : x.XwF es b')
    (hA : x.Anchored es a' b') (h : es.ppoM Pa Pr x.δ a' b') : es.poR a' b' := by
  obtain ⟨⟨a, b, hab, ra, rb⟩, hne⟩ := h
  have hfun := fun {e e₁ e₂ : EventId} => @FwdCtx.Remap.functional x.δ hx.fwdWF.uniq e e₁ e₂
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
  · refine absurd h ?_
    rcases hab with (hs | (⟨w, hs, ent, hm, hw, hr', -⟩ | ⟨r, ⟨ent, hm, hw, hr', -⟩, hs⟩)) | hal
    · exact sync_not_back hx hpo_trans hirr hF hs ra rb hne
    · exact hL a b a' b' hbase ra rb (.inr (.inr (.inr (.inr ⟨ent, hm, .inl hr'⟩))))
    · exact hL a b a' b' hbase ra rb (.inr (.inr (.inr (.inl ⟨ent, hm, .inr hw⟩))))
    · rcases hal.2 with hm | hm
      · exact hL a b a' b' hbase ra rb (.inl hm)
      · rcases hPa a b hm with h' | h'
        · exact hL a b a' b' hbase ra rb (.inr (.inl h'))
        · exact hL a b a' b' hbase ra rb (.inr (.inr (.inl h')))

/-- **The remapped `ppo_sync` has no backward pair**, with forwarding and
    write elision under their restrictions: every anchored pair of it lies in
    `⊑`, with no hypothesis on crossings or on forwarding. -/
theorem ppoSyncRM_po_T {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es)
    {a' b' : EventId} (hA : x.Anchored es a' b') (h : es.ppoSyncRM x.δ a' b') : es.poR a' b' := by
  obtain ⟨⟨a, b, hs, ra, rb⟩, hne⟩ := h
  rcases anchored_cmp hF hA with h | h | h
  · exact absurd h hne
  · exact h
  · exact absurd h (sync_not_back hx hpo_trans hirr hF hs ra rb hne)

theorem mayAlias_Pm_or_PJ {Pa : Pred} (hPa : Pa = x.Pm es ∨ ∃ j ∈ x.J, Pa = x.PJ es j)
    {a c : EventId} (h : es.mayAlias Pa a c) :
    es.mayAlias (x.Pm es) a c ∨ ∃ j ∈ x.J, es.mayAlias (x.PJ es j) a c := by
  rcases hPa with rfl | ⟨j, hj, rfl⟩
  · exact .inl h
  · exact .inr ⟨j, hj, h⟩

/-- **Each step of `≼` lies in `⊑`**, with forwarding and write elision under
    their restrictions, and `NoRevLoc`. -/
theorem ppoStep_po_T {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hL : NoRevLoc es x) (hT : RMWTightR es x)
    {a b : EventId} (h : x.ppoStep es a b) : es.poR a b := by
  obtain ⟨ha, hb, ⟨j, hj, hp, hwa, hwb⟩ | ⟨hs | ⟨hp, -⟩, hA⟩⟩ := h
  · exact ppoM_po_T hx hpo_trans hirr hF hL hT
      (fun _ _ h => mayAlias_Pm_or_PJ (.inr ⟨j, hj, rfl⟩) h) ha hb
      (anchored_of_inWin hx.inX ⟨j, hj, hwa, hwb⟩) hp
  · exact ppoSyncRM_po_T hx hpo_trans hirr hF hA hs
  · exact ppoM_po_T hx hpo_trans hirr hF hL hT
      (fun _ _ h => mayAlias_Pm_or_PJ (.inl rfl) h) ha hb hA hp

/-- **`DP ∪ ≼ ⊆ ⊑`**, with forwarding and write elision under their
    restrictions, `NoRevLoc`, and `DP ⊆ ⊑`. -/
theorem dep_po_T {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hL : NoRevLoc es x) (hT : RMWTightR es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b) {a b : EventId} (h : x.dep es a b) :
    x.poX es a b := by
  rcases h with hp | hd
  · exact ⟨.inl hp.1, .inl hp.2.1,
      ppo_po hpo_trans (fun _ _ h => ppoStep_po_T hx hpo_trans hirr hF hL hT h) hp⟩
  · exact ⟨.inl hd.1, .inl hd.2.1, hDP a b hd⟩

end Elided

/-! ## `HB_v`-coherence and `CoherenceT` -/

section Equiv

variable {es x}

/-- An acquire read that is not forwarded, or an acquire fence, is not
    elided: Write Elision elides writes, and Forwarding forwards reads and
    writes. -/
theorem not_elided_acq {Ω : Pred} (hx : x.IsExecution es Ω)
    (hnoAcqF : ∀ p ∈ x.δ.f, ¬ es.cls Event.isAcqR p.2) {d : EventId}
    (h : es.cls Event.isAcqR d ∨ es.cls Event.isAcqF d) : ¬ x.elided d := by
  rintro ⟨⟨q, p⟩, hp | hp, rfl⟩
  · rcases h with h | h
    · exact hnoAcqF _ hp h
    · obtain ⟨j₀, hb, -, -⟩ := fwd_edge hx hp
      obtain ⟨ev, hev, hrw⟩ := fwd_tgt_rw hb
      obtain ⟨ev', hev', hf⟩ := h
      dsimp only at hev hev'
      rw [hev] at hev'; cases hev'
      dsimp only at hrw
      rw [fence_not_rw hf] at hrw; cases hrw
  · obtain ⟨j₀, ⟨⟨-, hw, -, -⟩, -⟩, -⟩ := we_edge hx hp
    dsimp only at hw
    rcases h with h | h
    · exact cls_excl es (fun e h₁ h₂ => by
        rw [Event.not_write_of_isRead (isRead_of_isAcqR h₁)] at h₂; cases h₂) h hw
    · exact cls_excl es (fun e h₁ h₂ => by
        rw [Event.not_write_of_isFence (isFence_of_isAcqF h₁)] at h₂; cases h₂) h hw

/-- No step of `DP ∪ ≼ ∪ SW` ends at an elided event, where no elided write is
    justified in the execution and no acquire read is forwarded. -/
theorem step_tgt {Ω : Pred} (hx : x.IsExecution es Ω)
    (hnoAcqF : ∀ p ∈ x.δ.f, ¬ es.cls Event.isAcqR p.2)
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
    exact not_elided_acq hx hnoAcqF hacq

/-- A step of `DP ∪ ≼ ∪ SW` from an event that is not elided is a step of
    `⊑ ∪ SW` over `X ∖ †`. -/
theorem step_T {Ω : Pred} (hx : x.IsExecution es Ω)
    (hnoAcqF : ∀ p ∈ x.δ.f, ¬ es.cls Event.isAcqR p.2)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hL : NoRevLoc es x) (hT : RMWTightR es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b) (hJ : ∀ j ∈ x.J, ¬ x.elided j.w.id)
    {c d : EventId} (hc : ¬ x.elided c) (h : ((x.dep es).union (x.sw es)) c d) :
    ((x.poXT es).union (x.swT es)) c d := by
  have hd := step_tgt hx hnoAcqF hJ h
  rcases h with hdep | hs
  · exact .inl ⟨dep_po_T hx hpo_trans hirr hF hL hT hDP hdep, hc, hd⟩
  · exact .inr ⟨hs, hc, hd⟩

/-- An `ECO` edge ends at an elided event only if it is a read (a forwarded
    one), for a coherence order of `X ∖ †`. -/
theorem eco_tgt {Ω : Pred} (hx : x.IsExecution es Ω) {co : Rel}
    (hco : x.CoherenceOrderT es co) {a b : EventId} (h : x.eco co b a) (hel : x.elided a) :
    es.cls Event.isRead a := by
  have one : ∀ c d, ((x.rf.union co).union (x.fr co)) c d → x.elided d → es.cls Event.isRead d := by
    rintro c d ((h | h) | ⟨w, -, h⟩) hd
    · exact (hx.rf_wr c d h).2.1
    · exact absurd hd (hco.writes c d h).2.1.2
    · exact absurd hd (hco.writes w d h).2.1.2
  cases h with
  | single h => exact one _ _ h hel
  | tail _ h => exact one _ _ h hel

/-- No step of `DP ∪ ≼ ∪ SW` leaves an elided read: `≼` leaves images of
    `remap_δ`, `φ` gives an elided event no dependency, and `SW` leaves
    releasing writes and fences. -/
theorem no_step_elided_read (hphi : x.phi es) {a c : EventId} (hel : x.elided a)
    (hr : es.cls Event.isRead a) (h : ((x.dep es).union (x.sw es)) a c) : False := by
  rcases h with (hp | hd) | hs
  · obtain ⟨-, -, hp⟩ := hp
    have first : ∀ c, Relation.TransGen (x.ppoStep es) a c → ∃ d, x.ppoStep es a d := by
      intro c h
      induction h with
      | single h => exact ⟨_, h⟩
      | tail _ _ ih => exact ih
    obtain ⟨d, ⟨-, -, ⟨j, -, ⟨⟨_, _, _, ra, -⟩, -⟩, -⟩ | ⟨⟨⟨_, _, _, ra, -⟩, -⟩ |
      ⟨⟨⟨_, _, _, ra, -⟩, -⟩, -⟩, -⟩⟩⟩ := first c hp <;> exact remap_not_elided ra hel
  · exact hphi.1 a (.inr ⟨c, hd⟩) hel
  · rcases hs.1 with h | h
    · exact cls_excl es (fun e h₁ h₂ => by
        rw [Event.not_write_of_isRead h₁] at h₂; cases h₂) hr
        (cls_mono es (fun _ h => isWrite_of_isRelW h) h)
    · exact cls_excl es (fun e h₁ h₂ => not_read_fence h₁ h₂) hr
        (cls_mono es (fun _ h => isFence_of_isRelF h) h)

/-- **`CoherenceT` implies `HB_v`-coherence**, for one coherence order of
    `X ∖ †`: with forwarding and write elision under their restrictions,
    where no acquire read is forwarded, under `NoRevLoc`, `RMWTightR`,
    `DP ⊆ ⊑`, and no justification of an elided write. A forwarded acquire
    read is the target of `SW` in `HB_v` but not in `HB_T`. -/
theorem coherenceV_of_coherenceT {Ω : Pred} {co : Rel} (hx : x.IsExecution es Ω)
    (hphi : x.phi es) (hnoAcqF : ∀ p ∈ x.δ.f, ¬ es.cls Event.isAcqR p.2)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hL : NoRevLoc es x) (hT : RMWTightR es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b) (hJ : ∀ j ∈ x.J, ¬ x.elided j.w.id)
    (hco : x.CoherenceOrderT es co) (h : x.CoherenceT es co) : x.CoherenceV es co := by
  rintro a ⟨b, hab, hba⟩
  have ha : ¬ x.elided a := by
    intro hel
    rcases hba with rfl | heco
    · cases hab with
      | single s => exact step_tgt hx hnoAcqF hJ s hel
      | tail _ s => exact step_tgt hx hnoAcqF hJ s hel
    · have hr := eco_tgt hx hco heco hel
      have first : ∀ c, x.hbV es a c → ∃ d, ((x.dep es).union (x.sw es)) a d := by
        intro c h
        induction h with
        | single h => exact ⟨_, h⟩
        | tail _ _ ih => exact ih
      obtain ⟨d, hd⟩ := first b hab
      exact no_step_elided_read hphi hel hr hd
  -- the path stays among events that are not elided
  have path : ∀ c, x.hbV es a c → x.hbT es a c ∧ ¬ x.elided c := by
    intro c hc
    induction hc with
    | single s =>
        exact ⟨.single (step_T hx hnoAcqF hpo_trans hirr hF hL hT hDP hJ ha s),
          step_tgt hx hnoAcqF hJ s⟩
    | tail _ s ih =>
        exact ⟨.tail ih.1 (step_T hx hnoAcqF hpo_trans hirr hF hL hT hDP hJ ih.2 s),
          step_tgt hx hnoAcqF hJ s⟩
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
    `X ∖ †`, for fence-free executions with a location model, with forwarding
    and write elision under their restrictions, where no acquire read is
    forwarded, under `NoRevLoc`, `RMWTightR`, `DP ⊆ ⊑`, and no justification
    of an elided write. -/
theorem coherenceT_iff_coherenceV {Ω : Pred} {co : Rel} (hx : x.IsExecution es Ω)
    (hphi : x.phi es) (hnf : x.FenceFree es) (hnoAcqF : ∀ p ∈ x.δ.f, ¬ es.cls Event.isAcqR p.2)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hL : NoRevLoc es x) (hT : RMWTightR es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b) (hJ : ∀ j ∈ x.J, ¬ x.elided j.w.id)
    (hLtrans : ∀ a b c, x.sameLoc es a b → x.sameLoc es b c → x.sameLoc es a c)
    (hrfL : ∀ a b, x.rf a b → x.sameLoc es a b)
    (hco : x.CoherenceOrderT es co) (hcoL : ∀ a b, co a b → x.sameLoc es a b)
    (hm : LocModel es x) :
    x.CoherenceT es co ↔ x.CoherenceV es co :=
  ⟨coherenceV_of_coherenceT hx hphi hnoAcqF hpo_trans hirr hF hL hT hDP hJ hco,
   coherenceT_of_coherenceV hnf hpo_trans hirr hLtrans hrfL hcoL hm⟩

end Equiv

end Execution
