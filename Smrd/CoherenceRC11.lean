import Smrd.Executions

/-!
# Preserved coherence, the viewfront happens-before, and RC11's coherence axiom

`Execution.Coherence` is RC11's coherence axiom (Axiom
`def:mem-model-axiom:co`): `HB ; ECO?` irreflexive with `HB ≜ (⊑ ∪ SW)⁺` and
RC11's `SW`, closed under release sequences. This module relates it to two
other happens-before relations:

* *preserved coherence* `CoherenceP`, `HB_p ; ECO?` irreflexive with
  `HB_p ≜ (DP ∪ ≼ ∪ SW_ra)⁺` and `SW_ra ≜ rf ∩ (W_rel × R_acq)`, which the
  paper used before it adopted RC11's axiom;
* `CoherenceV`, over `HB_v ≜ (DP ∪ ≼ ∪ SW)⁺` with RC11's `SW`, the
  happens-before the operational semantics' viewfronts realise
  (`app-opsem.tex`), kept as the notion internal to the operational semantics.

The reductions over `HB_p` and `HB_v` assume the execution `FenceFree`: no
fence in `X` or on the branches `X` takes. `SW` then has the shape
`[W_rel] ; RS ; rf ; [R_acq]` (`sw_shape`). With fences `HB_v` is too weak:
`≼ ⊆ X × X`, so an `SW` edge at a fence is a dead end in `HB_v`
(`Smrd.FenceMP`). Section *Fences* replaces `≼` by `≼_F`, MoRDor's closure
over `X ∪ X_F` before its restriction to `X` (`ppoF`), and proves the
reduction for `HB_F ≜ (DP ∪ ≼_F ∪ SW)⁺` without `FenceFree`
(`coherence_of_coherenceF`, `coherenceF_iff_coherence`); without fences
`HB_F = HB_v` (`coherenceF_iff_coherenceV`), and `coherence_of_coherenceV` is
its corollary.

`coherence_of_coherenceP`: preserved coherence implies RC11 coherence when

* (`po|loc`) program order between accesses at one location is preserved,
  `⊑|loc ⊆ DP ∪ ≼`;
* (release, acquire) program order into a releasing write and out of an
  acquiring read is preserved, `⊑;[W_rel] ⊆ DP ∪ ≼` and `[R_acq];⊑ ⊆ DP ∪ ≼`;
* (release sequences) every write `⊑|loc`-after a releasing write is
  releasing, and every RMW that reads from a releasing write is
  acquire-release, so that release sequences consist of releasing writes; and
  the read of an RMW is `⊑`-before its write.

`coherenceP_of_coherence`: RC11 coherence implies preserved coherence when
`DP ∪ ≼ ⊆ ⊑`.

Both directions also assume that `⊑` is a strict order and that the
same-location relation is transitive and contains `rf` and `CO`.

The proof composes with `ECO` and probes irreflexivity, as in
`hb_eco1_irrefl_iff_hbLoc`. An `HB` path that contains an `SW` edge lies in
`HB_p` outright, by the release, acquire and release-sequence conditions. A
path made of `⊑` alone is one `⊑` edge, and `ECO` closes it into a cycle only
between events at one location, where `po|loc` applies.

`coherenceV_iff_coherence` states the same for `HB_v`. It needs only the
`po|loc`, release and acquire conditions.

The conditions are where the operational semantics falls short of RC11
(`TODO(rc11-co)` in `app-opsem.tex`). `≼_sync` contains `⊑;[W_rel]` and
`[R_acq];⊑`, but `≼` truncates them at the last justified event of a thread
and remaps them under forwarding. Release sequences beyond the releasing write
are not in `SW_ra`, but are in `HB_v`. For MoRDor's `≼`, `Smrd.PpoTail`
discharges the conditions: `DP ∪ ≼ ⊆ ⊑` without forwarding where no elision
crosses an event, (i) and (ii) where no event of the path is elided.
-/

namespace Execution

variable (es : EventStructure) (x : Execution)

/-- `SW_ra ≜ rf ∩ (W_rel × R_acq)`, without release sequences. -/
def swRA : Rel := fun w r => x.rf w r ∧ es.cls Event.isRelW w ∧ es.cls Event.isAcqR r

/-- `HB_p ≜ (DP ∪ ≼ ∪ SW_ra)⁺` -/
def hbP : Rel := Rel.plus ((x.dep es).union (x.swRA es))

/-- Preserved coherence: `HB_p ; ECO?` is irreflexive. -/
def CoherenceP (co : Rel) : Prop :=
  ∀ a, ¬ ∃ b, x.hbP es a b ∧ (b = a ∨ x.eco co b a)

/-- No fence in `X` or on the branches `X` takes. -/
def FenceFree : Prop := ∀ a, x.XwF es a → ¬ es.cls Event.isFence a

/-! ## Auxiliary facts -/

theorem transGen_trans {R : Rel} {a b c : EventId} (h₁ : Relation.TransGen R a b)
    (h₂ : Relation.TransGen R b c) : Relation.TransGen R a c := by
  induction h₂ with
  | single h => exact .tail h₁ h
  | tail _ h ih => exact .tail ih h

theorem transGen_mono {R S : Rel} (hRS : ∀ a b, R a b → S a b) {a b : EventId}
    (h : Relation.TransGen R a b) : Relation.TransGen S a b := by
  induction h with
  | single h => exact .single (hRS _ _ h)
  | tail _ h ih => exact .tail ih (hRS _ _ h)

theorem isWrite_of_isRelW {e : Event} (h : e.isRelW = true) : e.isWrite = true := by
  unfold Event.isRelW at h
  unfold Event.isWrite
  split at h <;> simp_all

theorem isRead_of_isAcqR {e : Event} (h : e.isAcqR = true) : e.isRead = true := by
  unfold Event.isAcqR at h
  unfold Event.isRead
  split at h <;> simp_all

theorem isFence_of_isRelF {e : Event} (h : e.isRelF = true) : e.isFence = true := by
  unfold Event.isRelF at h
  unfold Event.isFence
  split at h <;> simp_all

theorem isFence_of_isAcqF {e : Event} (h : e.isAcqF = true) : e.isFence = true := by
  unfold Event.isAcqF at h
  unfold Event.isFence
  split at h <;> simp_all

theorem not_write_fence {e : Event} (h₁ : e.isWrite = true) (h₂ : e.isFence = true) : False := by
  unfold Event.isWrite at h₁
  unfold Event.isFence at h₂
  split at h₁ <;> simp_all

theorem not_read_fence {e : Event} (h₁ : e.isRead = true) (h₂ : e.isFence = true) : False := by
  unfold Event.isRead at h₁
  unfold Event.isFence at h₂
  split at h₁ <;> simp_all

theorem cls_mono {p q : Event → Bool} (h : ∀ e, p e = true → q e = true) {a : EventId}
    (hp : es.cls p a) : es.cls q a := by
  obtain ⟨e, he, hpe⟩ := hp
  exact ⟨e, he, h e hpe⟩

theorem cls_excl {p q : Event → Bool} (h : ∀ e, p e = true → q e = true → False) {a : EventId}
    (hp : es.cls p a) (hq : es.cls q a) : False := by
  obtain ⟨e, he, hpe⟩ := hp
  obtain ⟨e', he', hqe⟩ := hq
  rw [he] at he'
  cases he'
  exact h e hpe hqe

/-- Without fences, RC11's `SW` is `[W_rel] ; RS ; rf ; [R_acq]`. -/
theorem sw_shape (hnf : x.FenceFree es) {a b : EventId} (h : x.sw es a b) :
    es.cls Event.isRelW a ∧ ∃ w', x.rs es a w' ∧ x.rf w' b ∧ es.cls Event.isAcqR b := by
  obtain ⟨hrel, w, w', r, hw, hrs, hrf, hr, hb, hacq⟩ := h
  rcases hw with rfl | ⟨hf, hpo⟩
  · rcases hb with rfl | ⟨hpo, hf⟩
    · refine ⟨?_, w', hrs, hrf, ?_⟩
      · rcases hrel with h | h
        · exact h
        · exact (cls_excl es (fun _ h₁ h₂ => not_write_fence h₁ h₂) hrs.1
            (cls_mono es (fun _ h => isFence_of_isRelF h) h)).elim
      · rcases hacq with h | h
        · exact h
        · exact (cls_excl es (fun _ h₁ h₂ => not_read_fence h₁ h₂) hr
            (cls_mono es (fun _ h => isFence_of_isAcqF h) h)).elim
    · exact (hnf _ hpo.2.1 hf).elim
  · exact (hnf _ hpo.1 hf).elim

theorem sameLoc_symm {a b : EventId} (h : x.sameLoc es a b) : x.sameLoc es b a := by
  obtain ⟨ea, eb, la, lb, ha, hb, hla, hlb, heq⟩ := h
  exact ⟨eb, ea, lb, la, hb, ha, hlb, hla, fun f hP hrf => (heq f hP hrf).symm⟩

/-- `sameLoc` is transitive: locations are compared as partial values. -/
theorem sameLoc_trans {a b c : EventId} (hab : x.sameLoc es a b) (hbc : x.sameLoc es b c) :
    x.sameLoc es a c := by
  obtain ⟨ea, eb, la, lb, hea, heb, hla, hlb, h₁⟩ := hab
  obtain ⟨eb', ec, lb', lc, heb', hec, hlb', hlc, h₂⟩ := hbc
  rw [heb] at heb'; cases heb'
  rw [hlb] at hlb'; cases hlb'
  exact ⟨ea, ec, la, lc, hea, hec, hla, hlc, fun f hP hrf => (h₁ f hP hrf).trans (h₂ f hP hrf)⟩

/-- Same-location pairs evaluate to one location under every model of
    `P ∧ φ_rf`. -/
theorem sameLoc_equivUnder {a b : EventId} {ea eb : Event} {la lb : Expr}
    (h : x.sameLoc es a b) (ha : es.ev a = some ea) (hb : es.ev b = some eb)
    (hla : ea.loc = some la) (hlb : eb.loc = some lb) :
    EquivUnder (Pred.and (x.P es) (x.phiRf es)) la lb := by
  obtain ⟨ea', eb', la', lb', ha', hb', hla', hlb', heq⟩ := h
  rw [ha] at ha'; cases ha'
  rw [hb] at hb'; cases hb'
  rw [hla] at hla'; cases hla'
  rw [hlb] at hlb'; cases hlb'
  intro f hf v₁ v₂ h₁ h₂
  have := heq f hf.1 hf.2
  rw [h₁, h₂] at this; exact Option.some.inj this

/-- `rf ⊆ sameLoc`, for an `rf` from writes to reads (`IsExecution.rf_wr`):
    `φ_rf` equates the locations along `rf`. -/
theorem rfLoc (hrfw : ∀ w r, x.rf w r → es.cls Event.isWrite w ∧ es.cls Event.isRead r)
    {w r : EventId} (h : x.rf w r) : x.sameLoc es w r := by
  obtain ⟨⟨ew, hw, hW⟩, ⟨er, hr, hR⟩⟩ := hrfw w r h
  have hlw : ∃ l, ew.loc = some l := by
    obtain ⟨id, kind, label, guards⟩ := ew
    cases kind <;> simp_all [Event.isWrite, Event.loc]
  have hlr : ∃ l, er.loc = some l := by
    obtain ⟨id, kind, label, guards⟩ := er
    cases kind <;> simp_all [Event.isRead, Event.loc]
  obtain ⟨lw, hlw⟩ := hlw
  obtain ⟨lr, hlr⟩ := hlr
  exact ⟨ew, er, lw, lr, hw, hr, hlw, hlr, fun f _ hrf => (hrf.1 w r ew er h hw hr).1 lw lr hlw hlr⟩

/-- `rf ⊆ sameLoc` in an execution. -/
theorem rfLoc_of_isExecution {Ω : Pred} (hx : x.IsExecution es Ω) :
    ∀ w r, x.rf w r → x.sameLoc es w r :=
  fun _ _ h => x.rfLoc es (fun w r h => ⟨(hx.rf_wr w r h).1, (hx.rf_wr w r h).2.1⟩) h

/-- `ECO` relates only events at one location, given that the same-location
    relation is transitive and contains `rf` and `CO`. -/
theorem eco_loc {co : Rel}
    (htrans : ∀ a b c, x.sameLoc es a b → x.sameLoc es b c → x.sameLoc es a c)
    (hrf : ∀ a b, x.rf a b → x.sameLoc es a b) (hco : ∀ a b, co a b → x.sameLoc es a b)
    {a b : EventId} (h : x.eco co a b) : x.sameLoc es b a := by
  have step := x.eco1_loc (fun _ _ h => x.sameLoc_symm es h) htrans hrf hco
  induction h with
  | single h => exact step _ _ h
  | tail _ h ih => exact htrans _ _ _ (step _ _ h) ih

/-! ## Preserved coherence implies RC11 coherence -/

section Forward

variable {es x}

/-- Under the release-sequence conditions, RC11's `SW` lies in `HB_p`. -/
theorem sw_hbP (hnf : x.FenceFree es)
    (hpoloc : ∀ a b, x.poloc es a b → x.dep es a b)
    (hacq : ∀ r b, es.cls Event.isAcqR r → x.poX es r b → x.dep es r b)
    (hRSpo : ∀ w w', es.cls Event.isRelW w → x.poloc es w w' →
      es.cls Event.isWrite w' → es.cls Event.isRelW w')
    (hRSrmw : ∀ w r w', es.cls Event.isRelW w → x.rf w r → x.rmwRel es r w' →
      es.cls Event.isAcqR r ∧ es.cls Event.isRelW w')
    (hrmw : ∀ r w, x.rmwRel es r w → x.poX es r w)
    {w r : EventId} (h : x.sw es w r) : x.hbP es w r := by
  obtain ⟨hrel, w'', ⟨-, w₀, h₀, hw₀, hseq⟩, hrf, hacqr⟩ := x.sw_shape es hnf h
  -- every write of the release sequence is releasing and `HB_p`-after `w`
  have base : es.cls Event.isRelW w₀ ∧ (w = w₀ ∨ x.hbP es w w₀) := by
    rcases h₀ with rfl | hpl
    · exact ⟨hrel, .inl rfl⟩
    · exact ⟨hRSpo _ _ hrel hpl hw₀, .inr (.single (.inl (hpoloc _ _ hpl)))⟩
  have extend : ∀ a b, es.cls Event.isRelW a → (w = a ∨ x.hbP es w a) →
      x.rfRmw es a b → es.cls Event.isRelW b ∧ (w = b ∨ x.hbP es w b) := by
    rintro a b hrela hwa ⟨r', hrf', hrmw'⟩
    obtain ⟨hacq', hrel'⟩ := hRSrmw _ _ _ hrela hrf' hrmw'
    have hsw : x.hbP es a r' := .single (.inr ⟨hrf', hrela, hacq'⟩)
    have hdep : x.hbP es r' b := .single (.inl (hacq _ _ hacq' (hrmw _ _ hrmw')))
    have hseg := transGen_trans hsw hdep
    refine ⟨hrel', .inr ?_⟩
    rcases hwa with rfl | hwa
    · exact hseg
    · exact transGen_trans hwa hseg
  have key : ∀ w', Rel.plus (x.rfRmw es) w₀ w' →
      es.cls Event.isRelW w' ∧ (w = w' ∨ x.hbP es w w') := by
    intro w' hw'
    induction hw' with
    | single hs => exact extend _ _ base.1 base.2 hs
    | tail _ hs ih => exact extend _ _ ih.1 ih.2 hs
  have key' : es.cls Event.isRelW w'' ∧ (w = w'' ∨ x.hbP es w w'') := by
    rcases hseq with rfl | hseq
    · exact base
    · exact key _ hseq
  obtain ⟨hrel'', hw''⟩ := key'
  have hsw : x.hbP es w'' r := .single (.inr ⟨hrf, hrel'', hacqr⟩)
  rcases hw'' with rfl | hw''
  · exact hsw
  · exact transGen_trans hw'' hsw

theorem sw_acq (hnf : x.FenceFree es) {w r : EventId} (h : x.sw es w r) : es.cls Event.isAcqR r := by
  obtain ⟨-, -, -, -, hacq⟩ := x.sw_shape es hnf h
  exact hacq

/-- An RC11 `HB` path is an `HB_p` path or a single `⊑` edge. -/
theorem hb_cases (hnf : x.FenceFree es)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hpoloc : ∀ a b, x.poloc es a b → x.dep es a b)
    (hrel : ∀ a w, x.poX es a w → es.cls Event.isRelW w → x.dep es a w)
    (hacq : ∀ r b, es.cls Event.isAcqR r → x.poX es r b → x.dep es r b)
    (hRSpo : ∀ w w', es.cls Event.isRelW w → x.poloc es w w' →
      es.cls Event.isWrite w' → es.cls Event.isRelW w')
    (hRSrmw : ∀ w r w', es.cls Event.isRelW w → x.rf w r → x.rmwRel es r w' →
      es.cls Event.isAcqR r ∧ es.cls Event.isRelW w')
    (hrmw : ∀ r w, x.rmwRel es r w → x.poX es r w)
    {a b : EventId} (h : x.hb es a b) : x.hbP es a b ∨ x.poX es a b := by
  have hsw := @sw_hbP es x hnf hpoloc hacq hRSpo hRSrmw hrmw
  have potr : ∀ a b c, x.poX es a b → x.poX es b c → x.poX es a c :=
    fun _ _ _ ⟨ha, _, h₁⟩ ⟨_, hc, h₂⟩ => ⟨ha, hc, hpo_trans _ _ _ h₁ h₂⟩
  -- the invariant: a single `⊑` edge, or an `HB_p` path to an acquiring read
  -- that is `b` or `⊑`-before it
  have inv : x.poX es a b ∨ ∃ r, x.hbP es a r ∧ es.cls Event.isAcqR r ∧
      (r = b ∨ x.poX es r b) := by
    induction h with
    | single h =>
      rcases h with hp | hs
      · exact .inl hp
      · exact .inr ⟨_, hsw hs, (sw_acq hnf hs), .inl rfl⟩
    | tail _ h ih =>
      rcases h with hp | hs
      · rcases ih with hpo | ⟨r, hr, hacqr, rfl | hpo⟩
        · exact .inl (potr _ _ _ hpo hp)
        · exact .inr ⟨r, hr, hacqr, .inr hp⟩
        · exact .inr ⟨r, hr, hacqr, .inr (potr _ _ _ hpo hp)⟩
      · have hc := hsw hs
        refine .inr ⟨_, ?_, (sw_acq hnf hs), .inl rfl⟩
        rcases ih with hpo | ⟨r, hr, hacqr, rfl | hpo⟩
        · exact transGen_trans (.single (.inl (hrel _ _ hpo (x.sw_shape es hnf hs).1))) hc
        · exact transGen_trans hr hc
        · exact transGen_trans (transGen_trans hr (.single (.inl (hacq _ _ hacqr hpo)))) hc
  rcases inv with hpo | ⟨r, hr, hacqr, rfl | hpo⟩
  · exact .inr hpo
  · exact .inl hr
  · exact .inl (transGen_trans hr (.single (.inl (hacq _ _ hacqr hpo))))

/-- Preserved coherence implies RC11's coherence axiom, under the
    `po|loc`, release, acquire and release-sequence conditions. -/
theorem coherence_of_coherenceP {co : Rel} (hnf : x.FenceFree es)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hpo_irrefl : ∀ a, ¬ es.poR a a)
    (hLtrans : ∀ a b c, x.sameLoc es a b → x.sameLoc es b c → x.sameLoc es a c)
    (hrfL : ∀ a b, x.rf a b → x.sameLoc es a b)
    (hcoL : ∀ a b, co a b → x.sameLoc es a b)
    (hpoloc : ∀ a b, x.poloc es a b → x.dep es a b)
    (hrel : ∀ a w, x.poX es a w → es.cls Event.isRelW w → x.dep es a w)
    (hacq : ∀ r b, es.cls Event.isAcqR r → x.poX es r b → x.dep es r b)
    (hRSpo : ∀ w w', es.cls Event.isRelW w → x.poloc es w w' →
      es.cls Event.isWrite w' → es.cls Event.isRelW w')
    (hRSrmw : ∀ w r w', es.cls Event.isRelW w → x.rf w r → x.rmwRel es r w' →
      es.cls Event.isAcqR r ∧ es.cls Event.isRelW w')
    (hrmw : ∀ r w, x.rmwRel es r w → x.poX es r w)
    (h : x.CoherenceP es co) : x.Coherence es co := by
  rintro a ⟨b, hab, hba⟩
  rcases hb_cases hnf hpo_trans hpoloc hrel hacq hRSpo hRSrmw hrmw hab with hp | hpo
  · exact h a ⟨b, hp, hba⟩
  · rcases hba with rfl | heco
    · exact hpo_irrefl _ hpo.2.2
    · have hl := x.eco_loc es hLtrans hrfL hcoL heco
      exact h a ⟨b, .single (.inl (hpoloc _ _ ⟨hpo, hl⟩)), .inr heco⟩

end Forward

/-! ## RC11 coherence implies preserved coherence -/

/-- `SW_ra ⊆ SW`: a releasing write heads its own release sequence. -/
theorem swRA_sw {w r : EventId} (h : x.swRA es w r) : x.sw es w r := by
  obtain ⟨hrf, hrel, hacq⟩ := h
  have hW := cls_mono es (fun _ h => isWrite_of_isRelW h) hrel
  exact ⟨.inl hrel, w, w, r, .inl rfl, ⟨hW, w, .inl rfl, hW, .inl rfl⟩, hrf,
    cls_mono es (fun _ h => isRead_of_isAcqR h) hacq, .inl rfl, .inl hacq⟩

/-- RC11's coherence axiom implies preserved coherence when `DP ∪ ≼ ⊆ ⊑`. -/
theorem coherenceP_of_coherence {co : Rel}
    (hdep : ∀ a b, x.dep es a b → x.poX es a b)
    (h : x.Coherence es co) : x.CoherenceP es co := by
  rintro a ⟨b, hab, hba⟩
  refine h a ⟨b, transGen_mono (fun _ _ h => ?_) hab, hba⟩
  rcases h with hd | hs
  · exact .inl (hdep _ _ hd)
  · exact .inr (x.swRA_sw es hs)

/-- Preserved coherence and RC11's coherence axiom coincide under the
    conditions of both directions. -/
theorem coherenceP_iff_coherence {co : Rel} (hnf : x.FenceFree es)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hpo_irrefl : ∀ a, ¬ es.poR a a)
    (hLtrans : ∀ a b c, x.sameLoc es a b → x.sameLoc es b c → x.sameLoc es a c)
    (hrfL : ∀ a b, x.rf a b → x.sameLoc es a b)
    (hcoL : ∀ a b, co a b → x.sameLoc es a b)
    (hpoloc : ∀ a b, x.poloc es a b → x.dep es a b)
    (hrel : ∀ a w, x.poX es a w → es.cls Event.isRelW w → x.dep es a w)
    (hacq : ∀ r b, es.cls Event.isAcqR r → x.poX es r b → x.dep es r b)
    (hRSpo : ∀ w w', es.cls Event.isRelW w → x.poloc es w w' →
      es.cls Event.isWrite w' → es.cls Event.isRelW w')
    (hRSrmw : ∀ w r w', es.cls Event.isRelW w → x.rf w r → x.rmwRel es r w' →
      es.cls Event.isAcqR r ∧ es.cls Event.isRelW w')
    (hrmw : ∀ r w, x.rmwRel es r w → x.poX es r w)
    (hdep : ∀ a b, x.dep es a b → x.poX es a b) :
    x.CoherenceP es co ↔ x.Coherence es co :=
  ⟨coherence_of_coherenceP hnf hpo_trans hpo_irrefl hLtrans hrfL hcoL hpoloc hrel hacq
      hRSpo hRSrmw hrmw,
   x.coherenceP_of_coherence es hdep⟩

/-! ## The viewfront happens-before over RC11's `SW`

The operational semantics realises release sequences in its viewfronts, so its
happens-before is `HB_v ≜ (DP ∪ ≼ ∪ SW)⁺` with RC11's `SW`. The
release-sequence conditions are then not needed. -/

/-- `HB_v ≜ (DP ∪ ≼ ∪ SW)⁺`, with RC11's `SW`. -/
def hbV : Rel := Rel.plus ((x.dep es).union (x.sw es))

/-- `HB_v ; ECO?` is irreflexive. -/
def CoherenceV (co : Rel) : Prop :=
  ∀ a, ¬ ∃ b, x.hbV es a b ∧ (b = a ∨ x.eco co b a)

/-! ## Fences: `≼` through `X_F`

RC11's `SW` reaches fences: a release fence heads it, an acquire fence ends
it (`sw`). `HB_v` cannot follow such an edge. Its dependency part `DP ∪ ≼`
lies in `X × X` (`Execution.ppo` restricts MoRDor's closure to `X`), so no
edge of `HB_v` enters a release fence or leaves an acquire fence, and an `SW`
edge at a fence is a dead end. Nor does `≼` cross a fence that only releases
or only acquires: MoRDor's `ppo_sync` relates every event to a later releasing
fence and an acquiring fence to every later event, but has no summand across
a fence, and the closure crosses only a fence that does both (`acq_rel`,
`sc`; `Smrd.PpoMordor`). So for message passing through fences,

    x := 0; y := 0; (x := 1; fence(rel); y :=_rlx 1 ∥ r1 :=_rlx y; fence(acq); r2 :=_rlx x)

with `r1 = 1` and `r2 = 0`, `HB_v`-coherence holds and RC11's coherence
fails (`Smrd.FenceMP`): `coherence_of_coherenceV` needs `FenceFree`.

`≼_F` (`ppoF`) is MoRDor's closure itself, before the restriction to `X`:
`(ppo_step)⁺` over `X ∪ X_F`, as `Execution.ppo` computes it. It keeps the
pairs into a releasing fence and out of an acquiring one, so the path
`x := 1 ≼_F fence(rel) SW fence(acq) ≼_F r2` is in `HB_F ≜ (DP ∪ ≼_F ∪ SW)⁺`
(`hbF`). `HB_F`-coherence (`CoherenceF`) agrees with RC11's coherence axiom
with fences (`coherenceF_iff_coherence`), under the conditions of
`coherenceV_iff_coherence` with condition (ii) extended to fences,
`⊑;[W_rel ∪ F_rel] ⊆ DP ∪ ≼_F` and `[R_acq ∪ F_acq];⊑ ⊆ DP ∪ ≼_F`, which
MoRDor's `≼_F` supplies between events that are not elided
(`Smrd.PpoTail.rel_depF_ne`, `acq_depF_ne`). Without fences `≼_F = ≼` and
`HB_F = HB_v` (`coherenceF_iff_coherenceV`), and the theorems over `HB_v`
above are the fence-free corollaries. -/

/-- `≼_F`: MoRDor's frozen closure over `X ∪ X_F`, before its restriction to
    `X` (`Execution.ppo`). -/
def ppoF : Rel := Relation.TransGen (x.ppoStep es)

/-- `DP ∪ ≼_F` -/
def depF : Rel := (x.ppoF es).union (x.DP)

/-- `HB_F ≜ (DP ∪ ≼_F ∪ SW)⁺`, with RC11's `SW`. -/
def hbF : Rel := Rel.plus ((x.depF es).union (x.sw es))

/-- `HB_F ; ECO?` is irreflexive. -/
def CoherenceF (co : Rel) : Prop :=
  ∀ a, ¬ ∃ b, x.hbF es a b ∧ (b = a ∨ x.eco co b a)

section Fences

variable {es x}

theorem ppoF_of_ppo {a b : EventId} (h : x.ppo es a b) : x.ppoF es a b := h.2.2

theorem depF_of_dep {a b : EventId} (h : x.dep es a b) : x.depF es a b := by
  rcases h with h | h
  · exact .inl (ppoF_of_ppo h)
  · exact .inr h

theorem ppoF_XwF {a b : EventId} (h : x.ppoF es a b) : x.XwF es a ∧ x.XwF es b := by
  induction h with
  | single h => exact ⟨h.1, h.2.1⟩
  | tail _ h ih => exact ⟨ih.1, h.2.1⟩

/-- Without fences `DP ∪ ≼_F` is `DP ∪ ≼`. -/
theorem dep_of_depF (hnf : x.FenceFree es) {a b : EventId} (h : x.depF es a b) :
    x.dep es a b := by
  have hX : ∀ c, x.XwF es c → x.X c := fun c hc => by
    rcases hc with hc | hc
    · exact hc
    · exact absurd hc.2.1 (hnf c (.inr hc))
  rcases h with h | h
  · exact .inl ⟨hX _ (ppoF_XwF h).1, hX _ (ppoF_XwF h).2, h⟩
  · exact .inr h

theorem hbF_of_hbV {a b : EventId} (h : x.hbV es a b) : x.hbF es a b :=
  transGen_mono (fun _ _ h => by
    rcases h with h | h
    · exact .inl (depF_of_dep h)
    · exact .inr h) h

theorem hbV_of_hbF (hnf : x.FenceFree es) {a b : EventId} (h : x.hbF es a b) : x.hbV es a b :=
  transGen_mono (fun _ _ h => by
    rcases h with h | h
    · exact .inl (dep_of_depF hnf h)
    · exact .inr h) h

/-- **Without fences `HB_F`-coherence is `HB_v`-coherence.** -/
theorem coherenceF_iff_coherenceV {co : Rel} (hnf : x.FenceFree es) :
    x.CoherenceF es co ↔ x.CoherenceV es co :=
  ⟨fun h a ⟨b, hab, hba⟩ => h a ⟨b, hbF_of_hbV hab, hba⟩,
   fun h a ⟨b, hab, hba⟩ => h a ⟨b, hbV_of_hbF hnf hab, hba⟩⟩

/-- `HB_v`-coherence follows from `HB_F`-coherence, with fences or without. -/
theorem coherenceV_of_coherenceF {co : Rel} (h : x.CoherenceF es co) : x.CoherenceV es co :=
  fun a ⟨b, hab, hba⟩ => h a ⟨b, hbF_of_hbV hab, hba⟩

/-- **An RC11 `HB` path is an `HB_F` path or a single `⊑` edge**, with fences:
    `SW` leaves a releasing write or fence and enters an acquiring read or
    fence, and condition (ii), extended to fences, enters and leaves them by
    `DP ∪ ≼_F`. -/
theorem hb_cases_F
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hrel : ∀ a w, x.poX es a w → (es.cls Event.isRelW w ∨ es.cls Event.isRelF w) →
      x.depF es a w)
    (hacq : ∀ r b, (es.cls Event.isAcqR r ∨ es.cls Event.isAcqF r) → x.poX es r b →
      x.depF es r b)
    {a b : EventId} (h : x.hb es a b) : x.hbF es a b ∨ x.poX es a b := by
  have potr : ∀ a b c, x.poX es a b → x.poX es b c → x.poX es a c :=
    fun _ _ _ ⟨ha, _, h₁⟩ ⟨_, hc, h₂⟩ => ⟨ha, hc, hpo_trans _ _ _ h₁ h₂⟩
  have src : ∀ {c d}, x.sw es c d → es.cls Event.isRelW c ∨ es.cls Event.isRelF c :=
    fun h => h.1
  have tgt : ∀ {c d}, x.sw es c d → es.cls Event.isAcqR d ∨ es.cls Event.isAcqF d := by
    intro c d h
    obtain ⟨-, -, -, -, -, -, -, -, -, h⟩ := h
    exact h
  have inv : x.poX es a b ∨ ∃ r, x.hbF es a r ∧
      (es.cls Event.isAcqR r ∨ es.cls Event.isAcqF r) ∧ (r = b ∨ x.poX es r b) := by
    induction h with
    | single h =>
      rcases h with hp | hs
      · exact .inl hp
      · exact .inr ⟨_, .single (.inr hs), tgt hs, .inl rfl⟩
    | tail _ h ih =>
      rcases h with hp | hs
      · rcases ih with hpo | ⟨r, hr, hacqr, rfl | hpo⟩
        · exact .inl (potr _ _ _ hpo hp)
        · exact .inr ⟨r, hr, hacqr, .inr hp⟩
        · exact .inr ⟨r, hr, hacqr, .inr (potr _ _ _ hpo hp)⟩
      · have hc : x.hbF es _ _ := .single (.inr hs)
        refine .inr ⟨_, ?_, tgt hs, .inl rfl⟩
        rcases ih with hpo | ⟨r, hr, hacqr, rfl | hpo⟩
        · exact transGen_trans (.single (.inl (hrel _ _ hpo (src hs)))) hc
        · exact transGen_trans hr hc
        · exact transGen_trans (transGen_trans hr (.single (.inl (hacq _ _ hacqr hpo)))) hc
  rcases inv with hpo | ⟨r, hr, hacqr, rfl | hpo⟩
  · exact .inr hpo
  · exact .inl hr
  · exact .inl (transGen_trans hr (.single (.inl (hacq _ _ hacqr hpo))))

/-- **`HB_F`-coherence implies RC11's coherence axiom, with fences**, under the
    `po|loc` condition and condition (ii) extended to fences. -/
theorem coherence_of_coherenceF {co : Rel}
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hpo_irrefl : ∀ a, ¬ es.poR a a)
    (hLtrans : ∀ a b c, x.sameLoc es a b → x.sameLoc es b c → x.sameLoc es a c)
    (hrfL : ∀ a b, x.rf a b → x.sameLoc es a b)
    (hcoL : ∀ a b, co a b → x.sameLoc es a b)
    (hpoloc : ∀ a b, x.poloc es a b → x.depF es a b)
    (hrel : ∀ a w, x.poX es a w → (es.cls Event.isRelW w ∨ es.cls Event.isRelF w) →
      x.depF es a w)
    (hacq : ∀ r b, (es.cls Event.isAcqR r ∨ es.cls Event.isAcqF r) → x.poX es r b →
      x.depF es r b)
    (h : x.CoherenceF es co) : x.Coherence es co := by
  rintro a ⟨b, hab, hba⟩
  rcases hb_cases_F hpo_trans hrel hacq hab with hp | hpo
  · exact h a ⟨b, hp, hba⟩
  · rcases hba with rfl | heco
    · exact hpo_irrefl _ hpo.2.2
    · have hl := x.eco_loc es hLtrans hrfL hcoL heco
      exact h a ⟨b, .single (.inl (hpoloc _ _ ⟨hpo, hl⟩)), .inr heco⟩

end Fences

/-- RC11's coherence axiom implies `HB_F`-coherence when `DP ∪ ≼_F ⊆ ⊑`. -/
theorem coherenceF_of_coherence {co : Rel}
    (hdep : ∀ a b, x.depF es a b → x.poX es a b)
    (h : x.Coherence es co) : x.CoherenceF es co := by
  rintro a ⟨b, hab, hba⟩
  refine h a ⟨b, transGen_mono (fun _ _ h => ?_) hab, hba⟩
  rcases h with hd | hs
  · exact .inl (hdep _ _ hd)
  · exact .inr hs

/-- **`HB_F`-coherence and RC11's coherence axiom coincide, with fences**,
    under the conditions of both directions. -/
theorem coherenceF_iff_coherence {co : Rel}
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hpo_irrefl : ∀ a, ¬ es.poR a a)
    (hLtrans : ∀ a b c, x.sameLoc es a b → x.sameLoc es b c → x.sameLoc es a c)
    (hrfL : ∀ a b, x.rf a b → x.sameLoc es a b)
    (hcoL : ∀ a b, co a b → x.sameLoc es a b)
    (hpoloc : ∀ a b, x.poloc es a b → x.depF es a b)
    (hrel : ∀ a w, x.poX es a w → (es.cls Event.isRelW w ∨ es.cls Event.isRelF w) →
      x.depF es a w)
    (hacq : ∀ r b, (es.cls Event.isAcqR r ∨ es.cls Event.isAcqF r) → x.poX es r b →
      x.depF es r b)
    (hdep : ∀ a b, x.depF es a b → x.poX es a b) :
    x.CoherenceF es co ↔ x.Coherence es co :=
  ⟨coherence_of_coherenceF hpo_trans hpo_irrefl hLtrans hrfL hcoL hpoloc hrel hacq,
   x.coherenceF_of_coherence es hdep⟩

section ForwardV

variable {es x}

/-- An RC11 `HB` path is an `HB_v` path or a single `⊑` edge. -/
theorem hb_cases_v (hnf : x.FenceFree es)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hrel : ∀ a w, x.poX es a w → es.cls Event.isRelW w → x.dep es a w)
    (hacq : ∀ r b, es.cls Event.isAcqR r → x.poX es r b → x.dep es r b)
    {a b : EventId} (h : x.hb es a b) : x.hbV es a b ∨ x.poX es a b := by
  have potr : ∀ a b c, x.poX es a b → x.poX es b c → x.poX es a c :=
    fun _ _ _ ⟨ha, _, h₁⟩ ⟨_, hc, h₂⟩ => ⟨ha, hc, hpo_trans _ _ _ h₁ h₂⟩
  have inv : x.poX es a b ∨ ∃ r, x.hbV es a r ∧ es.cls Event.isAcqR r ∧
      (r = b ∨ x.poX es r b) := by
    induction h with
    | single h =>
      rcases h with hp | hs
      · exact .inl hp
      · exact .inr ⟨_, .single (.inr hs), sw_acq hnf hs, .inl rfl⟩
    | tail _ h ih =>
      rcases h with hp | hs
      · rcases ih with hpo | ⟨r, hr, hacqr, rfl | hpo⟩
        · exact .inl (potr _ _ _ hpo hp)
        · exact .inr ⟨r, hr, hacqr, .inr hp⟩
        · exact .inr ⟨r, hr, hacqr, .inr (potr _ _ _ hpo hp)⟩
      · have hc : x.hbV es _ _ := .single (.inr hs)
        refine .inr ⟨_, ?_, sw_acq hnf hs, .inl rfl⟩
        rcases ih with hpo | ⟨r, hr, hacqr, rfl | hpo⟩
        · exact transGen_trans (.single (.inl (hrel _ _ hpo (x.sw_shape es hnf hs).1))) hc
        · exact transGen_trans hr hc
        · exact transGen_trans (transGen_trans hr (.single (.inl (hacq _ _ hacqr hpo)))) hc
  rcases inv with hpo | ⟨r, hr, hacqr, rfl | hpo⟩
  · exact .inr hpo
  · exact .inl hr
  · exact .inl (transGen_trans hr (.single (.inl (hacq _ _ hacqr hpo))))

/-- `HB_v`-coherence implies RC11's coherence axiom, under the `po|loc`,
    release and acquire conditions: the fence-free corollary of
    `coherence_of_coherenceF`. -/
theorem coherence_of_coherenceV {co : Rel} (hnf : x.FenceFree es)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hpo_irrefl : ∀ a, ¬ es.poR a a)
    (hLtrans : ∀ a b c, x.sameLoc es a b → x.sameLoc es b c → x.sameLoc es a c)
    (hrfL : ∀ a b, x.rf a b → x.sameLoc es a b)
    (hcoL : ∀ a b, co a b → x.sameLoc es a b)
    (hpoloc : ∀ a b, x.poloc es a b → x.dep es a b)
    (hrel : ∀ a w, x.poX es a w → es.cls Event.isRelW w → x.dep es a w)
    (hacq : ∀ r b, es.cls Event.isAcqR r → x.poX es r b → x.dep es r b)
    (h : x.CoherenceV es co) : x.Coherence es co :=
  coherence_of_coherenceF hpo_trans hpo_irrefl hLtrans hrfL hcoL
    (fun a b h => depF_of_dep (hpoloc a b h))
    (fun a w h hw => hw.elim (fun hw => depF_of_dep (hrel a w h hw))
      (fun hf => absurd (cls_mono es (fun _ h => isFence_of_isRelF h) hf) (hnf w h.2.1)))
    (fun r b hr h => hr.elim (fun hr => depF_of_dep (hacq r b hr h))
      (fun hf => absurd (cls_mono es (fun _ h => isFence_of_isAcqF h) hf) (hnf r h.1)))
    ((coherenceF_iff_coherenceV hnf).2 h)

end ForwardV

/-- RC11's coherence axiom implies `HB_v`-coherence when `DP ∪ ≼ ⊆ ⊑`. -/
theorem coherenceV_of_coherence {co : Rel}
    (hdep : ∀ a b, x.dep es a b → x.poX es a b)
    (h : x.Coherence es co) : x.CoherenceV es co := by
  rintro a ⟨b, hab, hba⟩
  refine h a ⟨b, transGen_mono (fun _ _ h => ?_) hab, hba⟩
  rcases h with hd | hs
  · exact .inl (hdep _ _ hd)
  · exact .inr hs

/-- `HB_v`-coherence and RC11's coherence axiom coincide under the conditions
    of both directions. -/
theorem coherenceV_iff_coherence {co : Rel} (hnf : x.FenceFree es)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hpo_irrefl : ∀ a, ¬ es.poR a a)
    (hLtrans : ∀ a b c, x.sameLoc es a b → x.sameLoc es b c → x.sameLoc es a c)
    (hrfL : ∀ a b, x.rf a b → x.sameLoc es a b)
    (hcoL : ∀ a b, co a b → x.sameLoc es a b)
    (hpoloc : ∀ a b, x.poloc es a b → x.dep es a b)
    (hrel : ∀ a w, x.poX es a w → es.cls Event.isRelW w → x.dep es a w)
    (hacq : ∀ r b, es.cls Event.isAcqR r → x.poX es r b → x.dep es r b)
    (hdep : ∀ a b, x.dep es a b → x.poX es a b) :
    x.CoherenceV es co ↔ x.Coherence es co :=
  ⟨coherence_of_coherenceV hnf hpo_trans hpo_irrefl hLtrans hrfL hcoL hpoloc hrel hacq,
   x.coherenceV_of_coherence es hdep⟩


end Execution
