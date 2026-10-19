import Smrd.Executions

/-!
# Preserved coherence and RC11's coherence axiom

`Execution.Coherence` is *preserved coherence* (Paragraph `def:pres-coherence`):
`HB_p ; ECO?` irreflexive with `HB_p ≜ (DP ∪ ≼ ∪ SW_ra)⁺`. RC11's axiom
(Axiom `def:mem-model-axiom:co`) asks the same of `HB ≜ (⊑ ∪ SW)⁺`, with
`SW` closed under release sequences. This module states RC11's axiom over an
execution and reduces the one to the other.

`coherenceRC_of_coherence`: preserved coherence implies RC11 coherence when

* (`po|loc`) program order between accesses at one location is preserved,
  `⊑|loc ⊆ DP ∪ ≼`;
* (release, acquire) program order into a releasing write and out of an
  acquiring read is preserved, `⊑;[W_rel] ⊆ DP ∪ ≼` and `[R_acq];⊑ ⊆ DP ∪ ≼`;
* (release sequences) every write `⊑|loc`-after a releasing write is
  releasing, and every RMW that reads from a releasing write is
  acquire-release, so that release sequences consist of releasing writes; and
  the read of an RMW is `⊑`-before its write.

`coherence_of_coherenceRC`: RC11 coherence implies preserved coherence when
`DP ∪ ≼ ⊆ ⊑`.

Both directions also assume that `⊑` is a strict order and that the
same-location relation is transitive and contains `rf` and `CO`.

The proof composes with `ECO` and probes irreflexivity, as in
`hb_eco1_irrefl_iff_hbLoc`. An `HB` path that contains an `SW` edge lies in
`HB_p` outright, by the release, acquire and release-sequence conditions. A
path made of `⊑` alone is one `⊑` edge, and `ECO` closes it into a cycle only
between events at one location, where `po|loc` applies.

The conditions are where the operational semantics falls short of RC11
(`TODO(rc11-co)` in `app-defs.tex`). `≼_sync` contains `⊑;[W_rel]` and
`[R_acq];⊑`, but `≼` truncates them at the last justified event of a thread
and remaps them under forwarding. Release sequences beyond the releasing write
are not in `SW_ra`. `DP ∪ ≼ ⊆ ⊑` is open under `remap_δ`.

Deviation from the paper: executions hold no fences (`Candidate`), so `SW`
here has no fence clauses. It is RC11's `SW` on fence-free programs.
-/

namespace Execution

variable (es : EventStructure) (x : Execution)

/-- `⊑` within `X`. -/
def poX : Rel := fun a b => x.X a ∧ x.X b ∧ es.poR a b

/-- `⊑|loc ≜ {(e₁, e₂) ∈ ⊑ | loc(e₁) ≡_P loc(e₂)}`, within `X`. -/
def poloc : Rel := fun a b => x.poX es a b ∧ x.sameLoc es a b

/-- `rf ; rmw`: from a write to the write of an RMW that reads from it. -/
def rfRmw : Rel := fun a b => ∃ r, x.rf a r ∧ x.rmwRel es r b

/-- `RS ≜ [W] ; ⊑|loc? ; [W] ; (rf ; rmw)*` -/
def rs : Rel := fun w w' =>
  es.cls Event.isWrite w ∧ ∃ w₀, (w₀ = w ∨ x.poloc es w w₀) ∧
    es.cls Event.isWrite w₀ ∧ (w' = w₀ ∨ Rel.plus (x.rfRmw es) w₀ w')

/-- `SW ≜ [W_rel] ; RS ; rf ; [R_acq]`, RC11's synchronises-with on
    fence-free programs. -/
def swRC : Rel := fun w r =>
  es.cls Event.isRelW w ∧ ∃ w', x.rs es w w' ∧ x.rf w' r ∧ es.cls Event.isAcqR r

/-- `HB ≜ (⊑ ∪ SW)⁺`, RC11's happens-before. -/
def hbRC : Rel := Rel.plus ((x.poX es).union (x.swRC es))

/-- RC11's `Coherence` axiom: `HB ; ECO?` is irreflexive. -/
def CoherenceRC (co : Rel) : Prop :=
  ∀ a, ¬ ∃ b, x.hbRC es a b ∧ (b = a ∨ x.eco co b a)

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

theorem sameLoc_symm {a b : EventId} (h : x.sameLoc es a b) : x.sameLoc es b a := by
  obtain ⟨ea, eb, la, lb, ha, hb, hla, hlb, heq⟩ := h
  exact ⟨eb, ea, lb, la, hb, ha, hlb, hla,
    fun f hf v₁ v₂ h₁ h₂ => (heq f hf v₂ v₁ h₂ h₁).symm⟩

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
theorem swRC_hb
    (hpoloc : ∀ a b, x.poloc es a b → x.dep es a b)
    (hacq : ∀ r b, es.cls Event.isAcqR r → x.poX es r b → x.dep es r b)
    (hRSpo : ∀ w w', es.cls Event.isRelW w → x.poloc es w w' →
      es.cls Event.isWrite w' → es.cls Event.isRelW w')
    (hRSrmw : ∀ w r w', es.cls Event.isRelW w → x.rf w r → x.rmwRel es r w' →
      es.cls Event.isAcqR r ∧ es.cls Event.isRelW w')
    (hrmw : ∀ r w, x.rmwRel es r w → x.poX es r w)
    {w r : EventId} (h : x.swRC es w r) : x.hb es w r := by
  obtain ⟨hrel, w'', ⟨-, w₀, h₀, hw₀, hseq⟩, hrf, hacqr⟩ := h
  -- every write of the release sequence is releasing and `HB_p`-after `w`
  have base : es.cls Event.isRelW w₀ ∧ (w = w₀ ∨ x.hb es w w₀) := by
    rcases h₀ with rfl | hpl
    · exact ⟨hrel, .inl rfl⟩
    · exact ⟨hRSpo _ _ hrel hpl hw₀, .inr (.single (.inl (hpoloc _ _ hpl)))⟩
  have extend : ∀ a b, es.cls Event.isRelW a → (w = a ∨ x.hb es w a) →
      x.rfRmw es a b → es.cls Event.isRelW b ∧ (w = b ∨ x.hb es w b) := by
    rintro a b hrela hwa ⟨r', hrf', hrmw'⟩
    obtain ⟨hacq', hrel'⟩ := hRSrmw _ _ _ hrela hrf' hrmw'
    have hsw : x.hb es a r' := .single (.inr ⟨hrf', hrela, hacq'⟩)
    have hdep : x.hb es r' b := .single (.inl (hacq _ _ hacq' (hrmw _ _ hrmw')))
    have hseg := transGen_trans hsw hdep
    refine ⟨hrel', .inr ?_⟩
    rcases hwa with rfl | hwa
    · exact hseg
    · exact transGen_trans hwa hseg
  have key : ∀ w', Rel.plus (x.rfRmw es) w₀ w' →
      es.cls Event.isRelW w' ∧ (w = w' ∨ x.hb es w w') := by
    intro w' hw'
    induction hw' with
    | single hs => exact extend _ _ base.1 base.2 hs
    | tail _ hs ih => exact extend _ _ ih.1 ih.2 hs
  have key' : es.cls Event.isRelW w'' ∧ (w = w'' ∨ x.hb es w w'') := by
    rcases hseq with rfl | hseq
    · exact base
    · exact key _ hseq
  obtain ⟨hrel'', hw''⟩ := key'
  have hsw : x.hb es w'' r := .single (.inr ⟨hrf, hrel'', hacqr⟩)
  rcases hw'' with rfl | hw''
  · exact hsw
  · exact transGen_trans hw'' hsw

theorem swRC_acq {w r : EventId} (h : x.swRC es w r) : es.cls Event.isAcqR r := by
  obtain ⟨-, -, -, -, hacq⟩ := h
  exact hacq

/-- An RC11 `HB` path is an `HB_p` path or a single `⊑` edge. -/
theorem hbRC_cases
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hpoloc : ∀ a b, x.poloc es a b → x.dep es a b)
    (hrel : ∀ a w, x.poX es a w → es.cls Event.isRelW w → x.dep es a w)
    (hacq : ∀ r b, es.cls Event.isAcqR r → x.poX es r b → x.dep es r b)
    (hRSpo : ∀ w w', es.cls Event.isRelW w → x.poloc es w w' →
      es.cls Event.isWrite w' → es.cls Event.isRelW w')
    (hRSrmw : ∀ w r w', es.cls Event.isRelW w → x.rf w r → x.rmwRel es r w' →
      es.cls Event.isAcqR r ∧ es.cls Event.isRelW w')
    (hrmw : ∀ r w, x.rmwRel es r w → x.poX es r w)
    {a b : EventId} (h : x.hbRC es a b) : x.hb es a b ∨ x.poX es a b := by
  have hsw := @swRC_hb es x hpoloc hacq hRSpo hRSrmw hrmw
  have potr : ∀ a b c, x.poX es a b → x.poX es b c → x.poX es a c :=
    fun _ _ _ ⟨ha, _, h₁⟩ ⟨_, hc, h₂⟩ => ⟨ha, hc, hpo_trans _ _ _ h₁ h₂⟩
  -- the invariant: a single `⊑` edge, or an `HB_p` path to an acquiring read
  -- that is `b` or `⊑`-before it
  have inv : x.poX es a b ∨ ∃ r, x.hb es a r ∧ es.cls Event.isAcqR r ∧
      (r = b ∨ x.poX es r b) := by
    induction h with
    | single h =>
      rcases h with hp | hs
      · exact .inl hp
      · exact .inr ⟨_, hsw hs, (swRC_acq hs), .inl rfl⟩
    | tail _ h ih =>
      rcases h with hp | hs
      · rcases ih with hpo | ⟨r, hr, hacqr, rfl | hpo⟩
        · exact .inl (potr _ _ _ hpo hp)
        · exact .inr ⟨r, hr, hacqr, .inr hp⟩
        · exact .inr ⟨r, hr, hacqr, .inr (potr _ _ _ hpo hp)⟩
      · have hc := hsw hs
        refine .inr ⟨_, ?_, (swRC_acq hs), .inl rfl⟩
        rcases ih with hpo | ⟨r, hr, hacqr, rfl | hpo⟩
        · exact transGen_trans (.single (.inl (hrel _ _ hpo hs.1))) hc
        · exact transGen_trans hr hc
        · exact transGen_trans (transGen_trans hr (.single (.inl (hacq _ _ hacqr hpo)))) hc
  rcases inv with hpo | ⟨r, hr, hacqr, rfl | hpo⟩
  · exact .inr hpo
  · exact .inl hr
  · exact .inl (transGen_trans hr (.single (.inl (hacq _ _ hacqr hpo))))

/-- Preserved coherence implies RC11's coherence axiom, under the
    `po|loc`, release, acquire and release-sequence conditions. -/
theorem coherenceRC_of_coherence {co : Rel}
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
    (h : x.Coherence es co) : x.CoherenceRC es co := by
  rintro a ⟨b, hab, hba⟩
  rcases hbRC_cases hpo_trans hpoloc hrel hacq hRSpo hRSrmw hrmw hab with hp | hpo
  · exact h a ⟨b, hp, hba⟩
  · rcases hba with rfl | heco
    · exact hpo_irrefl _ hpo.2.2
    · have hl := x.eco_loc es hLtrans hrfL hcoL heco
      exact h a ⟨b, .single (.inl (hpoloc _ _ ⟨hpo, hl⟩)), .inr heco⟩

end Forward

/-! ## RC11 coherence implies preserved coherence -/

/-- `SW_ra ⊆ SW`: a releasing write heads its own release sequence. -/
theorem sw_swRC {w r : EventId} (h : x.sw es w r) : x.swRC es w r := by
  obtain ⟨hrf, ⟨e, he, hrel⟩, hacq⟩ := h
  exact ⟨⟨e, he, hrel⟩, w, ⟨⟨e, he, isWrite_of_isRelW hrel⟩, w, .inl rfl,
    ⟨e, he, isWrite_of_isRelW hrel⟩, .inl rfl⟩, hrf, hacq⟩

/-- RC11's coherence axiom implies preserved coherence when `DP ∪ ≼ ⊆ ⊑`. -/
theorem coherence_of_coherenceRC {co : Rel}
    (hdep : ∀ a b, x.dep es a b → x.poX es a b)
    (h : x.CoherenceRC es co) : x.Coherence es co := by
  rintro a ⟨b, hab, hba⟩
  refine h a ⟨b, transGen_mono (fun _ _ h => ?_) hab, hba⟩
  rcases h with hd | hs
  · exact .inl (hdep _ _ hd)
  · exact .inr (x.sw_swRC es hs)

/-- Preserved coherence and RC11's coherence axiom coincide under the
    conditions of both directions. -/
theorem coherence_iff_coherenceRC {co : Rel}
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
    x.Coherence es co ↔ x.CoherenceRC es co :=
  ⟨coherenceRC_of_coherence hpo_trans hpo_irrefl hLtrans hrfL hcoL hpoloc hrel hacq
      hRSpo hRSrmw hrmw,
   x.coherence_of_coherenceRC es hdep⟩

end Execution
