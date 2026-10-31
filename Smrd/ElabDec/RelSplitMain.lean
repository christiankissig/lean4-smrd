import Smrd.ElabDec.Deciders

/-!
# `fwdRel` and `weRel` split for this library's restrictions

The decision procedure (`Smrd.ElabDec.Saturate`) takes the conditions of
Forwarding and Write Elision that do not depend on the justification as a
`RelSplit`. This module supplies it for the restrictions of
`Smrd.Justifications` (the acquire restriction on Forwarding, the release
restriction on Write Elision, no RMW access elided). It is the only module of
`Smrd.ElabDec` that unfolds `fwdRel` and `weRel`; a further restriction on
the two events (such as a join restriction) is added here.
-/

namespace EventStructure

variable (es : EventStructure)

/-- `fwdNoAcq` with the intermediate events bounded. -/
def noAcqP (e₁ e₂ : EventId) : Prop :=
  (es.cls Event.isAcqR e₂ → es.cls Event.isAcqR e₁) ∧
    (es.cls Event.isScR e₂ → es.cls Event.isScR e₁) ∧
    ∀ c ∈ es.po.map Prod.snd, es.poR e₁ c → es.poR c e₂ →
      ¬ es.cls Event.acquires c ∧ (es.cls Event.isSc e₂ → ¬ es.cls Event.isSc c)

/-- `weNoRel` with the intermediate events bounded. -/
def noRelP (e₁ e₂ : EventId) : Prop :=
  (es.cls Event.isRelW e₁ → es.cls Event.isRelW e₂) ∧
    ∀ c ∈ es.po.map Prod.snd, es.poR e₁ c → es.poR c e₂ → ¬ es.cls Event.publishes c

instance (e₁ e₂ : EventId) : Decidable (es.noAcqP e₁ e₂) := by unfold noAcqP; infer_instance
instance (e₁ e₂ : EventId) : Decidable (es.noRelP e₁ e₂) := by unfold noRelP; infer_instance

variable {es}

theorem mem_snd_of_poR {a c : EventId} (h : es.poR a c) : c ∈ es.po.map Prod.snd :=
  List.mem_map.2 ⟨(a, c), h, rfl⟩

theorem fwdNoAcq_iff {e₁ e₂ : EventId} : es.fwdNoAcq e₁ e₂ ↔ es.noAcqP e₁ e₂ := by
  unfold fwdNoAcq noAcqP
  exact and_congr_right' (and_congr_right' ⟨fun h c _ => h c, fun h c h1 => h c (mem_snd_of_poR h1) h1⟩)

theorem weNoRel_iff {e₁ e₂ : EventId} : es.weNoRel e₁ e₂ ↔ es.noRelP e₁ e₂ := by
  unfold weNoRel noRelP
  exact and_congr_right' ⟨fun h c _ => h c, fun h c h1 => h c (mem_snd_of_poR h1) h1⟩

variable (es)

/-- The split of `fwdRel` and `weRel` for the restrictions of this library. -/
def relSplit : es.RelSplit where
  fwdR a b := decide ((((es.cls Event.isWrite a ∧ es.cls Event.isRlxR b) ∨
      (es.cls Event.isWrite a ∧ es.cls Event.isRlxW b) ∨
      (es.cls Event.isRead a ∧ es.cls Event.isRead b)) ∧ ¬ es.cls Event.isVol b) ∧
    es.noAcqP a b ∧ ¬ es.RMWAcc b)
  weR a b := decide ((es.cls Event.isWrite a ∧ es.cls Event.isWrite b ∧ ¬ es.cls Event.isVol a) ∧
    es.noRelP a b ∧ ¬ es.RMWAcc a)
  fwd_iff j a b := by
    simp only [fwdRel, fwdRelBlind, decide_eq_true_eq, fwdNoAcq_iff]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩; exact ⟨h1, ⟨h2, h3⟩, h4, h5⟩
    · rintro ⟨h1, ⟨h2, h3⟩, h4, h5⟩; exact ⟨⟨h1, h2, h3⟩, h4, h5⟩
  we_iff j a b := by
    simp only [weRel, weRelBlind, decide_eq_true_eq, weNoRel_iff]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩; exact ⟨h1, ⟨h2, h3, h4⟩, h5, h6⟩
    · rintro ⟨h1, ⟨h2, h3, h4⟩, h5, h6⟩; exact ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩

end EventStructure
