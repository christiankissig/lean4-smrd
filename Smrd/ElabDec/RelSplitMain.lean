import Smrd.ElabDec.Deciders

/-!
# `fwdRel` and `weRel` split for this library's restrictions

The decision procedure (`Smrd.ElabDec.Saturate`) takes the conditions of
Forwarding and Write Elision that do not depend on the justification as a
`RelSplit`. This module supplies it for the restrictions of
`Smrd.Justifications` (the acquire and join restrictions on Forwarding, the
release and fork restrictions on Write Elision, no RMW access elided), each
with its quantifiers bounded by the events of `⊑`. It is the only module of
`Smrd.ElabDec` that unfolds `fwdRel` and `weRel`; a further restriction on
the two events is added here.
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

/-- `PoCmp` on the list `po`. -/
def poCmpP (a b : EventId) : Prop := a = b ∨ (a, b) ∈ es.po ∨ (b, a) ∈ es.po

/-- `Joinable` with the upper bound among `a`, `b` and the events of `⊑`. -/
def joinableP (a b : EventId) : Prop :=
  ∃ d ∈ a :: b :: es.po.map Prod.snd, (a = d ∨ (a, d) ∈ es.po) ∧ (b = d ∨ (b, d) ∈ es.po)

/-- `NoJoinMove` with the moved-around event among the events of `⊑`. -/
def noJoinP (u v : EventId) : Prop :=
  ∀ c ∈ es.po.map Prod.fst ++ es.po.map Prod.snd,
    (es.joinableP c u → es.poCmpP c u) → es.joinableP c v → es.poCmpP c v

/-- `Diverged` on the events' guards. -/
def divergedP (a b : EventId) : Prop :=
  match es.ev a, es.ev b with
  | some ea, some eb =>
      ∃ g₁ ∈ ea.guards, ∃ g₂ ∈ eb.guards, g₁.branch = g₂.branch ∧ g₁.cond = g₂.cond ∧ g₁.pos ≠ g₂.pos
  | _, _ => False

/-- `weNoFork` with the later event among the events of `⊑`. -/
def noForkP (e₁ e₂ : EventId) : Prop :=
  ∀ c ∈ es.po.map Prod.snd, (e₁, c) ∈ es.po → c ≠ e₂ →
    (es.divergedP c e₂ → es.joinableP c e₂) → es.poCmpP c e₂

instance (e₁ e₂ : EventId) : Decidable (es.noAcqP e₁ e₂) := by unfold noAcqP; infer_instance
instance (e₁ e₂ : EventId) : Decidable (es.noRelP e₁ e₂) := by unfold noRelP; infer_instance
instance (a b : EventId) : Decidable (es.poCmpP a b) := by unfold poCmpP; infer_instance
instance (a b : EventId) : Decidable (es.joinableP a b) := by unfold joinableP; infer_instance
instance (u v : EventId) : Decidable (es.noJoinP u v) := by unfold noJoinP; infer_instance
instance (a b : EventId) : Decidable (es.divergedP a b) := by
  unfold divergedP; split <;> infer_instance
instance (e₁ e₂ : EventId) : Decidable (es.noForkP e₁ e₂) := by unfold noForkP; infer_instance

variable {es}

theorem mem_snd_of_poR {a c : EventId} (h : es.poR a c) : c ∈ es.po.map Prod.snd :=
  List.mem_map.2 ⟨(a, c), h, rfl⟩

theorem fwdNoAcq_iff {e₁ e₂ : EventId} : es.fwdNoAcq e₁ e₂ ↔ es.noAcqP e₁ e₂ := by
  unfold fwdNoAcq noAcqP
  exact and_congr_right' (and_congr_right' ⟨fun h c _ => h c, fun h c h1 => h c (mem_snd_of_poR h1) h1⟩)

theorem weNoRel_iff {e₁ e₂ : EventId} : es.weNoRel e₁ e₂ ↔ es.noRelP e₁ e₂ := by
  unfold weNoRel noRelP
  exact and_congr_right' ⟨fun h c _ => h c, fun h c h1 => h c (mem_snd_of_poR h1) h1⟩

theorem mem_fst_of_poR {a c : EventId} (h : es.poR a c) : a ∈ es.po.map Prod.fst :=
  List.mem_map.2 ⟨(a, c), h, rfl⟩

theorem joinable_iff {a b : EventId} : es.Joinable a b ↔ es.joinableP a b := by
  constructor
  · rintro ⟨d, ha, hb⟩
    refine ⟨d, ?_, ha, hb⟩
    rcases ha with rfl | ha
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_snd_of_poR ha))
  · rintro ⟨d, -, ha, hb⟩
    exact ⟨d, ha, hb⟩

theorem noJoinMove_iff {u v : EventId} : es.NoJoinMove u v ↔ es.noJoinP u v := by
  constructor
  · intro h c _ hc hj
    exact h c (fun hj' => hc (joinable_iff.1 hj')) (joinable_iff.2 hj)
  · intro h c hc hj
    by_cases hm : c ∈ es.po.map Prod.fst ++ es.po.map Prod.snd
    · exact h c hm (fun hj' => hc (joinable_iff.2 hj')) (joinable_iff.1 hj)
    · obtain ⟨d, hcd, hvd⟩ := hj
      rcases hcd with rfl | hcd
      · rcases hvd with rfl | hvd
        · exact .inl rfl
        · exact absurd (List.mem_append_right _ (mem_snd_of_poR hvd)) hm
      · exact absurd (List.mem_append_left _ (mem_fst_of_poR hcd)) hm

theorem diverged_iff {a b : EventId} : es.Diverged a b ↔ es.divergedP a b := by
  unfold Diverged divergedP
  constructor
  · rintro ⟨ea, eb, ha, hb, h⟩; rw [ha, hb]; exact h
  · intro h
    split at h
    · exact ⟨_, _, ‹_›, ‹_›, h⟩
    · exact h.elim

theorem weNoFork_iff {e₁ e₂ : EventId} : es.weNoFork e₁ e₂ ↔ es.noForkP e₁ e₂ := by
  unfold weNoFork noForkP
  constructor
  · intro h c _ h1 hne hj
    exact h c h1 hne fun hd => joinable_iff.2 (hj (diverged_iff.1 hd))
  · intro h c h1 hne hj
    exact h c (mem_snd_of_poR h1) h1 hne fun hd => joinable_iff.1 (hj (diverged_iff.2 hd))

variable (es)

/-- The split of `fwdRel` and `weRel` for the restrictions of this library. -/
def relSplit : es.RelSplit where
  fwdR a b := decide ((((es.cls Event.isWrite a ∧ es.cls Event.isRlxR b) ∨
      (es.cls Event.isWrite a ∧ es.cls Event.isRlxW b) ∨
      (es.cls Event.isRead a ∧ es.cls Event.isRead b)) ∧ ¬ es.cls Event.isVol b) ∧
    es.noAcqP a b ∧ es.noJoinP b a ∧ ¬ es.RMWAcc b)
  weR a b := decide ((es.cls Event.isWrite a ∧ es.cls Event.isWrite b ∧ ¬ es.cls Event.isVol a) ∧
    es.noRelP a b ∧ es.noForkP a b ∧ ¬ es.RMWAcc a)
  fwd_iff j a b := by
    simp only [fwdRel, fwdRelBlind, decide_eq_true_eq, fwdNoAcq_iff, fwdNoJoin, noJoinMove_iff]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩; exact ⟨h1, ⟨h2, h3⟩, h4, h5, h6⟩
    · rintro ⟨h1, ⟨h2, h3⟩, h4, h5, h6⟩; exact ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
  we_iff j a b := by
    simp only [weRel, weRelBlind, decide_eq_true_eq, weNoRel_iff, weNoFork_iff]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩; exact ⟨h1, ⟨h2, h3, h4⟩, h5, h6, h7⟩
    · rintro ⟨h1, ⟨h2, h3, h4⟩, h5, h6, h7⟩; exact ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩

end EventStructure
