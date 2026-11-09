import Smrd.RC11
import Smrd.PSCExamples

/-!
# Relaxed coherence as a parallel theory

The sMRD model with RC11's coherence axiom replaced by the relaxed one, over a
happens-before built from the dependency order instead of from `⊑`:

    ConsistentV Ω ≜ IsExecution Ω ∧ φ ∧ NoThinAir ∧
                    ∃ co. CoherenceOrder co ∧ CoherenceV co ∧ Atomicity co ∧ PSC co

with `CoherenceV co` = `HB_v ; ECO?` irreflexive, `HB_v ≜ (DP ∪ ≼ ∪ SW)⁺` and
RC11's `SW` (`Execution.CoherenceV`). It is sMRD's `Consistent` with the one
axiom changed. The variants:

* `ConsistentF`: over `HB_F ≜ (DP ∪ ≼_F ∪ SW)⁺` (`Execution.CoherenceF`), with
  `≼_F` MoRDor's closure over `X ∪ X_F` before its restriction to `X`, the
  form that follows synchronisation through fences;
* `ConsistentVT`, `ConsistentFT`: the coherence order over the transformed
  execution `X ∖ †` (`CoherenceOrderT`) and RC11's SC axiom over it (`PSCT`),
  as in `ConsistentT`.

## The SC axiom

The relaxed model keeps RC11's SC axiom as `Consistent` and `ConsistentT`
state it (`PSC`, `PSCT`: `psc` over `⊑` and RC11's `HB`), so that it differs
from sMRD in the coherence axiom alone. MoRDor's sMRD model instead checks
`psc` over its relaxed happens-before; that variant is `PSCRelaxed`, `psc`
over `sb = DP ∪ ≼_F` and `hb = HB_F` (with `≼` and `HB_v` an `sc` fence has no
`sb`- or `hb`-edge, as with `SW` in `Smrd.FenceMP`). `psc` is monotone in
`sb`, `hb` and `CO` (`pscOf_mono`), so where `DP ∪ ≼_F ⊆ ⊑`, RC11's `PSC`
implies `PSCRelaxed` (`pscRelaxed_of_psc`). Without `sc` events both hold
for every coherence order.

## Relations

* `consistentV_of_consistent`: sMRD-consistent ⇒ `ConsistentV` where
  `DP ∪ ≼ ⊆ ⊑`; `consistent_of_consistentV` the converse for fence-free
  executions under the `po|loc`, release and acquire conditions;
  `consistentV_iff_consistent` both
  (`Execution.coherenceV_iff_coherence`). `consistentF_iff_consistent` is the
  same with fences, without `FenceFree` (`Execution.coherenceF_iff_coherence`).
* `consistentV_of_consistentF` always, `consistentF_iff_consistentV` without
  fences.
* `consistentVT_iff_consistentT` (fence-free) and `consistentFT_iff_consistentT`
  (with fences): over `X ∖ †`, with forwarding and write elision, under
  `NoRevLoc`, `RMWTightR`, `DP ⊆ ⊑`, a location model, and no acquire read
  forwarded (`Execution.coherenceT_iff_coherenceV`, `coherenceT_iff_coherenceF`).
  `consistentVT_iff_consistentV`: without elided events the two coherence
  orders agree.
* `consistentV_of_consistentRC11`: RC11-consistent ⇒ `ConsistentV` where
  `DP ∪ ≼ ⊆ ⊑`.

The equivalences take coherence orders within one location: `CoherenceOrder`
does not ask it, and `coLoc` cuts a coherence order to it, keeping every
axiom (they are antitone in `CO`).

## Where they differ

* **Fences.** `ConsistentV` admits message passing through `fence(rel)` and
  `fence(acq)` with the stale read, which `Consistent` and `ConsistentT` forbid
  (`fenceMP_separates`): an `SW` edge at a fence is a dead end in `HB_v`. The
  F-forms do not have this gap; `consistentF_iff_consistent` holds without
  `FenceFree`.
* **Elided writes.** `ConsistentV` orders the writes of `X`, elided ones
  included, and `HB_v` does not reach an elided write; at a fixed coherence
  order `HB_v`-coherence does not imply RC11's there
  (`PpoNecessity.coww_elided`). The relaxed axiom is matched with sMRD's over
  `X ∖ †` (`ConsistentVT` with `ConsistentT`), not with `Consistent`.
* **Forwarded acquire reads.** `consistentVT_iff_consistentT` asks that no
  acquire read be forwarded: such a read is an `SW`-target in `HB_v` and not in
  `HB_T`, and the equivalence is not proved there.
* **Conditions.** Beyond these, the equivalences hold under their
  hypotheses only (the `po|loc`, release and acquire conditions, and
  `DP ∪ ≼ ⊆ ⊑`), which MoRDor's `≼` discharges where nothing is elided
  (`Smrd.PpoTail`).
-/

namespace Smrd.Relaxed

open Execution

variable (es : EventStructure) (x : Execution)

/-! ## The model -/

/-- The relaxed coherence axiom, RC11's atomicity and RC11's SC axiom under
    one coherence order of `X`. -/
def CoherentV : Prop :=
  ∃ co, x.CoherenceOrder es co ∧ x.CoherenceV es co ∧ x.Atomicity es co ∧ x.PSC es co

/-- **The relaxed-coherence model**: sMRD with coherence over
    `HB_v = (DP ∪ ≼ ∪ SW)⁺`. -/
def ConsistentV (Ω : Pred) : Prop :=
  x.IsExecution es Ω ∧ x.phi es ∧ x.NoThinAir es ∧ CoherentV es x

/-- `CoherentV` over `HB_F = (DP ∪ ≼_F ∪ SW)⁺`, which reaches fences. -/
def CoherentF : Prop :=
  ∃ co, x.CoherenceOrder es co ∧ x.CoherenceF es co ∧ x.Atomicity es co ∧ x.PSC es co

/-- The relaxed-coherence model over `HB_F`. -/
def ConsistentF (Ω : Pred) : Prop :=
  x.IsExecution es Ω ∧ x.phi es ∧ x.NoThinAir es ∧ CoherentF es x

/-- `CoherentV` with the coherence order and the SC axiom over `X ∖ †`. -/
def CoherentVT : Prop :=
  ∃ co, x.CoherenceOrderT es co ∧ x.CoherenceV es co ∧ x.Atomicity es co ∧ x.PSCT es co

/-- The relaxed-coherence model over `HB_v`, coherence order over `X ∖ †`. -/
def ConsistentVT (Ω : Pred) : Prop :=
  x.IsExecution es Ω ∧ x.phi es ∧ x.NoThinAir es ∧ CoherentVT es x

/-- `CoherentF` with the coherence order and the SC axiom over `X ∖ †`. -/
def CoherentFT : Prop :=
  ∃ co, x.CoherenceOrderT es co ∧ x.CoherenceF es co ∧ x.Atomicity es co ∧ x.PSCT es co

/-- The relaxed-coherence model over `HB_F`, coherence order over `X ∖ †`. -/
def ConsistentFT (Ω : Pred) : Prop :=
  x.IsExecution es Ω ∧ x.phi es ∧ x.NoThinAir es ∧ CoherentFT es x

/-- RC11's SC axiom over the relaxed happens-before, as MoRDor's sMRD model
    checks it: `sb = DP ∪ ≼_F`, `hb = HB_F`. Not part of `ConsistentV`. -/
def PSCRelaxed (co : Rel) : Prop := x.PSCOf es (x.XwF es) (x.depF es) (x.hbF es) co

/-! ## Monotonicity in the coherence order -/

/-- A coherence order cut to pairs at one location. -/
def coLoc (co : Rel) : Rel := fun a b => co a b ∧ x.sameLoc es a b

variable {es x}

theorem fr_mono {co co' : Rel} (h : ∀ a b, co a b → co' a b) {a b : EventId}
    (hf : x.fr co a b) : x.fr co' a b := by
  obtain ⟨w, hw, hc⟩ := hf
  exact ⟨w, hw, h _ _ hc⟩

theorem eco_mono {co co' : Rel} (h : ∀ a b, co a b → co' a b) {a b : EventId}
    (he : x.eco co a b) : x.eco co' a b :=
  transGen_mono (fun _ _ s => by
    rcases s with (s | s) | s
    · exact .inl (.inl s)
    · exact .inl (.inr (h _ _ s))
    · exact .inr (fr_mono h s)) he

/-- Coherence-shaped axioms, `H ; ECO?` irreflexive, are antitone in `CO`. -/
theorem irr_eco_anti {H : Rel} {co co' : Rel} (h : ∀ a b, co a b → co' a b)
    (hc : ∀ a, ¬ ∃ b, H a b ∧ (b = a ∨ x.eco co' b a)) :
    ∀ a, ¬ ∃ b, H a b ∧ (b = a ∨ x.eco co b a) :=
  fun a ⟨b, hab, hba⟩ => hc a ⟨b, hab, hba.imp id (eco_mono h)⟩

theorem atomicity_anti {co co' : Rel} (h : ∀ a b, co a b → co' a b)
    (ha : x.Atomicity es co') : x.Atomicity es co :=
  fun r w hrw ⟨w', hf, hc⟩ => ha r w hrw ⟨w', fr_mono h hf, h _ _ hc⟩

/-- **`psc` is monotone in `sb`, `hb` and `CO`**, so the SC axiom is antitone. -/
theorem pscOf_mono {D : EvSet} {sb sb' hb hb' co co' : Rel}
    (hsb : ∀ a b, sb a b → sb' a b) (hhb : ∀ a b, hb a b → hb' a b)
    (hco : ∀ a b, co a b → co' a b) (h : x.PSCOf es D sb' hb' co') : x.PSCOf es D sb hb co := by
  have scb : ∀ a b, x.scbOf es sb hb co a b → x.scbOf es sb' hb' co' a b := by
    rintro a b (h | ⟨c, d, h₁, h₂, h₃, h₄, h₅⟩ | ⟨h₁, h₂⟩ | h | h)
    · exact .inl (hsb _ _ h)
    · exact .inr (.inl ⟨c, d, hsb _ _ h₁, h₂, hhb _ _ h₃, hsb _ _ h₄, h₅⟩)
    · exact .inr (.inr (.inl ⟨hhb _ _ h₁, h₂⟩))
    · exact .inr (.inr (.inr (.inl (hco _ _ h))))
    · exact .inr (.inr (.inr (.inr (fr_mono hco h))))
  have step : ∀ a b, ((x.pscBaseOf es D sb hb co).union (x.pscFOf es D hb co)) a b →
      ((x.pscBaseOf es D sb' hb' co').union (x.pscFOf es D hb' co')) a b := by
    rintro a b (⟨a', b', ha, hs, hb⟩ | ⟨h₁, h₂, h₃, h₄, h₅⟩)
    · refine .inl ⟨a', b', ?_, scb _ _ hs, ?_⟩
      · exact ha.imp id (fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃.imp id (hhb _ _)⟩)
      · exact hb.imp id (fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃.imp id (hhb _ _)⟩)
    · refine .inr ⟨h₁, h₂, h₃, h₄, ?_⟩
      rcases h₅ with h | ⟨c, d, hc, he, hd⟩
      · exact .inl (hhb _ _ h)
      · exact .inr ⟨c, d, hhb _ _ hc, eco_mono hco he, hhb _ _ hd⟩
  exact fun a hc => h a (transGen_mono step hc)

/-- **RC11's SC axiom implies its relaxed form** where `DP ∪ ≼_F ⊆ ⊑`. -/
theorem pscRelaxed_of_psc {co : Rel} (hdepF : ∀ a b, x.depF es a b → x.poX es a b)
    (h : x.PSC es co) : PSCRelaxed es x co :=
  pscOf_mono hdepF
    (fun _ _ hh => transGen_mono (fun _ _ s => s.imp (hdepF _ _) id) hh)
    (fun _ _ h => h) h

theorem coLoc_sub {co : Rel} : ∀ a b, coLoc es x co a b → co a b := fun _ _ h => h.1

theorem coLoc_loc {co : Rel} : ∀ a b, coLoc es x co a b → x.sameLoc es a b := fun _ _ h => h.2

theorem coherenceOrder_coLoc {co : Rel} (h : x.CoherenceOrder es co) :
    x.CoherenceOrder es (coLoc es x co) :=
  ⟨fun a b hab => h.writes a b hab.1, fun a hab => h.irrefl a hab.1,
   fun _ _ _ h₁ h₂ => ⟨h.trans _ _ _ h₁.1 h₂.1, x.sameLoc_trans es h₁.2 h₂.2⟩,
   fun a b ha hb hwa hwb hne hl => (h.total a b ha hb hwa hwb hne hl).imp
     (fun h' => ⟨h', hl⟩) (fun h' => ⟨h', x.sameLoc_symm es hl⟩)⟩

theorem coherenceOrderT_coLoc {co : Rel} (h : x.CoherenceOrderT es co) :
    x.CoherenceOrderT es (coLoc es x co) :=
  ⟨fun a b hab => h.writes a b hab.1, fun a hab => h.irrefl a hab.1,
   fun _ _ _ h₁ h₂ => ⟨h.trans _ _ _ h₁.1 h₂.1, x.sameLoc_trans es h₁.2 h₂.2⟩,
   fun a b ha hb hwa hwb hne hl => (h.total a b ha hb hwa hwb hne hl).imp
     (fun h' => ⟨h', hl⟩) (fun h' => ⟨h', x.sameLoc_symm es hl⟩)⟩

/-! ## Relations to sMRD's `Consistent` -/

/-- Same-location relation transitive, as `coherenceV_iff_coherence` asks. -/
theorem hLtrans : ∀ a b c, x.sameLoc es a b → x.sameLoc es b c → x.sameLoc es a c :=
  fun _ _ _ h₁ h₂ => x.sameLoc_trans es h₁ h₂

/-- **sMRD-consistency implies `ConsistentV`** where `DP ∪ ≼ ⊆ ⊑`. -/
theorem consistentV_of_consistent {Ω : Pred} (hdep : ∀ a b, x.dep es a b → x.poX es a b)
    (h : x.Consistent es Ω) : ConsistentV es x Ω := by
  obtain ⟨hx, hphi, hnta, co, ho, hc, ha, hp⟩ := h
  exact ⟨hx, hphi, hnta, co, ho, x.coherenceV_of_coherence es hdep hc, ha, hp⟩

/-- **`ConsistentV` implies sMRD-consistency** for fence-free executions,
    under the `po|loc`, release and acquire conditions. -/
theorem consistent_of_consistentV {Ω : Pred} (hnf : x.FenceFree es)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hpo_irrefl : ∀ a, ¬ es.poR a a)
    (hpoloc : ∀ a b, x.poloc es a b → x.dep es a b)
    (hrel : ∀ a w, x.poX es a w → es.cls Event.isRelW w → x.dep es a w)
    (hacq : ∀ r b, es.cls Event.isAcqR r → x.poX es r b → x.dep es r b)
    (h : ConsistentV es x Ω) : x.Consistent es Ω := by
  obtain ⟨hx, hphi, hnta, co, ho, hc, ha, hp⟩ := h
  refine ⟨hx, hphi, hnta, coLoc es x co, coherenceOrder_coLoc ho, ?_,
    atomicity_anti coLoc_sub ha, pscOf_mono (fun _ _ h => h) (fun _ _ h => h) coLoc_sub hp⟩
  exact coherence_of_coherenceV hnf hpo_trans hpo_irrefl hLtrans
    (x.rfLoc_of_isExecution es hx) coLoc_loc hpoloc hrel hacq (irr_eco_anti coLoc_sub hc)

/-- **`ConsistentV` and sMRD-consistency coincide** for fence-free executions,
    under the conditions of `Execution.coherenceV_iff_coherence`. -/
theorem consistentV_iff_consistent {Ω : Pred} (hnf : x.FenceFree es)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hpo_irrefl : ∀ a, ¬ es.poR a a)
    (hpoloc : ∀ a b, x.poloc es a b → x.dep es a b)
    (hrel : ∀ a w, x.poX es a w → es.cls Event.isRelW w → x.dep es a w)
    (hacq : ∀ r b, es.cls Event.isAcqR r → x.poX es r b → x.dep es r b)
    (hdep : ∀ a b, x.dep es a b → x.poX es a b) :
    ConsistentV es x Ω ↔ x.Consistent es Ω :=
  ⟨consistent_of_consistentV hnf hpo_trans hpo_irrefl hpoloc hrel hacq,
   consistentV_of_consistent hdep⟩

/-- **`ConsistentF` and sMRD-consistency coincide, with fences**, under the
    conditions of `Execution.coherenceF_iff_coherence`. -/
theorem consistentF_iff_consistent {Ω : Pred}
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hpo_irrefl : ∀ a, ¬ es.poR a a)
    (hpoloc : ∀ a b, x.poloc es a b → x.depF es a b)
    (hrel : ∀ a w, x.poX es a w → (es.cls Event.isRelW w ∨ es.cls Event.isRelF w) →
      x.depF es a w)
    (hacq : ∀ r b, (es.cls Event.isAcqR r ∨ es.cls Event.isAcqF r) → x.poX es r b →
      x.depF es r b)
    (hdepF : ∀ a b, x.depF es a b → x.poX es a b) :
    ConsistentF es x Ω ↔ x.Consistent es Ω := by
  constructor
  · rintro ⟨hx, hphi, hnta, co, ho, hc, ha, hp⟩
    refine ⟨hx, hphi, hnta, coLoc es x co, coherenceOrder_coLoc ho, ?_,
      atomicity_anti coLoc_sub ha, pscOf_mono (fun _ _ h => h) (fun _ _ h => h) coLoc_sub hp⟩
    exact coherence_of_coherenceF hpo_trans hpo_irrefl hLtrans
      (x.rfLoc_of_isExecution es hx) coLoc_loc hpoloc hrel hacq (irr_eco_anti coLoc_sub hc)
  · rintro ⟨hx, hphi, hnta, co, ho, hc, ha, hp⟩
    exact ⟨hx, hphi, hnta, co, ho, x.coherenceF_of_coherence es hdepF hc, ha, hp⟩

/-- **`ConsistentF` implies `ConsistentV`**, with fences or without. -/
theorem consistentV_of_consistentF {Ω : Pred} (h : ConsistentF es x Ω) : ConsistentV es x Ω := by
  obtain ⟨hx, hphi, hnta, co, ho, hc, ha, hp⟩ := h
  exact ⟨hx, hphi, hnta, co, ho, coherenceV_of_coherenceF hc, ha, hp⟩

/-- **Without fences `ConsistentF` is `ConsistentV`.** -/
theorem consistentF_iff_consistentV {Ω : Pred} (hnf : x.FenceFree es) :
    ConsistentF es x Ω ↔ ConsistentV es x Ω := by
  unfold ConsistentF ConsistentV CoherentF CoherentV
  simp only [coherenceF_iff_coherenceV hnf]

/-- **RC11-consistency implies `ConsistentV`** where `DP ∪ ≼ ⊆ ⊑`. -/
theorem consistentV_of_consistentRC11 {Ω : Pred} (hdep : ∀ a b, x.dep es a b → es.poR a b)
    (h : RC11.ConsistentRC11 es x Ω) : ConsistentV es x Ω :=
  consistentV_of_consistent
    (fun a b hd => ⟨.inl (RC11.dep_X hd).1, .inl (RC11.dep_X hd).2, hdep a b hd⟩)
    (RC11.consistent_of_consistentRC11 hdep h)

/-! ## Relations to sMRD's `ConsistentT` -/

/-- **Without elided events `ConsistentVT` is `ConsistentV`.** -/
theorem consistentVT_iff_consistentV {Ω : Pred} (h : ∀ a, ¬ x.elided a) :
    ConsistentVT es x Ω ↔ ConsistentV es x Ω := by
  unfold ConsistentVT ConsistentV CoherentVT CoherentV
  simp only [coherenceOrderT_iff h, pscT_iff_psc h]

/-- **`ConsistentVT` and `ConsistentT` coincide** for fence-free executions
    with a location model, with forwarding and write elision, under
    `NoRevLoc`, `RMWTightR`, `DP ⊆ ⊑`, where no acquire read is forwarded
    (`Execution.coherenceT_iff_coherenceV`). -/
theorem consistentVT_iff_consistentT {Ω : Pred} (hnf : x.FenceFree es)
    (hnoAcqF : ∀ p ∈ x.δ.f, ¬ es.cls Event.isAcqR p.2)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hL : NoRevLoc es x) (hT : RMWTightR es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b) (hm : LocModel es x) :
    ConsistentVT es x Ω ↔ x.ConsistentT es Ω := by
  constructor
  · rintro ⟨hx, hphi, hnta, co, ho, hc, ha, hp⟩
    have ho' := coherenceOrderT_coLoc ho
    refine ⟨hx, hphi, hnta, coLoc es x co, ho', ?_, atomicity_anti coLoc_sub ha,
      pscOf_mono (fun _ _ h => h) (fun _ _ h => h) coLoc_sub hp⟩
    exact (coherenceT_iff_coherenceV hx hphi hnf hnoAcqF hpo_trans hirr hL hT hDP hLtrans
      (x.rfLoc_of_isExecution es hx) ho' coLoc_loc hm).2 (irr_eco_anti coLoc_sub hc)
  · rintro ⟨hx, hphi, hnta, co, ho, hc, ha, hp⟩
    have ho' := coherenceOrderT_coLoc ho
    have hcT : x.CoherenceT es (coLoc es x co) := irr_eco_anti coLoc_sub hc
    refine ⟨hx, hphi, hnta, coLoc es x co, ho', ?_, atomicity_anti coLoc_sub ha,
      pscOf_mono (fun _ _ h => h) (fun _ _ h => h) coLoc_sub hp⟩
    exact (coherenceT_iff_coherenceV hx hphi hnf hnoAcqF hpo_trans hirr hL hT hDP hLtrans
      (x.rfLoc_of_isExecution es hx) ho' coLoc_loc hm).1 hcT

/-- **`ConsistentFT` and `ConsistentT` coincide, with fences**, under the
    hypotheses of `consistentVT_iff_consistentT` but `FenceFree`
    (`Execution.coherenceT_iff_coherenceF`). -/
theorem consistentFT_iff_consistentT {Ω : Pred}
    (hnoAcqF : ∀ p ∈ x.δ.f, ¬ es.cls Event.isAcqR p.2)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hL : NoRevLoc es x) (hT : RMWTightR es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b) (hm : LocModel es x) :
    ConsistentFT es x Ω ↔ x.ConsistentT es Ω := by
  constructor
  · rintro ⟨hx, hphi, hnta, co, ho, hc, ha, hp⟩
    have ho' := coherenceOrderT_coLoc ho
    refine ⟨hx, hphi, hnta, coLoc es x co, ho', ?_, atomicity_anti coLoc_sub ha,
      pscOf_mono (fun _ _ h => h) (fun _ _ h => h) coLoc_sub hp⟩
    exact (coherenceT_iff_coherenceF hx hphi hnoAcqF hpo_trans hirr hL hT hDP hLtrans
      (x.rfLoc_of_isExecution es hx) ho' coLoc_loc hm).2 (irr_eco_anti coLoc_sub hc)
  · rintro ⟨hx, hphi, hnta, co, ho, hc, ha, hp⟩
    have ho' := coherenceOrderT_coLoc ho
    have hcT : x.CoherenceT es (coLoc es x co) := irr_eco_anti coLoc_sub hc
    refine ⟨hx, hphi, hnta, coLoc es x co, ho', ?_, atomicity_anti coLoc_sub ha,
      pscOf_mono (fun _ _ h => h) (fun _ _ h => h) coLoc_sub hp⟩
    exact (coherenceT_iff_coherenceF hx hphi hnoAcqF hpo_trans hirr hL hT hDP hLtrans
      (x.rfLoc_of_isExecution es hx) ho' coLoc_loc hm).1 hcT

/-! ## Fences separate `ConsistentV` from `Consistent` -/

open EventStructure PpoKit PpoNecessity FenceMP in
/-- **Message passing through fences** (`Smrd.FenceMP`),
    `x := 0; y := 0; (x := 1; fence(rel); y := 1 ∥ r1 := y; fence(acq); r2 := x)`
    with `r1 = 1`, `r2 = 0`: consistent in the relaxed-coherence model over
    `HB_v`, and neither sMRD-consistent (`Consistent`, `ConsistentT`) nor
    RC11-consistent. -/
theorem fenceMP_separates :
    ConsistentV esMPF xMPF (fun _ => True) ∧ ¬ xMPF.Consistent esMPF (fun _ => True) ∧
    ¬ xMPF.ConsistentT esMPF (fun _ => True) ∧
    ¬ RC11.ConsistentRC11 esMPF xMPF (fun _ => True) := by
  have hdp : ∀ a b, ¬ xMPF.DP a b := fun _ _ => dp_none (es := esMPF) (rf := rfMPF) (by decide)
  have nta : xMPF.NoThinAir esMPF := by
    intro a h
    have hm : (a, a) ∈ stepsL ++ rfMPF := by
      refine transGen_mem (fun c d s => ?_) (by decide) h
      rcases s with (hp | hd) | hr
      · exact List.mem_append.2 (.inl (ppoF_mem (ppoF_of_ppo hp)))
      · exact absurd hd (hdp _ _)
      · exact List.mem_append.2 (.inr hr)
    have : ∀ p ∈ stepsL ++ rfMPF, p.1 ≠ p.2 := by decide
    exact this _ hm rfl
  have notCoh : ¬ xMPF.Coherent esMPF := fun ⟨_, ho, hc, _⟩ => mpf_rc11 ho hc
  have notC : ¬ xMPF.Consistent esMPF (fun _ => True) := fun h => notCoh h.2.2.2
  refine ⟨⟨mpf_exec.1, mpf_exec.2, nta, relL coMPF, summary.2.2.1, mpf_coherenceV,
      PSCExamples.atomicity_of (es := esMPF) (rf := rfMPF) rfl _,
      xMPF.psc_of_noSC esMPF (xMPF.scFree_of_es esMPF (esMPF.scFree_of_all (by decide))) _⟩,
    notC, fun h => notC ((RC11.consistentT_iff_consistent (not_elided_simple esMPF rfMPF)).1 h),
    fun h => notCoh h.2.2.2.2⟩

end Smrd.Relaxed
