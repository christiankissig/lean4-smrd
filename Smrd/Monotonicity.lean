import Smrd.Types
import Smrd.EventStructureSemantics
import Smrd.Fresh

/-!
# Monotonicity in the Step-Counter (Lemma `l:es-mono`)

`𝔼_n ⊆ 𝔼_{n+1}`: the event structure generated under per-loop step-counters
`n` embeds into the one generated under any larger `n'`, preserving events
(with their actions and value restrictions), program order and the
read-modify-write entries (`denote_mono`, `denote_mono_succ`).

## Embedding up to renaming

The paper identifies the events of the two structures by control label. Here
events are identified by ids drawn from a counter in generation order, and the
additional iterations `𝔼_{n+1}` unravels shift the ids -- and with them the
symbols, which are ids -- of every event generated after them; parallel
composition after a loop shifts thread ids likewise. The embedding is therefore
up to a renaming `θ` of event ids (and symbols) and `τ` of threads, injective on
the events of `𝔼_n` (`Embeds`).

## Proof

A simulation between the two runs of the interpreter (`interp_sim`). Where the
smaller run cuts a loop off, it generates nothing, and the empty structure
embeds into anything; everywhere else the two runs take the same steps, and
the events they generate correspond. As for `Smrd.Fresh`, each shape of event
generation is handled once, by a combinator lemma.
-/

/-! ## Renaming -/

/-- `f` and `g` agree below `b`. -/
def Agree (f g : Nat → Nat) (b : Nat) : Prop := ∀ i, i < b → f i = g i

/-- `f[i ↦ j]` -/
def upd (f : Nat → Nat) (i j : Nat) : Nat → Nat := fun x => if x = i then j else f x

theorem Agree.trans {f g h : Nat → Nat} {b c : Nat} (h₁ : Agree f g b) (h₂ : Agree g h c)
    (hcb : c ≤ b) : Agree f h c := fun i hi => (h₁ i (Nat.lt_of_lt_of_le hi hcb)).trans (h₂ i hi)

theorem Agree.upd_below {f g : Nat → Nat} {b i j : Nat} (h : Agree f (upd g i j) (i + 1))
    (hb : b ≤ i) : Agree f g b := by
  intro x hx
  rw [h x (by omega), upd, if_neg (by omega)]

theorem Agree.upd_at {f g : Nat → Nat} {i j : Nat} (h : Agree f (upd g i j) (i + 1)) :
    f i = j := by
  rw [h i (Nat.lt_succ_self _), upd, if_pos rfl]

/-- Rename the symbols of an expression. -/
def Expr.ren (θ : Nat → Nat) (e : Expr) : Expr := e.rename (fun α => some (θ α))

theorem Expr.ren_congr (e : Expr) {θ θ' : Nat → Nat} (h : ∀ α ∈ e.syms, θ α = θ' α) :
    e.ren θ = e.ren θ' := by
  induction e with
  | val v => rfl
  | sym α => simp [Expr.ren, Expr.rename, h α (by simp [Expr.syms])]
  | bin op a b iha ihb | eq a b iha ihb | le a b iha ihb | and a b iha ihb | or a b iha ihb =>
      simp only [Expr.syms, List.mem_append] at h
      simp only [Expr.ren, Expr.rename] at iha ihb ⊢
      rw [iha (fun α hα => h α (Or.inl hα)), ihb (fun α hα => h α (Or.inr hα))]
  | not a iha =>
      simp only [Expr.ren, Expr.rename] at iha ⊢
      rw [iha h]

def EventKind.ren (θ : Nat → Nat) : EventKind → EventKind
  | .read o l α   => .read o (l.ren θ) (θ α)
  | .write o l v  => .write o (l.ren θ) (v.ren θ)
  | .fence o      => .fence o
  | .branch c     => .branch (c.ren θ)
  | .alloc α s    => .alloc (θ α) (s.ren θ)
  | .dealloc l    => .dealloc (l.ren θ)

def Guard.ren (θ : Nat → Nat) (g : Guard) : Guard := ⟨θ g.branch, g.cond.ren θ, g.pos⟩

/-- Rename an event: its id and symbols by `θ`, its thread by `τ`. -/
def Event.ren (θ τ : Nat → Nat) (e : Event) : Event :=
  { id := θ e.id, kind := e.kind.ren θ, label := { e.label with thread := τ e.label.thread },
    guards := e.guards.map (Guard.ren θ) }

def RMWEntry.ren (θ : Nat → Nat) (x : RMWEntry) : RMWEntry := ⟨θ x.r, x.cond.ren θ, θ x.w⟩

@[simp] theorem Event.ren_id (θ τ : Nat → Nat) (e : Event) : (e.ren θ τ).id = θ e.id := rfl

/-- Renaming preserves value restrictions. -/
theorem Event.ren_valres (θ τ : Nat → Nat) (e : Event) :
    (e.ren θ τ).guards = e.guards.map (Guard.ren θ) := rfl

/-- `E₁` embeds into `E₂` along the renamings `θ` and `τ`: its events, program
    order and read-modify-write entries are carried over. -/
structure Embeds (θ τ : Nat → Nat) (E₁ E₂ : EventStructure) : Prop where
  events : ∀ e ∈ E₁.events, e.ren θ τ ∈ E₂.events
  po     : ∀ p ∈ E₁.po, (θ p.1, θ p.2) ∈ E₂.po
  rmw    : ∀ x ∈ E₁.rmw, x.ren θ ∈ E₂.rmw

namespace EventStructure

@[simp] theorem events_prefix (e : Event) (k : EventStructure) :
    («prefix» e k).events = e :: k.events := rfl
@[simp] theorem po_prefix (e : Event) (k : EventStructure) :
    («prefix» e k).po = k.events.map (fun e' => (e.id, e'.id)) ++ k.po := rfl
@[simp] theorem rmw_prefix (e : Event) (k : EventStructure) : («prefix» e k).rmw = k.rmw := rfl
@[simp] theorem events_plus (k k' : EventStructure) : (k.plus k').events = k.events ++ k'.events := rfl
@[simp] theorem po_plus (k k' : EventStructure) : (k.plus k').po = k.po ++ k'.po := rfl
@[simp] theorem rmw_plus (k k' : EventStructure) : (k.plus k').rmw = k.rmw ++ k'.rmw := rfl
@[simp] theorem events_addRMW (k : EventStructure) (r : EventId) (c : Expr) (w : EventId) :
    (k.addRMW r c w).events = k.events := rfl
@[simp] theorem po_addRMW (k : EventStructure) (r : EventId) (c : Expr) (w : EventId) :
    (k.addRMW r c w).po = k.po := rfl
@[simp] theorem rmw_addRMW (k : EventStructure) (r : EventId) (c : Expr) (w : EventId) :
    (k.addRMW r c w).rmw = ⟨r, c, w⟩ :: k.rmw := rfl

end EventStructure

namespace Embeds

open EventStructure

variable {θ τ : Nat → Nat}

theorem empty (E : EventStructure) : Embeds θ τ EventStructure.empty E :=
  ⟨by simp [EventStructure.empty], by simp [EventStructure.empty], by simp [EventStructure.empty]⟩

theorem «prefix» {e₁ e₂ : Event} {k₁ k₂ : EventStructure} (he : e₁.ren θ τ = e₂)
    (hk : Embeds θ τ k₁ k₂) : Embeds θ τ («prefix» e₁ k₁) («prefix» e₂ k₂) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e hmem
    simp only [events_prefix, List.mem_cons] at hmem ⊢
    rcases hmem with rfl | hmem
    · exact Or.inl he
    · exact Or.inr (hk.events e hmem)
  · intro p hmem
    simp only [po_prefix, List.mem_append, List.mem_map] at hmem ⊢
    rcases hmem with ⟨x, hx, rfl⟩ | hmem
    · exact Or.inl ⟨x.ren θ τ, hk.events x hx, by rw [← he]; rfl⟩
    · exact Or.inr (hk.po p hmem)
  · simpa using hk.rmw

theorem plus {k₁ k₂ k₁' k₂' : EventStructure} (h : Embeds θ τ k₁ k₂) (h' : Embeds θ τ k₁' k₂') :
    Embeds θ τ (k₁.plus k₁') (k₂.plus k₂') := by
  refine ⟨?_, ?_, ?_⟩ <;> intro x hx
  · simp only [events_plus, List.mem_append] at hx ⊢
    exact hx.elim (fun h₁ => Or.inl (h.events x h₁)) (fun h₁ => Or.inr (h'.events x h₁))
  · simp only [po_plus, List.mem_append] at hx ⊢
    exact hx.elim (fun h₁ => Or.inl (h.po x h₁)) (fun h₁ => Or.inr (h'.po x h₁))
  · simp only [rmw_plus, List.mem_append] at hx ⊢
    exact hx.elim (fun h₁ => Or.inl (h.rmw x h₁)) (fun h₁ => Or.inr (h'.rmw x h₁))

theorem addRMW {k₁ k₂ : EventStructure} {r₁ w₁ r₂ w₂ : EventId} {c₁ c₂ : Expr}
    (h : Embeds θ τ k₁ k₂) (hr : θ r₁ = r₂) (hw : θ w₁ = w₂) (hc : c₁.ren θ = c₂) :
    Embeds θ τ (k₁.addRMW r₁ c₁ w₁) (k₂.addRMW r₂ c₂ w₂) := by
  refine ⟨by simpa using h.events, by simpa using h.po, ?_⟩
  intro x hx
  simp only [rmw_addRMW, List.mem_cons] at hx ⊢
  rcases hx with rfl | hx
  · exact Or.inl (by simp [RMWEntry.ren, hr, hw, hc])
  · exact Or.inr (h.rmw x hx)

end Embeds

/-! ## Register states and value restrictions under renaming -/

theorem RegState.get_set (ρ : RegState) (r r' : Reg) (e : Expr) :
    (ρ.set r e).get r' = if r' = r then e else ρ.get r' := by
  simp only [RegState.get, RegState.set]
  by_cases h : r' = r
  · subst h; simp
  · have : (r' == r) = false := by simpa using h
    simp [List.lookup_cons, this, h]

/-- `ρ₂` is `ρ₁` renamed by `θ`, register by register. -/
def RegRel (θ : Nat → Nat) (ρ₁ ρ₂ : RegState) : Prop := ∀ r, ρ₂.get r = (ρ₁.get r).ren θ

/-- The symbols `ρ` holds are below `b`. -/
def RegBelow (b : Nat) (ρ : RegState) : Prop := ∀ r, ∀ α ∈ (ρ.get r).syms, α < b

/-- The branching events and symbols of the guards `φ` are below `b`. -/
def GuardsBelow (b : Nat) (φ : List Guard) : Prop :=
  ∀ g ∈ φ, g.branch < b ∧ ∀ α ∈ g.cond.syms, α < b

theorem PExpr.den_rel {θ : Nat → Nat} {ρ₁ ρ₂ : RegState} (h : RegRel θ ρ₁ ρ₂) (e : PExpr) :
    e.den ρ₂ = (e.den ρ₁).ren θ := by
  induction e with
  | reg r => exact h r
  | num n => rfl
  | bin op a b iha ihb | eq a b iha ihb | le a b iha ihb | and a b iha ihb | or a b iha ihb =>
      simp only [PExpr.den, Expr.ren, Expr.rename] at iha ihb ⊢
      rw [iha, ihb]
  | not a iha =>
      simp only [PExpr.den, Expr.ren, Expr.rename] at iha ⊢
      rw [iha]

theorem PExpr.den_below {b : Nat} {ρ : RegState} (h : RegBelow b ρ) (e : PExpr) :
    ∀ α ∈ (e.den ρ).syms, α < b := by
  induction e with
  | reg r => exact h r
  | num n => intro α hα; simp [PExpr.den, Expr.num, Expr.syms] at hα
  | bin op a b iha ihb | eq a b iha ihb | le a b iha ihb | and a b iha ihb | or a b iha ihb =>
      intro α hα
      simp only [PExpr.den, Expr.syms, List.mem_append] at hα
      exact hα.elim (iha α) (ihb α)
  | not a iha => exact iha

theorem RegRel.congr {θ θ' : Nat → Nat} {b : Nat} {ρ₁ ρ₂ : RegState} (h : RegRel θ ρ₁ ρ₂)
    (hb : RegBelow b ρ₁) (ha : Agree θ' θ b) : RegRel θ' ρ₁ ρ₂ := by
  intro r
  rw [h r]
  exact Expr.ren_congr _ (fun α hα => (ha α (hb r α hα)).symm)

theorem RegRel.set {θ : Nat → Nat} {ρ₁ ρ₂ : RegState} (h : RegRel θ ρ₁ ρ₂) (r : Reg)
    {v₁ v₂ : Expr} (hv : v₂ = v₁.ren θ) : RegRel θ (ρ₁.set r v₁) (ρ₂.set r v₂) := by
  intro r'
  rw [RegState.get_set, RegState.get_set]
  split
  · exact hv
  · exact h r'

theorem RegBelow.mono {b c : Nat} {ρ : RegState} (h : RegBelow b ρ) (hbc : b ≤ c) :
    RegBelow c ρ := fun r α hα => Nat.lt_of_lt_of_le (h r α hα) hbc

theorem RegBelow.set {b : Nat} {ρ : RegState} (h : RegBelow b ρ) (r : Reg) {v : Expr}
    (hv : ∀ α ∈ v.syms, α < b) : RegBelow b (ρ.set r v) := by
  intro r' α hα
  rw [RegState.get_set] at hα
  split at hα
  · exact hv α hα
  · exact h r' α hα

theorem GuardsBelow.mono {b c : Nat} {φ : List Guard} (h : GuardsBelow b φ) (hbc : b ≤ c) :
    GuardsBelow c φ := fun g hg =>
  ⟨Nat.lt_of_lt_of_le (h g hg).1 hbc, fun α hα => Nat.lt_of_lt_of_le ((h g hg).2 α hα) hbc⟩

theorem GuardsBelow.snoc {b : Nat} {φ : List Guard} (h : GuardsBelow b φ) {g : Guard}
    (hg : g.branch < b) (hc : ∀ α ∈ g.cond.syms, α < b) : GuardsBelow b (φ ++ [g]) := by
  intro g' hg'
  simp only [List.mem_append, List.mem_singleton] at hg'
  rcases hg' with hg' | rfl
  · exact h g' hg'
  · exact ⟨hg, hc⟩

theorem GuardsBelow.map_congr {θ θ' : Nat → Nat} {b : Nat} {φ : List Guard}
    (h : GuardsBelow b φ) (ha : Agree θ' θ b) : φ.map (Guard.ren θ') = φ.map (Guard.ren θ) := by
  apply List.map_congr_left
  intro g hg
  simp only [Guard.ren, ha g.branch (h g hg).1,
    Expr.ren_congr g.cond (fun α hα => ha α ((h g hg).2 α hα))]

/-- `⟦e⟧_{ρ₂}` is `⟦e⟧_{ρ₁}` renamed by any `θ` agreeing with the relating one
    on the symbols `ρ₁` holds. -/
theorem den_ren {θ₀ θ : Nat → Nat} {b : Nat} {ρ₁ ρ₂ : RegState} (h : RegRel θ₀ ρ₁ ρ₂)
    (hb : RegBelow b ρ₁) (ha : Agree θ θ₀ b) (e : PExpr) : (e.den ρ₁).ren θ = e.den ρ₂ := by
  rw [PExpr.den_rel h e]
  exact Expr.ren_congr _ (fun α hα => ha α (PExpr.den_below hb e α hα))

/-! ## Simulation between two runs -/

/-- `θ` maps `[a₁, b₁)` injectively into `[a₂, b₂)`. -/
def MapsInj (θ : Nat → Nat) (a₁ b₁ a₂ b₂ : Nat) : Prop :=
  (∀ i, a₁ ≤ i → i < b₁ → a₂ ≤ θ i ∧ θ i < b₂) ∧
  (∀ i i', a₁ ≤ i → i < b₁ → a₁ ≤ i' → i' < b₁ → θ i = θ i' → i = i')

/-- The run of `m₁` simulates into the run of `m₂`: from any states above the
    bounds `bI` (ids) and `bT` (threads), there are renamings extending `θ₀` and
    `τ₀` below the bounds that map the ids `m₁` allocates injectively onto ids
    `m₂` allocates, under which -- and under any further extension -- the
    structure `m₁` generates embeds into the one `m₂` generates. -/
def Sim (θ₀ τ₀ : Nat → Nat) (bI bT : Nat) (m₁ m₂ : Gen EventStructure) : Prop :=
  ∀ σ₁ σ₂ : GenState, bI ≤ σ₁.nextId → bT ≤ σ₁.nextThread →
    σ₁.nextId ≤ (m₁.run σ₁).2.nextId ∧ σ₁.nextThread ≤ (m₁.run σ₁).2.nextThread ∧
    σ₂.nextId ≤ (m₂.run σ₂).2.nextId ∧
    ∃ θ τ, Agree θ θ₀ bI ∧ Agree τ τ₀ bT ∧
      MapsInj θ σ₁.nextId (m₁.run σ₁).2.nextId σ₂.nextId (m₂.run σ₂).2.nextId ∧
      ∀ θ' τ', Agree θ' θ (m₁.run σ₁).2.nextId → Agree τ' τ (m₁.run σ₁).2.nextThread →
        Embeds θ' τ' (m₁.run σ₁).1 (m₂.run σ₂).1

/-- Continuations simulate: related arguments give simulating runs. -/
def KSim (θ₀ τ₀ : Nat → Nat) (bI bT : Nat) (κ₁ κ₂ : Cont) : Prop :=
  ∀ θ τ b b' ρ₁ ρ₂ φ, bI ≤ b → bT ≤ b' → Agree θ θ₀ bI → Agree τ τ₀ bT →
    RegRel θ ρ₁ ρ₂ → RegBelow b ρ₁ → GuardsBelow b φ →
    Sim θ τ b b' (κ₁ ρ₁ φ) (κ₂ ρ₂ (φ.map (Guard.ren θ)))

theorem KSim.mono {θ₀ τ₀ θ τ : Nat → Nat} {bI bT b b' : Nat} {κ₁ κ₂ : Cont}
    (h : KSim θ₀ τ₀ bI bT κ₁ κ₂) (hb : bI ≤ b) (hb' : bT ≤ b') (hθ : Agree θ θ₀ bI)
    (hτ : Agree τ τ₀ bT) : KSim θ τ b b' κ₁ κ₂ :=
  fun θ' τ' c c' ρ₁ ρ₂ φ hc hc' hθ' hτ' hρ hB hG =>
    h θ' τ' c c' ρ₁ ρ₂ φ (Nat.le_trans hb hc) (Nat.le_trans hb' hc')
      (hθ'.trans hθ hb) (hτ'.trans hτ hb') hρ hB hG

theorem Agree.refl (f : Nat → Nat) (b : Nat) : Agree f f b := fun _ _ => rfl

theorem Agree.mono {f g : Nat → Nat} {b c : Nat} (h : Agree f g b) (hcb : c ≤ b) : Agree f g c :=
  fun i hi => h i (Nat.lt_of_lt_of_le hi hcb)

theorem MapsInj.congr {θ θ' : Nat → Nat} {a₁ b₁ a₂ b₂ : Nat} (h : MapsInj θ a₁ b₁ a₂ b₂)
    (ha : Agree θ' θ b₁) : MapsInj θ' a₁ b₁ a₂ b₂ := by
  refine ⟨fun i h₁ h₂ => ?_, fun i i' h₁ h₂ h₃ h₄ he => ?_⟩
  · rw [ha i h₂]; exact h.1 i h₁ h₂
  · rw [ha i h₂, ha i' h₄] at he; exact h.2 i i' h₁ h₂ h₃ h₄ he

namespace Sim

variable {θ₀ τ₀ : Nat → Nat} {bI bT : Nat}

/-- The empty structure simulates into anything. -/
theorem empty {m₂ : Gen EventStructure} (h₂ : Gen.Fresh m₂) :
    Sim θ₀ τ₀ bI bT (pure EventStructure.empty) m₂ := by
  intro σ₁ σ₂ _ _
  refine ⟨Nat.le_refl _, Nat.le_refl _, (h₂ σ₂).1, θ₀, τ₀, Agree.refl _ _, Agree.refl _ _,
    ⟨fun i h₁ h₂ => absurd (Nat.lt_of_le_of_lt h₁ h₂) (Nat.lt_irrefl _),
     fun i _ h₁ h₂ => absurd (Nat.lt_of_le_of_lt h₁ h₂) (Nat.lt_irrefl _)⟩,
    fun _ _ _ _ => Embeds.empty _⟩

/-- Map the structures on both sides. -/
theorem map {A₁ A₂ : Gen EventStructure} {f₁ f₂ : EventStructure → EventStructure}
    (h : Sim θ₀ τ₀ bI bT A₁ A₂)
    (hf : ∀ θ τ k₁ k₂, Agree θ θ₀ bI → Agree τ τ₀ bT → Embeds θ τ k₁ k₂ →
      Embeds θ τ (f₁ k₁) (f₂ k₂)) :
    Sim θ₀ τ₀ bI bT (do let k ← A₁; pure (f₁ k)) (do let k ← A₂; pure (f₂ k)) := by
  intro σ₁ σ₂ hI hT
  have hr₁ : StateT.run (do let k ← A₁; pure (f₁ k) : Gen EventStructure) σ₁
      = (f₁ (A₁.run σ₁).1, (A₁.run σ₁).2) := rfl
  have hr₂ : StateT.run (do let k ← A₂; pure (f₂ k) : Gen EventStructure) σ₂
      = (f₂ (A₂.run σ₂).1, (A₂.run σ₂).2) := rfl
  rw [hr₁, hr₂]
  obtain ⟨m₁, t₁, m₂, θ, τ, hθ, hτ, hmap, hemb⟩ := h σ₁ σ₂ hI hT
  refine ⟨m₁, t₁, m₂, θ, τ, hθ, hτ, hmap, fun θ' τ' hθ' hτ' => ?_⟩
  exact hf θ' τ' _ _ (hθ'.trans hθ (Nat.le_trans hI m₁)) (hτ'.trans hτ (Nat.le_trans hT t₁))
    (hemb θ' τ' hθ' hτ')

/-- Generate one event on each side: the first id maps to the second. -/
theorem mk {ctx₁ ctx₂ : Ctx} {pc₁ pc₂ : List Nat} {φ₁ φ₂ : List Guard}
    {kind₁ kind₂ : EventId → EventKind} {M₁ M₂ : Event → Gen EventStructure}
    (hM : ∀ i j, bI ≤ i → Sim (upd θ₀ i j) τ₀ (i + 1) bT
      (M₁ (mkE ctx₁ pc₁ φ₁ kind₁ i)) (M₂ (mkE ctx₂ pc₂ φ₂ kind₂ j))) :
    Sim θ₀ τ₀ bI bT (do let e ← mkEvent ctx₁ pc₁ φ₁ kind₁; M₁ e)
      (do let e ← mkEvent ctx₂ pc₂ φ₂ kind₂; M₂ e) := by
  intro σ₁ σ₂ hI hT
  have hr₁ : StateT.run (do let e ← mkEvent ctx₁ pc₁ φ₁ kind₁; M₁ e : Gen EventStructure) σ₁
      = (M₁ (mkE ctx₁ pc₁ φ₁ kind₁ σ₁.nextId)).run ⟨σ₁.nextId + 1, σ₁.nextThread⟩ := rfl
  have hr₂ : StateT.run (do let e ← mkEvent ctx₂ pc₂ φ₂ kind₂; M₂ e : Gen EventStructure) σ₂
      = (M₂ (mkE ctx₂ pc₂ φ₂ kind₂ σ₂.nextId)).run ⟨σ₂.nextId + 1, σ₂.nextThread⟩ := rfl
  rw [hr₁, hr₂]
  obtain ⟨m₁, t₁, m₂, θ, τ, hθ, hτ, hmap, hemb⟩ :=
    hM σ₁.nextId σ₂.nextId hI ⟨σ₁.nextId + 1, σ₁.nextThread⟩ ⟨σ₂.nextId + 1, σ₂.nextThread⟩
      (Nat.le_refl _) hT
  generalize (M₁ (mkE ctx₁ pc₁ φ₁ kind₁ σ₁.nextId)).run ⟨σ₁.nextId + 1, σ₁.nextThread⟩ = r₁
    at m₁ t₁ hmap hemb ⊢
  generalize (M₂ (mkE ctx₂ pc₂ φ₂ kind₂ σ₂.nextId)).run ⟨σ₂.nextId + 1, σ₂.nextThread⟩ = r₂
    at m₂ hmap hemb ⊢
  obtain ⟨k₁, s₁⟩ := r₁
  obtain ⟨k₂, s₂⟩ := r₂
  simp only at m₁ t₁ m₂ hmap hemb ⊢
  have hij := hθ.upd_at
  refine ⟨Nat.le_trans (Nat.le_succ _) m₁, t₁, Nat.le_trans (Nat.le_succ _) m₂, θ, τ,
    hθ.upd_below hI, hτ, ⟨fun i h₁ h₂ => ?_, fun i i' h₁ h₂ h₃ h₄ he => ?_⟩, hemb⟩
  · by_cases hi : i = σ₁.nextId
    · subst hi; rw [hij]; unfold EventId at *; omega
    · have := hmap.1 i (by unfold EventId at *; omega) h₂; unfold EventId at *; omega
  · by_cases hi : i = σ₁.nextId <;> by_cases hi' : i' = σ₁.nextId
    · rw [hi, hi']
    · have := hmap.1 i' (by unfold EventId at *; omega) h₄
      rw [hi, hij] at he; unfold EventId at *; omega
    · have := hmap.1 i (by unfold EventId at *; omega) h₂
      rw [hi', hij] at he; unfold EventId at *; omega
    · exact hmap.2 i i' (by unfold EventId at *; omega) h₂ (by unfold EventId at *; omega) h₄ he

/-- Allocate a fresh thread on each side: the first maps to the second. -/
theorem thread {M₁ M₂ : ThreadId → Gen EventStructure}
    (hM : ∀ t₁ t₂, bT ≤ t₁ → Sim θ₀ (upd τ₀ t₁ t₂) bI (t₁ + 1) (M₁ t₁) (M₂ t₂)) :
    Sim θ₀ τ₀ bI bT (do let t ← freshThread; M₁ t) (do let t ← freshThread; M₂ t) := by
  intro σ₁ σ₂ hI hT
  have hr₁ : StateT.run (do let t ← freshThread; M₁ t : Gen EventStructure) σ₁
      = (M₁ σ₁.nextThread).run ⟨σ₁.nextId, σ₁.nextThread + 1⟩ := rfl
  have hr₂ : StateT.run (do let t ← freshThread; M₂ t : Gen EventStructure) σ₂
      = (M₂ σ₂.nextThread).run ⟨σ₂.nextId, σ₂.nextThread + 1⟩ := rfl
  rw [hr₁, hr₂]
  obtain ⟨m₁, t₁, m₂, θ, τ, hθ, hτ, hmap, hemb⟩ :=
    hM σ₁.nextThread σ₂.nextThread hT ⟨σ₁.nextId, σ₁.nextThread + 1⟩ ⟨σ₂.nextId, σ₂.nextThread + 1⟩
      hI (Nat.le_refl _)
  exact ⟨m₁, Nat.le_trans (Nat.le_succ _) t₁, m₂, θ, τ, hθ, hτ.upd_below hT, hmap, hemb⟩

/-- Two generators in sequence on each side, combined. -/
theorem seq2 {A₁ A₂ B₁ B₂ : Gen EventStructure} {f₁ f₂ : EventStructure → EventStructure → EventStructure}
    (hA : Sim θ₀ τ₀ bI bT A₁ A₂)
    (hB : ∀ θ τ b b', bI ≤ b → bT ≤ b' → Agree θ θ₀ bI → Agree τ τ₀ bT → Sim θ τ b b' B₁ B₂)
    (hf : ∀ θ τ k₁ k₂ k₁' k₂', Agree θ θ₀ bI → Agree τ τ₀ bT → Embeds θ τ k₁ k₂ →
      Embeds θ τ k₁' k₂' → Embeds θ τ (f₁ k₁ k₁') (f₂ k₂ k₂')) :
    Sim θ₀ τ₀ bI bT (do let k ← A₁; let k' ← B₁; pure (f₁ k k'))
      (do let k ← A₂; let k' ← B₂; pure (f₂ k k')) := by
  intro σ₁ σ₂ hI hT
  have hr₁ : StateT.run (do let k ← A₁; let k' ← B₁; pure (f₁ k k') : Gen EventStructure) σ₁
      = (f₁ (A₁.run σ₁).1 (B₁.run (A₁.run σ₁).2).1, (B₁.run (A₁.run σ₁).2).2) := rfl
  have hr₂ : StateT.run (do let k ← A₂; let k' ← B₂; pure (f₂ k k') : Gen EventStructure) σ₂
      = (f₂ (A₂.run σ₂).1 (B₂.run (A₂.run σ₂).2).1, (B₂.run (A₂.run σ₂).2).2) := rfl
  rw [hr₁, hr₂]
  obtain ⟨m₁, t₁, m₂, θ, τ, hθ, hτ, hmap, hemb⟩ := hA σ₁ σ₂ hI hT
  generalize A₁.run σ₁ = r₁ at m₁ t₁ hmap hemb ⊢
  generalize A₂.run σ₂ = r₂ at m₂ hmap hemb ⊢
  obtain ⟨k₁, s₁⟩ := r₁
  obtain ⟨k₂, s₂⟩ := r₂
  simp only at m₁ t₁ m₂ hmap hemb ⊢
  obtain ⟨m₁', t₁', m₂', θ', τ', hθ', hτ', hmap', hemb'⟩ :=
    hB θ τ s₁.nextId s₁.nextThread (Nat.le_trans hI m₁) (Nat.le_trans hT t₁) hθ hτ s₁ s₂
      (Nat.le_refl _) (Nat.le_refl _)
  generalize B₁.run s₁ = q₁ at m₁' t₁' hmap' hemb' ⊢
  generalize B₂.run s₂ = q₂ at m₂' hmap' hemb' ⊢
  obtain ⟨k₁', s₁'⟩ := q₁
  obtain ⟨k₂', s₂'⟩ := q₂
  simp only at m₁' t₁' m₂' hmap' hemb' ⊢
  have hmap₁ := hmap.congr hθ'
  refine ⟨Nat.le_trans m₁ m₁', Nat.le_trans t₁ t₁', Nat.le_trans m₂ m₂', θ', τ',
    hθ'.trans hθ (Nat.le_trans hI m₁), hτ'.trans hτ (Nat.le_trans hT t₁),
    ⟨fun i h₁ h₂ => ?_, fun i i' h₁ h₂ h₃ h₄ he => ?_⟩, fun θ'' τ'' hθ'' hτ'' => ?_⟩
  · by_cases hi : i < s₁.nextId
    · have := hmap₁.1 i h₁ hi; unfold EventId at *; omega
    · have := hmap'.1 i (by unfold EventId at *; omega) h₂; unfold EventId at *; omega
  · by_cases hi : i < s₁.nextId <;> by_cases hi' : i' < s₁.nextId
    · exact hmap₁.2 i i' h₁ hi h₃ hi' he
    · have := hmap₁.1 i h₁ hi; have := hmap'.1 i' (by unfold EventId at *; omega) h₄
      unfold EventId at *; omega
    · have := hmap'.1 i (by unfold EventId at *; omega) h₂; have := hmap₁.1 i' h₃ hi'
      unfold EventId at *; omega
    · exact hmap'.2 i i' (by unfold EventId at *; omega) h₂ (by unfold EventId at *; omega) h₄ he
  · exact hf θ'' τ'' _ _ _ _
      ((hθ''.trans hθ' m₁').trans hθ (Nat.le_trans hI m₁))
      ((hτ''.trans hτ' t₁').trans hτ (Nat.le_trans hT t₁))
      (hemb θ'' τ'' (hθ''.trans hθ' m₁') (hτ''.trans hτ' t₁')) (hemb' θ'' τ'' hθ'' hτ'')

end Sim

/-! ## The interpreter simulates into itself under larger step-counters -/

theorem Agree.upd_self {θ₀ : Nat → Nat} {bI i : Nat} (j : Nat) (hi : bI ≤ i) :
    Agree (upd θ₀ i j) θ₀ bI := by
  intro x hx
  simp only [upd]
  rw [if_neg (by omega)]

theorem mkE_ren_eq {ctx ctx₂ : Ctx} {pc : List Nat} {φ₁ φ₂ : List Guard}
    {kind₁ kind₂ : EventId → EventKind} {θ τ : Nat → Nat} {i j : Nat} (hθ : θ i = j)
    (hctx : ({ ctx with thread := τ ctx.thread } : Ctx) = ctx₂) (hφ : φ₁.map (Guard.ren θ) = φ₂)
    (hk : (kind₁ i).ren θ = kind₂ j) :
    (mkE ctx pc φ₁ kind₁ i).ren θ τ = mkE ctx₂ pc φ₂ kind₂ j := by
  subst hctx
  simp only [mkE, Event.ren, hθ, hφ, hk]

theorem Ctx.enter_thread (ctx : Ctx) (t : ThreadId) (ℓ : LoopId) (k : Nat) :
    ({ ctx with thread := t } : Ctx).enter ℓ k = { ctx.enter ℓ k with thread := t } := by
  unfold Ctx.enter; split <;> rfl

/-- Entering a loop commutes with retagging the thread. -/
theorem Ctx.enter_retag (ctx : Ctx) {t t' : ThreadId} (ℓ : LoopId) (k : Nat) (h : t' = t) :
    ({ ctx.enter ℓ k with thread := t' } : Ctx) = ({ ctx with thread := t } : Ctx).enter ℓ k := by
  subst h
  unfold Ctx.enter
  by_cases hc : ctx.iter.any (·.1 == ℓ) = true <;> simp [hc]

theorem Ctx.enter_thread_eq (ctx : Ctx) (ℓ : LoopId) (k : Nat) :
    (ctx.enter ℓ k).thread = ctx.thread := by
  unfold Ctx.enter; split <;> rfl

theorem Bounds.dec_mono {n₁ n₂ : Bounds} (h : ∀ l, n₁ l ≤ n₂ l) (ℓ : LoopId) :
    ∀ l, n₁.dec ℓ l ≤ n₂.dec ℓ l := by
  intro l; have := h l; unfold Bounds.dec; split <;> omega

theorem KSim.app {θ₀ τ₀ θ τ : Nat → Nat} {bI bT b b' : Nat} {κ₁ κ₂ : Cont}
    (h : KSim θ₀ τ₀ bI bT κ₁ κ₂) {ρ₁ ρ₂ : RegState} {φ φ₂ : List Guard} (hb : bI ≤ b)
    (hb' : bT ≤ b') (hθ : Agree θ θ₀ bI) (hτ : Agree τ τ₀ bT) (hρ : RegRel θ ρ₁ ρ₂)
    (hB : RegBelow b ρ₁) (hG : GuardsBelow b φ) (hφ : φ.map (Guard.ren θ) = φ₂) :
    Sim θ τ b b' (κ₁ ρ₁ φ) (κ₂ ρ₂ φ₂) :=
  hφ ▸ h θ τ b b' ρ₁ ρ₂ φ hb hb' hθ hτ hρ hB hG

theorem Guard.ren_mk (θ : Nat → Nat) (i : Nat) (c : Expr) (p : Bool) :
    Guard.ren θ ⟨i, c, p⟩ = ⟨θ i, c.ren θ, p⟩ := rfl

theorem Expr.ren_sym (θ : Nat → Nat) (α : Nat) : (Expr.sym α).ren θ = .sym (θ α) := rfl

theorem Expr.ren_val (θ : Nat → Nat) (v : Val) : (Expr.val v).ren θ = .val v := rfl

/-- `omega` through the abbreviations `EventId`, `Sym` and `ThreadId` of `Nat`,
    which it does not unfold itself. -/
macro "nomega" : tactic => `(tactic| ((try simp only [mkE_id] at *) <;> first
  | omega
  | (unfold EventId at *; omega)
  | (unfold Sym at *; omega)
  | (unfold ThreadId at *; omega)
  | (unfold EventId Sym at *; omega)
  | (unfold EventId ThreadId at *; omega)
  | (unfold EventId Sym ThreadId at *; omega)))

open Sim in
/-- **The simulation.** Under per-loop step-counters `n₁ ≤ n₂`, the run of
    `⟨s⟩_{n₁}` simulates into the run of `⟨s⟩_{n₂}`, given related register
    states, value restrictions, contexts and continuations. -/
theorem interp_sim : ∀ (N : Nat) (s : Stmt) (n₁ n₂ : Bounds) (ctx ctx₂ : Ctx) (pc : List Nat)
    (ρ₁ ρ₂ : RegState) (φ φ₂ : List Guard) (κ₁ κ₂ : Cont) (θ₀ τ₀ : Nat → Nat) (bI bT : Nat),
    sumB s.loops n₁ + sizeOf s < N → (∀ l, n₁ l ≤ n₂ l) →
    ctx₂ = { ctx with thread := τ₀ ctx.thread } → φ₂ = φ.map (Guard.ren θ₀) →
    RegRel θ₀ ρ₁ ρ₂ → RegBelow bI ρ₁ → GuardsBelow bI φ → ctx.thread < bT →
    KSim θ₀ τ₀ bI bT κ₁ κ₂ → (∀ ρ φ, Gen.Fresh (κ₂ ρ φ)) →
    Sim θ₀ τ₀ bI bT (interp n₁ ctx pc s ρ₁ κ₁ φ) (interp n₂ ctx₂ pc s ρ₂ κ₂ φ₂)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hN, _, _, _, _, _, _, _, _, _ =>
      absurd hN (Nat.not_lt_zero _)
  | N + 1, s, n₁, n₂, ctx, ctx₂, pc, ρ₁, ρ₂, φ, φ₂, κ₁, κ₂, θ₀, τ₀, bI, bT,
      hN, hn, hctx, hφ, hρ, hB, hG, hthr, hκ, hfr => by
    subst hctx hφ
    have hτc : ∀ τ : Nat → Nat, Agree τ τ₀ bT → τ ctx.thread = τ₀ ctx.thread :=
      fun τ hτ => hτ ctx.thread hthr
    -- The facts every generated event of the first run needs, under a renaming
    -- extending `θ₀` below `bI`.
    have hφr : ∀ θ : Nat → Nat, Agree θ θ₀ bI → φ.map (Guard.ren θ) = φ.map (Guard.ren θ₀) :=
      fun θ hθ => hG.map_congr hθ
    have hden : ∀ θ : Nat → Nat, Agree θ θ₀ bI → ∀ e : PExpr, (e.den ρ₁).ren θ = e.den ρ₂ :=
      fun θ hθ e => den_ren hρ hB hθ e
    -- Relating the register state and value restriction after one new event.
    have hρu : ∀ i j, bI ≤ i → RegRel (upd θ₀ i j) ρ₁ ρ₂ := fun i j hi => hρ.congr hB (Agree.upd_self j hi)
    cases s with
    | skip =>
        rw [interp.eq_def n₁ ctx pc, interp.eq_def n₂ _ pc]
        exact hκ.app (Nat.le_refl _) (Nat.le_refl _) (Agree.refl _ _) (Agree.refl _ _) hρ hB hG rfl
    | assign r e =>
        rw [interp.eq_def n₁ ctx pc, interp.eq_def n₂ _ pc]
        exact hκ.app (Nat.le_refl _) (Nat.le_refl _) (Agree.refl _ _) (Agree.refl _ _)
          (hρ.set r (PExpr.den_rel hρ e)) (hB.set r (PExpr.den_below hB e)) hG rfl
    | addrOf r x =>
        rw [interp.eq_def n₁ ctx pc, interp.eq_def n₂ _ pc]
        exact hκ.app (Nat.le_refl _) (Nat.le_refl _) (Agree.refl _ _) (Agree.refl _ _)
          (hρ.set r rfl) (hB.set r (by simp [Expr.glob, Expr.syms])) hG rfl
    | load o r x =>
        rw [interp.eq_def n₁ ctx pc, interp.eq_def n₂ _ pc]
        refine mk (fun i j hi => map ?_ (fun θ τ k₁ k₂ hθ hτ hk => Embeds.prefix ?_ hk))
        · exact hκ.app (by nomega) (Nat.le_refl _) (Agree.upd_self j hi) (Agree.refl _ _)
            ((hρu i j hi).set r (by simp [Expr.ren_sym, upd])) ((hB.mono (by nomega)).set r
              (by simp [Expr.syms] <;> nomega)) (hG.mono (by nomega)) (hφr _ (Agree.upd_self j hi))
        · exact mkE_ren_eq hθ.upd_at (by rw [hτc τ hτ]) (hφr θ (hθ.upd_below hi))
            (by simp [EventKind.ren, Expr.ren_val, Expr.glob, hθ.upd_at])
    | loadPtr o r p =>
        rw [interp.eq_def n₁ ctx pc, interp.eq_def n₂ _ pc]
        refine mk (fun i j hi => map ?_ (fun θ τ k₁ k₂ hθ hτ hk => Embeds.prefix ?_ hk))
        · exact hκ.app (by nomega) (Nat.le_refl _) (Agree.upd_self j hi) (Agree.refl _ _)
            ((hρu i j hi).set r (by simp [Expr.ren_sym, upd])) ((hB.mono (by nomega)).set r
              (by simp [Expr.syms] <;> nomega)) (hG.mono (by nomega)) (hφr _ (Agree.upd_self j hi))
        · exact mkE_ren_eq hθ.upd_at (by rw [hτc τ hτ]) (hφr θ (hθ.upd_below hi))
            (by simp [EventKind.ren, hθ.upd_at, hden θ (hθ.upd_below hi)])
    | store o x v =>
        rw [interp.eq_def n₁ ctx pc, interp.eq_def n₂ _ pc]
        refine mk (fun i j hi => map ?_ (fun θ τ k₁ k₂ hθ hτ hk => Embeds.prefix ?_ hk))
        · exact hκ.app (by nomega) (Nat.le_refl _) (Agree.upd_self j hi) (Agree.refl _ _)
            (hρu i j hi) (hB.mono (by nomega)) (hG.mono (by nomega)) (hφr _ (Agree.upd_self j hi))
        · exact mkE_ren_eq hθ.upd_at (by rw [hτc τ hτ]) (hφr θ (hθ.upd_below hi))
            (by simp [EventKind.ren, Expr.ren_val, Expr.glob, hden θ (hθ.upd_below hi)])
    | storePtr o p v =>
        rw [interp.eq_def n₁ ctx pc, interp.eq_def n₂ _ pc]
        refine mk (fun i j hi => map ?_ (fun θ τ k₁ k₂ hθ hτ hk => Embeds.prefix ?_ hk))
        · exact hκ.app (by nomega) (Nat.le_refl _) (Agree.upd_self j hi) (Agree.refl _ _)
            (hρu i j hi) (hB.mono (by nomega)) (hG.mono (by nomega)) (hφr _ (Agree.upd_self j hi))
        · exact mkE_ren_eq hθ.upd_at (by rw [hτc τ hτ]) (hφr θ (hθ.upd_below hi))
            (by simp [EventKind.ren, hden θ (hθ.upd_below hi)])
    | fence o =>
        rw [interp.eq_def n₁ ctx pc, interp.eq_def n₂ _ pc]
        refine mk (fun i j hi => map ?_ (fun θ τ k₁ k₂ hθ hτ hk => Embeds.prefix ?_ hk))
        · exact hκ.app (by nomega) (Nat.le_refl _) (Agree.upd_self j hi) (Agree.refl _ _)
            (hρu i j hi) (hB.mono (by nomega)) (hG.mono (by nomega)) (hφr _ (Agree.upd_self j hi))
        · exact mkE_ren_eq hθ.upd_at (by rw [hτc τ hτ]) (hφr θ (hθ.upd_below hi)) (by simp [EventKind.ren])
    | malloc r sz =>
        rw [interp.eq_def n₁ ctx pc, interp.eq_def n₂ _ pc]
        refine mk (fun i j hi => map ?_ (fun θ τ k₁ k₂ hθ hτ hk => Embeds.prefix ?_ hk))
        · exact hκ.app (by nomega) (Nat.le_refl _) (Agree.upd_self j hi) (Agree.refl _ _)
            ((hρu i j hi).set r (by simp [Expr.ren_sym, upd])) ((hB.mono (by nomega)).set r
              (by simp [Expr.syms] <;> nomega)) (hG.mono (by nomega)) (hφr _ (Agree.upd_self j hi))
        · exact mkE_ren_eq hθ.upd_at (by rw [hτc τ hτ]) (hφr θ (hθ.upd_below hi))
            (by simp [EventKind.ren, hθ.upd_at, hden θ (hθ.upd_below hi)])
    | free r =>
        rw [interp.eq_def n₁ ctx pc, interp.eq_def n₂ _ pc]
        refine mk (fun i j hi => map ?_ (fun θ τ k₁ k₂ hθ hτ hk => Embeds.prefix ?_ hk))
        · exact hκ.app (by nomega) (Nat.le_refl _) (Agree.upd_self j hi) (Agree.refl _ _)
            (hρu i j hi) (hB.mono (by nomega)) (hG.mono (by nomega)) (hφr _ (Agree.upd_self j hi))
        · refine mkE_ren_eq hθ.upd_at (by rw [hτc τ hτ]) (hφr θ (hθ.upd_below hi)) ?_
          simp only [EventKind.ren]
          rw [hρ r]
          exact congrArg _ (Expr.ren_congr _ (fun α hα => (hθ.upd_below hi) α (hB r α hα)))
    | fadd or ow r x v =>
        rw [interp.eq_def n₁ ctx pc, interp.eq_def n₂ _ pc]
        refine mk (fun i j hi => mk (fun i' j' hi' => map ?_
          (fun θ τ k₁ k₂ hθ hτ hk => Embeds.addRMW (Embeds.prefix ?_ (Embeds.prefix ?_ hk)) ?_ ?_ ?_)))
        · have ha : Agree (upd (upd θ₀ i j) i' j') θ₀ bI :=
            (Agree.upd_self j' hi').trans (Agree.upd_self j hi) (by nomega)
          exact hκ.app (by nomega) (Nat.le_refl _) ha (Agree.refl _ _)
            ((hρ.congr hB ha).set r (by simp [Expr.ren_sym, upd] <;> nomega))
            ((hB.mono (by nomega)).set r (by simp [Expr.syms] <;> nomega)) (hG.mono (by nomega))
            (hφr _ ha)
        all_goals
          have hθ' := hθ.upd_below hi'
          have hθ₀ := hθ'.upd_below hi
          have hi₁ := hθ'.upd_at
          have hi₂ := hθ.upd_at
        · exact mkE_ren_eq hi₁ (by rw [hτc τ hτ]) (hφr θ hθ₀)
            (by simp [EventKind.ren, Expr.ren_val, Expr.glob, hi₁])
        · exact mkE_ren_eq hi₂ (by rw [hτc τ hτ]) (hφr θ hθ₀)
            (by simp [EventKind.ren, Expr.glob, Expr.ren, Expr.rename, hi₁,
                  ← hden θ hθ₀ v])
        · exact hi₁
        · exact hi₂
        · rfl
    | cas or ow r x e₁ e₂ =>
        rw [interp.eq_def n₁ ctx pc, interp.eq_def n₂ _ pc]
        dsimp only
        refine mk (fun i j hi => mk (fun i' j' hi' => mk (fun i'' j'' hi'' => seq2 ?_ ?_
          (fun θ τ k₁ k₂ k₁' k₂' hθ hτ hk hk' => Embeds.addRMW (Embeds.prefix ?_
            (Embeds.prefix ?_ (Embeds.plus (Embeds.prefix ?_ hk) hk'))) ?_ ?_ ?_))))
        · have ha : Agree (upd (upd (upd θ₀ i j) i' j') i'' j'') θ₀ bI :=
            ((Agree.upd_self j'' hi'').trans (Agree.upd_self j' hi') (by nomega)).trans
              (Agree.upd_self j hi) (by nomega)
          refine hκ.app (by nomega) (Nat.le_refl _) ha (Agree.refl _ _)
            ((hρ.congr hB ha).set r rfl) ((hB.mono (by nomega)).set r (by simp [Expr.tt, Expr.syms]))
            ((hG.mono (by nomega)).snoc (by nomega) ?_) ?_
          · intro α hα
            simp only [Expr.syms, List.mem_append, List.mem_singleton] at hα
            rcases hα with rfl | hα
            · nomega
            · have := PExpr.den_below hB e₁ α hα; nomega
          · simp only [List.map_append, List.map_cons, List.map_nil, Guard.ren_mk, hφr _ ha]
            simp [upd, Expr.ren, Expr.rename, ← hden _ ha e₁]
            exact ⟨fun h => absurd h (by nomega), by rw [if_neg (by nomega), if_neg (by nomega)]⟩
        · intro θ τ b b' hb hb' hθ hτ
          have ha : Agree θ θ₀ bI :=
            ((hθ.upd_below hi'').upd_below hi').upd_below hi
          have hθi : θ i = j := ((hθ.upd_below hi'').upd_below hi').upd_at
          have hθi' : θ i' = j' := (hθ.upd_below hi'').upd_at
          refine hκ.app (by nomega) hb' ha hτ ((hρ.congr hB ha).set r rfl)
            ((hB.mono (by nomega)).set r (by simp [Expr.ff, Expr.syms]))
            ((hG.mono (by nomega)).snoc (by nomega) ?_) ?_
          · intro α hα
            simp only [Expr.syms, List.mem_append, List.mem_singleton] at hα
            rcases hα with rfl | hα
            · nomega
            · have := PExpr.den_below hB e₁ α hα; nomega
          · simp only [List.map_append, List.map_cons, List.map_nil, Guard.ren_mk, hφr _ ha]
            simp [Expr.ren, Expr.rename, hθi, hθi', ← hden _ ha e₁]
        all_goals
          have h₃ := hθ.upd_below hi''
          have h₂ := h₃.upd_below hi'
          have hθ₀ := h₂.upd_below hi
          have hi₁ := h₂.upd_at
          have hi₂ := h₃.upd_at
          have hi₃ := hθ.upd_at
        · exact mkE_ren_eq hi₁ (by rw [hτc τ hτ]) (hφr θ hθ₀)
            (by simp [EventKind.ren, Expr.ren_val, Expr.glob, hi₁])
        · exact mkE_ren_eq hi₂ (by rw [hτc τ hτ]) (hφr θ hθ₀)
            (by simp [EventKind.ren, Expr.ren, Expr.rename, hi₁, ← hden θ hθ₀ e₁])
        · refine mkE_ren_eq hi₃ (by rw [hτc τ hτ]) ?_
            (by simp [EventKind.ren, Expr.ren_val, Expr.glob, hden θ hθ₀ e₂])
          simp only [List.map_append, List.map_cons, List.map_nil, Guard.ren_mk, hφr θ hθ₀]
          simp [Expr.ren, Expr.rename, hi₁, hi₂, ← hden θ hθ₀ e₁]
        · exact hi₁
        · exact hi₃
        · simp [Expr.ren, Expr.rename, hi₁, ← hden θ hθ₀ e₁]
    | seq s₁ s₂ =>
        rw [interp.eq_def n₁ ctx pc, interp.eq_def n₂ _ pc]
        simp only [Stmt.loops, sumB_append, Stmt.seq.sizeOf_spec] at hN
        refine interp_sim N s₁ n₁ n₂ ctx _ (pc ++ [0]) ρ₁ ρ₂ φ _ _ _ θ₀ τ₀ bI bT (by nomega) hn rfl rfl
          hρ hB hG hthr ?_ ?_
        · intro θ τ b b' ρ₁' ρ₂' φ' hb hb' hθ hτ hρ' hB' hG'
          exact interp_sim N s₂ n₁ n₂ ctx _ (pc ++ [1]) ρ₁' ρ₂' φ' _ κ₁ κ₂ θ τ b b' (by nomega) hn
            (by rw [hτc τ hτ]) rfl hρ' hB' hG' (by nomega) (hκ.mono hb hb' hθ hτ) hfr
        · exact fun ρ' φ' => interp_fresh _ n₂ _ _ s₂ ρ' κ₂ φ' (Nat.lt_succ_self _) hfr
    | par s₁ s₂ =>
        rw [interp.eq_def n₁ ctx pc, interp.eq_def n₂ _ pc]
        simp only [Stmt.loops, sumB_append, Stmt.par.sizeOf_spec] at hN
        refine thread (fun t₁ t₂ ht => seq2 ?_ ?_ (fun θ τ k₁ k₂ k₁' k₂' _ _ hk hk' => Embeds.plus hk hk'))
        · have hτu : Agree (upd τ₀ t₁ t₂) τ₀ bT := Agree.upd_self t₂ ht
          exact interp_sim N s₁ n₁ n₂ ctx _ (pc ++ [0]) ρ₁ ρ₂ φ _ κ₁ κ₂ θ₀ (upd τ₀ t₁ t₂) bI (t₁ + 1)
            (by nomega) hn (by rw [hτu ctx.thread hthr]) rfl hρ hB hG (by nomega)
            (hκ.mono (Nat.le_refl _) (by nomega) (Agree.refl _ _) hτu) hfr
        · intro θ τ b b' hb hb' hθ hτ
          exact interp_sim N s₂ n₁ n₂ { ctx with thread := t₁ } _ (pc ++ [1]) ρ₁ ρ₂ φ _ κ₁ κ₂ θ τ b b'
            (by nomega) hn (by simp [hτ.upd_at]) (hφr θ hθ).symm (hρ.congr hB hθ) (hB.mono hb)
            (hG.mono hb) (by simp <;> nomega)
            (hκ.mono hb (by nomega) hθ (hτ.upd_below ht)) hfr
    | ite b s₁ s₂ =>
        rw [interp.eq_def n₁ ctx pc, interp.eq_def n₂ _ pc]
        simp only [Stmt.loops, sumB_append, Stmt.ite.sizeOf_spec] at hN
        refine mk (fun i j hi => seq2 ?_ ?_
          (fun θ τ k₁ k₂ k₁' k₂' hθ hτ hk hk' => Embeds.prefix ?_ (Embeds.plus hk hk')))
        · have ha := Agree.upd_self (θ₀ := θ₀) j hi
          refine interp_sim N s₁ n₁ n₂ ctx _ (pc ++ [0]) ρ₁ ρ₂ _ _ κ₁ κ₂ _ τ₀ (i + 1) bT (by nomega) hn
            rfl ?_ (hρu i j hi) (hB.mono (by nomega))
            ((hG.mono (by nomega)).snoc (by nomega)
              (fun α hα => by have := PExpr.den_below hB b α hα <;> nomega)) hthr
            (hκ.mono (by nomega) (Nat.le_refl _) ha (Agree.refl _ _)) hfr
          simp only [List.map_append, List.map_cons, List.map_nil, Guard.ren_mk, hφr _ ha,
            hden _ ha b]
          simp [upd]
        · intro θ τ b' b'' hb hb' hθ hτ
          have ha : Agree θ θ₀ bI := hθ.upd_below hi
          refine interp_sim N s₂ n₁ n₂ ctx _ (pc ++ [1]) ρ₁ ρ₂ _ _ κ₁ κ₂ θ τ b' b'' (by nomega) hn
            (by rw [hτc τ hτ]) ?_ (hρ.congr hB ha) (hB.mono (by nomega))
            ((hG.mono (by nomega)).snoc (by nomega)
              (fun α hα => by have := PExpr.den_below hB b α hα <;> nomega)) (by nomega)
            (hκ.mono (by nomega) hb' ha hτ) hfr
          simp only [List.map_append, List.map_cons, List.map_nil, Guard.ren_mk, hφr _ ha,
            hden _ ha b, mkE_id, hθ.upd_at]
        · exact mkE_ren_eq hθ.upd_at (by rw [hτc τ hτ]) (hφr θ (hθ.upd_below hi))
            (by simp [EventKind.ren, hden θ (hθ.upd_below hi)])
    | «while» ℓ b body =>
        by_cases h₁ : n₁ ℓ = 0
        · rw [interp.eq_def n₁ ctx pc]
          dsimp only
          rw [dif_pos h₁]
          exact empty (interp_fresh _ n₂ _ _ _ ρ₂ κ₂ _ (Nat.lt_succ_self _) hfr)
        · have h₂ : ¬ n₂ ℓ = 0 := by have := hn ℓ; nomega
          rw [interp.eq_def n₁ ctx pc, interp.eq_def n₂ _ pc]
          dsimp only
          rw [dif_neg h₁, dif_neg h₂]
          simp only [Stmt.loops, sumB_cons, Stmt.while.sizeOf_spec] at hN
          have hd₁ := sumB_dec_le body.loops n₁ ℓ
          have hd₂ := Bounds.dec_self n₁ ℓ
          refine mk (fun i j hi => seq2 ?_ ?_
            (fun θ τ k₁ k₂ k₁' k₂' hθ hτ hk hk' => Embeds.prefix ?_ (Embeds.plus hk hk')))
          · have ha := Agree.upd_self (θ₀ := θ₀) j hi
            refine interp_sim N body (n₁.dec ℓ) (n₂.dec ℓ) _ _ (pc ++ [0]) ρ₁ ρ₂ _ _ _ _ _ τ₀ (i + 1) bT
              (by nomega) (Bounds.dec_mono hn ℓ)
              (Ctx.enter_retag ctx _ _ (by rw [Ctx.enter_thread_eq])).symm ?_ (hρu i j hi)
              (hB.mono (by nomega))
              ((hG.mono (by nomega)).snoc (by nomega)
                (fun α hα => by have := PExpr.den_below hB b α hα <;> nomega))
              (by simp only [Ctx.enter_thread_eq]; exact hthr) ?_ ?_
            · simp only [List.map_append, List.map_cons, List.map_nil, Guard.ren_mk, hφr _ ha,
                hden _ ha b]
              simp [upd]
            · intro θ τ c c' ρ₁' ρ₂' φ' hc hc' hθ hτ hρ' hB' hG'
              exact interp_sim N (.while ℓ b body) (n₁.dec ℓ) (n₂.dec ℓ) _ _ pc ρ₁' ρ₂' φ' _ κ₁ κ₂ θ τ
                c c' (by simp only [Stmt.loops, sumB_cons, Stmt.while.sizeOf_spec] <;> nomega)
                (Bounds.dec_mono hn ℓ)
                (Ctx.enter_retag ctx _ _ (by rw [Ctx.enter_thread_eq, hτ ctx.thread (by nomega)])).symm
                rfl hρ' hB' hG'
                (by rw [Ctx.enter_thread_eq]; nomega)
                (hκ.mono (by nomega) (by nomega) (hθ.trans ha (by nomega)) hτ) hfr
            · exact fun ρ' φ' => interp_fresh _ _ _ _ _ ρ' κ₂ φ' (Nat.lt_succ_self _) hfr
          · intro θ τ c c' hc hc' hθ hτ
            have ha : Agree θ θ₀ bI := hθ.upd_below hi
            refine hκ.app (by nomega) hc' ha hτ (hρ.congr hB ha) (hB.mono (by nomega))
              ((hG.mono (by nomega)).snoc (by nomega)
                (fun α hα => by have := PExpr.den_below hB b α hα <;> nomega)) ?_
            simp only [List.map_append, List.map_cons, List.map_nil, Guard.ren_mk, hφr _ ha,
              hden _ ha b, mkE_id, hθ.upd_at]
          · refine mkE_ren_eq hθ.upd_at ?_ (hφr θ (hθ.upd_below hi))
              (by simp [EventKind.ren, hden θ (hθ.upd_below hi)])
            exact Ctx.enter_retag ctx _ _ (by rw [Ctx.enter_thread_eq]; exact hτc τ hτ)

/-! ## Lemma `l:es-mono` -/

/-- **Monotonicity in the step-counter.** Under per-loop step-counters
    `n₁ ≤ n₂`, `⟨P⟩_{n₁}` embeds into `⟨P⟩_{n₂}`: there are renamings of ids
    and threads, injective on the ids of `⟨P⟩_{n₁}`, carrying its events --
    actions, labels and value restrictions -- program order and
    read-modify-write entries into `⟨P⟩_{n₂}`. -/
theorem denote_mono (P : Stmt) (n₁ n₂ : Bounds) (h : ∀ ℓ, n₁ ℓ ≤ n₂ ℓ) :
    ∃ θ τ, (∀ a ∈ (denote n₁ P).ids, ∀ b ∈ (denote n₁ P).ids, θ a = θ b → a = b) ∧
      Embeds θ τ (denote n₁ P) (denote n₂ P) := by
  have hsim := interp_sim _ P n₁ n₂ ⟨0, []⟩ ⟨0, []⟩ [] [] [] [] [] (fun _ _ => pure .empty)
    (fun _ _ => pure .empty) id id 0 1 (Nat.lt_succ_self _) h rfl rfl (fun _ => rfl)
    (fun r α hα => by simp [RegState.get, Expr.num, Expr.syms] at hα) (fun g hg => by simp at hg)
    (by decide)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => Sim.empty Gen.Fresh.pure_empty)
    (fun _ _ => Gen.Fresh.pure_empty)
  obtain ⟨_, _, _, θ, τ, _, _, hmap, hemb⟩ := hsim {} {} (Nat.le_refl _) (Nat.le_refl _)
  have hfr := interp_fresh _ n₁ ⟨0, []⟩ [] P [] (fun _ _ => pure .empty) [] (Nat.lt_succ_self _)
    (fun _ _ => Gen.Fresh.pure_empty) {}
  refine ⟨θ, τ, fun a ha b hb hab => hmap.2 a b (hfr.2.2 a ha).1 (hfr.2.2 a ha).2
    (hfr.2.2 b hb).1 (hfr.2.2 b hb).2 hab, hemb θ τ (Agree.refl _ _) (Agree.refl _ _)⟩

/-- `𝔼_n ⊆ 𝔼_{n+1}` for the uniform step-counters of Lemma `l:es-mono`. -/
theorem denote_mono_succ (P : Stmt) (n : Nat) :
    ∃ θ τ, (∀ a ∈ (denote (.uniform n) P).ids, ∀ b ∈ (denote (.uniform n) P).ids,
        θ a = θ b → a = b) ∧
      Embeds θ τ (denote (.uniform n) P) (denote (.uniform (n + 1)) P) :=
  denote_mono P _ _ (fun _ => Nat.le_succ n)
