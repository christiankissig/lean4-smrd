import Smrd.Fresh
import Smrd.DPPast

/-!
# The semantics introduces symbols before their uses (`denote_symWF`)

`⟨P⟩_n` is `SymWF`: every symbol of an event's value restriction and
expressions is the id of an event `⊑`-before it, and a read introduces its own
id. With `Smrd.DPPast` this makes `DP ⊆ ⊑` a consequence of the forwarding
window and `LiftPast` alone, for the event structures of programs.

The proof follows `interp_inv` (`Smrd.Fresh`), but the invariant is relative
to the symbols `A` in scope: the registers and the guards may mention symbols
of events generated before, which the continuation's events see as `⊑`-earlier
through `prefix`.
-/

namespace SymWFDenote

open EventStructure

/-- `k`'s events depend only on symbols in `A` or on `⊑`-earlier events of `k`,
    and reads and allocations introduce their own ids. -/
def Good (A : Sym → Prop) (k : EventStructure) : Prop :=
  ∀ e ∈ k.events, (∀ α ∈ e.depSyms, A α ∨ (α, e.id) ∈ k.po) ∧
    (∀ o l α v, e.kind = .read o l α v → α = e.id)

def HoldsA (A : Sym → Prop) (m : Gen EventStructure) : Prop :=
  ∀ σ : GenState, Good A (m.run σ).1

/-- The symbols of the registers and the guards are in `A`. -/
def SymsIn (A : Sym → Prop) (ρ : RegState) (φ : List Guard) : Prop :=
  (∀ p ∈ ρ, ∀ α ∈ p.2.syms, A α) ∧ (∀ g ∈ φ, ∀ α ∈ g.cond.syms, A α)

theorem Good.mono {A B : Sym → Prop} (hAB : ∀ α, A α → B α) {k : EventStructure}
    (h : Good A k) : Good B k := fun e he =>
  ⟨fun α hα => (h e he).1 α hα |>.imp (hAB α) id, (h e he).2⟩

theorem good_empty (A : Sym → Prop) : Good A .empty := fun _ he => by cases he

theorem Good.plus {A : Sym → Prop} {k₁ k₂ : EventStructure} (h₁ : Good A k₁) (h₂ : Good A k₂) :
    Good A (k₁.plus k₂) := by
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact ⟨fun α hα => ((h₁ e he).1 α hα).imp id (fun h => List.mem_append_left _ h), (h₁ e he).2⟩
  · exact ⟨fun α hα => ((h₂ e he).1 α hα).imp id (fun h => List.mem_append_right _ h), (h₂ e he).2⟩

theorem Good.join {A : Sym → Prop} {k₁ k₂ : EventStructure} (h₁ : Good A k₁) (h₂ : Good A k₂) :
    Good A (k₁.join k₂) := by
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact ⟨fun α hα => ((h₁ e he).1 α hα).imp id
      (fun h => List.mem_append_left _ (List.mem_append_left _ h)), (h₁ e he).2⟩
  · exact ⟨fun α hα => ((h₂ e he).1 α hα).imp id
      (fun h => List.mem_append_left _ (List.mem_append_right _ h)), (h₂ e he).2⟩

theorem Good.addRMW {A : Sym → Prop} {k : EventStructure} (h : Good A k) (r : EventId) (c : Expr)
    (w : EventId) : Good A (k.addRMW r c w) := h

theorem Good.prefix {A : Sym → Prop} {e : Event} {k : EventStructure}
    (hd : ∀ α ∈ e.depSyms, A α) (hr : ∀ o l α v, e.kind = .read o l α v → α = e.id)
    (hk : Good (fun α => A α ∨ α = e.id) k) : Good A («prefix» e k) := by
  intro e' he'
  rcases List.mem_cons.1 he' with rfl | he'
  · exact ⟨fun α hα => .inl (hd α hα), hr⟩
  · refine ⟨fun α hα => ?_, (hk e' he').2⟩
    rcases (hk e' he').1 α hα with (h | rfl) | h
    · exact .inl h
    · exact .inr (List.mem_append_left _ (List.mem_map.2 ⟨e', he', rfl⟩))
    · exact .inr (List.mem_append_right _ h)

theorem mem_of_lookup {ρ : RegState} {r : Reg} {v : Expr} (h : ρ.lookup r = some v) :
    (r, v) ∈ ρ := by
  induction ρ with
  | nil => cases h
  | cons p ρ ih =>
      obtain ⟨k, b⟩ := p
      simp only [List.lookup] at h
      split at h
      · rename_i heq
        cases h
        have : r = k := by simpa using heq
        subst this; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

theorem mem_syms_den {ρ : RegState} {α : Sym} :
    ∀ {p : PExpr}, α ∈ (p.den ρ).syms → ∃ q ∈ ρ, α ∈ q.2.syms := by
  intro p
  induction p with
  | reg r =>
      intro h
      simp only [PExpr.den, RegState.get] at h
      cases hl : ρ.lookup r with
      | none => rw [hl] at h; simp [Expr.num, Expr.syms] at h
      | some v =>
          rw [hl] at h
          have hm := mem_of_lookup hl
          exact ⟨(r, v), hm, h⟩
  | num n => intro h; simp [PExpr.den, Expr.num, Expr.syms] at h
  | bin op a b iha ihb | eq a b iha ihb | le a b iha ihb | and a b iha ihb | or a b iha ihb =>
      intro h; simp only [PExpr.den, Expr.syms, List.mem_append] at h
      rcases h with h | h
      · exact iha h
      · exact ihb h
  | not a iha => intro h; simp only [PExpr.den, Expr.syms] at h; exact iha h

theorem SymsIn.den {A : Sym → Prop} {ρ : RegState} {φ : List Guard} (h : SymsIn A ρ φ)
    (p : PExpr) : ∀ α ∈ (p.den ρ).syms, A α := fun α hα => by
  obtain ⟨q, hq, hα⟩ := mem_syms_den hα
  exact h.1 q hq α hα

theorem SymsIn.get {A : Sym → Prop} {ρ : RegState} {φ : List Guard} (h : SymsIn A ρ φ)
    (r : Reg) : ∀ α ∈ (ρ.get r).syms, A α := h.den (.reg r)

theorem SymsIn.mono {A B : Sym → Prop} (hAB : ∀ α, A α → B α) {ρ : RegState} {φ : List Guard}
    (h : SymsIn A ρ φ) : SymsIn B ρ φ :=
  ⟨fun p hp α hα => hAB α (h.1 p hp α hα), fun g hg α hα => hAB α (h.2 g hg α hα)⟩

theorem SymsIn.set {A : Sym → Prop} {ρ : RegState} {φ : List Guard} (h : SymsIn A ρ φ)
    (r : Reg) (v : Expr) (hv : ∀ α ∈ v.syms, A α) : SymsIn A (ρ.set r v) φ := by
  refine ⟨fun p hp α hα => ?_, h.2⟩
  rcases List.mem_cons.1 hp with rfl | hp
  · exact hv α hα
  · exact h.1 p hp α hα

theorem SymsIn.guard {A : Sym → Prop} {ρ : RegState} {φ : List Guard} (h : SymsIn A ρ φ)
    (g : Guard) (hg : ∀ α ∈ g.cond.syms, A α) : SymsIn A ρ (φ ++ [g]) := by
  refine ⟨h.1, fun g' hg' α hα => ?_⟩
  rcases List.mem_append.1 hg' with hg' | hg'
  · exact h.2 g' hg' α hα
  · simp only [List.mem_singleton] at hg'; subst hg'; exact hg α hα

theorem SymsIn.valres {A : Sym → Prop} {ρ : RegState} {φ : List Guard} (h : SymsIn A ρ φ)
    (e : Event) (he : e.guards = φ) : ∀ α ∈ e.valres.syms, A α := by
  intro α hα
  simp only [Event.valres, he] at hα
  obtain ⟨c, hc, hα⟩ := (Expr.mem_syms_conj _ α).1 hα
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hc
  unfold Guard.expr at hα
  split at hα
  · exact h.2 g hg α hα
  · exact h.2 g hg α (by simpa [Expr.syms] using hα)

/-- One event `mkE … i` whose expressions' symbols are in `A`, prefixed to a
    continuation that holds with the event's own id in scope. -/
theorem mk_prefix {A : Sym → Prop} {ρ : RegState} (ctx : Ctx) (pc : List Nat) (φ : List Guard)
    (kind : EventId → EventKind) (m : Event → Gen EventStructure) (hφ : SymsIn A ρ φ)
    (hx : ∀ i, ∀ α ∈ (mkE ctx pc φ kind i).exprSyms, A α)
    (hr : ∀ i o l α v, kind i = .read o l α v → α = i)
    (hm : ∀ e, HoldsA (fun α => A α ∨ α = e.id) (m e)) :
    HoldsA A (do let e ← mkEvent ctx pc φ kind; let k ← m e; pure («prefix» e k)) := by
  intro σ
  exact Good.prefix (fun α hα => by
      rcases List.mem_append.1 hα with h | h
      · exact hφ.valres _ rfl α h
      · exact hx σ.nextId α h)
    (fun o l α v h => hr σ.nextId o l α v h) (hm _ _)

/-- The continuation hypothesis: `κ` holds for every larger scope. -/
def KOK (A : Sym → Prop) (κ : Cont) : Prop :=
  ∀ (B : Sym → Prop), (∀ α, A α → B α) → ∀ ρ φ, SymsIn B ρ φ → HoldsA B (κ ρ φ)

theorem KOK.mono {A B : Sym → Prop} (hAB : ∀ α, A α → B α) {κ : Cont} (h : KOK A κ) : KOK B κ :=
  fun C hBC => h C (fun α hα => hBC α (hAB α hα))

theorem ext_left {A : Sym → Prop} {i : EventId} : ∀ α, A α → A α ∨ α = i := fun _ h => .inl h

open EventStructure in
theorem interp_good :
    ∀ (N : Nat) (n : Bounds) (ctx : Ctx) (pc : List Nat) (s : Stmt)
    (ρ : RegState) (κ : Cont) (φ : List Guard) (A : Sym → Prop),
    sumB s.loops n + sizeOf s < N → SymsIn A ρ φ → KOK A κ →
    HoldsA A (interp n ctx pc s ρ κ φ)
  | 0, _, _, _, _, _, _, _, _, hN, _, _ => absurd hN (Nat.not_lt_zero _)
  | N + 1, n, ctx, pc, s, ρ, κ, φ, A, hN, hS, hκ => by
    -- a store-like event: no symbol introduced, continuation at the same `ρ`
    have noRead : ∀ (k : EventId → EventKind), (∀ i, ∀ o l α v, k i ≠ .read o l α v) →
        ∀ i o l α v, k i = .read o l α v → α = i := fun k hk i o l α v h => absurd h (hk i o l α v)
    cases s with
    | skip => rw [interp.eq_def]; exact hκ A (fun _ h => h) ρ φ hS
    | assign r e =>
        rw [interp.eq_def]; exact hκ A (fun _ h => h) _ φ (hS.set r _ (hS.den e))
    | addrOf r x =>
        rw [interp.eq_def]
        exact hκ A (fun _ h => h) _ φ (hS.set r _ (by simp [Expr.glob, Expr.syms]))
    | load o r x vl =>
        rw [interp.eq_def]
        refine mk_prefix ctx pc φ _ _ hS (fun i α h => by simp [mkE, Event.exprSyms, Expr.glob, Expr.syms] at h)
          (fun i o' l α v h => by cases h; rfl) (fun e => ?_)
        exact hκ _ ext_left _ φ ((hS.mono ext_left).set r _ (by simp [Expr.syms]))
    | loadPtr o r p vl =>
        rw [interp.eq_def]
        refine mk_prefix ctx pc φ _ _ hS (fun i α h => hS.den p α (by simpa [mkE, Event.exprSyms] using h))
          (fun i o' l α v h => by cases h; rfl) (fun e => ?_)
        exact hκ _ ext_left _ φ ((hS.mono ext_left).set r _ (by simp [Expr.syms]))
    | store o x v vl =>
        rw [interp.eq_def]
        refine mk_prefix ctx pc φ _ _ hS (fun i α h => ?_)
          (noRead _ (fun i o l α v h => by cases h)) (fun e => hκ _ ext_left ρ φ (hS.mono ext_left))
        simp only [mkE, Event.exprSyms, Expr.glob, Expr.syms, List.nil_append] at h
        exact hS.den v α h
    | storePtr o p v vl =>
        rw [interp.eq_def]
        refine mk_prefix ctx pc φ _ _ hS (fun i α h => ?_)
          (noRead _ (fun i o l α v h => by cases h)) (fun e => hκ _ ext_left ρ φ (hS.mono ext_left))
        simp only [mkE, Event.exprSyms, List.mem_append] at h
        rcases h with h | h
        · exact hS.den p α h
        · exact hS.den v α h
    | fence o =>
        rw [interp.eq_def]
        exact mk_prefix ctx pc φ _ _ hS (fun i α h => by simp [mkE, Event.exprSyms] at h)
          (noRead _ (fun i o l α v h => by cases h)) (fun e => hκ _ ext_left ρ φ (hS.mono ext_left))
    | malloc r sz =>
        rw [interp.eq_def]
        refine mk_prefix ctx pc φ _ _ hS (fun i α h => hS.den sz α (by simpa [mkE, Event.exprSyms] using h))
          (noRead _ (fun i o l α v h => by cases h)) (fun e => ?_)
        exact hκ _ ext_left _ φ ((hS.mono ext_left).set r _ (by simp [Expr.syms]))
    | free r =>
        rw [interp.eq_def]
        exact mk_prefix ctx pc φ _ _ hS (fun i α h => hS.get r α (by simpa [mkE, Event.exprSyms] using h))
          (noRead _ (fun i o l α v h => by cases h)) (fun e => hκ _ ext_left ρ φ (hS.mono ext_left))
    | fadd or ow r x v =>
        rw [interp.eq_def]
        intro σ
        refine Good.addRMW (Good.prefix (fun α hα => ?_) (fun o l α v h => by cases h; rfl)
          (Good.prefix (fun α hα => ?_) (fun o l α v h => by cases h)
            (hκ _ (fun α h => .inl (.inl h)) _ φ ?_ _))) _ _ _
        · rcases List.mem_append.1 hα with h | h
          · exact hS.valres _ rfl α h
          · simp [Event.exprSyms, Expr.glob, Expr.syms] at h
        · rcases List.mem_append.1 hα with h | h
          · exact .inl (hS.valres _ rfl α h)
          · simp only [Event.exprSyms, Expr.glob, Expr.syms, List.nil_append, List.mem_append,
              List.mem_singleton] at h
            rcases h with h | h
            · exact .inr h
            · exact .inl (hS.den v α h)
        · refine ((hS.mono (fun α h => .inl (.inl h))).set r _ ?_)
          intro α h; simp only [Expr.syms, List.mem_singleton] at h; exact .inl (.inr h)
    | cas or ow r x e₁ e₂ =>
        rw [interp.eq_def]
        intro σ
        -- scopes: A, A ∪ {er}, then the branch and the write add none
        have hA1 : SymsIn (fun α => A α ∨ α = σ.nextId) ρ φ := hS.mono ext_left
        have hc : ∀ α ∈ (Expr.eq (.sym σ.nextId) (e₁.den ρ)).syms, A α ∨ α = σ.nextId := by
          intro α h
          simp only [Expr.syms, List.mem_append, List.mem_singleton] at h
          rcases h with h | h
          · exact .inr h
          · exact .inl (hS.den e₁ α h)
        refine Good.addRMW (Good.prefix (fun α hα => ?_) (fun o l α v h => by cases h; rfl)
          (Good.prefix (fun α hα => ?_) (fun o l α v h => by cases h)
            (Good.plus
              (Good.prefix (fun α hα => ?_) (fun o l α v h => by cases h)
                (hκ _ (fun α h => .inl (.inl (.inl h))) _ _ ?_ _))
              (hκ _ (fun α h => .inl (.inl h)) _ _ ?_ _)))) _ _ _
        · rcases List.mem_append.1 hα with h | h
          · exact hS.valres _ rfl α h
          · simp [Event.exprSyms, Expr.glob, Expr.syms] at h
        · rcases List.mem_append.1 hα with h | h
          · exact hA1.valres _ rfl α h
          · simp [Event.exprSyms] at h
        · rcases List.mem_append.1 hα with h | h
          · exact .inl ((hA1.guard _ hc).valres _ rfl α h)
          · simp only [Event.exprSyms, Expr.glob, Expr.syms, List.nil_append] at h
            exact .inl (.inl (hS.den e₂ α h))
        · exact ((hA1.guard _ hc).mono (fun α h => .inl (.inl h))).set r _
            (by simp [Expr.tt, Expr.syms])
        · exact ((hA1.guard _ hc).mono (fun α h => .inl h)).set r _
            (by simp [Expr.ff, Expr.syms])
    | seq s₁ s₂ =>
        rw [interp.eq_def]
        simp only [Stmt.loops, sumB_append, Stmt.seq.sizeOf_spec] at hN
        exact interp_good N n ctx (pc ++ [0]) s₁ ρ _ φ A (by omega) hS
          (fun B hAB ρ' φ' hS' => interp_good N n ctx (pc ++ [1]) s₂ ρ' κ φ' B (by omega) hS'
            (hκ.mono hAB))
    | par s₁ s₂ =>
        rw [interp.eq_def]
        simp only [Stmt.loops, sumB_append, Stmt.par.sizeOf_spec] at hN
        intro σ
        -- the threads end in the empty continuation; `κ` runs once, after both
        exact Good.join (Good.plus
          (interp_good N n ctx (pc ++ [0]) s₁ ρ _ φ A (by omega) hS
            (fun _ _ _ _ _ _ => good_empty _) _)
          (interp_good N n _ (pc ++ [1]) s₂ ρ _ φ A (by omega) hS
            (fun _ _ _ _ _ _ => good_empty _) _))
          (hκ A (fun _ h => h) ρ φ hS _)
    | ite b s₁ s₂ =>
        rw [interp.eq_def]
        simp only [Stmt.loops, sumB_append, Stmt.ite.sizeOf_spec] at hN
        intro σ
        have hA1 : SymsIn (fun α => A α ∨ α = σ.nextId) ρ φ := hS.mono ext_left
        have hb : ∀ α ∈ (b.den ρ).syms, A α ∨ α = σ.nextId := fun α h => .inl (hS.den b α h)
        refine Good.prefix (fun α hα => ?_) (fun o l α v h => by cases h)
          (Good.plus (interp_good N n ctx _ s₁ ρ κ _ _ (by omega) (hA1.guard _ hb)
              (hκ.mono ext_left) _)
            (interp_good N n ctx _ s₂ ρ κ _ _ (by omega) (hA1.guard _ hb) (hκ.mono ext_left) _))
        rcases List.mem_append.1 hα with h | h
        · exact hS.valres _ rfl α h
        · simp [Event.exprSyms] at h
    | «while» ℓ b body =>
        rw [interp.eq_def]
        dsimp only
        split
        · exact fun _ => good_empty A
        · simp only [Stmt.loops, sumB_cons, Stmt.while.sizeOf_spec] at hN
          have h₁ := sumB_dec_le body.loops n ℓ
          have h₂ := Bounds.dec_self n ℓ
          intro σ
          have hA1 : SymsIn (fun α => A α ∨ α = σ.nextId) ρ φ := hS.mono ext_left
          have hb : ∀ α ∈ (b.den ρ).syms, A α ∨ α = σ.nextId := fun α h => .inl (hS.den b α h)
          refine Good.prefix (fun α hα => ?_) (fun o l α v h => by cases h)
            (Good.plus
              (interp_good N (n.dec ℓ) _ _ body ρ _ _ _ (by omega) (hA1.guard _ hb)
                (fun B hAB ρ' φ' hS' => interp_good N (n.dec ℓ) _ pc (.while ℓ b body) ρ' κ φ' B
                  (by simp only [Stmt.loops, sumB_cons, Stmt.while.sizeOf_spec]; omega) hS'
                  (hκ.mono (fun α h => hAB α (.inl h)))) _)
              (hκ _ ext_left _ _ (hA1.guard _ hb) _))
          rcases List.mem_append.1 hα with h | h
          · exact hS.valres _ rfl α h
          · simp [Event.exprSyms] at h

/-- **`⟨P⟩_n` introduces symbols before their uses.** -/
theorem denote_symWF (n : Bounds) (P : Stmt) : (denote n P).SymWF := by
  have h := interp_good _ n ⟨0, []⟩ [] P [] (fun _ _ => pure .empty) [] (fun _ => False)
    (Nat.lt_succ_self _) ⟨fun p hp => (by cases hp), fun g hg => (by cases hg)⟩
    (fun _ _ _ _ _ _ => good_empty _) {}
  refine ⟨fun e he α hα => ?_, fun e he => (h e he).2⟩
  rcases (h e he).1 α hα with h | h
  · exact h.elim
  · exact h

end SymWFDenote
