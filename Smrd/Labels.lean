import Smrd.Types
import Smrd.EventStructureSemantics
import Smrd.Fresh
import Smrd.Conjuncts
import Smrd.Executions
import Smrd.Monotonicity

/-!
# Labels Are Unique

The paper relies on control labels being unique in `P̄` (Appendix A, before
Definition `def:justs`): a conflict-free set of events contains at most one
event per label, so that a justification can recover its event by label. This
module proves it of `⟨P⟩_n` (`labels_unique`, `conflictFree_label_inj`), for
programs whose loop identifiers are distinct (`P.loops.Nodup`).

It rests on the join after a parallel composition (`interp`'s `par` case): the
continuation runs once, after both threads. Were it run after each thread, as
in the paper's Definition `def:gen-es`, the two copies would carry one label and
no conflicting guards (`x := 1; (y := 1 ∥ z := 1); w := 1`).

Labels are unique already without their thread: two events of `⟨P⟩_n` with the
same program counter and iterations are generated along different outcomes of a
branching (`Diverge`), and their value restrictions conflict.

## Deviations from the paper

* The hypothesis `P.loops.Nodup`, which the paper's loop identifiers satisfy.
  Without it a loop nested in a loop of the same identifier reuses iteration
  labels along one path: `Ctx.enter` overwrites the outer iteration.

## Proof

An induction over the interpreter, as in `Smrd.Fresh`. The events a run
generates are its own -- below its program counter, at its iterations
(`Own`) -- or the continuation's, and the continuation's lie outside `Own`.
Two events of one run with the same program counter and iterations are
therefore both its own, and then generated on different sides of a branching,
or both the continuation's.
-/

namespace Labels

open EventStructure

/-! ## Divergence -/

/-- `e₁` and `e₂` lie on different outcomes of one branching: their value
    restrictions hold a guard and its negation. -/
def Diverge (e₁ e₂ : Event) : Prop :=
  ∃ g₁ ∈ e₁.guards, ∃ g₂ ∈ e₂.guards, g₁.branch = g₂.branch ∧ g₁.cond = g₂.cond ∧ g₁.pos ≠ g₂.pos

theorem Diverge.symm {e₁ e₂ : Event} (h : Diverge e₁ e₂) : Diverge e₂ e₁ := by
  obtain ⟨g₁, h₁, g₂, h₂, hb, hc, hp⟩ := h
  exact ⟨g₂, h₂, g₁, h₁, hb.symm, hc.symm, Ne.symm hp⟩

/-- Diverging events have unsatisfiable value restrictions together. -/
theorem Diverge.not_sat {e₁ e₂ : Event} (h : Diverge e₁ e₂) :
    ¬ Sat (Pred.and e₁.valres.holds e₂.valres.holds) := by
  rintro ⟨f, h₁, h₂⟩
  obtain ⟨g₁, hg₁, g₂, hg₂, -, hc, hp⟩ := h
  have a₁ := (Expr.holds_conj _ f).1 h₁ _ (List.mem_map_of_mem hg₁)
  have a₂ := (Expr.holds_conj _ f).1 h₂ _ (List.mem_map_of_mem hg₂)
  unfold Guard.expr Expr.holds at a₁ a₂
  rcases g₁ with ⟨b₁, c₁, p₁⟩
  rcases g₂ with ⟨b₂, c₂, p₂⟩
  simp only at hc hp a₁ a₂
  subst hc
  cases p₁ <;> cases p₂ <;> simp_all [Expr.eval]

/-- Two events with the same program counter and iterations are one event, or
    diverge. -/
def LU (k : EventStructure) : Prop :=
  ∀ e₁ ∈ k.events, ∀ e₂ ∈ k.events, e₁.label.pc = e₂.label.pc → e₁.label.iter = e₂.label.iter →
    e₁ = e₂ ∨ Diverge e₁ e₂

/-- Regions of control positions: program counters and iterations. -/
abbrev Region := List Nat → List (LoopId × Nat) → Prop

/-- A structure generated under the value restriction `φ`, whose events are in
    the region `R` or have the property `Q` (the continuation's), with
    labels unique up to divergence. -/
structure Good (φ : List Guard) (R : Region) (Q : Event → Prop) (k : EventStructure) : Prop where
  guards : ∀ e ∈ k.events, ∃ G, e.guards = φ ++ G
  cover  : ∀ e ∈ k.events, R e.label.pc e.label.iter ∨ Q e
  lu     : LU k

namespace Good

variable {φ : List Guard} {R R' : Region} {Q Q' : Event → Prop}

theorem empty : Good φ R Q EventStructure.empty :=
  ⟨by simp [EventStructure.empty], by simp [EventStructure.empty], by simp [LU, EventStructure.empty]⟩

theorem mono (h : Good φ R Q k) (hR : ∀ p it, R p it → R' p it) (hQ : ∀ e, Q e → Q' e) :
    Good φ R' Q' k :=
  ⟨h.guards, fun e he => (h.cover e he).elim (fun h => Or.inl (hR _ _ h)) (fun h => Or.inr (hQ e h)),
    h.lu⟩

/-- Under a longer value restriction. -/
theorem weaken {G₀ : List Guard} (h : Good (φ ++ G₀) R Q k) : Good φ R Q k :=
  ⟨fun e he => by obtain ⟨G, hG⟩ := h.guards e he; exact ⟨G₀ ++ G, by simp [hG]⟩, h.cover, h.lu⟩

/-- A region of a run counts as the continuation's to the run before it. -/
theorem toQ (h : Good φ R Q k) : Good φ (fun _ _ => False) (fun e => R e.label.pc e.label.iter ∨ Q e) k :=
  ⟨h.guards, fun e he => Or.inr (h.cover e he), h.lu⟩

theorem ofQ (h : Good φ R (fun e => R' e.label.pc e.label.iter ∨ Q e) k) :
    Good φ (fun p it => R p it ∨ R' p it) Q k :=
  ⟨h.guards, fun e he => by
    rcases h.cover e he with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h, h.lu⟩

theorem addRMW (h : Good φ R Q k) (r : EventId) (c : Expr) (w : EventId) :
    Good φ R Q (k.addRMW r c w) := ⟨h.guards, h.cover, h.lu⟩

/-- An event before a structure, at a position the structure does not take. -/
theorem «prefix» {e : Event} (hg : ∃ G, e.guards = φ ++ G)
    (hR : ¬ R e.label.pc e.label.iter)
    (hQ : ∀ e', Q e' → ¬ (e'.label.pc = e.label.pc ∧ e'.label.iter = e.label.iter))
    (h : Good φ R Q k) :
    Good φ (fun p it => (p = e.label.pc ∧ it = e.label.iter) ∨ R p it) Q («prefix» e k) := by
  have sep : ∀ e' ∈ k.events, ¬ (e'.label.pc = e.label.pc ∧ e'.label.iter = e.label.iter) := by
    intro e' he' ⟨hp, hi⟩
    rcases h.cover e' he' with hr | hq
    · exact hR (hp ▸ hi ▸ hr)
    · exact hQ e' hq ⟨hp, hi⟩
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx y hy hp hi => ?_⟩
  · simp only [events_prefix, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hg
    · exact h.guards x hx
  · simp only [events_prefix, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
    · rcases h.cover x hx with hr | hq
      · exact Or.inl (Or.inr hr)
      · exact Or.inr hq
  · simp only [events_prefix, List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact Or.inl rfl
    · exact absurd ⟨hp.symm, hi.symm⟩ (sep y hy)
    · exact absurd ⟨hp, hi⟩ (sep x hx)
    · exact h.lu x hx y hy hp hi

/-- The two outcomes of a branching. -/
theorem plus_div {R₁ R₂ : Region} {k₁ k₂ : EventStructure} {g₁ g₂ : Guard}
    (hb : g₁.branch = g₂.branch) (hc : g₁.cond = g₂.cond) (hp : g₁.pos ≠ g₂.pos)
    (h₁ : Good (φ ++ [g₁]) R₁ Q k₁) (h₂ : Good (φ ++ [g₂]) R₂ Q k₂) :
    Good φ (fun p it => R₁ p it ∨ R₂ p it) Q (k₁.plus k₂) := by
  have div : ∀ x ∈ k₁.events, ∀ y ∈ k₂.events, Diverge x y := by
    intro x hx y hy
    obtain ⟨G₁, hG₁⟩ := h₁.guards x hx
    obtain ⟨G₂, hG₂⟩ := h₂.guards y hy
    exact ⟨g₁, by simp [hG₁], g₂, by simp [hG₂], hb, hc, hp⟩
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx y hy hpc hi => ?_⟩
  · simp only [events_plus, List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨G, hG⟩ := h₁.guards x hx; exact ⟨[g₁] ++ G, by simp [hG]⟩
    · obtain ⟨G, hG⟩ := h₂.guards x hx; exact ⟨[g₂] ++ G, by simp [hG]⟩
  · simp only [events_plus, List.mem_append] at hx
    rcases hx with hx | hx
    · exact (h₁.cover x hx).imp_left Or.inl
    · exact (h₂.cover x hx).imp_left Or.inr
  · simp only [events_plus, List.mem_append] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact h₁.lu x hx y hy hpc hi
    · exact Or.inr (div x hx y hy)
    · exact Or.inr (div y hy x hx).symm
    · exact h₂.lu x hx y hy hpc hi

/-- Two structures at disjoint positions, composed by `combine`, whose events
    are those of both. -/
theorem disj {R₁ R₂ : Region} {Q₁ Q₂ : Event → Prop} {k₁ k₂ : EventStructure}
    (k : EventStructure) (hev : ∀ x, x ∈ k.events ↔ x ∈ k₁.events ∨ x ∈ k₂.events)
    (hsep : ∀ x ∈ k₁.events, ∀ y ∈ k₂.events,
      ¬ (x.label.pc = y.label.pc ∧ x.label.iter = y.label.iter))
    (h₁ : Good φ R₁ Q₁ k₁) (h₂ : Good φ R₂ Q₂ k₂) :
    Good φ (fun p it => R₁ p it ∨ R₂ p it) (fun e => Q₁ e ∨ Q₂ e) k := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx y hy hpc hi => ?_⟩
  · rcases (hev x).1 hx with hx | hx
    · exact h₁.guards x hx
    · exact h₂.guards x hx
  · rcases (hev x).1 hx with hx | hx
    · rcases h₁.cover x hx with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
    · rcases h₂.cover x hx with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
  · rcases (hev x).1 hx with hx | hx <;> rcases (hev y).1 hy with hy | hy
    · exact h₁.lu x hx y hy hpc hi
    · exact absurd ⟨hpc, hi⟩ (hsep x hx y hy)
    · exact absurd ⟨hpc.symm, hi.symm⟩ (hsep y hy x hx)
    · exact h₂.lu x hx y hy hpc hi

end Good

/-! ## Program counters and iterations -/

theorem prefix_ne {pc p : List Nat} {a b : Nat} (hab : a ≠ b) (h₁ : pc ++ [a] <+: p)
    (h₂ : pc ++ [b] <+: p) : False := by
  obtain ⟨t₁, rfl⟩ := h₁
  obtain ⟨t₂, h⟩ := h₂
  simp only [List.append_assoc, List.append_cancel_left_eq, List.cons_append, List.nil_append,
    List.cons.injEq] at h
  exact hab h.1.symm

theorem not_prefix_snoc {pc : List Nat} {a : Nat} (h : pc ++ [a] <+: pc) : False := by
  obtain ⟨t, ht⟩ := h
  have := congrArg List.length ht
  simp at this

theorem prefix_snoc {pc p : List Nat} {a : Nat} (h : pc ++ [a] <+: p) : pc <+: p :=
  (List.prefix_append pc [a]).trans h

theorem lookup_cons_if (a k : LoopId) (v : Nat) (l : List (LoopId × Nat)) :
    ((k, v) :: l).lookup a = if a = k then some v else l.lookup a := by
  simp only [List.lookup_cons]
  split <;> simp_all

theorem lookup_none_of_any {ℓ : LoopId} :
    ∀ l : List (LoopId × Nat), l.any (·.1 == ℓ) = false → l.lookup ℓ = none
  | [], _ => rfl
  | (m, v) :: l, h => by
      simp only [List.any_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
      rw [lookup_cons_if, if_neg (Ne.symm h.1)]
      exact lookup_none_of_any l h.2

theorem lookup_enter_self (ctx : Ctx) (ℓ : LoopId) (k : Nat) :
    (ctx.enter ℓ k).iter.lookup ℓ = some k := by
  obtain ⟨t, l⟩ := ctx
  have key : ∀ l : List (LoopId × Nat), l.any (·.1 == ℓ) = true →
      (l.map fun p => if p.1 = ℓ then (ℓ, k) else p).lookup ℓ = some k := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
        obtain ⟨m, v⟩ := p
        intro hany
        by_cases hm : m = ℓ
        · subst hm; simp
        · simp only [List.map_cons, if_neg hm, lookup_cons_if, if_neg (Ne.symm hm)]
          simp only [List.any_cons, Bool.or_eq_true, beq_iff_eq] at hany
          rcases hany with h | h
          · exact absurd h hm
          · exact ih h
  simp only [Ctx.enter]
  split
  · exact key l (by assumption)
  · rename_i h
    simp only [Bool.not_eq_true] at h
    simp [List.lookup_append, lookup_none_of_any l h]

theorem lookup_enter_other (ctx : Ctx) {ℓ ℓ' : LoopId} (h : ℓ' ≠ ℓ) (k : Nat) :
    (ctx.enter ℓ' k).iter.lookup ℓ = ctx.iter.lookup ℓ := by
  obtain ⟨t, l⟩ := ctx
  have key : ∀ l : List (LoopId × Nat),
      (l.map fun p => if p.1 = ℓ' then (ℓ', k) else p).lookup ℓ = l.lookup ℓ := by
    intro l
    induction l with
    | nil => rfl
    | cons p l ih =>
        obtain ⟨m, v⟩ := p
        by_cases hm : m = ℓ'
        · subst hm
          have hml : ℓ ≠ m := Ne.symm h
          simp [lookup_cons_if, hml, ih]
        · simp only [List.map_cons, if_neg hm, lookup_cons_if, ih]
  simp only [Ctx.enter]
  split
  · exact key l
  · simp only [List.lookup_append, lookup_cons_if, if_neg (Ne.symm h), List.lookup_nil]
    cases l.lookup ℓ <;> rfl

/-! ## The region of a run -/

/-- The positions a run of `⟨s⟩` at `pc` in context `ctx` generates events at:
    below `pc`, at the iterations of `ctx` -- later ones for the loops of `s`
    the context is in, which only a `while` re-entering itself has. -/
def Own (ctx : Ctx) (pc : List Nat) (s : Stmt) : Region := fun p it =>
  pc <+: p ∧ ∀ m j, ctx.iter.lookup m = some j → ∃ j', it.lookup m = some j' ∧
    (m ∈ s.loops → j < j') ∧ (m ∉ s.loops → j' = j)

/-- The context is in no loop of `s`, unless `s` is that loop re-entered. -/
def CtxOK (ctx : Ctx) (s : Stmt) : Prop :=
  ∀ m ∈ s.loops, (ctx.iter.lookup m).isSome → ∃ b body, s = .while m b body

theorem own_here (ctx : Ctx) (pc : List Nat) (s : Stmt) (hok : CtxOK ctx s)
    (hs : ∀ m b body, s ≠ .while m b body) : Own ctx pc s pc ctx.iter := by
  refine ⟨List.prefix_refl _, fun m j hj => ⟨j, hj, fun hm => ?_, fun _ => rfl⟩⟩
  obtain ⟨b, body, he⟩ := hok m hm (by simp [hj])
  exact absurd he (hs m b body)

/-- A part `s'` at `pc ++ [i]` of a statement `s` other than a loop. -/
theorem own_sub {ctx : Ctx} {pc : List Nat} {s s' : Stmt} {i : Nat} (hok : CtxOK ctx s)
    (hs : ∀ m b body, s ≠ .while m b body) (hsub : ∀ m ∈ s'.loops, m ∈ s.loops) :
    ∀ p it, Own ctx (pc ++ [i]) s' p it → Own ctx pc s p it := by
  intro p it ⟨hp, hit⟩
  refine ⟨prefix_snoc hp, fun m j hj => ?_⟩
  have hm : m ∉ s.loops := fun hm => by
    obtain ⟨b, body, he⟩ := hok m hm (by simp [hj])
    exact hs m b body he
  obtain ⟨j', hj', -, h₂⟩ := hit m j hj
  exact ⟨j', hj', fun h => absurd h hm, fun _ => h₂ (fun h => hm (hsub m h))⟩

theorem ctxOK_sub {ctx : Ctx} {s s' : Stmt} (hok : CtxOK ctx s)
    (hs : ∀ m b body, s ≠ .while m b body) (hsub : ∀ m ∈ s'.loops, m ∈ s.loops) : CtxOK ctx s' := by
  intro m hm hsome
  obtain ⟨b, body, he⟩ := hok m (hsub m hm) hsome
  exact absurd he (hs m b body)

/-- Regions below different positions are disjoint. -/
theorem own_disj {ctx ctx' : Ctx} {pc : List Nat} {s s' : Stmt} {a b : Nat} (hab : a ≠ b)
    {p : List Nat} {it it' : List (LoopId × Nat)} (h : Own ctx (pc ++ [a]) s p it)
    (h' : Own ctx' (pc ++ [b]) s' p it') : False :=
  prefix_ne hab h.1 h'.1

/-! ## Generators -/

/-- Every structure `m` generates is `Good`. -/
def GGood (φ : List Guard) (R : Region) (Q : Event → Prop) (m : Gen EventStructure) : Prop :=
  ∀ σ : GenState, Good φ R Q (m.run σ).1

/-- Continuations: called under a longer value restriction, they generate
    `Good` structures with no region of their own. -/
def KGood (φ : List Guard) (Q : Event → Prop) (κ : Cont) : Prop :=
  ∀ ρ G, GGood (φ ++ G) (fun _ _ => False) Q (κ ρ (φ ++ G))

theorem KGood.app {φ : List Guard} {Q : Event → Prop} {κ : Cont} (h : KGood φ Q κ) (ρ : RegState)
    (G : List Guard) : GGood (φ ++ G) (fun _ _ => False) Q (κ ρ (φ ++ G)) := h ρ G

theorem KGood.app' {φ : List Guard} {Q : Event → Prop} {κ : Cont} (h : KGood φ Q κ) (ρ : RegState) :
    GGood φ (fun _ _ => False) Q (κ ρ φ) := by
  have := h ρ []; simpa using this

theorem KGood.snoc {φ : List Guard} {Q : Event → Prop} {κ : Cont} (h : KGood φ Q κ) (g : Guard) :
    KGood (φ ++ [g]) Q κ := fun ρ G => by
  have := h ρ ([g] ++ G); simpa using this

theorem KGood.empty (φ : List Guard) (Q : Event → Prop) :
    KGood φ Q (fun _ _ => pure EventStructure.empty) := fun _ _ _ => Good.empty

/-- Separation of the continuation from a region. -/
def Sep (Q : Event → Prop) (R : Region) : Prop :=
  ∀ e, Q e → ¬ R e.label.pc e.label.iter

/-! ## The interpreter -/

open EventStructure in
/-- **Labels are unique in a run**, up to divergence: every run of `⟨s⟩` is
    `Good`, with its own events in `Own ctx pc s`, provided the continuation's
    are `Good` and outside. -/
theorem interp_good : ∀ (N : Nat) (n : Bounds) (ctx : Ctx) (pc : List Nat) (s : Stmt)
    (ρ : RegState) (κ : Cont) (φ : List Guard) (Q : Event → Prop),
    sumB s.loops n + sizeOf s < N → s.loops.Nodup → CtxOK ctx s →
    Sep Q (Own ctx pc s) → KGood φ Q κ →
    GGood φ (Own ctx pc s) Q (interp n ctx pc s ρ κ φ)
  | 0, _, _, _, _, _, _, _, _, hN, _, _, _, _ => absurd hN (Nat.not_lt_zero _)
  | N + 1, n, ctx, pc, s, ρ, κ, φ, Q, hN, hnd, hok, hsep, hκ => by
    -- the region of an event of `s` itself, at `pc'` below `pc`
    have here : ∀ pc', pc <+: pc' → (∀ m b body, s ≠ .while m b body) →
        Own ctx pc s pc' ctx.iter := fun pc' h hs =>
      ⟨h, (own_here ctx pc s hok hs).2⟩
    -- one event before the continuation's run, at the position `pc'`
    have atom : ∀ (pc' : List Nat) (kind : EventId → EventKind) (M : Event → Gen EventStructure),
        pc <+: pc' → (∀ m b body, s ≠ .while m b body) →
        (∀ e, GGood φ (fun _ _ => False) Q (M e)) →
        GGood φ (Own ctx pc s) Q (do let e ← mkEvent ctx pc' φ kind; let k ← M e; pure («prefix» e k)) := by
      intro pc' kind M hpc hs hM σ
      refine (Good.prefix (e := mkE ctx pc' φ kind σ.nextId) ⟨[], by simp [mkE]⟩ (fun h => h)
        (fun e' hq ⟨hp, hi⟩ => hsep e' hq (by rw [hp, hi]; exact here pc' hpc hs))
        (hM _ _)).mono (fun p it h => ?_) (fun _ h => h)
      rcases h with ⟨hp, hi⟩ | h
      · rw [hp, hi]; exact here pc' hpc hs
      · exact h.elim
    cases s with
    | skip =>
        rw [interp.eq_def]
        exact fun σ => (hκ.app' ρ σ).mono (fun _ _ h => h.elim) (fun _ h => h)
    | assign r e =>
        rw [interp.eq_def]
        exact fun σ => (hκ.app' _ σ).mono (fun _ _ h => h.elim) (fun _ h => h)
    | addrOf r x =>
        rw [interp.eq_def]
        exact fun σ => (hκ.app' _ σ).mono (fun _ _ h => h.elim) (fun _ h => h)
    | load o r x =>
        rw [interp.eq_def]
        exact atom pc _ _ (List.prefix_refl _) (fun _ _ _ h => Stmt.noConfusion h)
          (fun _ => hκ.app' _)
    | loadPtr o r p =>
        rw [interp.eq_def]
        exact atom pc _ _ (List.prefix_refl _) (fun _ _ _ h => Stmt.noConfusion h)
          (fun _ => hκ.app' _)
    | store o x v =>
        rw [interp.eq_def]
        exact atom pc _ _ (List.prefix_refl _) (fun _ _ _ h => Stmt.noConfusion h)
          (fun _ => hκ.app' _)
    | storePtr o p v =>
        rw [interp.eq_def]
        exact atom pc _ _ (List.prefix_refl _) (fun _ _ _ h => Stmt.noConfusion h)
          (fun _ => hκ.app' _)
    | fence o =>
        rw [interp.eq_def]
        exact atom pc _ _ (List.prefix_refl _) (fun _ _ _ h => Stmt.noConfusion h)
          (fun _ => hκ.app' _)
    | malloc r sz =>
        rw [interp.eq_def]
        exact atom pc _ _ (List.prefix_refl _) (fun _ _ _ h => Stmt.noConfusion h)
          (fun _ => hκ.app' _)
    | free r =>
        rw [interp.eq_def]
        exact atom pc _ _ (List.prefix_refl _) (fun _ _ _ h => Stmt.noConfusion h)
          (fun _ => hκ.app' _)
    | fadd or ow r x v =>
        rw [interp.eq_def]
        have hs : ∀ m b body, Stmt.fadd or ow r x v ≠ .while m b body :=
          fun _ _ _ h => Stmt.noConfusion h
        intro σ
        let er := mkE ctx (pc ++ [0]) φ (fun α => .read or (Expr.glob x) α false) σ.nextId
        let ew := mkE ctx (pc ++ [1]) φ
          (fun _ => .write ow (Expr.glob x) (.bin .add (.sym er.id) (v.den ρ)) false) (σ.nextId + 1)
        have hk := hκ.app' (ρ.set r (.sym er.id)) ⟨σ.nextId + 2, σ.nextThread⟩
        have h₁ := Good.prefix (e := ew) ⟨[], by simp [ew, mkE]⟩ (fun h => h)
          (fun e' hq ⟨hp, hi⟩ => hsep e' hq (by
            rw [hp, hi]; exact here _ (List.prefix_append _ _) hs)) hk
        have h₂ := Good.prefix (e := er) ⟨[], by simp [er, mkE]⟩
          (by
            rintro (⟨hp, -⟩ | h)
            · simp [er, ew, mkE] at hp
            · exact h)
          (fun e' hq ⟨hp, hi⟩ => hsep e' hq (by
            rw [hp, hi]; exact here _ (List.prefix_append _ _) hs)) h₁
        refine (h₂.addRMW er.id Expr.tt ew.id).mono (fun p it h => ?_) (fun _ h => h)
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
        · exact here _ (List.prefix_append _ _) hs
        · exact here _ (List.prefix_append _ _) hs
        · exact h.elim
    | cas or ow r x e₁ e₂ =>
        rw [interp.eq_def]
        have hs : ∀ m b body, Stmt.cas or ow r x e₁ e₂ ≠ .while m b body :=
          fun _ _ _ h => Stmt.noConfusion h
        intro σ
        let er := mkE ctx (pc ++ [0]) φ (fun α => .read or (Expr.glob x) α false) σ.nextId
        let c : Expr := .eq (.sym er.id) (e₁.den ρ)
        let ec := mkE ctx (pc ++ [1]) φ (fun _ => .branch c) (σ.nextId + 1)
        let φT := φ ++ [⟨ec.id, c, true⟩]
        let φF := φ ++ [⟨ec.id, c, false⟩]
        let ew := mkE ctx (pc ++ [2]) φT (fun _ => .write ow (Expr.glob x) (e₂.den ρ) false)
          (σ.nextId + 2)
        have hown : ∀ i, Own ctx pc (.cas or ow r x e₁ e₂) (pc ++ [i]) ctx.iter :=
          fun i => here _ (List.prefix_append _ _) hs
        have hq : ∀ i, ∀ e', Q e' → ¬ (e'.label.pc = pc ++ [i] ∧ e'.label.iter = ctx.iter) :=
          fun i e' hq ⟨hp, hi⟩ => hsep e' hq (by rw [hp, hi]; exact hown i)
        have hT := (hκ.snoc ⟨ec.id, c, true⟩).app' (ρ.set r Expr.tt) ⟨σ.nextId + 3, σ.nextThread⟩
        have hF := (hκ.snoc ⟨ec.id, c, false⟩).app' (ρ.set r Expr.ff)
          ((κ (ρ.set r Expr.tt) φT).run ⟨σ.nextId + 3, σ.nextThread⟩).2
        have hw := Good.prefix (e := ew) ⟨[], by simp [ew, mkE, φT]⟩ (fun h => h) (hq 2) hT
        have hpl := Good.plus_div (φ := φ) (g₁ := ⟨ec.id, c, true⟩) (g₂ := ⟨ec.id, c, false⟩)
          rfl rfl (by simp) hw hF
        have hc := Good.prefix (e := ec) ⟨[], by simp [ec, mkE]⟩
          (by
            rintro ((⟨hp, -⟩ | h) | h)
            · simp [ec, ew, mkE] at hp
            · exact h
            · exact h)
          (hq 1) hpl
        have hr := Good.prefix (e := er) ⟨[], by simp [er, mkE]⟩
          (by
            rintro (⟨hp, -⟩ | ((⟨hp, -⟩ | h) | h))
            · simp [er, ec, mkE] at hp
            · simp [er, ew, mkE] at hp
            · exact h
            · exact h)
          (hq 0) hc
        refine (hr.addRMW er.id c ew.id).mono (fun p it h => ?_) (fun _ h => h)
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | (⟨rfl, rfl⟩ | h) | h
        · exact hown 0
        · exact hown 1
        · exact hown 2
        · exact h.elim
        · exact h.elim
    | seq s₁ s₂ =>
        rw [interp.eq_def]
        simp only [Stmt.loops, sumB_append, Stmt.seq.sizeOf_spec] at hN
        have hs : ∀ m b body, Stmt.seq s₁ s₂ ≠ .while m b body := fun _ _ _ h => Stmt.noConfusion h
        simp only [Stmt.loops, List.nodup_append] at hnd
        have sub₁ : ∀ m ∈ s₁.loops, m ∈ (Stmt.seq s₁ s₂).loops := fun m h => by simp [Stmt.loops, h]
        have sub₂ : ∀ m ∈ s₂.loops, m ∈ (Stmt.seq s₁ s₂).loops := fun m h => by simp [Stmt.loops, h]
        have i₁ := own_sub (pc := pc) (i := 0) hok hs sub₁
        have i₂ := own_sub (pc := pc) (i := 1) hok hs sub₂
        have h₂ : ∀ ρ' G, GGood (φ ++ G) (Own ctx (pc ++ [1]) s₂) Q
            (interp n ctx (pc ++ [1]) s₂ ρ' κ (φ ++ G)) := fun ρ' G =>
          interp_good N n ctx (pc ++ [1]) s₂ ρ' κ (φ ++ G) Q (by omega) hnd.2.1
            (ctxOK_sub hok hs sub₂) (fun e hq h => hsep e hq (i₂ _ _ h))
            (fun ρ'' G' => by have := hκ ρ'' (G ++ G'); simpa using this)
        intro σ
        refine (Good.ofQ (interp_good N n ctx (pc ++ [0]) s₁ ρ _ φ
          (fun e => Own ctx (pc ++ [1]) s₂ e.label.pc e.label.iter ∨ Q e) (by omega) hnd.1
          (ctxOK_sub hok hs sub₁) ?_ (fun ρ' G σ' => (h₂ ρ' G σ').toQ) σ)).mono
          (fun p it h => h.elim (i₁ p it) (i₂ p it)) (fun _ h => h)
        rintro e (h | h) h'
        · exact own_disj (by decide) h' h
        · exact hsep e h (i₁ _ _ h')
    | par s₁ s₂ =>
        rw [interp.eq_def]
        simp only [Stmt.loops, sumB_append, Stmt.par.sizeOf_spec] at hN
        have hs : ∀ m b body, Stmt.par s₁ s₂ ≠ .while m b body := fun _ _ _ h => Stmt.noConfusion h
        simp only [Stmt.loops, List.nodup_append] at hnd
        have sub₁ : ∀ m ∈ s₁.loops, m ∈ (Stmt.par s₁ s₂).loops := fun m h => by simp [Stmt.loops, h]
        have sub₂ : ∀ m ∈ s₂.loops, m ∈ (Stmt.par s₁ s₂).loops := fun m h => by simp [Stmt.loops, h]
        have i₁ := own_sub (pc := pc) (i := 0) hok hs sub₁
        have i₂ : ∀ t p it, Own { ctx with thread := t } (pc ++ [1]) s₂ p it →
            Own ctx pc (.par s₁ s₂) p it := fun _ => own_sub (pc := pc) (i := 1) hok hs sub₂
        intro σ
        let σ' : GenState := ⟨σ.nextId, σ.nextThread + 1⟩
        let k₁ := (interp n ctx (pc ++ [0]) s₁ ρ (fun _ _ => pure .empty) φ).run σ'
        let k₂ := (interp n { ctx with thread := σ.nextThread } (pc ++ [1]) s₂ ρ
          (fun _ _ => pure .empty) φ).run k₁.2
        have g₁ : Good φ (Own ctx (pc ++ [0]) s₁) (fun _ => False) k₁.1 :=
          interp_good N n ctx (pc ++ [0]) s₁ ρ _ φ (fun _ => False) (by omega) hnd.1
            (ctxOK_sub hok hs sub₁) (fun _ h => h.elim) (KGood.empty _ _) σ'
        have g₂ : Good φ (Own { ctx with thread := σ.nextThread } (pc ++ [1]) s₂) (fun _ => False)
            k₂.1 :=
          interp_good N n { ctx with thread := σ.nextThread } (pc ++ [1]) s₂ ρ _ φ (fun _ => False) (by omega) hnd.2.1
            (ctxOK_sub hok hs sub₂) (fun _ h => h.elim) (KGood.empty _ _) k₁.2
        have g₃ := hκ.app' ρ k₂.2
        have g₁₂ := Good.disj (k₁.1.plus k₂.1) (fun x => by simp [events_plus])
          (fun x hx y hy ⟨hp, hi⟩ => by
            rcases g₁.cover x hx with h | h
            · rcases g₂.cover y hy with h' | h'
              · exact own_disj (by decide) h (hp ▸ hi ▸ h')
              · exact h'
            · exact h) g₁ g₂
        have g := Good.disj ((k₁.1.plus k₂.1).join ((κ ρ φ).run k₂.2).1)
          (fun x => by simp [events_join, or_assoc]) (fun x hx y hy ⟨hp, hi⟩ => by
            rcases g₁₂.cover x hx with h | h
            · rcases g₃.cover y hy with h' | h'
              · exact h'
              · exact hsep y h' (by
                  rw [← hp, ← hi]
                  rcases h with h | h
                  · exact i₁ _ _ h
                  · exact i₂ _ _ _ h)
            · rcases h with h | h <;> exact h) g₁₂ g₃
        refine g.mono (fun p it h => ?_) (fun e h => ?_)
        · rcases h with (h | h) | h
          · exact i₁ _ _ h
          · exact i₂ _ _ _ h
          · exact h.elim
        · rcases h with (h | h) | h
          · exact h.elim
          · exact h.elim
          · exact h
    | ite b s₁ s₂ =>
        rw [interp.eq_def]
        simp only [Stmt.loops, sumB_append, Stmt.ite.sizeOf_spec] at hN
        have hs : ∀ m b' body, Stmt.ite b s₁ s₂ ≠ .while m b' body :=
          fun _ _ _ h => Stmt.noConfusion h
        simp only [Stmt.loops, List.nodup_append] at hnd
        have sub₁ : ∀ m ∈ s₁.loops, m ∈ (Stmt.ite b s₁ s₂).loops := fun m h => by simp [Stmt.loops, h]
        have sub₂ : ∀ m ∈ s₂.loops, m ∈ (Stmt.ite b s₁ s₂).loops := fun m h => by simp [Stmt.loops, h]
        have i₁ := own_sub (pc := pc) (i := 0) hok hs sub₁
        have i₂ := own_sub (pc := pc) (i := 1) hok hs sub₂
        intro σ
        let c := b.den ρ
        let eb := mkE ctx pc φ (fun _ => .branch c) σ.nextId
        let φT := φ ++ [⟨eb.id, c, true⟩]
        let φF := φ ++ [⟨eb.id, c, false⟩]
        have hT : Good φT (Own ctx (pc ++ [0]) s₁) Q
            ((interp n ctx (pc ++ [0]) s₁ ρ κ φT).run ⟨σ.nextId + 1, σ.nextThread⟩).1 :=
          interp_good N n ctx (pc ++ [0]) s₁ ρ κ φT Q (by omega) hnd.1 (ctxOK_sub hok hs sub₁)
            (fun e hq h => hsep e hq (i₁ _ _ h)) (hκ.snoc _) _
        have hF : Good φF (Own ctx (pc ++ [1]) s₂) Q
            ((interp n ctx (pc ++ [1]) s₂ ρ κ φF).run
              ((interp n ctx (pc ++ [0]) s₁ ρ κ φT).run ⟨σ.nextId + 1, σ.nextThread⟩).2).1 :=
          interp_good N n ctx (pc ++ [1]) s₂ ρ κ φF Q (by omega) hnd.2.1 (ctxOK_sub hok hs sub₂)
            (fun e hq h => hsep e hq (i₂ _ _ h)) (hκ.snoc _) _
        have hpl := Good.plus_div (φ := φ) (g₁ := ⟨eb.id, c, true⟩) (g₂ := ⟨eb.id, c, false⟩)
          rfl rfl (by simp) hT hF
        have hown : Own ctx pc (.ite b s₁ s₂) pc ctx.iter := here pc (List.prefix_refl _) hs
        refine (Good.prefix (e := eb) ⟨[], by simp [eb, mkE]⟩
          (by
            rintro (h | h)
            · exact not_prefix_snoc h.1
            · exact not_prefix_snoc h.1)
          (fun e' hq ⟨hp, hi⟩ => hsep e' hq (by rw [hp, hi]; exact hown)) hpl).mono
          (fun p it h => ?_) (fun _ h => h)
        rcases h with ⟨rfl, rfl⟩ | h | h
        · exact hown
        · exact i₁ _ _ h
        · exact i₂ _ _ h
    | «while» ℓ b body =>
        rw [interp.eq_def]
        dsimp only
        split
        · exact fun _ => Good.empty
        · simp only [Stmt.loops, sumB_cons, Stmt.while.sizeOf_spec] at hN
          have hd₁ := sumB_dec_le body.loops n ℓ
          have hd₂ := Bounds.dec_self n ℓ
          simp only [Stmt.loops, List.nodup_cons] at hnd
          obtain ⟨hℓb, hndb⟩ := hnd
          intro σ
          let k := match ctx.iter.lookup ℓ with
            | some j => j + 1
            | none   => 0
          let ctx' := ctx.enter ℓ k
          have hk' : ctx'.iter.lookup ℓ = some k := lookup_enter_self ctx ℓ k
          have hoth : ∀ m, m ≠ ℓ → ctx'.iter.lookup m = ctx.iter.lookup m :=
            fun m hm => lookup_enter_other ctx (Ne.symm hm) k
          -- the context is in no loop of the body
          have hnb : ∀ m ∈ body.loops, ctx.iter.lookup m = none := by
            intro m hm
            cases hlk : ctx.iter.lookup m with
            | none => rfl
            | some j =>
                obtain ⟨b', body', he⟩ := hok m (by simp [Stmt.loops, hm]) (by simp [hlk])
                simp only [Stmt.while.injEq] at he
                exact absurd (he.1 ▸ hm) hℓb
          have hokb : CtxOK ctx' body := by
            intro m hm hsome
            have hmℓ : m ≠ ℓ := fun h => hℓb (h ▸ hm)
            rw [hoth m hmℓ, hnb m hm] at hsome
            simp at hsome
          have hokw : CtxOK ctx' (.while ℓ b body) := by
            intro m hm hsome
            simp only [Stmt.loops, List.mem_cons] at hm
            rcases hm with rfl | hm
            · exact ⟨b, body, rfl⟩
            · have hmℓ : m ≠ ℓ := fun h => hℓb (h ▸ hm)
              rw [hoth m hmℓ, hnb m hm] at hsome
              simp at hsome
          -- the regions: the body's iteration `k`, the later ones, and both within the loop's
          have hkk : ∀ j, ctx.iter.lookup ℓ = some j → j < k := by
            intro j hj
            show j < (match ctx.iter.lookup ℓ with | some j => j + 1 | none => 0)
            rw [hj]; exact Nat.lt_succ_self j
          have incl : ∀ (s' : Stmt) (pc' : List Nat), pc <+: pc' → (∀ m ∈ s'.loops, m ∈ ℓ :: body.loops) →
              (∀ p it, Own ctx' pc' s' p it → (ℓ ∈ s'.loops → ∀ j', it.lookup ℓ = some j' → k < j') →
                Own ctx pc (.while ℓ b body) p it) := by
            intro s' pc' hpc hsub p it ⟨hp, hit⟩ hgt
            refine ⟨hpc.trans hp, fun m j hj => ?_⟩
            by_cases hmℓ : m = ℓ
            · subst hmℓ
              obtain ⟨j', hj', h₁, h₂⟩ := hit m k hk'
              refine ⟨j', hj', fun _ => ?_, fun h => absurd (by simp [Stmt.loops]) h⟩
              have := hkk j hj
              by_cases hin : m ∈ s'.loops
              · have := hgt hin j' hj'; omega
              · have := h₂ hin; omega
            · have hj' : ctx'.iter.lookup m = some j := by rw [hoth m hmℓ]; exact hj
              have hmb : m ∉ body.loops := fun hm => by rw [hnb m hm] at hj; simp at hj
              have hmw : m ∉ (Stmt.while ℓ b body).loops := by
                simp only [Stmt.loops, List.mem_cons, not_or]; exact ⟨hmℓ, hmb⟩
              have hms : m ∉ s'.loops := fun h => by
                rcases List.mem_cons.1 (hsub m h) with h | h
                · exact hmℓ h
                · exact hmb h
              obtain ⟨j'', hj'', -, h₂⟩ := hit m j hj'
              exact ⟨j'', hj'', fun h => absurd h hmw, fun _ => h₂ hms⟩
          have iB : ∀ p it, Own ctx' (pc ++ [0]) body p it → Own ctx pc (.while ℓ b body) p it :=
            fun p it h => incl body (pc ++ [0]) (List.prefix_append _ _)
              (fun m hm => List.mem_cons_of_mem _ hm) p it h (fun h => absurd h hℓb)
          have iW : ∀ p it, Own ctx' pc (.while ℓ b body) p it →
              Own ctx pc (.while ℓ b body) p it := by
            intro p it h
            refine incl (.while ℓ b body) pc (List.prefix_refl _) (fun m hm => hm) p it h ?_
            intro _ j' hj'
            obtain ⟨j'', hj'', h₁, -⟩ := h.2 ℓ k hk'
            rw [hj'] at hj''
            cases hj''
            exact h₁ (by simp [Stmt.loops])
          have dBW : ∀ p it, Own ctx' (pc ++ [0]) body p it → ¬ Own ctx' pc (.while ℓ b body) p it := by
            intro p it hB hW
            obtain ⟨j₁, hj₁, -, h₁⟩ := hB.2 ℓ k hk'
            obtain ⟨j₂, hj₂, h₂, -⟩ := hW.2 ℓ k hk'
            rw [hj₁] at hj₂
            cases hj₂
            have := h₁ hℓb
            have := h₂ (by simp [Stmt.loops])
            omega
          let c := b.den ρ
          let eb := mkE ctx' pc φ (fun _ => .branch c) σ.nextId
          let φT := φ ++ [⟨eb.id, c, true⟩]
          let φF := φ ++ [⟨eb.id, c, false⟩]
          let κw : Cont := fun ρ' φ' => interp (n.dec ℓ) ctx' pc (.while ℓ b body) ρ' κ φ'
          have hκw : KGood φT (fun e => Own ctx' pc (.while ℓ b body) e.label.pc e.label.iter ∨ Q e)
              κw := by
            intro ρ' G σ'
            exact (interp_good N (n.dec ℓ) ctx' pc (.while ℓ b body) ρ' κ (φT ++ G) Q
              (by simp only [Stmt.loops, sumB_cons, Stmt.while.sizeOf_spec]; omega)
              (List.nodup_cons.2 ⟨hℓb, hndb⟩) hokw (fun e hq h => hsep e hq (iW _ _ h))
              (fun ρ'' G' => by have := hκ ρ'' ([⟨eb.id, c, true⟩] ++ G ++ G'); simpa [φT] using this)
              σ').toQ
          have hT : Good φT (Own ctx' (pc ++ [0]) body)
              (fun e => Own ctx' pc (.while ℓ b body) e.label.pc e.label.iter ∨ Q e)
              ((interp (n.dec ℓ) ctx' (pc ++ [0]) body ρ κw φT).run ⟨σ.nextId + 1, σ.nextThread⟩).1 :=
            interp_good N (n.dec ℓ) ctx' (pc ++ [0]) body ρ κw φT _ (by omega) hndb hokb
              (by
                rintro e (h | h) h'
                · exact dBW _ _ h' h
                · exact hsep e h (iB _ _ h'))
              hκw _
          have hF := (hκ.snoc ⟨eb.id, c, false⟩).app' ρ
            ((interp (n.dec ℓ) ctx' (pc ++ [0]) body ρ κw φT).run ⟨σ.nextId + 1, σ.nextThread⟩).2
          have hpl := Good.plus_div (φ := φ) (g₁ := ⟨eb.id, c, true⟩) (g₂ := ⟨eb.id, c, false⟩)
            rfl rfl (by simp) (Good.ofQ hT) hF
          have hown : Own ctx pc (.while ℓ b body) pc ctx'.iter := by
            refine ⟨List.prefix_refl _, fun m j hj => ?_⟩
            by_cases hmℓ : m = ℓ
            · subst hmℓ
              exact ⟨k, hk', fun _ => hkk j hj, fun h => absurd (by simp [Stmt.loops]) h⟩
            · have hmb : m ∉ body.loops := fun hm => by rw [hnb m hm] at hj; simp at hj
              refine ⟨j, by rw [hoth m hmℓ]; exact hj, fun h => ?_, fun _ => rfl⟩
              simp only [Stmt.loops, List.mem_cons] at h
              rcases h with h | h
              · exact absurd h hmℓ
              · exact absurd h hmb
          refine (Good.prefix (e := eb) ⟨[], by simp [eb, mkE]⟩
            (by
              rintro ((h | h) | h)
              · exact not_prefix_snoc h.1
              · obtain ⟨j', hj', h₁, -⟩ := h.2 ℓ k hk'
                simp only [eb, mkE] at hj'
                rw [hk'] at hj'
                cases hj'
                have := h₁ (by simp [Stmt.loops])
                omega
              · exact h)
            (fun e' hq ⟨hp, hi⟩ => hsep e' hq (by rw [hp, hi]; exact hown)) hpl).mono
            (fun p it h => ?_) (fun _ h => h)
          rcases h with ⟨rfl, rfl⟩ | ((h | h) | h)
          · exact hown
          · exact iB _ _ h
          · exact iW _ _ h
          · exact h.elim

end Labels

open Labels in
/-- **Labels are unique in `P̄`.** In `⟨P⟩_n`, for a program with distinct loop
    identifiers, two distinct events with the same program counter and
    iterations -- a fortiori the same control label -- diverge: their value
    restrictions hold a branching's condition and its negation. This rests on
    the join after `∥`: the continuation of a parallel composition runs once. -/
theorem denote_diverge (n : Bounds) (P : Stmt) (hP : P.loops.Nodup) {e₁ e₂ : Event}
    (h₁ : e₁ ∈ (denote n P).events) (h₂ : e₂ ∈ (denote n P).events)
    (hpc : e₁.label.pc = e₂.label.pc) (hit : e₁.label.iter = e₂.label.iter) (hne : e₁ ≠ e₂) :
    Diverge e₁ e₂ := by
  have hg := interp_good _ n ⟨0, []⟩ [] P [] (fun _ _ => pure .empty) [] (fun _ => False)
    (Nat.lt_succ_self _) hP (fun m _ h => by simp at h) (fun _ h => h.elim) (KGood.empty _ _) {}
  exact (hg.lu e₁ h₁ e₂ h₂ hpc hit).resolve_left hne

open Labels in
/-- Labels are unique in `P̄` (Appendix A): distinct events of `⟨P⟩_n` with the
    same control label are in conflict. -/
theorem labels_unique (n : Bounds) (P : Stmt) (hP : P.loops.Nodup) {e₁ e₂ : Event}
    (h₁ : e₁ ∈ (denote n P).events) (h₂ : e₂ ∈ (denote n P).events)
    (hl : e₁.label = e₂.label) (hne : e₁ ≠ e₂) : (denote n P).Conflict e₁.id e₂.id :=
  ⟨e₁, e₂, denote_ev n P h₁, denote_ev n P h₂,
    (denote_diverge n P hP h₁ h₂ (by rw [hl]) (by rw [hl]) hne).not_sat⟩

/-- **A conflict-free set contains at most one event per label** (Appendix A,
    the sentence before Definition `def:justs`). -/
theorem conflictFree_label_inj (n : Bounds) (P : Stmt) (hP : P.loops.Nodup) {X : EvSet}
    (hX : ∀ a b, X a → X b → ¬ (denote n P).Conflict a b) {e₁ e₂ : Event}
    (h₁ : e₁ ∈ (denote n P).events) (h₂ : e₂ ∈ (denote n P).events) (hx₁ : X e₁.id)
    (hx₂ : X e₂.id) (hl : e₁.label = e₂.label) : e₁ = e₂ := by
  by_cases hne : e₁ = e₂
  · exact hne
  · exact absurd (labels_unique n P hP h₁ h₂ hl hne) (hX _ _ hx₁ hx₂)
