import Smrd.Types
import Smrd.EventStructureSemantics

/-!
# Fresh Event Ids

The semantics `⟨P⟩_n` allocates every event id from a counter, so the events
of the event structure it generates have pairwise distinct ids
(`denote_ids_nodup`). Consequently `EventStructure.ev` finds each event by
its id (`ev_of_mem`), and in particular the origin of a symbol -- the event
whose id it is -- is well defined.

The proof is an induction over the interpreter along its termination measure.
Each shape of event generation the interpreter uses is handled once, by the
combinator lemmas below.
-/

/-- `l` has no duplicates, and lies in `[lo, hi)`. -/
def InRange (lo hi : Nat) (l : List Nat) : Prop :=
  l.Nodup ∧ ∀ x ∈ l, lo ≤ x ∧ x < hi

namespace InRange

theorem nil (lo hi : Nat) : InRange lo hi [] := ⟨List.nodup_nil, by simp⟩

theorem cons {lo hi : Nat} {l : List Nat} (h : InRange (lo + 1) hi l) (hlt : lo < hi) :
    InRange lo hi (lo :: l) := by
  refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, h.1⟩, ?_⟩
  · have := (h.2 lo hm).1; omega
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨Nat.le_refl _, hlt⟩
    · have := h.2 x hx; omega

theorem append {a b c : Nat} {l₁ l₂ : List Nat} (h₁ : InRange a b l₁) (h₂ : InRange b c l₂)
    (hab : a ≤ b) (hbc : b ≤ c) : InRange a c (l₁ ++ l₂) := by
  refine ⟨List.nodup_append.2 ⟨h₁.1, h₂.1, fun x hx y hy hxy => ?_⟩, fun x hx => ?_⟩
  · have := h₁.2 x hx; have := h₂.2 y hy; omega
  · simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · have := h₁.2 x hx; omega
    · have := h₂.2 x hx; omega

end InRange

/-! ## Generators that allocate fresh ids -/

/-- A generator of event structures allocates the ids of the events it
    returns from the counter, each once. -/
def Gen.Fresh (m : Gen EventStructure) : Prop :=
  ∀ s : GenState, s.nextId ≤ (m.run s).2.nextId ∧
    InRange s.nextId (m.run s).2.nextId (m.run s).1.ids

namespace EventStructure

@[simp] theorem ids_prefix (e : Event) (k : EventStructure) : («prefix» e k).ids = e.id :: k.ids := by
  simp [«prefix», ids]

@[simp] theorem ids_plus (k₁ k₂ : EventStructure) : (k₁.plus k₂).ids = k₁.ids ++ k₂.ids := by
  simp [plus, ids]

@[simp] theorem ids_addRMW (k : EventStructure) (r : EventId) (b : Expr) (w : EventId) :
    (k.addRMW r b w).ids = k.ids := rfl

@[simp] theorem ids_empty : empty.ids = [] := rfl

/-- With distinct ids, `ev` finds every event by its id. -/
theorem ev_of_mem {es : EventStructure} (hnd : es.ids.Nodup) {e : Event} (he : e ∈ es.events) :
    es.ev e.id = some e := by
  obtain ⟨events, po, rmw⟩ := es
  simp only [ev, ids] at *
  induction events with
  | nil => simp at he
  | cons a l ih =>
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
      simp only [List.find?_cons]
      by_cases hae : a = e
      · subst hae; simp
      · have hel : e ∈ l := (List.mem_cons.1 he).resolve_left (fun h => hae h.symm)
        have hid : a.id ≠ e.id := fun h => hnd.1 ⟨e, hel, h.symm⟩
        have hb : (a.id == e.id) = false := by rw [beq_eq_false_iff_ne]; exact hid
        simp only [hb]
        exact ih hnd.2 hel

end EventStructure

/-- The event `mkEvent` generates at counter value `i`. -/
def mkE (ctx : Ctx) (pc : List Nat) (φ : List Guard) (kind : EventId → EventKind) (i : EventId) :
    Event :=
  { id := i, kind := kind i, label := ⟨ctx.thread, pc, ctx.iter⟩, guards := φ }

@[simp] theorem mkE_id (ctx : Ctx) (pc : List Nat) (φ : List Guard) (kind : EventId → EventKind)
    (i : EventId) : (mkE ctx pc φ kind i).id = i := rfl

namespace Gen.Fresh

open EventStructure

theorem pure_empty : Gen.Fresh (pure EventStructure.empty) := by
  intro s
  exact ⟨Nat.le_refl _, InRange.nil _ _⟩

/-- One event, prefixed to what a continuation generates. -/
theorem mk_prefix (ctx : Ctx) (pc : List Nat) (φ : List Guard) (kind : EventId → EventKind)
    (m : Event → Gen EventStructure) (hm : ∀ e, Gen.Fresh (m e)) :
    Gen.Fresh (do let e ← mkEvent ctx pc φ kind; let k ← m e; pure («prefix» e k)) := by
  intro s
  have hr : StateT.run (do let e ← mkEvent ctx pc φ kind; let k ← m e; pure («prefix» e k)
      : Gen EventStructure) s
      = («prefix» (mkE ctx pc φ kind s.nextId)
          ((m (mkE ctx pc φ kind s.nextId)).run ⟨s.nextId + 1, s.nextThread⟩).1,
         ((m (mkE ctx pc φ kind s.nextId)).run ⟨s.nextId + 1, s.nextThread⟩).2) := rfl
  rw [hr]
  obtain ⟨h₁, h₂⟩ := hm (mkE ctx pc φ kind s.nextId) ⟨s.nextId + 1, s.nextThread⟩
  generalize (m (mkE ctx pc φ kind s.nextId)).run ⟨s.nextId + 1, s.nextThread⟩ = r at h₁ h₂ ⊢
  obtain ⟨k, s₂⟩ := r
  simp only [ids_prefix, mkE_id] at h₁ h₂ ⊢
  exact ⟨Nat.le_of_succ_le h₁, InRange.cons h₂ (Nat.lt_of_succ_le h₁)⟩

/-- A branching event over the coproduct of two generators. -/
theorem mk_branch (ctx : Ctx) (pc : List Nat) (φ : List Guard) (kind : EventId → EventKind)
    (m₁ m₂ : Event → Gen EventStructure) (h₁ : ∀ e, Gen.Fresh (m₁ e)) (h₂ : ∀ e, Gen.Fresh (m₂ e)) :
    Gen.Fresh (do
      let e ← mkEvent ctx pc φ kind
      let k₁ ← m₁ e
      let k₂ ← m₂ e
      pure («prefix» e (k₁.plus k₂))) := by
  intro s
  let e := mkE ctx pc φ kind s.nextId
  have hr : StateT.run (do
      let e ← mkEvent ctx pc φ kind
      let k₁ ← m₁ e
      let k₂ ← m₂ e
      pure («prefix» e (k₁.plus k₂)) : Gen EventStructure) s
      = («prefix» e (((m₁ e).run ⟨s.nextId + 1, s.nextThread⟩).1.plus
          ((m₂ e).run ((m₁ e).run ⟨s.nextId + 1, s.nextThread⟩).2).1),
         ((m₂ e).run ((m₁ e).run ⟨s.nextId + 1, s.nextThread⟩).2).2) := rfl
  rw [hr]
  obtain ⟨a₁, a₂⟩ := h₁ e ⟨s.nextId + 1, s.nextThread⟩
  generalize (m₁ e).run ⟨s.nextId + 1, s.nextThread⟩ = r₁ at a₁ a₂ ⊢
  obtain ⟨k₁, s₁⟩ := r₁
  obtain ⟨b₁, b₂⟩ := h₂ e s₁
  generalize (m₂ e).run s₁ = r₂ at b₁ b₂ ⊢
  obtain ⟨k₂, s₂⟩ := r₂
  simp only [ids_prefix, ids_plus] at a₁ a₂ b₁ b₂ ⊢
  have hle := Nat.le_trans a₁ b₁
  refine ⟨?_, InRange.cons (InRange.append a₂ b₂ a₁ b₁) ?_⟩
  all_goals (unfold EventId at *; omega)

/-- `fadd`: a read and a write, prefixed to a continuation, with an RMW entry. -/
theorem mk_fadd (ctx : Ctx) (pc₁ pc₂ : List Nat) (φ : List Guard) (kind₁ : EventId → EventKind)
    (kind₂ : Event → EventId → EventKind) (b : Expr) (m : Event → Gen EventStructure)
    (hm : ∀ e, Gen.Fresh (m e)) :
    Gen.Fresh (do
      let er ← mkEvent ctx pc₁ φ kind₁
      let ew ← mkEvent ctx pc₂ φ (kind₂ er)
      let k ← m er
      pure ((«prefix» er («prefix» ew k)).addRMW er.id b ew.id)) := by
  intro s
  let er := mkE ctx pc₁ φ kind₁ s.nextId
  let ew := mkE ctx pc₂ φ (kind₂ er) (s.nextId + 1)
  have hr : StateT.run (do
      let er ← mkEvent ctx pc₁ φ kind₁
      let ew ← mkEvent ctx pc₂ φ (kind₂ er)
      let k ← m er
      pure ((«prefix» er («prefix» ew k)).addRMW er.id b ew.id) : Gen EventStructure) s
      = (((«prefix» er («prefix» ew ((m er).run ⟨s.nextId + 2, s.nextThread⟩).1)).addRMW
            er.id b ew.id),
         ((m er).run ⟨s.nextId + 2, s.nextThread⟩).2) := rfl
  rw [hr]
  obtain ⟨a₁, a₂⟩ := hm er ⟨s.nextId + 2, s.nextThread⟩
  generalize (m er).run ⟨s.nextId + 2, s.nextThread⟩ = r at a₁ a₂ ⊢
  obtain ⟨k, s₁⟩ := r
  simp only [ids_addRMW, ids_prefix] at a₁ a₂ ⊢
  refine ⟨?_, InRange.cons (InRange.cons a₂ ?_) ?_⟩
  all_goals (unfold EventId at *; omega)

/-- `cas`: a read and a branching event, then the successful outcome's write
    prefixed to one continuation, and the failing outcome's continuation. The
    statement mirrors the `do` block of `interp`, `have`s included, so that it
    applies syntactically. -/
theorem mk_cas (ctx : Ctx) (pc₀ pc₁ pc₂ : List Nat) (φ : List Guard) (kind₀ : EventId → EventKind)
    (cf : Event → Expr) (kind₁ : Expr → EventId → EventKind) (kind₂ : EventId → EventKind)
    (mT mF : List Guard → Gen EventStructure)
    (hT : ∀ g, Gen.Fresh (mT g)) (hF : ∀ g, Gen.Fresh (mF g)) :
    Gen.Fresh (do
      let er ← mkEvent ctx pc₀ φ kind₀
      have c : Expr := cf er
      let ec ← mkEvent ctx pc₁ φ (kind₁ c)
      have φT : List Guard := φ ++ [⟨ec.id, c, true⟩]
      have φF : List Guard := φ ++ [⟨ec.id, c, false⟩]
      let ew ← mkEvent ctx pc₂ φT kind₂
      let kT ← mT φT
      let kF ← mF φF
      pure ((«prefix» er («prefix» ec ((«prefix» ew kT).plus kF))).addRMW er.id c ew.id)) := by
  intro s
  let er := mkE ctx pc₀ φ kind₀ s.nextId
  let c := cf er
  let ec := mkE ctx pc₁ φ (kind₁ c) (s.nextId + 1)
  let φT : List Guard := φ ++ [⟨ec.id, c, true⟩]
  let φF : List Guard := φ ++ [⟨ec.id, c, false⟩]
  let ew := mkE ctx pc₂ φT kind₂ (s.nextId + 2)
  have hr : StateT.run (do
      let er ← mkEvent ctx pc₀ φ kind₀
      have c : Expr := cf er
      let ec ← mkEvent ctx pc₁ φ (kind₁ c)
      have φT : List Guard := φ ++ [⟨ec.id, c, true⟩]
      have φF : List Guard := φ ++ [⟨ec.id, c, false⟩]
      let ew ← mkEvent ctx pc₂ φT kind₂
      let kT ← mT φT
      let kF ← mF φF
      pure ((«prefix» er («prefix» ec ((«prefix» ew kT).plus kF))).addRMW er.id c ew.id)
      : Gen EventStructure) s
      = ((«prefix» er («prefix» ec ((«prefix» ew ((mT φT).run ⟨s.nextId + 3, s.nextThread⟩).1).plus
            ((mF φF).run ((mT φT).run ⟨s.nextId + 3, s.nextThread⟩).2).1))).addRMW er.id c ew.id,
         ((mF φF).run ((mT φT).run ⟨s.nextId + 3, s.nextThread⟩).2).2) := rfl
  rw [hr]
  obtain ⟨a₁, a₂⟩ := hT φT ⟨s.nextId + 3, s.nextThread⟩
  generalize (mT φT).run ⟨s.nextId + 3, s.nextThread⟩ = r₁ at a₁ a₂ ⊢
  obtain ⟨kT, s₁⟩ := r₁
  obtain ⟨b₁, b₂⟩ := hF φF s₁
  generalize (mF φF).run s₁ = r₂ at b₁ b₂ ⊢
  obtain ⟨kF, s₂⟩ := r₂
  simp only [ids_addRMW, ids_prefix, ids_plus] at a₁ a₂ b₁ b₂ ⊢
  have hle := Nat.le_trans a₁ b₁
  refine ⟨?_, InRange.cons (InRange.cons (InRange.cons (InRange.append a₂ b₂ a₁ b₁) ?_) ?_) ?_⟩
  all_goals (unfold EventId at *; omega)

/-- Parallel composition: a fresh thread, and the coproduct of two generators. -/
theorem par (m₁ : Gen EventStructure) (m₂ : ThreadId → Gen EventStructure)
    (h₁ : Gen.Fresh m₁) (h₂ : ∀ t, Gen.Fresh (m₂ t)) :
    Gen.Fresh (do
      let t ← freshThread
      let k₁ ← m₁
      let k₂ ← m₂ t
      pure (k₁.plus k₂)) := by
  intro s
  have hr : StateT.run (do
      let t ← freshThread
      let k₁ ← m₁
      let k₂ ← m₂ t
      pure (k₁.plus k₂) : Gen EventStructure) s
      = ((m₁.run ⟨s.nextId, s.nextThread + 1⟩).1.plus
          ((m₂ s.nextThread).run (m₁.run ⟨s.nextId, s.nextThread + 1⟩).2).1,
         ((m₂ s.nextThread).run (m₁.run ⟨s.nextId, s.nextThread + 1⟩).2).2) := rfl
  rw [hr]
  obtain ⟨a₁, a₂⟩ := h₁ ⟨s.nextId, s.nextThread + 1⟩
  generalize m₁.run ⟨s.nextId, s.nextThread + 1⟩ = r₁ at a₁ a₂ ⊢
  obtain ⟨k₁, s₁⟩ := r₁
  obtain ⟨b₁, b₂⟩ := h₂ s.nextThread s₁
  generalize (m₂ s.nextThread).run s₁ = r₂ at b₁ b₂ ⊢
  obtain ⟨k₂, s₂⟩ := r₂
  simp only [ids_plus] at a₁ a₂ b₁ b₂ ⊢
  exact ⟨Nat.le_trans a₁ b₁, InRange.append a₂ b₂ a₁ b₁⟩

end Gen.Fresh

/-! ## The interpreter allocates fresh ids -/

open Gen.Fresh in
/-- Every event `⟨s⟩_{n ρ κ φ}` generates has a fresh id, provided the
    continuation's events do; by induction along the termination measure of
    `interp`. -/
theorem interp_fresh : ∀ (N : Nat) (n : Bounds) (ctx : Ctx) (pc : List Nat) (s : Stmt)
    (ρ : RegState) (κ : Cont) (φ : List Guard),
    sumB s.loops n + sizeOf s < N → (∀ ρ φ, Gen.Fresh (κ ρ φ)) →
    Gen.Fresh (interp n ctx pc s ρ κ φ)
  | 0, _, _, _, _, _, _, _, hN, _ => absurd hN (Nat.not_lt_zero _)
  | N + 1, n, ctx, pc, s, ρ, κ, φ, hN, hκ => by
    rw [interp.eq_def]
    cases s with
    | skip => exact hκ _ _
    | assign r e => exact hκ _ _
    | addrOf r x => exact hκ _ _
    | load o r x =>
        exact mk_prefix ctx pc φ _ (fun e => κ (ρ.set r (.sym e.id)) φ) (fun _ => hκ _ _)
    | loadPtr o r p =>
        exact mk_prefix ctx pc φ _ (fun e => κ (ρ.set r (.sym e.id)) φ) (fun _ => hκ _ _)
    | store o x v => exact mk_prefix ctx pc φ _ (fun _ => κ ρ φ) (fun _ => hκ _ _)
    | storePtr o p v => exact mk_prefix ctx pc φ _ (fun _ => κ ρ φ) (fun _ => hκ _ _)
    | fence o => exact mk_prefix ctx pc φ _ (fun _ => κ ρ φ) (fun _ => hκ _ _)
    | malloc r sz =>
        exact mk_prefix ctx pc φ _ (fun e => κ (ρ.set r (.sym e.id)) φ) (fun _ => hκ _ _)
    | free r => exact mk_prefix ctx pc φ _ (fun _ => κ ρ φ) (fun _ => hκ _ _)
    | fadd or ow r x v =>
        exact mk_fadd ctx (pc ++ [0]) (pc ++ [1]) φ (fun α => .read or (Expr.glob x) α)
          (fun er _ => .write ow (Expr.glob x) (.bin .add (.sym er.id) (v.den ρ))) Expr.tt
          (fun er => κ (ρ.set r (.sym er.id)) φ) (fun _ => hκ _ _)
    | cas or ow r x e₁ e₂ =>
        exact mk_cas ctx (pc ++ [0]) (pc ++ [1]) (pc ++ [2]) φ (fun α => .read or (Expr.glob x) α)
          (fun er => .eq (.sym er.id) (e₁.den ρ)) (fun c _ => .branch c)
          (fun _ => .write ow (Expr.glob x) (e₂.den ρ))
          (fun g => κ (ρ.set r Expr.tt) g) (fun g => κ (ρ.set r Expr.ff) g)
          (fun _ => hκ _ _) (fun _ => hκ _ _)
    | seq s₁ s₂ =>
        simp only [Stmt.loops, sumB_append, Stmt.seq.sizeOf_spec] at hN
        exact interp_fresh N n ctx (pc ++ [0]) s₁ ρ _ φ (by omega)
          (fun ρ' φ' => interp_fresh N n ctx (pc ++ [1]) s₂ ρ' κ φ' (by omega) hκ)
    | par s₁ s₂ =>
        simp only [Stmt.loops, sumB_append, Stmt.par.sizeOf_spec] at hN
        exact par (interp n ctx (pc ++ [0]) s₁ ρ κ φ)
          (fun t => interp n { ctx with thread := t } (pc ++ [1]) s₂ ρ κ φ)
          (interp_fresh N n ctx (pc ++ [0]) s₁ ρ κ φ (by omega) hκ)
          (fun t => interp_fresh N n _ (pc ++ [1]) s₂ ρ κ φ (by omega) hκ)
    | ite b s₁ s₂ =>
        simp only [Stmt.loops, sumB_append, Stmt.ite.sizeOf_spec] at hN
        exact mk_branch ctx pc φ _
          (fun eb => interp n ctx (pc ++ [0]) s₁ ρ κ (φ ++ [⟨eb.id, b.den ρ, true⟩]))
          (fun eb => interp n ctx (pc ++ [1]) s₂ ρ κ (φ ++ [⟨eb.id, b.den ρ, false⟩]))
          (fun _ => interp_fresh N n ctx _ s₁ ρ κ _ (by omega) hκ)
          (fun _ => interp_fresh N n ctx _ s₂ ρ κ _ (by omega) hκ)
    | «while» ℓ b body =>
        dsimp only
        split
        · exact pure_empty
        · simp only [Stmt.loops, sumB_cons, Stmt.while.sizeOf_spec] at hN
          have h₁ := sumB_dec_le body.loops n ℓ
          have h₂ := Bounds.dec_self n ℓ
          refine mk_branch _ pc φ (fun _ => .branch (b.den ρ)) _ _ (fun _ => ?_) (fun _ => hκ _ _)
          exact interp_fresh N (n.dec ℓ) _ _ body ρ _ _ (by omega)
            (fun ρ' φ' => interp_fresh N (n.dec ℓ) _ pc (.while ℓ b body) ρ' κ φ'
              (by simp only [Stmt.loops, sumB_cons, Stmt.while.sizeOf_spec]; omega) hκ)

/-- The events of `⟨P⟩_n` have pairwise distinct ids. -/
theorem denote_ids_nodup (n : Bounds) (P : Stmt) : (denote n P).ids.Nodup :=
  (interp_fresh _ n ⟨0, []⟩ [] P [] (fun _ _ => pure .empty) [] (Nat.lt_succ_self _)
    (fun _ _ => Gen.Fresh.pure_empty) {}).2.1

/-- In `⟨P⟩_n`, `ev` finds every event by its id. -/
theorem denote_ev (n : Bounds) (P : Stmt) {e : Event} (he : e ∈ (denote n P).events) :
    (denote n P).ev e.id = some e :=
  EventStructure.ev_of_mem (denote_ids_nodup n P) he
