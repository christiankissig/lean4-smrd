import Smrd.RMWWFDenote
import Smrd.Labels

/-!
# The RMWs of `⟨P⟩_n` are tight (`denote_rmwTight`)

`Execution.RMWTight` asks of every RMW `(e_r, c, e_w)` that no event of
`X ∪ X_F` lie `⊑`-between `e_r` and `e_w`, and, where `e_w` is in `X ∪ X_F`,
that every event of `X ∪ X_F` `⊑`-after `e_r` be `e_w` or `⊑`-after it. This
module proves it for every execution of `⟨P⟩_n` whose `X` is a maximal
conflict-free set (`denote_rmwTight`), from the shape the interpreter gives:

* `fadd` generates `e_r` immediately before `e_w`, and the continuation after
  `e_w`;
* `cas` generates `e_r`, its branch `e_c`, then `e_w` and the continuation
  under the success guard, and a second copy of the continuation under the
  failure guard. Only `e_c`, a branch, lies between `e_r` and `e_w`; the
  events `⊑`-after `e_r` and not after `e_w` are `e_c` and the failure copy,
  whose guards diverge from `e_w`'s (`Labels.Diverge`).

The combinators keep both facts (`Inv`, closed under `prefix`, `plus` and
`join` once the ids are distinct). A branch is neither in `X` nor in `X_F`, and
an event that diverges from `e_w` is in conflict with it, so not in
`X ∪ X_F` together with `e_w`.

The second clause cannot be asked of every RMW: for
`x := 0; r := CAS(x, 1, 2); y := 1` the copy of `y := 1` under the failure
guard is `⊑`-after the read and not after the write, and `{x := 0, e_r, y := 1}`
is a maximal conflict-free set.

`RMWTightR` follows where `δ` has no edge (`rmwTightR_of_noEdge`).
-/

namespace RMWTightDenote

open EventStructure Execution

/-! ## Value restrictions extend the context's -/

/-- The events of `k` carry value restrictions extending `φ`. -/
def GExt (φ : List Guard) (k : EventStructure) : Prop :=
  ∀ e ∈ k.events, ∃ G, e.guards = φ ++ G

namespace GExt

variable {φ : List Guard}

theorem empty : GExt φ EventStructure.empty := by
  simp [GExt, EventStructure.empty]

theorem weaken {G₀ : List Guard} {k : EventStructure} (h : GExt (φ ++ G₀) k) : GExt φ k :=
  fun e he => by obtain ⟨G, hG⟩ := h e he; exact ⟨G₀ ++ G, by simp [hG]⟩

theorem «prefix» {e : Event} {k : EventStructure} (he : e.guards = φ) (h : GExt φ k) :
    GExt φ («prefix» e k) := by
  intro x hx
  simp only [events_prefix, List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact ⟨[], by simp [he]⟩
  · exact h x hx

theorem plus {k k' : EventStructure} (h : GExt φ k) (h' : GExt φ k') : GExt φ (k.plus k') := by
  intro x hx
  simp only [events_plus, List.mem_append] at hx
  rcases hx with hx | hx
  · exact h x hx
  · exact h' x hx

theorem join {k k' : EventStructure} (h : GExt φ k) (h' : GExt φ k') : GExt φ (k.join k') := by
  intro x hx
  simp only [events_join, List.mem_append] at hx
  rcases hx with hx | hx
  · exact h x hx
  · exact h' x hx

theorem addRMW {k : EventStructure} (h : GExt φ k) (r : EventId) (c : Expr) (w : EventId) :
    GExt φ (k.addRMW r c w) := h

end GExt

open EventStructure in
/-- Every event a run of `⟨s⟩` generates under `φ` has a value restriction
    extending `φ`, provided the continuation's do. -/
theorem interp_gext :
    ∀ (N : Nat) (n : Bounds) (ctx : Ctx) (pc : List Nat) (s : Stmt)
    (ρ : RegState) (κ : Cont) (φ : List Guard),
    sumB s.loops n + sizeOf s < N → (∀ ρ φ', Gen.Holds (GExt φ') (κ ρ φ')) →
    Gen.Holds (GExt φ) (interp n ctx pc s ρ κ φ)
  | 0, _, _, _, _, _, _, _, hN, _ => absurd hN (Nat.not_lt_zero _)
  | N + 1, n, ctx, pc, s, ρ, κ, φ, hN, hκ => by
    have pre1 : ∀ (kind : EventId → EventKind) (m : Event → Gen EventStructure),
        (∀ e, Gen.Holds (GExt φ) (m e)) →
        Gen.Holds (GExt φ)
          (do let e ← mkEvent ctx pc φ kind; let k ← m e; pure («prefix» e k)) :=
      fun kind m hm σ => GExt.prefix (φ := φ) rfl (hm _ _)
    cases s with
    | skip => rw [interp.eq_def]; exact hκ _ _
    | assign r e => rw [interp.eq_def]; exact hκ _ _
    | addrOf r x => rw [interp.eq_def]; exact hκ _ _
    | load o r x => rw [interp.eq_def]; exact pre1 _ _ (fun _ => hκ _ _)
    | loadPtr o r p => rw [interp.eq_def]; exact pre1 _ _ (fun _ => hκ _ _)
    | store o x v => rw [interp.eq_def]; exact pre1 _ _ (fun _ => hκ _ _)
    | storePtr o p v => rw [interp.eq_def]; exact pre1 _ _ (fun _ => hκ _ _)
    | fence o => rw [interp.eq_def]; exact pre1 _ _ (fun _ => hκ _ _)
    | malloc r sz => rw [interp.eq_def]; exact pre1 _ _ (fun _ => hκ _ _)
    | free r => rw [interp.eq_def]; exact pre1 _ _ (fun _ => hκ _ _)
    | fadd or ow r x v =>
        rw [interp.eq_def]
        intro σ
        exact GExt.addRMW (φ := φ) (GExt.prefix rfl (GExt.prefix rfl (hκ _ φ _))) _ _ _
    | cas or ow r x e₁ e₂ =>
        rw [interp.eq_def]
        intro σ
        exact GExt.addRMW (φ := φ) (GExt.prefix rfl (GExt.prefix rfl
          (GExt.plus (GExt.prefix rfl (hκ _ _ _)).weaken (hκ _ _ _).weaken))) _ _ _
    | seq s₁ s₂ =>
        rw [interp.eq_def]
        simp only [Stmt.loops, sumB_append, Stmt.seq.sizeOf_spec] at hN
        exact interp_gext N n ctx (pc ++ [0]) s₁ ρ _ φ (by omega)
          (fun ρ' φ' => interp_gext N n ctx (pc ++ [1]) s₂ ρ' κ φ' (by omega) hκ)
    | par s₁ s₂ =>
        rw [interp.eq_def]
        simp only [Stmt.loops, sumB_append, Stmt.par.sizeOf_spec] at hN
        intro σ
        exact GExt.join (GExt.plus
          (interp_gext N n ctx (pc ++ [0]) s₁ ρ (fun _ _ => pure .empty) φ (by omega)
            (fun _ _ _ => GExt.empty) _)
          (interp_gext N n _ (pc ++ [1]) s₂ ρ (fun _ _ => pure .empty) φ (by omega)
            (fun _ _ _ => GExt.empty) _))
          (hκ _ _ _)
    | ite b s₁ s₂ =>
        rw [interp.eq_def]
        simp only [Stmt.loops, sumB_append, Stmt.ite.sizeOf_spec] at hN
        intro σ
        exact GExt.prefix (φ := φ) rfl (GExt.plus
          (interp_gext N n ctx _ s₁ ρ κ _ (by omega) hκ _).weaken
          (interp_gext N n ctx _ s₂ ρ κ _ (by omega) hκ _).weaken)
    | «while» ℓ b body =>
        rw [interp.eq_def]
        dsimp only
        split
        · exact fun _ => GExt.empty
        · simp only [Stmt.loops, sumB_cons, Stmt.while.sizeOf_spec] at hN
          have h₁ := sumB_dec_le body.loops n ℓ
          have h₂ := Bounds.dec_self n ℓ
          intro σ
          exact GExt.prefix (φ := φ) rfl (GExt.plus
            (interp_gext N (n.dec ℓ) _ _ body ρ _ _ (by omega)
              (fun ρ' φ' => interp_gext N (n.dec ℓ) _ pc (.while ℓ b body) ρ' κ φ'
                (by simp only [Stmt.loops, sumB_cons, Stmt.while.sizeOf_spec]; omega) hκ) _).weaken
            (hκ _ _ _).weaken)

/-! ## The invariant -/

/-- `a` is a branch of `k`. -/
def IsBr (k : EventStructure) (a : EventId) : Prop :=
  ∃ e ∈ k.events, e.id = a ∧ e.isBranch = true

/-- `w` and `b` are events of `k` on different outcomes of one branching. -/
def Div (k : EventStructure) (w b : EventId) : Prop :=
  ∃ ew ∈ k.events, ∃ eb ∈ k.events, ew.id = w ∧ eb.id = b ∧ Labels.Diverge ew eb

/-- The shape of the RMWs of `k`: only a branch lies `⊑`-between the read and
    the write, and an event `⊑`-after the read is the write, `⊑`-after it, a
    branch, or diverges from it. -/
def Tight (k : EventStructure) : Prop :=
  ∀ ent ∈ k.rmw,
    (∀ a, (a, ent.w) ∈ k.po → a = ent.r ∨ (a, ent.r) ∈ k.po ∨ IsBr k a) ∧
    (∀ b, (ent.r, b) ∈ k.po → b = ent.w ∨ (ent.w, b) ∈ k.po ∨ IsBr k b ∨ Div k ent.w b)

/-- `Tight`, with what the combinators need to keep it: `⊑` and the RMWs
    relate events of `k`, and the ids are distinct. -/
def Inv (k : EventStructure) : Prop :=
  (∀ a b, (a, b) ∈ k.po → a ∈ k.ids ∧ b ∈ k.ids) ∧
  (∀ ent ∈ k.rmw, ent.r ∈ k.ids ∧ ent.w ∈ k.ids) ∧
  (k.ids.Nodup → Tight k)

/-- `k'` has the events and the pairs of `k`. -/
def Sub (k k' : EventStructure) : Prop :=
  (∀ e ∈ k.events, e ∈ k'.events) ∧ ∀ p ∈ k.po, p ∈ k'.po

theorem IsBr.mono {k k' : EventStructure} (hs : Sub k k') {a : EventId} (h : IsBr k a) :
    IsBr k' a := by
  obtain ⟨e, he, h₁, h₂⟩ := h
  exact ⟨e, hs.1 e he, h₁, h₂⟩

theorem Div.mono {k k' : EventStructure} (hs : Sub k k') {w b : EventId} (h : Div k w b) :
    Div k' w b := by
  obtain ⟨ew, hew, eb, heb, h₁, h₂, h₃⟩ := h
  exact ⟨ew, hs.1 ew hew, eb, hs.1 eb heb, h₁, h₂, h₃⟩

theorem lift₁ {k k' : EventStructure} (hs : Sub k k') {a r : EventId}
    (h : a = r ∨ (a, r) ∈ k.po ∨ IsBr k a) : a = r ∨ (a, r) ∈ k'.po ∨ IsBr k' a := by
  rcases h with h | h | h
  · exact .inl h
  · exact .inr (.inl (hs.2 _ h))
  · exact .inr (.inr (h.mono hs))

theorem lift₂ {k k' : EventStructure} (hs : Sub k k') {b w : EventId}
    (h : b = w ∨ (w, b) ∈ k.po ∨ IsBr k b ∨ Div k w b) :
    b = w ∨ (w, b) ∈ k'.po ∨ IsBr k' b ∨ Div k' w b := by
  rcases h with h | h | h | h
  · exact .inl h
  · exact .inr (.inl (hs.2 _ h))
  · exact .inr (.inr (.inl (h.mono hs)))
  · exact .inr (.inr (.inr (h.mono hs)))

theorem sub_prefix (e : Event) (k : EventStructure) : Sub k («prefix» e k) :=
  ⟨fun _ h => List.mem_cons_of_mem _ h, fun _ h => mem_po_prefix.2 (.inr h)⟩

theorem sub_plus_left (k k' : EventStructure) : Sub k (k.plus k') :=
  ⟨fun _ h => List.mem_append_left _ h, fun p h => by
    obtain ⟨a, b⟩ := p; exact mem_po_plus.2 (.inl h)⟩

theorem sub_plus_right (k k' : EventStructure) : Sub k' (k.plus k') :=
  ⟨fun _ h => List.mem_append_right _ h, fun p h => by
    obtain ⟨a, b⟩ := p; exact mem_po_plus.2 (.inr h)⟩

theorem sub_join_left (k k' : EventStructure) : Sub k (k.join k') :=
  ⟨fun _ h => List.mem_append_left _ h, fun p h => by
    obtain ⟨a, b⟩ := p; exact mem_po_join.2 (.inl h)⟩

theorem sub_join_right (k k' : EventStructure) : Sub k' (k.join k') :=
  ⟨fun _ h => List.mem_append_right _ h, fun p h => by
    obtain ⟨a, b⟩ := p; exact mem_po_join.2 (.inr (.inl h))⟩

namespace Inv

theorem empty : Inv EventStructure.empty :=
  ⟨fun _ _ h => by simp [EventStructure.empty] at h,
    fun _ h => by simp [EventStructure.empty] at h,
    fun _ _ h => by simp [EventStructure.empty] at h⟩

theorem «prefix» (e : Event) {k : EventStructure} (h : Inv k) : Inv («prefix» e k) := by
  obtain ⟨hin, hrm, hT⟩ := h
  refine ⟨fun a b hab => ?_, fun ent hm => ?_, fun hnd => ?_⟩
  · rcases mem_po_prefix.1 hab with ⟨rfl, hb⟩ | hab
    · simp [hb]
    · simp [(hin a b hab).1, (hin a b hab).2]
  · simp [(hrm ent hm).1, (hrm ent hm).2]
  · simp only [ids_prefix, List.nodup_cons] at hnd
    obtain ⟨hne, hnd⟩ := hnd
    have hs := sub_prefix e k
    intro ent hm
    obtain ⟨h₁, h₂⟩ := hT hnd ent hm
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · rcases mem_po_prefix.1 ha with ⟨rfl, -⟩ | ha
      · exact .inr (.inl (mem_po_prefix.2 (.inl ⟨rfl, (hrm ent hm).1⟩)))
      · exact lift₁ hs (h₁ a ha)
    · rcases mem_po_prefix.1 hb with ⟨he, -⟩ | hb
      · exact absurd (he ▸ (hrm ent hm).1) hne
      · exact lift₂ hs (h₂ b hb)

theorem plus {k k' : EventStructure} (h : Inv k) (h' : Inv k') : Inv (k.plus k') := by
  obtain ⟨hin, hrm, hT⟩ := h
  obtain ⟨hin', hrm', hT'⟩ := h'
  refine ⟨fun a b hab => ?_, fun ent hm => ?_, fun hnd => ?_⟩
  · rcases mem_po_plus.1 hab with h | h
    · simp [(hin a b h).1, (hin a b h).2]
    · simp [(hin' a b h).1, (hin' a b h).2]
  · rcases List.mem_append.1 hm with h | h
    · simp [(hrm ent h).1, (hrm ent h).2]
    · simp [(hrm' ent h).1, (hrm' ent h).2]
  · rw [ids_plus] at hnd
    have dj := fun {a : EventId} (h₁ : a ∈ k.ids) (h₂ : a ∈ k'.ids) => not_mem_of_disj hnd h₁ h₂
    intro ent hm
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨h₁, h₂⟩ := hT (List.nodup_append.1 hnd).1 ent hm
      have hs := sub_plus_left k k'
      refine ⟨fun a ha => ?_, fun b hb => ?_⟩
      · rcases mem_po_plus.1 ha with ha | ha
        · exact lift₁ hs (h₁ a ha)
        · exact (dj (hrm ent hm).2 (hin' _ _ ha).2).elim
      · rcases mem_po_plus.1 hb with hb | hb
        · exact lift₂ hs (h₂ b hb)
        · exact (dj (hrm ent hm).1 (hin' _ _ hb).1).elim
    · obtain ⟨h₁, h₂⟩ := hT' (List.nodup_append.1 hnd).2.1 ent hm
      have hs := sub_plus_right k k'
      refine ⟨fun a ha => ?_, fun b hb => ?_⟩
      · rcases mem_po_plus.1 ha with ha | ha
        · exact (dj (hin _ _ ha).2 (hrm' ent hm).2).elim
        · exact lift₁ hs (h₁ a ha)
      · rcases mem_po_plus.1 hb with hb | hb
        · exact (dj (hin _ _ hb).1 (hrm' ent hm).1).elim
        · exact lift₂ hs (h₂ b hb)

theorem join {k k' : EventStructure} (h : Inv k) (h' : Inv k') : Inv (k.join k') := by
  obtain ⟨hin, hrm, hT⟩ := h
  obtain ⟨hin', hrm', hT'⟩ := h'
  refine ⟨fun a b hab => ?_, fun ent hm => ?_, fun hnd => ?_⟩
  · rcases mem_po_join.1 hab with h | h | ⟨ha, hb⟩
    · simp [(hin a b h).1, (hin a b h).2]
    · simp [(hin' a b h).1, (hin' a b h).2]
    · simp [ha, hb]
  · rcases List.mem_append.1 hm with h | h
    · simp [(hrm ent h).1, (hrm ent h).2]
    · simp [(hrm' ent h).1, (hrm' ent h).2]
  · rw [ids_join] at hnd
    have dj := fun {a : EventId} (h₁ : a ∈ k.ids) (h₂ : a ∈ k'.ids) => not_mem_of_disj hnd h₁ h₂
    intro ent hm
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨h₁, h₂⟩ := hT (List.nodup_append.1 hnd).1 ent hm
      have hs := sub_join_left k k'
      refine ⟨fun a ha => ?_, fun b hb => ?_⟩
      · rcases mem_po_join.1 ha with ha | ha | ⟨-, hw⟩
        · exact lift₁ hs (h₁ a ha)
        · exact (dj (hrm ent hm).2 (hin' _ _ ha).2).elim
        · exact (dj (hrm ent hm).2 hw).elim
      · rcases mem_po_join.1 hb with hb | hb | ⟨-, hb⟩
        · exact lift₂ hs (h₂ b hb)
        · exact (dj (hrm ent hm).1 (hin' _ _ hb).1).elim
        · exact .inr (.inl (mem_po_join.2 (.inr (.inr ⟨(hrm ent hm).2, hb⟩))))
    · obtain ⟨h₁, h₂⟩ := hT' (List.nodup_append.1 hnd).2.1 ent hm
      have hs := sub_join_right k k'
      refine ⟨fun a ha => ?_, fun b hb => ?_⟩
      · rcases mem_po_join.1 ha with ha | ha | ⟨ha, -⟩
        · exact (dj (hin _ _ ha).2 (hrm' ent hm).2).elim
        · exact lift₁ hs (h₁ a ha)
        · exact .inr (.inl (mem_po_join.2 (.inr (.inr ⟨ha, (hrm' ent hm).1⟩))))
      · rcases mem_po_join.1 hb with hb | hb | ⟨hr, -⟩
        · exact (dj (hin _ _ hb).1 (hrm' ent hm).1).elim
        · exact lift₂ hs (h₂ b hb)
        · exact (dj hr (hrm' ent hm).1).elim

/-- An RMW entry added on top of `k`: `Inv` for the new entry from the facts
    about it, for the old ones from `Inv k`. -/
theorem addRMW {k : EventStructure} (h : Inv k) {r w : EventId} {c : Expr}
    (hr : r ∈ k.ids) (hw : w ∈ k.ids)
    (hnew : k.ids.Nodup →
      (∀ a, (a, w) ∈ k.po → a = r ∨ (a, r) ∈ k.po ∨ IsBr k a) ∧
      (∀ b, (r, b) ∈ k.po → b = w ∨ (w, b) ∈ k.po ∨ IsBr k b ∨ Div k w b)) :
    Inv (k.addRMW r c w) := by
  obtain ⟨hin, hrm, hT⟩ := h
  refine ⟨hin, fun ent hm => ?_, fun hnd ent hm => ?_⟩
  · rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨hr, hw⟩
    · exact hrm ent hm
  · rcases List.mem_cons.1 hm with rfl | hm
    · exact hnew hnd
    · exact hT hnd ent hm

/-- `fadd`: the read immediately before the write. -/
theorem fadd (er ew : Event) {k : EventStructure} (h : Inv k) :
    Inv ((EventStructure.prefix er (EventStructure.prefix ew k)).addRMW er.id Expr.tt ew.id) := by
  have hK := (h.prefix ew).prefix er
  refine hK.addRMW (by simp) (by simp) fun hnd => ?_
  rw [ids_prefix, ids_prefix] at hnd
  have h₁ := List.nodup_cons.1 hnd
  have her₁ : er.id ≠ ew.id := fun h => h₁.1 (h ▸ List.mem_cons_self)
  have her₂ : er.id ∉ k.ids := fun h => h₁.1 (List.mem_cons_of_mem _ h)
  have hew : ew.id ∉ k.ids := (List.nodup_cons.1 h₁.2).1
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases mem_po_prefix.1 ha with ⟨rfl, -⟩ | ha
    · exact .inl rfl
    · rcases mem_po_prefix.1 ha with ⟨-, hw⟩ | ha
      · exact absurd hw hew
      · exact absurd (h.1 _ _ ha).2 hew
  · rcases mem_po_prefix.1 hb with ⟨-, hb⟩ | hb
    · rw [ids_prefix, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact .inl rfl
      · exact .inr (.inl (mem_po_prefix.2 (.inr (mem_po_prefix.2 (.inl ⟨rfl, hb⟩)))))
    · rcases mem_po_prefix.1 hb with ⟨he, -⟩ | hb
      · exact absurd he her₁
      · exact absurd (h.1 _ _ hb).1 her₂

/-- `cas`: the read, the branch, the write and the continuation under the
    success guard, and the continuation under the failure guard. -/
theorem cas (er ec ew : Event) {kT kF : EventStructure} {φ : List Guard} {c : Expr}
    (hT : Inv kT) (hF : Inv kF) (hG : GExt (φ ++ [⟨ec.id, c, false⟩]) kF)
    (hew : ew.guards = φ ++ [⟨ec.id, c, true⟩]) (hbr : ec.isBranch = true) :
    Inv ((EventStructure.prefix er (EventStructure.prefix ec
      ((EventStructure.prefix ew kT).plus kF))).addRMW er.id c ew.id) := by
  have hK := (((hT.prefix ew).plus hF).prefix ec).prefix er
  refine hK.addRMW (by simp) (by simp) fun hnd => ?_
  rw [ids_prefix, ids_prefix, ids_plus] at hnd
  have h₁ := List.nodup_cons.1 hnd
  have her₁ : er.id ≠ ec.id := fun h => h₁.1 (h ▸ List.mem_cons_self)
  have her₂ : er.id ∉ (EventStructure.prefix ew kT).ids ++ kF.ids :=
    fun h => h₁.1 (List.mem_cons_of_mem _ h)
  have hdj : ((EventStructure.prefix ew kT).ids ++ kF.ids).Nodup := (List.nodup_cons.1 h₁.2).2
  have hewT : ew.id ∉ kT.ids := by
    have := (List.nodup_append.1 hdj).1
    simp only [ids_prefix, List.nodup_cons] at this
    exact this.1
  have hewF : ew.id ∉ kF.ids := fun h =>
    not_mem_of_disj hdj (by simp [ids_prefix]) h
  -- the events of `K`
  let K := EventStructure.prefix er (EventStructure.prefix ec
    ((EventStructure.prefix ew kT).plus kF))
  have hsub : Sub ((EventStructure.prefix ew kT).plus kF) K :=
    ⟨fun e he => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he),
      fun p hp => (sub_prefix er _).2 _ ((sub_prefix ec _).2 _ hp)⟩
  have hecK : ec ∈ K.events := List.mem_cons_of_mem _ List.mem_cons_self
  have hewK : ew ∈ K.events :=
    hsub.1 _ (List.mem_append_left _ List.mem_cons_self)
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases mem_po_prefix.1 ha with ⟨rfl, -⟩ | ha
    · exact .inl rfl
    rcases mem_po_prefix.1 ha with ⟨rfl, -⟩ | ha
    · exact .inr (.inr ⟨ec, hecK, rfl, hbr⟩)
    rcases mem_po_plus.1 ha with ha | ha
    · rcases mem_po_prefix.1 ha with ⟨-, hw⟩ | ha
      · exact absurd hw hewT
      · exact absurd (hT.1 _ _ ha).2 hewT
    · exact absurd (hF.1 _ _ ha).2 hewF
  · rcases mem_po_prefix.1 hb with ⟨-, hb⟩ | hb
    · simp only [ids_prefix, ids_plus, List.mem_cons, List.mem_append] at hb
      rcases hb with rfl | (rfl | hb) | hb
      · exact .inr (.inr (.inl ⟨ec, hecK, rfl, hbr⟩))
      · exact .inl rfl
      · exact .inr (.inl (hsub.2 _ (mem_po_plus.2 (.inl (mem_po_prefix.2 (.inl ⟨rfl, hb⟩))))))
      · obtain ⟨eb, heb, rfl⟩ := List.mem_map.1 hb
        obtain ⟨G, hG'⟩ := hG eb heb
        refine .inr (.inr (.inr ⟨ew, hewK, eb, hsub.1 _ (List.mem_append_right _ heb), rfl, rfl,
          ⟨⟨ec.id, c, true⟩, by rw [hew]; exact List.mem_append_right _ List.mem_cons_self,
            ⟨ec.id, c, false⟩, by rw [hG']; exact List.mem_append_left _ (List.mem_append_right _
              List.mem_cons_self), rfl, rfl, by simp⟩⟩))
    · rcases mem_po_prefix.1 hb with ⟨he, -⟩ | hb
      · exact absurd he her₁
      · rcases mem_po_plus.1 hb with hb | hb
        · rcases mem_po_prefix.1 hb with ⟨he, -⟩ | hb
          · exact absurd (List.mem_append_left _ (he ▸ (by simp [ids_prefix]))) her₂
          · exact absurd (List.mem_append_left _ (by simp [ids_prefix, (hT.1 _ _ hb).1])) her₂
        · exact absurd (List.mem_append_right _ (hF.1 _ _ hb).1) her₂

end Inv

open EventStructure in
/-- The RMWs of every run of `⟨s⟩` are `Tight`, provided the continuation's
    are and its events' value restrictions extend the context's. -/
theorem interp_inv :
    ∀ (N : Nat) (n : Bounds) (ctx : Ctx) (pc : List Nat) (s : Stmt)
    (ρ : RegState) (κ : Cont) (φ : List Guard),
    sumB s.loops n + sizeOf s < N → (∀ ρ φ', Gen.Holds Inv (κ ρ φ')) →
    (∀ ρ φ', Gen.Holds (GExt φ') (κ ρ φ')) →
    Gen.Holds Inv (interp n ctx pc s ρ κ φ)
  | 0, _, _, _, _, _, _, _, hN, _, _ => absurd hN (Nat.not_lt_zero _)
  | N + 1, n, ctx, pc, s, ρ, κ, φ, hN, hκ, hκG => by
    have pre1 : ∀ (kind : EventId → EventKind) (m : Event → Gen EventStructure),
        (∀ e, Gen.Holds Inv (m e)) →
        Gen.Holds Inv (do let e ← mkEvent ctx pc φ kind; let k ← m e; pure («prefix» e k)) :=
      fun kind m hm σ => Inv.prefix _ (hm _ _)
    cases s with
    | skip => rw [interp.eq_def]; exact hκ _ _
    | assign r e => rw [interp.eq_def]; exact hκ _ _
    | addrOf r x => rw [interp.eq_def]; exact hκ _ _
    | load o r x => rw [interp.eq_def]; exact pre1 _ _ (fun _ => hκ _ _)
    | loadPtr o r p => rw [interp.eq_def]; exact pre1 _ _ (fun _ => hκ _ _)
    | store o x v => rw [interp.eq_def]; exact pre1 _ _ (fun _ => hκ _ _)
    | storePtr o p v => rw [interp.eq_def]; exact pre1 _ _ (fun _ => hκ _ _)
    | fence o => rw [interp.eq_def]; exact pre1 _ _ (fun _ => hκ _ _)
    | malloc r sz => rw [interp.eq_def]; exact pre1 _ _ (fun _ => hκ _ _)
    | free r => rw [interp.eq_def]; exact pre1 _ _ (fun _ => hκ _ _)
    | fadd or ow r x v =>
        rw [interp.eq_def]
        intro σ
        exact Inv.fadd _ _ (hκ _ _ _)
    | cas or ow r x e₁ e₂ =>
        rw [interp.eq_def]
        intro σ
        exact Inv.cas _ _ _ (hκ _ _ _) (hκ _ _ _) (hκG _ _ _) rfl rfl
    | seq s₁ s₂ =>
        rw [interp.eq_def]
        simp only [Stmt.loops, sumB_append, Stmt.seq.sizeOf_spec] at hN
        exact interp_inv N n ctx (pc ++ [0]) s₁ ρ _ φ (by omega)
          (fun ρ' φ' => interp_inv N n ctx (pc ++ [1]) s₂ ρ' κ φ' (by omega) hκ hκG)
          (fun ρ' φ' => interp_gext N n ctx (pc ++ [1]) s₂ ρ' κ φ' (by omega) hκG)
    | par s₁ s₂ =>
        rw [interp.eq_def]
        simp only [Stmt.loops, sumB_append, Stmt.par.sizeOf_spec] at hN
        intro σ
        exact Inv.join (Inv.plus
          (interp_inv N n ctx (pc ++ [0]) s₁ ρ (fun _ _ => pure .empty) φ (by omega)
            (fun _ _ _ => Inv.empty) (fun _ _ _ => GExt.empty) _)
          (interp_inv N n _ (pc ++ [1]) s₂ ρ (fun _ _ => pure .empty) φ (by omega)
            (fun _ _ _ => Inv.empty) (fun _ _ _ => GExt.empty) _))
          (hκ _ _ _)
    | ite b s₁ s₂ =>
        rw [interp.eq_def]
        simp only [Stmt.loops, sumB_append, Stmt.ite.sizeOf_spec] at hN
        intro σ
        exact Inv.prefix _ (Inv.plus (interp_inv N n ctx _ s₁ ρ κ _ (by omega) hκ hκG _)
          (interp_inv N n ctx _ s₂ ρ κ _ (by omega) hκ hκG _))
    | «while» ℓ b body =>
        rw [interp.eq_def]
        dsimp only
        split
        · exact fun _ => Inv.empty
        · simp only [Stmt.loops, sumB_cons, Stmt.while.sizeOf_spec] at hN
          have h₁ := sumB_dec_le body.loops n ℓ
          have h₂ := Bounds.dec_self n ℓ
          have hm : sumB (Stmt.while ℓ b body).loops (n.dec ℓ) +
              sizeOf (Stmt.while ℓ b body) < N := by
            simp only [Stmt.loops, sumB_cons, Stmt.while.sizeOf_spec]; omega
          intro σ
          exact Inv.prefix _ (Inv.plus
            (interp_inv N (n.dec ℓ) _ _ body ρ _ _ (by omega)
              (fun ρ' φ' => interp_inv N (n.dec ℓ) _ pc (.while ℓ b body) ρ' κ φ' hm hκ hκG)
              (fun ρ' φ' => interp_gext N (n.dec ℓ) _ pc (.while ℓ b body) ρ' κ φ' hm hκG) _)
            (hκ _ _ _))

/-- **The RMWs of `⟨P⟩_n` have the shape `Tight`.** -/
theorem denote_tight (n : Bounds) (P : Stmt) : Tight (denote n P) :=
  (interp_inv _ n ⟨0, []⟩ [] P [] (fun _ _ => pure .empty) [] (Nat.lt_succ_self _)
    (fun _ _ _ => Inv.empty) (fun _ _ _ => GExt.empty) {}).2.2 (denote_ids_nodup n P)

theorem not_branch_fence {e : Event} (hb : e.isBranch = true) (hf : e.isFence = true) : False := by
  obtain ⟨id, kind, label, guards⟩ := e
  cases kind <;> simp_all [Event.isBranch, Event.isFence]

/-- A branch is neither in `X` nor in `X_F`. -/
theorem not_XwF_of_isBr {n : Bounds} {P : Stmt} {x : Execution}
    (hmax : (denote n P).MaximalConflictFree x.X) {a : EventId} (hbr : IsBr (denote n P) a) :
    ¬ x.XwF (denote n P) a := by
  obtain ⟨e, he, rfl, hb⟩ := hbr
  have hev := denote_ev n P he
  rintro (hX | hF)
  · exact (hmax.1 _ hX).2.1 ⟨e, hev, hb⟩
  · obtain ⟨e', he', hf⟩ := hF.2.1
    rw [hev] at he'; cases he'
    exact not_branch_fence hb hf

/-- **The RMWs of `⟨P⟩_n` are tight** for every execution whose `X` is a
    maximal conflict-free set: no event of `X ∪ X_F` lies `⊑`-between the
    read and the write, and where the write is in `X ∪ X_F`, every event of
    `X ∪ X_F` `⊑`-after the read is the write or `⊑`-after it. -/
theorem denote_rmwTight {n : Bounds} {P : Stmt} {x : Execution}
    (hmax : (denote n P).MaximalConflictFree x.X) : RMWTight (denote n P) x := by
  have hT := denote_tight n P
  refine ⟨fun ent hm a ha hpo => ?_, fun ent hm hw b hb hpo => ?_⟩
  · rcases (hT ent hm).1 a hpo with h | h | h
    · exact .inl h
    · exact .inr h
    · exact absurd ha (not_XwF_of_isBr hmax h)
  · rcases (hT ent hm).2 b hpo with h | h | h | ⟨ew, hew, eb, heb, hwid, rfl, hd⟩
    · exact .inl h
    · exact .inr h
    · exact absurd hb (not_XwF_of_isBr hmax h)
    · -- `e_w` and `b` diverge: they are in conflict, and not both in `X ∪ X_F`
      have hc : (denote n P).Conflict ent.w eb.id :=
        ⟨ew, eb, hwid ▸ denote_ev n P hew, denote_ev n P heb, hd.not_sat⟩
      have hc' : (denote n P).Conflict eb.id ent.w :=
        ⟨eb, ew, denote_ev n P heb, hwid ▸ denote_ev n P hew, hd.symm.not_sat⟩
      -- the write of an RMW has a location, so it is no fence
      have hwX : x.X ent.w := by
        rcases hw with hw | hw
        · exact hw
        · obtain ⟨-, e₂, -, l₂, -, he₂, -, hl₂, -⟩ := (RMWWFDenote.denote_rmwWF n P ent hm).2
          obtain ⟨e', he', hf⟩ := hw.2.1
          rw [he₂] at he'; cases he'
          obtain ⟨id, kind, label, guards⟩ := e₂
          cases kind <;> simp_all [Event.isFence, Event.loc]
      rcases hb with hbX | hbF
      · exact absurd hc (hmax.2.1 _ _ hwX hbX)
      · exact absurd hc (hbF.2.2 _ hwX)

end RMWTightDenote
