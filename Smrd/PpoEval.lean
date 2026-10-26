import Smrd.PpoTail

/-!
# Evaluating MoRDor's `≼` on concrete executions

`Execution.ppo` is a relation over semantic predicates and cannot be evaluated
as it stands. For event structures whose locations are globals and which have
no read-modify-writes, executions without fences, and forwarding contexts of
depth one, its alias queries reduce to syntactic equality of locations, and
`≼` to a list computation (`ppoEval`), which `ppoEval_iff` proves equal to
`Execution.ppo`. It is what the differential test against MoRDor
(`scripts/ppo_diff.py`, through the `smrd-ppo` executable) evaluates.

The hypotheses of `ppoEval_iff`: the locations of the structure are globals
(`GlobLocs`), it has no RMW entries, the execution has no fence on its path
(`FenceFree`), `X` is the list `Xs`, `δ` has depth one with unique
predecessors, the predicates `P_j ∧ ψ_δ` and MoRDor's combined predicate are
satisfiable, and the computed closure is closed (`closedB`, checked when it is
evaluated).
-/

namespace PpoEval

open EventStructure

variable (es : EventStructure)

/-- The location of an event, if any. -/
def locOf (a : EventId) : Option Expr := (es.ev a).bind Event.loc

/-- A classifier as a boolean. -/
def clsB (p : Event → Bool) (a : EventId) : Bool :=
  match es.ev a with
  | some e => p e
  | none => false

theorem cls_iff {p : Event → Bool} {a : EventId} : es.cls p a ↔ clsB es p a = true := by
  unfold clsB EventStructure.cls
  cases es.ev a <;> simp

/-- The same location, syntactically. -/
def aliasB (a b : EventId) : Bool :=
  match locOf es a, locOf es b with
  | some l₁, some l₂ => decide (l₁ = l₂)
  | _, _ => false

def syncB (a b : EventId) : Bool := clsB es Event.isAcqM a || clsB es Event.isRelM b

/-- MoRDor's `ppo_sync`, as a list. -/
def syncL : List (EventId × EventId) := es.po.filter fun p => syncB es p.1 p.2

/-- The base relation of `ForwardingContext.ppo` without RMWs, as a list. -/
def baseL : List (EventId × EventId) := es.po.filter fun p => syncB es p.1 p.2 || aliasB es p.1 p.2

/-- `remap_δ` for a context of depth one. -/
def rm (δ : FwdCtx) (a : EventId) : EventId :=
  match (δ.f ++ δ.we).find? (fun p => p.2 == a) with
  | some p => p.1
  | none => a

/-- A pair is the image of a pair of `L` under `rm`, with distinct ends. -/
def imgB (δ : FwdCtx) (L : List (EventId × EventId)) (a b : EventId) : Bool :=
  a != b && L.any fun p => rm δ p.1 == a && rm δ p.2 == b

def winB (j : Justification) (a : EventId) : Bool := a == j.w.id || decide ((a, j.w.id) ∈ es.po)

/-- A step of MoRDor's `≼`, over the events `Xs`. -/
def stepB (Xs : List EventId) (J : List Justification) (δ : FwdCtx) (a b : EventId) : Bool :=
  decide (a ∈ Xs) && decide (b ∈ Xs) &&
    ((J.any fun j => winB es j a && winB es j b && imgB δ (baseL es) a b) ||
     imgB δ (syncL es) a b || (imgB δ (baseL es) a b && aliasB es a b))

/-- The steps among `Xs`. -/
def stepL (Xs : List EventId) (J : List Justification) (δ : FwdCtx) : List (EventId × EventId) :=
  (Xs.flatMap fun a => Xs.map fun b => (a, b)).filter fun p => stepB es Xs J δ p.1 p.2

/-- One round of composition. -/
def extend (R L : List (EventId × EventId)) : List (EventId × EventId) :=
  L ++ (L.flatMap fun p => (R.filter fun q => q.1 == p.2).map fun q => (p.1, q.2))

/-- `n` rounds of composition, kept within the pairs `U`. -/
def iter (U R : List (EventId × EventId)) : Nat → List (EventId × EventId)
  | 0 => R
  | n + 1 =>
      let E := extend R (iter U R n)
      U.filter fun p => decide (p ∈ E)

/-- `L` is closed under appending an `R`-step. -/
def closedB (R L : List (EventId × EventId)) : Bool :=
  L.all fun p => R.all fun q => q.1 != p.2 || decide ((p.1, q.2) ∈ L)

/-- **MoRDor's `≼` of an execution**, computed. -/
def ppoEval (Xs : List EventId) (J : List Justification) (δ : FwdCtx) : List (EventId × EventId) :=
  iter (Xs.flatMap fun a => Xs.map fun b => (a, b)) (stepL es Xs J δ) Xs.length

/-! ## The closure -/

theorem mem_iter_sound {U R : List (EventId × EventId)} {n : Nat} {a b : EventId}
    (h : (a, b) ∈ iter U R n) : Relation.TransGen (fun a b => (a, b) ∈ R) a b := by
  induction n generalizing a b with
  | zero => exact .single h
  | succ n ih =>
      simp only [iter, extend] at h
      rcases List.mem_append.1 (of_decide_eq_true (List.mem_filter.1 h).2) with h | h
      · exact ih h
      · obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 h
        obtain ⟨q, hq', he⟩ := List.mem_map.1 hq
        obtain ⟨hqR, hq1⟩ := List.mem_filter.1 hq'
        cases he
        have := beq_iff_eq.1 hq1
        exact .tail (ih (a := p.1) (b := p.2) hp) (this ▸ hqR)

theorem R_sub_iter {U R : List (EventId × EventId)} (hRU : ∀ p ∈ R, p ∈ U) {n : Nat}
    {p : EventId × EventId} (h : p ∈ R) : p ∈ iter U R n := by
  induction n with
  | zero => exact h
  | succ n ih =>
      simp only [iter, extend]
      exact List.mem_filter.2 ⟨hRU p h, decide_eq_true (List.mem_append.2 (.inl ih))⟩

theorem mem_of_closed {R L : List (EventId × EventId)} (hR : ∀ p ∈ R, p ∈ L)
    (hc : closedB R L = true) {a b : EventId}
    (h : Relation.TransGen (fun a b => (a, b) ∈ R) a b) : (a, b) ∈ L := by
  induction h with
  | single h => exact hR _ h
  | tail _ h ih =>
      have := List.all_eq_true.1 hc _ ih
      have := List.all_eq_true.1 this _ h
      simp only [bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at this
      exact this

/-! ## The steps -/

/-- Every location of the structure is a global. -/
def GlobLocs : Prop := ∀ e ∈ es.events, ∀ l, e.loc = some l → ∃ x, l = Expr.glob x

/-- `δ` has depth one: no source of an edge is a target. -/
def Depth1 (δ : FwdCtx) : Prop := ∀ c a, δ.edge c a → ∀ d, ¬ δ.edge d c

variable {es}

theorem ev_mem {a : EventId} {e : Event} (h : es.ev a = some e) : e ∈ es.events := by
  unfold EventStructure.ev at h
  exact List.mem_of_find?_eq_some h

theorem loc_glob (hg : GlobLocs es) {a : EventId} {e : Event} {l : Expr} (he : es.ev a = some e)
    (hl : e.loc = some l) : ∃ x, l = Expr.glob x := hg e (ev_mem he) l hl

theorem glob_eval (x : Var) (f : Valuation) : (Expr.glob x).eval f = some (.loc ⟨.global x, 0⟩) := rfl

theorem mustAlias_iff (hg : GlobLocs es) {a b : EventId} : es.mustAlias a b ↔ aliasB es a b = true := by
  unfold aliasB locOf
  constructor
  · rintro ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, hs⟩
    obtain ⟨x, rfl⟩ := loc_glob hg h₁ hl₁
    obtain ⟨y, rfl⟩ := loc_glob hg h₂ hl₂
    have := hs (fun _ => .num 0) _ _ (glob_eval x _) (glob_eval y _)
    simp only [Val.loc.injEq, Loc.mk.injEq, LocBase.global.injEq, and_true] at this
    subst this
    simp [h₁, h₂, hl₁, hl₂]
  · intro h
    cases h₁ : es.ev a with
    | none => simp [h₁] at h
    | some e₁ =>
      cases h₂ : es.ev b with
      | none => simp [h₁, h₂] at h
      | some e₂ =>
        cases hl₁ : e₁.loc with
        | none => simp [h₁, h₂, hl₁] at h
        | some l₁ =>
          cases hl₂ : e₂.loc with
          | none => simp [h₁, h₂, hl₁, hl₂] at h
          | some l₂ =>
            simp [h₁, h₂, hl₁, hl₂] at h
            subst h
            exact ⟨e₁, e₂, l₁, l₁, h₁, h₂, hl₁, hl₂, fun f v₁ v₂ h₁ h₂ => by
              rw [h₁] at h₂; cases h₂; rfl⟩

theorem mayAlias_iff (hg : GlobLocs es) {P : Pred} (hP : Sat P) {a b : EventId} :
    es.mayAlias P a b ↔ aliasB es a b = true := by
  constructor
  · rintro ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, -, hq⟩
    obtain ⟨x, rfl⟩ := loc_glob hg h₁ hl₁
    obtain ⟨y, rfl⟩ := loc_glob hg h₂ hl₂
    have hxy : x = y := by simpa [Expr.holds, Expr.eval, Expr.glob] using hq
    subst hxy
    unfold aliasB locOf
    simp [h₁, h₂, hl₁, hl₂]
  · intro h
    obtain ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, hs⟩ := (mustAlias_iff hg).2 h
    obtain ⟨x, rfl⟩ := loc_glob hg h₁ hl₁
    obtain ⟨y, rfl⟩ := loc_glob hg h₂ hl₂
    have := hs (fun _ => .num 0) _ _ (glob_eval x _) (glob_eval y _)
    simp only [Val.loc.injEq, Loc.mk.injEq, LocBase.global.injEq, and_true] at this
    subst this
    obtain ⟨f, hf⟩ := hP
    exact ⟨e₁, e₂, _, _, h₁, h₂, hl₁, hl₂, f, hf, by simp [Expr.holds, Expr.eval, Expr.glob]⟩

theorem baseM_iff (hg : GlobLocs es) (hrmw : es.rmw = []) {Pa Pr : Pred} (hP : Sat Pa)
    {a b : EventId} : es.ppoBaseM Pa Pr a b ↔ (a, b) ∈ baseL es := by
  unfold baseL
  rw [List.mem_filter]
  constructor
  · rintro ((⟨hpo, h⟩ | (⟨_, -, ent, hm, -⟩ | ⟨_, ⟨ent, hm, -⟩, -⟩)) | ⟨hpo, h⟩)
    · refine ⟨hpo, ?_⟩
      rcases h with h | h <;> simp [syncB, (cls_iff es).1 h]
    · rw [hrmw] at hm; cases hm
    · rw [hrmw] at hm; cases hm
    · refine ⟨hpo, ?_⟩
      rcases h with h | h
      · simp [(mustAlias_iff hg).1 h]
      · simp [(mayAlias_iff hg hP).1 h]
  · rintro ⟨hpo, h⟩
    simp only [Bool.or_eq_true, syncB] at h
    rcases h with (h | h) | h
    · exact .inl (.inl ⟨hpo, .inl ((cls_iff es).2 h)⟩)
    · exact .inl (.inl ⟨hpo, .inr ((cls_iff es).2 h)⟩)
    · exact .inr ⟨hpo, .inl ((mustAlias_iff hg).2 h)⟩

theorem syncM_iff {a b : EventId} : es.ppoSyncM a b ↔ (a, b) ∈ syncL es := by
  unfold syncL syncB EventStructure.ppoSyncM
  rw [List.mem_filter]
  simp only [Bool.or_eq_true, ← cls_iff]
  rfl

theorem remap_iff {δ : FwdCtx} (hd : Depth1 δ) (hu : ∀ a b e, δ.edge a e → δ.edge b e → a = b)
    {a a' : EventId} : δ.Remap a a' ↔ a' = rm δ a := by
  have find_some : ∀ c, δ.edge c a → rm δ a = c := by
    intro c hc
    unfold rm
    cases hf : (δ.f ++ δ.we).find? (fun p => p.2 == a) with
    | none =>
        exfalso
        have := List.find?_eq_none.1 hf (c, a) (List.mem_append.2 hc)
        simp at this
    | some p =>
        have hp := List.mem_of_find?_eq_some hf
        have hp2 : p.2 = a := by simpa using List.find?_some hf
        exact hu p.1 c a (List.mem_append.1 (hp2 ▸ hp)) hc
  have find_none : (∀ c, ¬ δ.edge c a) → rm δ a = a := by
    intro hn
    unfold rm
    cases hf : (δ.f ++ δ.we).find? (fun p => p.2 == a) with
    | none => rfl
    | some p =>
        exfalso
        have hp := List.mem_of_find?_eq_some hf
        have hp2 : p.2 = a := by simpa using List.find?_some hf
        exact hn p.1 (List.mem_append.1 (hp2 ▸ hp))
  constructor
  · intro h
    cases h with
    | canon hno => exact (find_none hno).symm
    | step he hr =>
        cases hr with
        | canon _ => exact (find_some _ he).symm
        | step he' _ => exact absurd he' (hd _ _ he _)
  · rintro rfl
    by_cases hex : ∃ c, δ.edge c a
    · obtain ⟨c, hc⟩ := hex
      rw [find_some c hc]
      exact .step hc (.canon (fun d hdc => hd _ _ hc d hdc))
    · have hn : ∀ c, ¬ δ.edge c a := fun c hc => hex ⟨c, hc⟩
      rw [find_none hn]
      exact .canon hn

theorem remapRel_iff {δ : FwdCtx} (hd : Depth1 δ) (hu : ∀ a b e, δ.edge a e → δ.edge b e → a = b)
    {R : Rel} {L : List (EventId × EventId)} (hRL : ∀ a b, R a b ↔ (a, b) ∈ L) {a b : EventId} :
    (δ.remapRel R).offDiag a b ↔ imgB δ L a b = true := by
  unfold imgB
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨a₀, b₀, hR, ha, hb⟩, hne⟩
    exact ⟨hne, (a₀, b₀), (hRL _ _).1 hR, ((remap_iff hd hu).1 ha).symm,
      ((remap_iff hd hu).1 hb).symm⟩
  · rintro ⟨hne, p, hp, h₁, h₂⟩
    exact ⟨⟨p.1, p.2, (hRL _ _).2 hp, (remap_iff hd hu).2 h₁.symm, (remap_iff hd hu).2 h₂.symm⟩, hne⟩

variable {x : Execution}

theorem step_iff (hg : GlobLocs es) (hrmw : es.rmw = []) (hnf : x.FenceFree es)
    {Xs : List EventId} (hX : ∀ a, x.X a ↔ a ∈ Xs)
    (hd : Depth1 x.δ) (hu : ∀ a b e, x.δ.edge a e → x.δ.edge b e → a = b)
    (hPJ : ∀ j ∈ x.J, Sat (x.PJ es j)) (hPm : Sat (x.Pm es)) {a b : EventId} :
    x.ppoStep es a b ↔ stepB es Xs x.J x.δ a b = true := by
  have hw : ∀ c, x.XwF es c ↔ c ∈ Xs := fun c =>
    ⟨fun h => (hX c).1 (Execution.X_of_XwF hnf h), fun h => .inl ((hX c).2 h)⟩
  have hb : ∀ {Pa Pr : Pred}, Sat Pa → ∀ c d, es.ppoBaseM Pa Pr c d ↔ (c, d) ∈ baseL es :=
    fun hP _ _ => baseM_iff hg hrmw hP
  unfold stepB Execution.ppoStep
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true]
  rw [hw, hw]
  constructor
  · rintro ⟨ha, hb', h⟩
    refine ⟨⟨ha, hb'⟩, ?_⟩
    rcases h with ⟨j, hj, hp, hwa, hwb⟩ | hs | ⟨hp, hal⟩
    · refine .inl (.inl ⟨j, hj, ⟨⟨?_, ?_⟩, (remapRel_iff hd hu (hb (hPJ j hj))).1 hp⟩⟩)
      · rcases hwa with h | h
        · simp [winB, h]
        · simp [winB, show (a, j.w.id) ∈ es.po from h]
      · rcases hwb with h | h
        · simp [winB, h]
        · simp [winB, show (b, j.w.id) ∈ es.po from h]
    · exact .inl (.inr ((remapRel_iff hd hu (fun _ _ => syncM_iff)).1 hs))
    · exact .inr ⟨(remapRel_iff hd hu (hb hPm)).1 hp, (mayAlias_iff hg hPm).1 hal⟩
  · rintro ⟨⟨ha, hb'⟩, h⟩
    refine ⟨ha, hb', ?_⟩
    rcases h with (⟨j, hj, ⟨hwa, hwb⟩, hi⟩ | hi) | ⟨hi, hal⟩
    · refine .inl ⟨j, hj, (remapRel_iff hd hu (hb (hPJ j hj))).2 hi, ?_, ?_⟩
      · simp only [winB, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hwa
        exact hwa
      · simp only [winB, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hwb
        exact hwb
    · exact .inr (.inl ((remapRel_iff hd hu (fun _ _ => syncM_iff)).2 hi))
    · exact .inr (.inr ⟨(remapRel_iff hd hu (hb hPm)).2 hi, (mayAlias_iff hg hPm).2 hal⟩)

/-- **The computed `≼` is MoRDor's `≼`**, under the hypotheses of the module
    docstring; `closedB` is checked on the computed list. -/
theorem ppoEval_iff (hg : GlobLocs es) (hrmw : es.rmw = []) (hnf : x.FenceFree es)
    {Xs : List EventId} (hX : ∀ a, x.X a ↔ a ∈ Xs)
    (hd : Depth1 x.δ) (hu : ∀ a b e, x.δ.edge a e → x.δ.edge b e → a = b)
    (hPJ : ∀ j ∈ x.J, Sat (x.PJ es j)) (hPm : Sat (x.Pm es))
    (hc : closedB (stepL es Xs x.J x.δ) (ppoEval es Xs x.J x.δ) = true) {a b : EventId} :
    x.ppo es a b ↔ (a, b) ∈ ppoEval es Xs x.J x.δ := by
  have hR : ∀ c d, x.ppoStep es c d ↔ (c, d) ∈ stepL es Xs x.J x.δ := by
    intro c d
    rw [step_iff hg hrmw hnf hX hd hu hPJ hPm]
    unfold stepL
    rw [List.mem_filter]
    constructor
    · intro h
      have hc : c ∈ Xs := by
        unfold stepB at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1
      have hd' : d ∈ Xs := by
        unfold stepB at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.2
      exact ⟨List.mem_flatMap.2 ⟨c, hc, List.mem_map.2 ⟨d, hd', rfl⟩⟩, h⟩
    · exact fun h => h.2
  have hTG : ∀ c d, Relation.TransGen (x.ppoStep es) c d ↔
      Relation.TransGen (fun a b => (a, b) ∈ stepL es Xs x.J x.δ) c d := fun c d =>
    ⟨fun h => Execution.transGen_mono (fun _ _ h => (hR _ _).1 h) h,
     fun h => Execution.transGen_mono (fun _ _ h => (hR _ _).2 h) h⟩
  have hXstep : ∀ c d, (c, d) ∈ stepL es Xs x.J x.δ → c ∈ Xs ∧ d ∈ Xs := by
    intro c d h
    have h := (List.mem_filter.1 h).2
    unfold stepB at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1
  constructor
  · rintro ⟨-, -, h⟩
    exact mem_of_closed (fun p hp => R_sub_iter (fun q hq => (List.mem_filter.1 hq).1) hp) hc
      ((hTG a b).1 h)
  · intro h
    have htg := mem_iter_sound h
    have hab : a ∈ Xs ∧ b ∈ Xs := by
      constructor
      · cases htg with
        | single h => exact (hXstep _ _ h).1
        | tail h₁ _ =>
            have : ∀ c, Relation.TransGen (fun a b => (a, b) ∈ stepL es Xs x.J x.δ) a c → a ∈ Xs := by
              intro c hc
              induction hc with
              | single h => exact (hXstep _ _ h).1
              | tail _ _ ih => exact ih
            exact this _ h₁
      · cases htg with
        | single h => exact (hXstep _ _ h).2
        | tail _ h => exact (hXstep _ _ h).2
    exact ⟨(hX a).2 hab.1, (hX b).2 hab.2, (hTG a b).2 htg⟩

end PpoEval
