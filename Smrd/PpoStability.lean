import Smrd.PpoKit

/-!
# The untruncated `≼` is stable, the truncated one is not

The paper's `≼` (`Execution.ppoTrunc`, Definition `def:freeze` and sMRD Def. 4.9)
keeps a pair only inside a justification window, `{e | e ⊑ w_j ∨ e = w_j}`.
Whether two events are ordered then depends on what follows them in their
thread. MoRDor's `≼` (`Execution.ppo`) keeps the synchronisation and location
pairs uncut, and is decided by the two events. This module states the argument
in three steps, using only the event structure semantics (`denote`).

## (A) The truncated `≼` is unstable under extension

* (A1) `ppoTrunc_not_stable_seq`: in `x := 1 ∥ (r1 := x; r2 := x)` no execution
  orders the two reads (`trunc_seq_none`: every justification justifies an
  effectful event of the structure, and none follows the reads). Appending the
  unrelated `z := 1` to the reader orders them in every execution without
  forwarding or elision (`trunc_seq_ext`): `z := 1` is justified, and its
  window covers the reads. MoRDor's `≼` orders them in both (`ppo_seq₁`,
  `ppo_seq₂`).
* (A2) `ppoTrunc_not_mono`: in `while (0 = 0) { z := 1; r1 := x; r2 := x }`, the
  structure at step-counter 1 embeds into the one at 2 identically
  (`embeds_L`, the embedding of `denote_mono` with `θ = id`). At 1 no execution
  orders the two reads of the first iteration (they follow its last write); at
  2 every execution without forwarding or elision does (the second iteration's
  `z := 1` follows them). The truncated `≼` of `𝔼_n` is not the restriction of
  that of `𝔼_{n+1}`.

## (B) The untruncated `≼` is local, and stable along prefix embeddings

* `ppoStep_iff_local`: without forwarding or elision, without RMWs, with global
  locations and a satisfiable combined predicate, a step of MoRDor's `≼`
  relates `a` and `b` iff both are on the path `X ∪ X_F`, `a ≠ b`, and
  `ppo_sync` relates them or they are `⊑`-ordered at one location -- nothing
  of `J`, the windows or the rest of the execution enters.
* `ppo_stable_of_prefix`: hence along an inclusion `𝔼₁ ⊆ 𝔼₂` that preserves
  events and `⊑` and whose image is `⊑`-downward closed in `𝔼₂`, for
  executions related by restriction (`X₁ = X₂ ∩ E₁`, likewise `X ∪ X_F`), the
  two `≼` agree on `E₁`. Downward closure is needed: the closure is
  transitive, and an event inserted `⊑`-between two old ones can order them
  (`R x; W y rel; W y` orders the read before the second write through the
  release write).
* `ppo_mono_L`: (B) on the example of (A2): MoRDor's `≼` of `𝔼₁` is that of `𝔼₂`
  restricted to `E₁`, in every pair of executions without forwarding or
  elision. The loop example's embedding is downward closed, as the loop ends
  the program; in general `denote_mono`'s embedding is not (events after a loop
  follow the iterations it adds), and its renaming `θ` is not the identity. The
  corollary for `denote_mono` with a renaming, for the events not after the
  loop that is cut, is left as a conjecture.

## (C) No verdict changes

* `noThinAir_iff_trunc`: for executions without forwarding or elision, of
  programs without fences or RMWs, with `DP ⊆ ⊑` and a location model,
  No-Thin-Air over MoRDor's `≼` is No-Thin-Air over the paper's truncated `≼`.
  It goes through `noThinAir_iff_win` (`Smrd.PpoTail`), over MoRDor's own cut
  to the windows, whose conditions are (1) every step of `≼` in `⊑` -- which
  also holds without forwarding where no elision crosses an event
  (`Smrd.PpoTail.ppoStep_po_we`, `noThinAir_iff_win_we`; the truncated side
  of this theorem is still taken without elision) -- and (2) `DP ⊆ ⊑`, with (3) the
  combined predicate built into `≼`; then `ppoTrunc ⊆ ppoWin ⊆ ppoTrunc⁺`
  (`ppoTrunc_sub_win`, `win_sub_trunc`).
* `dep_po`: under (1) and (2), `DP ∪ ≼ ⊆ ⊑`, which the converse of
  `coherenceV_iff_coherence` needs.
* `coherence_congr`: RC11's `Coherence` does not mention `≼`: it is a function
  of `X`, `rf` and the frozen `P` (through `sameLoc` and `rmw`), so replacing
  the truncated `≼` by the untruncated one changes no coherence verdict.
-/

namespace PpoStability

open EventStructure PpoKit Execution

def st (o : MemOrd) (x : String) (n : Nat) : Stmt := .store o x (.num n) false
def ld (o : MemOrd) (r x : String) : Stmt := .load o r x false

/-- `0 = 0`, the loop condition. -/
def cT : Expr := Expr.eq (Expr.num 0) (Expr.num 0)
def gd (b : EventId) : Guard := ⟨b, cT, true⟩

def W (i t : Nat) (pc : List Nat) (it : List (LoopId × Nat)) (gs : List Guard) (o : MemOrd)
    (x : String) (n : Nat) : Event :=
  ⟨i, .write o (Expr.glob x) (Expr.num n) false, ⟨t, pc, it⟩, gs⟩
def R (i t : Nat) (pc : List Nat) (it : List (LoopId × Nat)) (gs : List Guard) (o : MemOrd)
    (x : String) : Event :=
  ⟨i, .read o (Expr.glob x) i false, ⟨t, pc, it⟩, gs⟩
def B (i : Nat) (it : List (LoopId × Nat)) (gs : List Guard) : Event :=
  ⟨i, .branch cT, ⟨0, [], it⟩, gs⟩

theorem remap_self {x : Execution} (hel : ∀ a, ¬ x.elided a) (a : EventId) : x.δ.Remap a a :=
  .canon fun c h => hel a ((x.elided_iff a).2 ⟨c, h⟩)

/-! ## (A1) Sequential composition -/

/-- `x := 1 ∥ (r1 := x; r2 := x)` -/
def p₁ : Stmt := .par (st .rlx "x" 1) (.seq (ld .rlx "r1" "x") (ld .rlx "r2" "x"))
/-- `x := 1 ∥ (r1 := x; r2 := x; z := 1)` -/
def p₂ : Stmt := .par (st .rlx "x" 1)
  (.seq (ld .rlx "r1" "x") (.seq (ld .rlx "r2" "x") (st .rlx "z" 1)))

def es₁ : EventStructure :=
  ⟨[W 0 0 [0] [] [] .rlx "x" 1, R 1 1 [1, 0] [] [] .rlx "x", R 2 1 [1, 1] [] [] .rlx "x"],
   [(1, 2)], []⟩
def es₂ : EventStructure :=
  ⟨[W 0 0 [0] [] [] .rlx "x" 1, R 1 1 [1, 0] [] [] .rlx "x", R 2 1 [1, 1, 0] [] [] .rlx "x",
    W 3 1 [1, 1, 1] [] [] .rlx "z" 1], [(1, 2), (1, 3), (2, 3)], []⟩

unseal interp in
theorem denote_p₁ : denote (fun _ => 0) p₁ = es₁ := rfl
unseal interp in
theorem denote_p₂ : denote (fun _ => 0) p₂ = es₂ := rfl

theorem S₁ : Simple es₁ := ⟨by decide, by decide, rfl⟩
theorem S₂ : Simple es₂ := ⟨by decide, by decide, rfl⟩

/-- In `x := 1 ∥ (r1 := x; r2 := x)`, no execution's truncated `≼` orders the
    two reads. -/
theorem trunc_seq_none {x : Execution} {Ω : Pred} (hX : x.IsExecution es₁ Ω) :
    ¬ x.ppoTrunc es₁ 1 2 := by
  rintro ⟨j, hj, -, -, -, h1, -⟩
  obtain ⟨e, he, hid, hef⟩ := Generated.w_mem (hX.generated j hj)
  rw [← hid] at h1
  simp only [es₁, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl
  · rcases h1 with h | h
    · cases h
    · simp [EventStructure.poR, es₁, W] at h
  all_goals simp [R, Event.isEffect, Event.isWrite, Event.isAlloc, Event.isDealloc] at hef

/-- With `z := 1` appended, every execution without forwarding or elision
    orders them. -/
theorem trunc_seq_ext {x : Execution} {Ω : Pred} (hX : x.IsExecution es₂ Ω)
    (hel : ∀ a, ¬ x.elided a) : x.ppoTrunc es₂ 1 2 := by
  have X : ∀ e ∈ es₂.events, e.isBranch = false → e.isFence = false → x.X e.id :=
    fun e he hb hf => all_in_X hX S₂ (cand_of_mem S₂.nodup he hb hf)
  have X1 : x.X 1 := X (R 1 1 [1, 0] [] [] .rlx "x") (by simp [es₂]) rfl rfl
  have X2 : x.X 2 := X (R 2 1 [1, 1, 0] [] [] .rlx "x") (by simp [es₂]) rfl rfl
  have X3 : x.X 3 := X (W 3 1 [1, 1, 1] [] [] .rlx "z" 1) (by simp [es₂]) rfl rfl
  obtain ⟨j, hj, hjw, -⟩ := hX.justified 3 X3 ⟨W 3 1 [1, 1, 1] [] [] .rlx "z" 1, by decide, rfl⟩ (hel 3)
  obtain ⟨f, hJ, -⟩ := hX.consistent
  refine ⟨j, hj, ⟨⟨1, 2, .inr ⟨show (1, 2) ∈ es₂.po by decide, ?_⟩, remap_self hel 1,
    remap_self hel 2⟩, by decide⟩, X1, X2, .inr (by rw [hjw]; show (1, 3) ∈ es₂.po; decide),
    .inr (by rw [hjw]; show (2, 3) ∈ es₂.po; decide)⟩
  exact ⟨_, _, _, _, rfl, rfl, rfl, rfl, f, hJ j hj, by simp [Expr.holds, Expr.eval, Expr.glob]⟩

/-- MoRDor's `≼` orders the reads with or without `z := 1`. -/
theorem ppo_seq₁ {x : Execution} {Ω : Pred} (hX : x.IsExecution es₁ Ω)
    (hel : ∀ a, ¬ x.elided a) : x.ppo es₁ 1 2 := by
  obtain ⟨f, hf⟩ := sat_Pm hX S₁ hel
  exact ppo_of_alias hel hf (y := "x") rfl rfl rfl rfl (show (1, 2) ∈ es₁.po by decide) (by decide)
    (all_in_X hX S₁ (cand_of_mem S₁.nodup (e := R 1 1 [1, 0] [] [] .rlx "x") (by simp [es₁]) rfl rfl))
    (all_in_X hX S₁ (cand_of_mem S₁.nodup (e := R 2 1 [1, 1] [] [] .rlx "x") (by simp [es₁]) rfl rfl))

theorem ppo_seq₂ {x : Execution} {Ω : Pred} (hX : x.IsExecution es₂ Ω)
    (hel : ∀ a, ¬ x.elided a) : x.ppo es₂ 1 2 := by
  obtain ⟨f, hf⟩ := sat_Pm hX S₂ hel
  exact ppo_of_alias hel hf (y := "x") rfl rfl rfl rfl (show (1, 2) ∈ es₂.po by decide) (by decide)
    (all_in_X hX S₂ (cand_of_mem S₂.nodup (e := R 1 1 [1, 0] [] [] .rlx "x") (by simp [es₂]) rfl rfl))
    (all_in_X hX S₂ (cand_of_mem S₂.nodup (e := R 2 1 [1, 1, 0] [] [] .rlx "x") (by simp [es₂]) rfl rfl))

/-- **(A1)** The truncated `≼` is not stable under sequential composition:
    appending an unrelated write to the reader orders its reads. Both
    programs have executions without forwarding or elision (`simple`). -/
theorem ppoTrunc_not_stable_seq :
    (∀ (x : Execution) (Ω : Pred), x.IsExecution es₁ Ω → ¬ x.ppoTrunc es₁ 1 2) ∧
    (∀ (x : Execution) (Ω : Pred), x.IsExecution es₂ Ω → (∀ a, ¬ x.elided a) →
      x.ppoTrunc es₂ 1 2) ∧
    (simple es₁ []).IsExecution es₁ (fun _ => True) ∧
    (simple es₂ []).IsExecution es₂ (fun _ => True) :=
  ⟨fun _ _ hX => trunc_seq_none hX, fun _ _ hX hel => trunc_seq_ext hX hel,
   isExecution_simple S₁ (by decide), isExecution_simple S₂ (by decide)⟩

/-! ## (A2) The step counter -/

/-- `while (0 = 0) { z := 1; r1 := x; r2 := x }` -/
def lp : Stmt :=
  .while 0 (.eq (.num 0) (.num 0)) (.seq (st .rlx "z" 1) (.seq (ld .rlx "r1" "x") (ld .rlx "r2" "x")))

def esL₁ : EventStructure :=
  ⟨[B 0 [(0, 0)] [], W 1 0 [0, 0] [(0, 0)] [gd 0] .rlx "z" 1,
    R 2 0 [0, 1, 0] [(0, 0)] [gd 0] .rlx "x", R 3 0 [0, 1, 1] [(0, 0)] [gd 0] .rlx "x"],
   [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)], []⟩
def esL₂ : EventStructure :=
  ⟨[B 0 [(0, 0)] [], W 1 0 [0, 0] [(0, 0)] [gd 0] .rlx "z" 1,
    R 2 0 [0, 1, 0] [(0, 0)] [gd 0] .rlx "x", R 3 0 [0, 1, 1] [(0, 0)] [gd 0] .rlx "x",
    B 4 [(0, 1)] [gd 0], W 5 0 [0, 0] [(0, 1)] [gd 0, gd 4] .rlx "z" 1,
    R 6 0 [0, 1, 0] [(0, 1)] [gd 0, gd 4] .rlx "x", R 7 0 [0, 1, 1] [(0, 1)] [gd 0, gd 4] .rlx "x"],
   [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 2), (1, 3), (1, 4), (1, 5),
    (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7),
    (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)], []⟩

unseal interp in
theorem denote_L₁ : denote (fun _ => 1) lp = esL₁ := rfl
unseal interp in
theorem denote_L₂ : denote (fun _ => 2) lp = esL₂ := rfl

/-- The embedding of `l:es-mono` (`denote_mono`) is the identity here. -/
theorem embeds_L : Embeds id id esL₁ esL₂ := ⟨by decide, by decide, by decide⟩

theorem SL₁ : Simple esL₁ := ⟨by decide, by decide, rfl⟩
theorem SL₂ : Simple esL₂ := ⟨by decide, by decide, rfl⟩

theorem trunc_L₁_none {x : Execution} {Ω : Pred} (hX : x.IsExecution esL₁ Ω) :
    ¬ x.ppoTrunc esL₁ 2 3 := by
  rintro ⟨j, hj, -, -, -, h1, -⟩
  obtain ⟨e, he, hid, hef⟩ := Generated.w_mem (hX.generated j hj)
  rw [← hid] at h1
  simp only [esL₁, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · simp [B, Event.isEffect, Event.isWrite, Event.isAlloc, Event.isDealloc] at hef
  · rcases h1 with h | h
    · cases h
    · simp [EventStructure.poR, esL₁, W] at h
  all_goals simp [R, Event.isEffect, Event.isWrite, Event.isAlloc, Event.isDealloc] at hef

theorem trunc_L₂ {x : Execution} {Ω : Pred} (hX : x.IsExecution esL₂ Ω)
    (hel : ∀ a, ¬ x.elided a) : x.ppoTrunc esL₂ 2 3 := by
  have X : ∀ e ∈ esL₂.events, e.isBranch = false → e.isFence = false → x.X e.id :=
    fun e he hb hf => all_in_X hX SL₂ (cand_of_mem SL₂.nodup he hb hf)
  have X2 : x.X 2 := X (R 2 0 [0, 1, 0] [(0, 0)] [gd 0] .rlx "x") (by simp [esL₂]) rfl rfl
  have X3 : x.X 3 := X (R 3 0 [0, 1, 1] [(0, 0)] [gd 0] .rlx "x") (by simp [esL₂]) rfl rfl
  have X5 : x.X 5 := X (W 5 0 [0, 0] [(0, 1)] [gd 0, gd 4] .rlx "z" 1) (by simp [esL₂]) rfl rfl
  obtain ⟨j, hj, hjw, -⟩ := hX.justified 5 X5 ⟨W 5 0 [0, 0] [(0, 1)] [gd 0, gd 4] .rlx "z" 1, by decide, rfl⟩ (hel 5)
  obtain ⟨f, hJ, -⟩ := hX.consistent
  refine ⟨j, hj, ⟨⟨2, 3, .inr ⟨show (2, 3) ∈ esL₂.po by decide, ?_⟩, remap_self hel 2,
    remap_self hel 3⟩, by decide⟩, X2, X3, .inr (by rw [hjw]; show (2, 5) ∈ esL₂.po; decide),
    .inr (by rw [hjw]; show (3, 5) ∈ esL₂.po; decide)⟩
  exact ⟨_, _, _, _, rfl, rfl, rfl, rfl, f, hJ j hj, by simp [Expr.holds, Expr.eval, Expr.glob]⟩

/-- **(A2)** The truncated frozen `≼` is not monotone in the step counter: the
    reads `2`, `3` of the first iteration are unordered in every execution at
    step-counter 1 and ordered in every execution without forwarding or
    elision at step-counter 2, along the identity embedding `𝔼₁ ⊆ 𝔼₂`. -/
theorem ppoTrunc_not_mono :
    denote (fun _ => 1) lp = esL₁ ∧ denote (fun _ => 2) lp = esL₂ ∧ Embeds id id esL₁ esL₂ ∧
    (∀ (x : Execution) (Ω : Pred), x.IsExecution esL₁ Ω → ¬ x.ppoTrunc esL₁ 2 3) ∧
    (∀ (x : Execution) (Ω : Pred), x.IsExecution esL₂ Ω → (∀ a, ¬ x.elided a) →
      x.ppoTrunc esL₂ 2 3) ∧
    (simple esL₂ []).IsExecution esL₂ (fun _ => True) :=
  ⟨denote_L₁, denote_L₂, embeds_L, fun _ _ hX => trunc_L₁_none hX,
   fun _ _ hX hel => trunc_L₂ hX hel, isExecution_simple SL₂ (by decide)⟩

/-! ## (B) Locality and stability of the untruncated `≼` -/

/-- Two events at one global location. -/
def SameGlob (es : EventStructure) (a b : EventId) : Prop :=
  ∃ ea eb y, es.ev a = some ea ∧ es.ev b = some eb ∧ ea.loc = some (Expr.glob y) ∧
    eb.loc = some (Expr.glob y)

theorem sameGlob_of_mem {es : EventStructure} (hg : GlobLocs es) {a b : EventId}
    (h : ∃ e₁ e₂ l₁ l₂, es.ev a = some e₁ ∧ es.ev b = some e₂ ∧ e₁.loc = some l₁ ∧
      e₂.loc = some l₂ ∧ ∃ f, (Expr.eq l₁ l₂).holds f) : SameGlob es a b := by
  obtain ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, hf⟩ := h
  obtain ⟨x, rfl⟩ := hg e₁ (ev_inv h₁).1 _ hl₁
  obtain ⟨y, rfl⟩ := hg e₂ (ev_inv h₂).1 _ hl₂
  have : x = y := by simp [Expr.holds, Expr.eval, Expr.glob] at hf; exact hf
  subst this
  exact ⟨e₁, e₂, x, h₁, h₂, hl₁, hl₂⟩

theorem sameGlob_of_alias {es : EventStructure} (hg : GlobLocs es) {P : Pred} {a b : EventId}
    (h : es.mustAlias a b ∨ es.mayAlias P a b) : SameGlob es a b := by
  rcases h with ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, hs⟩ | ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, -, hf⟩
  · obtain ⟨x, rfl⟩ := hg e₁ (ev_inv h₁).1 _ hl₁
    obtain ⟨y, rfl⟩ := hg e₂ (ev_inv h₂).1 _ hl₂
    have hxy := hs (fun _ => .num 0) _ _ rfl rfl
    cases hxy
    exact ⟨e₁, e₂, x, h₁, h₂, hl₁, hl₂⟩
  · exact sameGlob_of_mem hg ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, hf⟩

/-- The local relation: on the path, distinct, and `ppo_sync`-related or
    `⊑`-ordered at one location. -/
def Local (es : EventStructure) (x : Execution) (a b : EventId) : Prop :=
  x.XwF es a ∧ x.XwF es b ∧ a ≠ b ∧ (es.ppoSyncM a b ∨ (es.poR a b ∧ SameGlob es a b))

/-- **(B) Locality.** Without forwarding or elision, RMWs, or locations other
    than globals, and with a satisfiable combined predicate, a step of MoRDor's
    `≼` is decided by the two events, their being on the path, and `⊑`. -/
theorem ppoStep_iff_local {es : EventStructure} {x : Execution} (hr : es.rmw = [])
    (hg : GlobLocs es) (hδ : ∀ a b, ¬ x.δ.edge a b) {f : Valuation} (hf : x.Pm es f)
    {a b : EventId} : x.ppoStep es a b ↔ Local es x a b := by
  have base : ∀ {Pa Pr : Pred}, es.ppoM Pa Pr x.δ a b →
      a ≠ b ∧ (es.ppoSyncM a b ∨ (es.poR a b ∧ SameGlob es a b)) := by
    intro Pa Pr ⟨hab, hne⟩
    refine ⟨hne, ?_⟩
    rcases (FwdCtx.remapRel_of_noEdge hδ).1 hab with (hs | (⟨c, -, hc⟩ | ⟨c, hc, -⟩)) | ⟨hpo, hal⟩
    · exact .inl hs
    · exact absurd hc (not_rmwPairs hr)
    · exact absurd hc (not_rmwPairs hr)
    · exact .inr ⟨hpo, sameGlob_of_alias hg hal⟩
  constructor
  · rintro ⟨ha, hb, ⟨j, -, hp, -⟩ | ⟨hs | ⟨hp, -⟩, -⟩⟩
    · exact ⟨ha, hb, base hp⟩
    · exact ⟨ha, hb, base (es.ppoSyncRM_sub_ppoM (x.Pm es) (x.Pm es) x.δ _ _ hs)⟩
    · exact ⟨ha, hb, base hp⟩
  · rintro ⟨ha, hb, hne, hs | ⟨hpo, ea, eb, y, hea, heb, hla, hlb⟩⟩
    · exact ⟨ha, hb, .inr ⟨.inl ⟨(FwdCtx.remapRel_of_noEdge hδ).2 hs, hne⟩,
        ⟨b, hb, .inr hs.1, .inl rfl⟩⟩⟩
    · have hal : es.mayAlias (x.Pm es) a b :=
        ⟨ea, eb, _, _, hea, heb, hla, hlb, f, hf, by simp [Expr.holds, Expr.eval, Expr.glob]⟩
      exact ⟨ha, hb, .inr ⟨.inr ⟨⟨(FwdCtx.remapRel_of_noEdge hδ).2 (.inr ⟨hpo, .inr hal⟩), hne⟩,
        hal⟩, ⟨b, hb, .inr hpo, .inl rfl⟩⟩⟩

/-- An inclusion `𝔼₁ ⊆ 𝔼₂` preserving events and `⊑`, with image `⊑`-downward
    closed, and executions related by restriction. -/
structure PrefixExec (es₁ es₂ : EventStructure) (x₁ x₂ : Execution) : Prop where
  ev    : ∀ a e, es₁.ev a = some e → es₂.ev a = some e
  po    : ∀ a b, es₁.inE a → es₁.inE b → (es₁.poR a b ↔ es₂.poR a b)
  down  : ∀ a b, es₂.poR a b → es₁.inE b → es₁.inE a
  X     : ∀ a, x₁.X a ↔ es₁.inE a ∧ x₂.X a
  XwF   : ∀ a, x₁.XwF es₁ a ↔ es₁.inE a ∧ x₂.XwF es₂ a

theorem ev_of_inE {es : EventStructure} {a : EventId} (h : es.inE a) : ∃ e, es.ev a = some e := by
  obtain ⟨e, he, rfl⟩ := h
  unfold EventStructure.ev
  cases h' : es.events.find? (·.id == e.id) with
  | some e' => exact ⟨e', rfl⟩
  | none => exact absurd (List.find?_eq_none.1 h' e he) (by simp)

theorem inE_of_po {es : EventStructure} {a b : EventId} (h : es.poR a b)
    (hpo : ∀ p ∈ es.po, es.inE p.1 ∧ es.inE p.2) : es.inE a ∧ es.inE b := hpo _ h

theorem Local.transfer {es₁ es₂ : EventStructure} {x₁ x₂ : Execution}
    (H : PrefixExec es₁ es₂ x₁ x₂) {a b : EventId} (ha : es₁.inE a) (hb : es₁.inE b) :
    Local es₁ x₁ a b ↔ Local es₂ x₂ a b := by
  have cls : ∀ (p : Event → Bool) c, es₁.inE c → (es₁.cls p c ↔ es₂.cls p c) := by
    intro p c hc
    obtain ⟨e, he⟩ := ev_of_inE hc
    constructor
    · rintro ⟨e', he', hp⟩; rw [he] at he'; cases he'; exact ⟨e, H.ev c e he, hp⟩
    · rintro ⟨e', he', hp⟩; rw [H.ev c e he] at he'; cases he'; exact ⟨e, he, hp⟩
  have sync : es₁.ppoSyncM a b ↔ es₂.ppoSyncM a b := by
    unfold EventStructure.ppoSyncM
    rw [H.po a b ha hb, cls _ a ha, cls _ b hb]
  have sg : SameGlob es₁ a b ↔ SameGlob es₂ a b := by
    obtain ⟨ea, hea⟩ := ev_of_inE ha
    obtain ⟨eb, heb⟩ := ev_of_inE hb
    constructor
    · rintro ⟨ea', eb', y, h₁, h₂, h₃, h₄⟩
      exact ⟨ea', eb', y, H.ev a _ h₁, H.ev b _ h₂, h₃, h₄⟩
    · rintro ⟨ea', eb', y, h₁, h₂, h₃, h₄⟩
      rw [H.ev a _ hea] at h₁; rw [H.ev b _ heb] at h₂; cases h₁; cases h₂
      exact ⟨ea, eb, y, hea, heb, h₃, h₄⟩
  unfold Local
  rw [H.XwF a, H.XwF b, sync, sg, H.po a b ha hb]
  simp only [ha, hb, true_and]

/-- **(B) Stability along prefix embeddings.** For executions without
    forwarding or elision of structures without RMWs and with global
    locations, related by restriction along a downward-closed inclusion, the
    untruncated `≼` agree on the smaller structure. -/
theorem ppo_stable_of_prefix {es₁ es₂ : EventStructure} {x₁ x₂ : Execution}
    (H : PrefixExec es₁ es₂ x₁ x₂)
    (hr₁ : es₁.rmw = []) (hr₂ : es₂.rmw = []) (hg₁ : GlobLocs es₁) (hg₂ : GlobLocs es₂)
    (hδ₁ : ∀ a b, ¬ x₁.δ.edge a b) (hδ₂ : ∀ a b, ¬ x₂.δ.edge a b)
    {f₁ f₂ : Valuation} (hf₁ : x₁.Pm es₁ f₁) (hf₂ : x₂.Pm es₂ f₂)
    {a b : EventId} (ha : es₁.inE a) (hb : es₁.inE b) :
    x₁.ppo es₁ a b ↔ x₂.ppo es₂ a b := by
  have st₁ := fun {c d : EventId} => ppoStep_iff_local (x := x₁) hr₁ hg₁ hδ₁ hf₁ (a := c) (b := d)
  have st₂ := fun {c d : EventId} => ppoStep_iff_local (x := x₂) hr₂ hg₂ hδ₂ hf₂ (a := c) (b := d)
  have lpo : ∀ {c d}, Local es₂ x₂ c d → es₂.poR c d := by
    rintro c d ⟨-, -, -, hs | ⟨hpo, -⟩⟩
    · exact hs.1
    · exact hpo
  constructor
  · rintro ⟨hXa, hXb, h⟩
    refine ⟨((H.X a).1 hXa).2, ((H.X b).1 hXb).2, ?_⟩
    -- every step of `x₁` lies in `E₁`, and transfers
    have gen : ∀ c d, Relation.TransGen (x₁.ppoStep es₁) c d →
        es₁.inE c ∧ es₁.inE d ∧ Relation.TransGen (x₂.ppoStep es₂) c d := by
      intro c d h
      have inE : ∀ c d, x₁.ppoStep es₁ c d → es₁.inE c ∧ es₁.inE d := by
        intro c d hs
        obtain ⟨hc, hd, -⟩ := st₁.1 hs
        exact ⟨((H.XwF c).1 hc).1, ((H.XwF d).1 hd).1⟩
      induction h with
      | single hs =>
          obtain ⟨hc, hd⟩ := inE _ _ hs
          exact ⟨hc, hd, .single (st₂.2 ((Local.transfer H hc hd).1 (st₁.1 hs)))⟩
      | tail _ hs ih =>
          obtain ⟨hc, -, ih⟩ := ih
          obtain ⟨hm, hd⟩ := inE _ _ hs
          exact ⟨hc, hd, .tail ih (st₂.2 ((Local.transfer H hm hd).1 (st₁.1 hs)))⟩
    exact (gen a b h).2.2
  · rintro ⟨hXa, hXb, h⟩
    refine ⟨(H.X a).2 ⟨ha, hXa⟩, (H.X b).2 ⟨hb, hXb⟩, ?_⟩
    -- every intermediate event is `⊑`-before `b`, so in `E₁`
    have gen : ∀ c d, Relation.TransGen (x₂.ppoStep es₂) c d → es₁.inE d →
        es₁.inE c ∧ Relation.TransGen (x₁.ppoStep es₁) c d := by
      intro c d h
      induction h with
      | single hs =>
          intro hd
          have hc := H.down _ _ (lpo (st₂.1 hs)) hd
          exact ⟨hc, .single (st₁.2 ((Local.transfer H hc hd).2 (st₂.1 hs)))⟩
      | tail _ hs ih =>
          intro hd
          have hm := H.down _ _ (lpo (st₂.1 hs)) hd
          obtain ⟨hc, ih⟩ := ih hm
          exact ⟨hc, .tail ih (st₁.2 ((Local.transfer H hm hd).2 (st₂.1 hs)))⟩
    exact (gen a b h hb).2

/-- **(B) on the example of (A2)**: MoRDor's `≼` of `𝔼₁` is that of `𝔼₂`
    restricted to `E₁`, for any two executions without forwarding or elision;
    it orders the two reads of the first iteration in both. -/
theorem ppo_mono_L {x₁ x₂ : Execution} {Ω₁ Ω₂ : Pred} (hX₁ : x₁.IsExecution esL₁ Ω₁)
    (hX₂ : x₂.IsExecution esL₂ Ω₂) (hel₁ : ∀ a, ¬ x₁.elided a) (hel₂ : ∀ a, ¬ x₂.elided a)
    {a b : EventId} (ha : a < 4) (hb : b < 4) :
    (x₁.ppo esL₁ a b ↔ x₂.ppo esL₂ a b) ∧ x₁.ppo esL₁ 2 3 := by
  obtain ⟨f₁, hf₁⟩ := sat_Pm hX₁ SL₁ hel₁
  obtain ⟨f₂, hf₂⟩ := sat_Pm hX₂ SL₂ hel₂
  have hg₁ : GlobLocs esL₁ := globLocs_of (by decide)
  have hg₂ : GlobLocs esL₂ := globLocs_of (by decide)
  have hδ₁ := noEdge_of_noElided hel₁
  have hδ₂ := noEdge_of_noElided hel₂
  -- both relations lie in `aliasL`, which is closed
  have b₁ : ∀ c d, x₁.ppo esL₁ c d → (c, d) ∈ syncML esL₁ ++ aliasL esL₁ :=
    fun c d h => transGen_mem (fun _ _ hs => ppoStep_mem rfl hg₁ hδ₁ hs) (by decide) h.2.2
  have b₂ : ∀ c d, x₂.ppo esL₂ c d → (c, d) ∈ syncML esL₂ ++ aliasL esL₂ :=
    fun c d h => transGen_mem (fun _ _ hs => ppoStep_mem rfl hg₂ hδ₂ hs) (by decide) h.2.2
  have X₁ : ∀ e ∈ esL₁.events, e.isBranch = false → e.isFence = false → x₁.X e.id :=
    fun e he hb hf => all_in_X hX₁ SL₁ (cand_of_mem SL₁.nodup he hb hf)
  have X₂ : ∀ e ∈ esL₂.events, e.isBranch = false → e.isFence = false → x₂.X e.id :=
    fun e he hb hf => all_in_X hX₂ SL₂ (cand_of_mem SL₂.nodup he hb hf)
  have p₁ : x₁.ppo esL₁ 2 3 := ppo_of_alias hel₁ hf₁ (y := "x") rfl rfl rfl rfl (show (2, 3) ∈ esL₁.po by decide)
    (by decide) (X₁ (R 2 0 [0, 1, 0] [(0, 0)] [gd 0] .rlx "x") (by simp [esL₁]) rfl rfl)
    (X₁ (R 3 0 [0, 1, 1] [(0, 0)] [gd 0] .rlx "x") (by simp [esL₁]) rfl rfl)
  have p₂ : x₂.ppo esL₂ 2 3 := ppo_of_alias hel₂ hf₂ (y := "x") rfl rfl rfl rfl (show (2, 3) ∈ esL₂.po by decide)
    (by decide) (X₂ (R 2 0 [0, 1, 0] [(0, 0)] [gd 0] .rlx "x") (by simp [esL₂]) rfl rfl)
    (X₂ (R 3 0 [0, 1, 1] [(0, 0)] [gd 0] .rlx "x") (by simp [esL₂]) rfl rfl)
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, p₁⟩
  · have key : ∀ p ∈ syncML esL₁ ++ aliasL esL₁, p.1 < 4 → p.2 < 4 → p = (2, 3) := by decide
    have := key _ (b₁ a b h) ha hb
    cases this; exact p₂
  · have key : ∀ p ∈ syncML esL₂ ++ aliasL esL₂, p.1 < 4 → p.2 < 4 → p = (2, 3) := by decide
    have := key _ (b₂ a b h) ha hb
    cases this; exact p₁

/-! ## (C) No verdict changes -/

/-- **`DP ∪ ≼ ⊆ ⊑`** under conditions (1) (every step of `≼` in `⊑`) and (2)
    (`DP ⊆ ⊑`). -/
theorem dep_po {es : EventStructure} {x : Execution}
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hstep : ∀ a b, x.ppoStep es a b → es.poR a b) (hDP : ∀ a b, x.DP a b → es.poR a b)
    {a b : EventId} (h : x.dep es a b) : es.poR a b := by
  rcases h with hp | hd
  · exact ppo_po hpo_trans hstep hp
  · exact hDP a b hd

/-- RC11's `Coherence` does not mention `≼`: two executions with the same
    events, `rf` and frozen predicate have the same coherence verdict. -/
theorem coherence_congr {es : EventStructure} {x x' : Execution} {co : Rel}
    (hX : x.X = x'.X) (hrf : x.rf = x'.rf) (hP : x.P es = x'.P es) :
    x.Coherence es co ↔ x'.Coherence es co := by
  obtain ⟨X, J, rf⟩ := x
  obtain ⟨X', J', rf'⟩ := x'
  simp only at hX hrf
  subst hX hrf
  have hrr : Execution.rfRmw es ⟨X, J, rf⟩ = Execution.rfRmw es ⟨X, J', rf⟩ := by
    funext a b
    simp only [Execution.rfRmw, Execution.rmwRel, hP]
  have hsw : Execution.sw es ⟨X, J, rf⟩ = Execution.sw es ⟨X, J', rf⟩ := by
    funext a b
    simp only [Execution.sw, Execution.rs, Execution.poloc, Execution.sameLoc, hP, hrr]
    rfl
  unfold Execution.Coherence Execution.hb
  rw [hsw]
  rfl

theorem mayAlias_of_must {es : EventStructure} {P : Pred} {a b : EventId} (f : Valuation)
    (hf : P f) (hm : es.mustAlias a b)
    (hdef : ∀ e l, (es.ev a = some e ∨ es.ev b = some e) → e.loc = some l → (l.eval f).isSome) :
    es.mayAlias P a b := by
  obtain ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, hs⟩ := hm
  obtain ⟨v₁, hv₁⟩ := Option.isSome_iff_exists.1 (hdef e₁ l₁ (.inl h₁) hl₁)
  obtain ⟨v₂, hv₂⟩ := Option.isSome_iff_exists.1 (hdef e₂ l₂ (.inr h₂) hl₂)
  have := hs f v₁ v₂ hv₁ hv₂
  subst this
  exact ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, hf, by simp [Expr.holds, Expr.eval, hv₁, hv₂]⟩

/-- In a program without fences, the paper's and MoRDor's synchronisation
    pairs agree between events that are not branches. -/
theorem sync_iff {es : EventStructure} (hnf : ∀ e ∈ es.events, e.isFence = false)
    {a b : EventId} (hna : ¬ es.cls Event.isBranch a) (hnb : ¬ es.cls Event.isBranch b) :
    es.ppoSync a b ↔ es.ppoSyncM a b := by
  have nf : ∀ c, ¬ es.cls Event.isFence c := by
    rintro c ⟨e, he, hp⟩; rw [hnf e (ev_inv he).1] at hp; cases hp
  have nrf : ∀ c, ¬ es.cls Event.isRelF c := by
    rintro c ⟨e, he, hp⟩; apply nf c; refine ⟨e, he, ?_⟩
    obtain ⟨id, k, l, g⟩ := e; cases k <;> simp_all [Event.isRelF, Event.isFence]
  have naf : ∀ c, ¬ es.cls Event.isAcqF c := by
    rintro c ⟨e, he, hp⟩; apply nf c; refine ⟨e, he, ?_⟩
    obtain ⟨id, k, l, g⟩ := e; cases k <;> simp_all [Event.isAcqF, Event.isFence]
  have acqM : ∀ c, es.cls Event.isAcqM c ↔ es.cls Event.isAcqR c := by
    intro c; constructor
    · rintro ⟨e, he, hp⟩
      simp only [Event.isAcqM, Bool.or_eq_true] at hp
      rcases hp with hp | hp
      · exact ⟨e, he, hp⟩
      · exact absurd ⟨e, he, hp⟩ (naf c)
    · rintro ⟨e, he, hp⟩; exact ⟨e, he, by simp [Event.isAcqM, hp]⟩
  have relM : ∀ c, es.cls Event.isRelM c ↔ es.cls Event.isRelW c := by
    intro c; constructor
    · rintro ⟨e, he, hp⟩
      simp only [Event.isRelM, Bool.or_eq_true] at hp
      rcases hp with hp | hp
      · exact ⟨e, he, hp⟩
      · exact absurd ⟨e, he, hp⟩ (nrf c)
    · rintro ⟨e, he, hp⟩; exact ⟨e, he, by simp [Event.isRelM, hp]⟩
  constructor
  · rintro ⟨(⟨c, hpo, rfl, hc⟩ | ⟨c, ⟨d, -, -, hd⟩, -⟩) | (⟨c, ⟨rfl, hc⟩, hpo⟩ | ⟨c, ⟨d, -, -, hd⟩, -⟩), -⟩
    · exact ⟨hpo, .inr ((relM _).2 hc)⟩
    · exact absurd hd (nrf _)
    · exact ⟨hpo, .inl ((acqM _).2 hc)⟩
    · exact absurd hd (naf _)
  · rintro ⟨hpo, ha | hb⟩
    · exact ⟨.inr (.inl ⟨a, ⟨rfl, (acqM a).1 ha⟩, hpo⟩), fun h => h.elim (nf a) hna,
        fun h => h.elim (nf b) hnb⟩
    · exact ⟨.inl (.inl ⟨b, hpo, rfl, (relM b).1 hb⟩), fun h => h.elim (nf a) hna,
        fun h => h.elim (nf b) hnb⟩

theorem not_branch_of_X {es : EventStructure} {x : Execution} {Ω : Pred}
    (hx : x.IsExecution es Ω) {a : EventId} (h : x.X a) : ¬ es.cls Event.isBranch a :=
  (hx.maximal.1 a h).2.1

/-- The paper's truncated `≼` is contained in MoRDor's cut to the windows, for
    executions without forwarding or elision of programs without fences or
    RMWs. -/
theorem ppoTrunc_sub_win {es : EventStructure} {x : Execution} {Ω : Pred}
    (hx : x.IsExecution es Ω) (hnf : ∀ e ∈ es.events, e.isFence = false) (hr : es.rmw = [])
    (hδ : ∀ a b, ¬ x.δ.edge a b) {a b : EventId} (h : x.ppoTrunc es a b) : x.ppoWin es a b := by
  obtain ⟨j, hj, ⟨hab, hne⟩, ha, hb, hwa, hwb⟩ := h
  refine ⟨ha, hb, .single ⟨.inl ha, .inl hb, .inl ⟨j, hj, ⟨?_, hne⟩, hwa, hwb⟩⟩⟩
  refine (FwdCtx.remapRel_of_noEdge hδ).2 ?_
  rcases (FwdCtx.remapRel_of_noEdge hδ).1 hab with (hs | hm) | ⟨hpo, hal⟩
  · exact .inl (.inl ((sync_iff hnf (not_branch_of_X hx ha) (not_branch_of_X hx hb)).1 hs))
  · rcases hm with ⟨⟨c, -, hc⟩ | ⟨c, hc, -⟩, -⟩ <;> exact absurd hc (not_rmwPairs hr)
  · refine .inr ⟨hpo, .inr ?_⟩
    obtain ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, hP, heq⟩ := hal
    exact ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f,
      ⟨hP, fun p hp => absurd (Or.inl hp) (fun h => hδ p.1 p.2 (by simpa using h))⟩, heq⟩

/-- Each step of MoRDor's cut to the windows is a pair of the paper's
    truncated `≼`, under the same conditions and a location model. -/
theorem win_step_sub_trunc {es : EventStructure} {x : Execution} {Ω : Pred}
    (hx : x.IsExecution es Ω) (hnf : ∀ e ∈ es.events, e.isFence = false) (hr : es.rmw = [])
    (hδ : ∀ a b, ¬ x.δ.edge a b) (hm : LocModel es x) {a b : EventId}
    (h : x.ppoWinStep es a b) : x.ppoTrunc es a b := by
  have hff : x.FenceFree es := by
    rintro c - ⟨e, he, hp⟩; rw [hnf e (ev_inv he).1] at hp; cases hp
  obtain ⟨hXa, hXb, hs⟩ := h
  have ha := X_of_XwF hff hXa
  have hb := X_of_XwF hff hXb
  obtain ⟨f, hPm, hdef⟩ := hm
  have hdef' : ∀ e l, (es.ev a = some e ∨ es.ev b = some e) → e.loc = some l →
      (l.eval f).isSome := by
    rintro e l (h | h) hl
    · exact hdef a e l ha h hl
    · exact hdef b e l hb h hl
  -- a base pair of MoRDor's templates is one of the paper's under `P_j`
  have conv : ∀ (j : Justification), j ∈ x.J → ∀ {Pa Pr : Pred}, Entails Pa j.P.holds →
      es.ppoM Pa Pr x.δ a b → es.ppo j.P.holds x.δ a b := by
    intro j hj Pa Pr hPa ⟨hab, hne⟩
    refine ⟨(FwdCtx.remapRel_of_noEdge hδ).2 ?_, hne⟩
    rcases (FwdCtx.remapRel_of_noEdge hδ).1 hab with (hs | (⟨c, -, hc⟩ | ⟨c, hc, -⟩)) | ⟨hpo, hal⟩
    · exact .inl (.inl ((sync_iff hnf (not_branch_of_X hx ha) (not_branch_of_X hx hb)).2 hs))
    · exact absurd hc (not_rmwPairs hr)
    · exact absurd hc (not_rmwPairs hr)
    · refine .inr ⟨hpo, ?_⟩
      rcases hal with hmu | hal
      · exact mayAlias_of_must f (hPm.1 j hj) hmu hdef'
      · exact es.mayAlias_mono hPa hal
  rcases hs with ⟨j, hj, hp, hwa, hwb⟩ | ⟨hp, j, hj, hwa, hwb⟩
  · exact ⟨j, hj, conv j hj (fun _ h => h.1) hp, ha, hb, hwa, hwb⟩
  · rcases hp with hs | ⟨hp, -⟩
    · exact ⟨j, hj, conv j hj (Pa := x.Pm es) (Pr := x.Pm es) (fun _ h => h.1 j hj)
        (es.ppoSyncRM_sub_ppoM _ _ _ _ _ hs), ha, hb, hwa, hwb⟩
    · exact ⟨j, hj, conv j hj (fun _ h => h.1 j hj) hp, ha, hb, hwa, hwb⟩

theorem acyclic_plus_iff {R S : Rel} {T : Rel} (hRT : ∀ a b, R a b → T a b)
    (hTR : ∀ a b, T a b → Relation.TransGen R a b) :
    Rel.Acyclic (T.union S) ↔ Rel.Acyclic (R.union S) := by
  have up : ∀ a b, Relation.TransGen (T.union S) a b → Relation.TransGen (R.union S) a b := by
    intro a b h
    induction h with
    | single h =>
        rcases h with h | h
        · exact transGen_mono (fun _ _ h => .inl h) (hTR _ _ h)
        · exact .single (.inr h)
    | tail _ h ih =>
        rcases h with h | h
        · exact transGen_trans ih (transGen_mono (fun _ _ h => .inl h) (hTR _ _ h))
        · exact .tail ih (.inr h)
  constructor
  · intro h a ha
    exact h a (transGen_mono (fun c d h => by
      rcases h with h | h
      · exact .inl (hRT _ _ h)
      · exact .inr h) ha)
  · intro h a ha; exact h a (up a a ha)

/-- **(C) No-Thin-Air does not change**: for executions without forwarding or
    elision of programs without fences or RMWs, with `DP ⊆ ⊑` and a location
    model, No-Thin-Air over MoRDor's untruncated `≼` is No-Thin-Air over the
    paper's truncated `≼`. -/
theorem noThinAir_iff_trunc {es : EventStructure} {x : Execution} {Ω : Pred}
    (hx : x.IsExecution es Ω) (hphi : x.phi es)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a)
    (hnf : ∀ e ∈ es.events, e.isFence = false) (hr : es.rmw = [])
    (hδ : ∀ a b, ¬ x.δ.edge a b) (hm : LocModel es x) (hDP : ∀ a b, x.DP a b → es.poR a b) :
    x.NoThinAir es ↔ Rel.Acyclic (((x.ppoTrunc es).union x.DP).union x.rf) := by
  have hT : RMWTight es x := by
    refine ⟨fun ent h => ?_, fun ent h => ?_⟩ <;> (rw [hr] at h; cases h)
  rw [noThinAir_iff_win hx hphi hpo_trans hirr (fun _ _ h => ppoStep_po hδ hT h) hDP]
  -- `ppoWin ∪ DP` against `ppoTrunc ∪ DP`
  have e1 : Rel.Acyclic ((depWin es x).union x.rf) ↔
      Rel.Acyclic ((x.ppoWin es).union (x.DP.union x.rf)) := by
    unfold Rel.Acyclic depWin
    constructor
    · intro h a ha; apply h a; refine transGen_mono (fun c d h => ?_) ha
      rcases h with h | h | h
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr h
    · intro h a ha; apply h a; refine transGen_mono (fun c d h => ?_) ha
      rcases h with (h | h) | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
  have e2 : Rel.Acyclic (((x.ppoTrunc es).union x.DP).union x.rf) ↔
      Rel.Acyclic ((x.ppoTrunc es).union (x.DP.union x.rf)) := by
    unfold Rel.Acyclic
    constructor
    · intro h a ha; apply h a; refine transGen_mono (fun c d h => ?_) ha
      rcases h with h | h | h
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr h
    · intro h a ha; apply h a; refine transGen_mono (fun c d h => ?_) ha
      rcases h with (h | h) | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
  rw [e1, e2]
  exact acyclic_plus_iff (fun _ _ h => ppoTrunc_sub_win hx hnf hr hδ h)
    (fun _ _ h => transGen_mono (fun _ _ h => win_step_sub_trunc hx hnf hr hδ hm h) h.2.2)

end PpoStability
