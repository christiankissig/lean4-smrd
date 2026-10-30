import Smrd.CoherenceT
import Smrd.RoutineHyps

/-!
# Entailment of the forwarding predicate (`FwdEntails`)

`NoRevLoc` (`Smrd.CoherenceT`), the forwarding hypothesis of `dep_po_T`, does
not follow from the restrictions on Forwarding and Write Elision
(`Smrd.FwdAcrossAlias`): `pred` is taken under the predicate `P_{j₀}` and
context `δ_{j₀}` of the justification `j₀` an edge was generated against,
while the parts of `≼` ask their alias queries under each justification's own
predicate `P_j ∧ ψ_δ`, with the shared `δ`. This module asks the alias
queries of `≼` to be no weaker than the one `pred` answered.

## The condition

For each edge `(s, t)` of `F ∪ WE` (`t` remapped onto `s`), `EdgeGen` names a
justification `j₀` it was generated against and the `⊑`-ordered pair
`(u, v)` that `pred` related: `u -F_{j₀}→ v` with `(u, v) = (s, t)`, or
`u -WE_{j₀}→ v` with `(u, v) = (t, s)`; and `δ_{j₀}`'s edges are among the
shared ones. Every edge of an execution has such a `j₀`, generated
(`edgeGen_of_execution`). `FwdEntailsOn scope` asks, for each edge, one such
`j₀` with

* `P_j ∧ ψ_δ ⊨ P_{j₀} ∧ ψ_{δ_{j₀}}` for every `j ∈ J` in `scope j u v t`, and
* `p_combined ⊨ P_{j₀} ∧ ψ_{δ_{j₀}}`.

The scopes:

* `FwdEntails`: `j`'s window contains `v` (the forwarded event `e₂`, or the
  eliding write) -- the candidate as proposed;
* `FwdEntailsSrc`: `j`'s window contains `u` or `v` -- the first proposed
  strengthening;
* `FwdEntailsImg`: `j`'s window contains `remap_δ(t)`, the image of the moved
  event under the shared context;
* `FwdEntailsAll`: every `j ∈ J` -- the second proposed strengthening, alias
  queries of every justification answered under `P_{j₀}`.

Differences from the proposal: `j₀` is existential (one generating
justification that satisfies the entailment suffices; the theorems are
stronger for it), and it carries `δ_{j₀} ⊆ δ` (as every generated one does).

## Results

* `noRev_of_edges`: the core. A `⊑`-pair `a ⊑ b` at one location under a
  valuation `f` is not reversed by `remap_δ` if `f` satisfies
  `P_{j₀} ∧ ψ_{δ_{j₀}}` for the edges on the chains of `a` and `b`. A
  reversal makes some edge `(u, v)` of those chains cross an event `c`,
  `u ⊑ c ⊑ v`, at the same location under `f` (Forwarding on `b`'s chain
  across `a`, or Write Elision on `a`'s chain across `remap_δ(b)`), and the
  image of `c` under `δ_{j₀}` is then `≼`-between `u` and `v` in `j₀`
  (`no_cross`), against `pred`. No hypothesis on the shape of the chains.
* `dep_po_E`: **`DP ∪ ≼ ⊆ ⊑` under `FwdEntailsImg`**, with the hypotheses of
  `dep_po_T` but `NoRevLoc`, plus `Sat P` (from `φ`), locations that evaluate
  (`LocsEval`, from `TotalLocs`), and `NoRevRMW`, the part of `NoRevLoc` for
  pairs with an RMW access, which entailment of predicates does not address.
  `Smrd.FwdEntailsRMW` drops it (`dep_po_R`, with `RMWWF`) and refutes it
  from the restrictions (`Smrd.RMWCross`).
* `noRevLoc_of_fwdEntailsAll`: `FwdEntailsAll` (with `NoRevRMW`) implies
  `NoRevLoc` itself. The window-restricted conditions cannot: `NoRevLoc`'s
  `LocLinked` asks alias queries of every justification, windows or not, so
  any justification with a weaker predicate (an initialising write's
  pre-justification) witnesses it (`FwdPastWindow.locLinked_79_init`).
* `fwdEntailsOn_of_valid`: where each edge has a generating justification
  whose predicate is valid (no Strengthening, no guards), every scope holds;
  `fwdEntailsOn_of_noEdge`: without edges, trivially.

`Smrd.FwdPastWindow` refutes `FwdEntails`, and `Smrd.FwdChain`
`FwdEntailsSrc`, as sufficient conditions for `DP ∪ ≼ ⊆ ⊑`: consistent
executions satisfying them with `≼ ⊄ ⊑`, which `FwdEntailsImg` rules out.
`Smrd.FwdEntailsCheck` shows that the execution of `Smrd.FwdAcrossAlias`
violates every scope, and that the positive executions with an elision satisfy
every scope.
-/

namespace Execution

open EventStructure

/-! ## Locations as values -/

/-- The value of an event's location under a valuation, if it has one. -/
def locVal (es : EventStructure) (f : Valuation) (a : EventId) : Option Val :=
  ((es.ev a).bind Event.loc).bind (·.eval f)

theorem locVal_eq {es : EventStructure} {f : Valuation} {a : EventId} {e : Event} {l : Expr}
    (he : es.ev a = some e) (hl : e.loc = some l) : locVal es f a = l.eval f := by
  simp [locVal, he, hl]

theorem locVal_some {es : EventStructure} {f : Valuation} {a : EventId} {v : Val}
    (h : locVal es f a = some v) : ∃ e l, es.ev a = some e ∧ e.loc = some l ∧ l.eval f = some v := by
  unfold locVal at h
  cases he : es.ev a with
  | none => simp [he] at h
  | some e =>
      cases hl : e.loc with
      | none => simp [he, hl] at h
      | some l => exact ⟨e, l, rfl, hl, by simpa [he, hl] using h⟩

theorem eq_holds_iff {l₁ l₂ : Expr} {f : Valuation} :
    (Expr.eq l₁ l₂).holds f ↔ ∃ v, l₁.eval f = some v ∧ l₂.eval f = some v := by
  unfold Expr.holds
  simp only [Expr.eval]
  cases h₁ : l₁.eval f <;> cases h₂ : l₂.eval f <;> simp [eq_comm]

theorem of_mayAlias {es : EventStructure} {P : Pred} {a b : EventId} (h : es.mayAlias P a b) :
    ∃ f, P f ∧ ∃ v, locVal es f a = some v ∧ locVal es f b = some v := by
  obtain ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, hP, heq⟩ := h
  obtain ⟨v, hv₁, hv₂⟩ := eq_holds_iff.1 heq
  exact ⟨f, hP, v, by rw [locVal_eq h₁ hl₁, hv₁], by rw [locVal_eq h₂ hl₂, hv₂]⟩

theorem mayAlias_of {es : EventStructure} {P : Pred} {a b : EventId} {f : Valuation} {v : Val}
    (hP : P f) (ha : locVal es f a = some v) (hb : locVal es f b = some v) : es.mayAlias P a b := by
  obtain ⟨e₁, l₁, h₁, hl₁, hv₁⟩ := locVal_some ha
  obtain ⟨e₂, l₂, h₂, hl₂, hv₂⟩ := locVal_some hb
  exact ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, f, hP, eq_holds_iff.2 ⟨v, hv₁, hv₂⟩⟩

/-- Every location evaluates under every valuation. Programs that do not
    compute pointers have it (`locsEval_of_totalLocs`). -/
def LocsEval (es : EventStructure) : Prop :=
  ∀ a e l f, es.ev a = some e → e.loc = some l → (l.eval f).isSome

theorem locsEval_of_totalLocs {es : EventStructure} (ht : es.TotalLocs) : LocsEval es :=
  fun a e l f he hl => locsEvalAt_of_totalLocs ht (fun _ => True) f a e l trivial he hl

/-- Under `LocsEval`, locations equal outright are equal under every
    valuation. -/
theorem locVal_of_mustAlias {es : EventStructure} (hev : LocsEval es) {a b : EventId}
    (h : es.mustAlias a b) (f : Valuation) :
    ∃ v, locVal es f a = some v ∧ locVal es f b = some v := by
  obtain ⟨e₁, e₂, l₁, l₂, h₁, h₂, hl₁, hl₂, hs⟩ := h
  obtain ⟨v₁, hv₁⟩ := Option.isSome_iff_exists.1 (hev a e₁ l₁ f h₁ hl₁)
  obtain ⟨v₂, hv₂⟩ := Option.isSome_iff_exists.1 (hev b e₂ l₂ f h₂ hl₂)
  have := hs f v₁ v₂ hv₁ hv₂
  subst this
  exact ⟨v₁, by rw [locVal_eq h₁ hl₁, hv₁], by rw [locVal_eq h₂ hl₂, hv₂]⟩

/-! ## Remapping chains -/

/-- The image of `remap_δ` has no `F ∪ WE`-predecessor. -/
theorem canon_of_remap {δ : FwdCtx} {a a' : EventId} (h : δ.Remap a a') :
    ∀ b, ¬ δ.edge b a' := by
  induction h with
  | canon h => exact h
  | step _ _ ih => exact ih

/-- A predecessor of an event on its chain has the same image. -/
theorem remap_inv_step {δ : FwdCtx} (hu : ∀ a b e, δ.edge a e → δ.edge b e → a = b)
    {q p e' : EventId} (he : δ.edge q p) (h : δ.Remap p e') : δ.Remap q e' := by
  cases h with
  | canon hno => exact absurd he (hno q)
  | step he' hr => exact hu _ _ _ he he' ▸ hr

/-- **A sub-context's chain is a prefix**: with `δ₀ ⊆ δ` and unique
    predecessors in `δ`, the image of `a` under `δ₀` lies on its chain in
    `δ`. -/
theorem remap_prefix {δ₀ δ : FwdCtx} (hsub : ∀ a b, δ₀.edge a b → δ.edge a b)
    (hu : ∀ a b e, δ.edge a e → δ.edge b e → a = b) {a a' : EventId} (h : δ.Remap a a') :
    ∃ a₀, δ₀.Remap a a₀ ∧ δ.Remap a₀ a' := by
  induction h with
  | @canon e hno => exact ⟨e, .canon fun b hb => hno b (hsub _ _ hb), .canon hno⟩
  | @step q e e' he hr ih =>
      by_cases h₀ : ∃ b, δ₀.edge b e
      · obtain ⟨b, hb⟩ := h₀
        obtain rfl := hu _ _ _ (hsub _ _ hb) he
        obtain ⟨a₀, h₁, h₂⟩ := ih
        exact ⟨a₀, .step hb h₁, h₂⟩
      · exact ⟨e, .canon fun b hb => h₀ ⟨b, hb⟩, .step he hr⟩

variable {es : EventStructure} {x : Execution}

/-- `remap_stay_up` (`Smrd.CoherenceT`), with the crossing Forwarding edge on
    the chain. -/
theorem remap_stay_up' {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c) (hF : PoForest es)
    {c e e' : EventId} (h : x.δ.Remap e e') (hc : c = e ∨ es.poR c e) :
    (c = e' ∨ es.poR c e') ∨ x.δ.Remap c e' ∨
      ∃ q p, (q, p) ∈ x.δ.f ∧ es.poR q c ∧ es.poR c p ∧ x.δ.Remap p e' := by
  revert hc
  induction h with
  | canon _ => exact fun hc => .inl hc
  | @step q e e' he hr ih =>
      rintro (rfl | hce)
      · exact .inr (.inl (.step he hr))
      · rcases edge_cases hx he with ⟨hf, hqe⟩ | ⟨-, heq⟩
        · rcases hF q c e (.inr hqe) (.inr hce) with rfl | hqc | hcq
          · exact .inr (.inl hr)
          · exact .inr (.inr ⟨q, e, hf, hqc, hce, .step he hr⟩)
          · exact ih (.inr hcq)
        · exact ih (.inr (hpo_trans _ _ _ hce heq))

/-- `remap_enter_up` (`Smrd.CoherenceT`), with the crossing Write Elision edge
    on the chain. -/
theorem remap_enter_up' {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c) (hF : PoForest es)
    {c e e' : EventId} (h : x.δ.Remap e e') (hc : ¬ (c = e ∨ es.poR c e))
    (hc' : c = e' ∨ es.poR c e') :
    x.δ.Remap c e' ∨ ∃ q p, (q, p) ∈ x.δ.we ∧ es.poR p c ∧ es.poR c q ∧ x.δ.Remap p e' := by
  revert hc
  induction h with
  | canon _ => exact fun hc => absurd hc' hc
  | @step q e e' he hr ih =>
      intro hc
      by_cases hq : c = q ∨ es.poR c q
      · rcases edge_cases hx he with ⟨-, hqe⟩ | ⟨hw, heq⟩
        · rcases hq with rfl | hcq
          · exact absurd (.inr hqe) hc
          · exact absurd (.inr (hpo_trans _ _ _ hcq hqe)) hc
        · rcases hq with rfl | hcq
          · exact .inl hr
          · rcases hF c e q (.inr hcq) (.inr heq) with rfl | hce | hec
            · exact absurd (.inl rfl) hc
            · exact absurd (.inr hce) hc
            · exact .inr ⟨q, e, hw, hec, hcq, .step he hr⟩
      · exact ih hc' hq

/-! ## The condition -/

/-- `P_{j₀} ∧ ψ_{δ_{j₀}}`: the predicate `pred` and the location equivalence
    of `fwdBase` were answered under. -/
def PredOf (es : EventStructure) (j₀ : Justification) : Pred :=
  Pred.and j₀.P.holds (j₀.δ.psi es)

/-- The edge `(s, t)` of `F ∪ WE` was generated against `j₀`, which related
    the `⊑`-ordered pair `(u, v)`: a Forwarding edge `u -F_{j₀}→ v`,
    `(u, v) = (s, t)`, or a Write Elision edge `u -WE_{j₀}→ v` (`u` elided into
    `v`), `(u, v) = (t, s)`; and `δ_{j₀}` is part of the shared context. -/
def EdgeGen (es : EventStructure) (x : Execution) (j₀ : Justification) (s t u v : EventId) : Prop :=
  (((s, t) ∈ x.δ.f ∧ u = s ∧ v = t ∧ es.fwdRel j₀ s t) ∨
    ((s, t) ∈ x.δ.we ∧ u = t ∧ v = s ∧ es.weRel j₀ t s)) ∧
  (∀ p ∈ j₀.δ.f, p ∈ x.δ.f) ∧ (∀ p ∈ j₀.δ.we, p ∈ x.δ.we)

/-- **The alias queries of `≼` are no weaker than `pred`'s**, for the
    justifications in `scope j u v t`: each edge `(s, t)` has a generating
    `j₀` (`EdgeGen`) with `P_j ∧ ψ_δ ⊨ P_{j₀} ∧ ψ_{δ_{j₀}}` for every
    `j ∈ J` in scope, and `p_combined ⊨ P_{j₀} ∧ ψ_{δ_{j₀}}`. -/
def FwdEntailsOn (es : EventStructure) (x : Execution)
    (scope : Justification → EventId → EventId → EventId → Prop) : Prop :=
  ∀ s t, x.δ.edge s t → ∃ j₀ u v, EdgeGen es x j₀ s t u v ∧
    (∀ j ∈ x.J, scope j u v t → Entails (x.PJ es j) (PredOf es j₀)) ∧
    Entails (x.Pm es) (PredOf es j₀)

/-- The candidate: every `j` whose window contains `e₂` (`v`: the forwarded
    event, or the eliding write). -/
def FwdEntails (es : EventStructure) (x : Execution) : Prop :=
  FwdEntailsOn es x fun j _ v _ => Win es j v

/-- Every `j` whose window contains `e₁` or `e₂`. -/
def FwdEntailsSrc (es : EventStructure) (x : Execution) : Prop :=
  FwdEntailsOn es x fun j u v _ => Win es j u ∨ Win es j v

/-- Every `j` whose window contains the image `remap_δ(t)` of the moved
    event under the shared context. -/
def FwdEntailsImg (es : EventStructure) (x : Execution) : Prop :=
  FwdEntailsOn es x fun j _ _ t => ∃ t', x.δ.Remap t t' ∧ Win es j t'

/-- Every `j ∈ J`. -/
def FwdEntailsAll (es : EventStructure) (x : Execution) : Prop :=
  FwdEntailsOn es x fun _ _ _ _ => True

theorem FwdEntailsOn.mono {s₁ s₂ : Justification → EventId → EventId → EventId → Prop}
    (hs : ∀ j u v t, s₂ j u v t → s₁ j u v t) (h : FwdEntailsOn es x s₁) : FwdEntailsOn es x s₂ :=
  fun s t he => by
    obtain ⟨j₀, u, v, hg, hJ, hm⟩ := h s t he
    exact ⟨j₀, u, v, hg, fun j hj hsc => hJ j hj (hs _ _ _ _ hsc), hm⟩

theorem FwdEntailsAll.on (h : FwdEntailsAll es x) (scope) : FwdEntailsOn es x scope :=
  h.mono fun _ _ _ _ _ => trivial

theorem FwdEntailsSrc.fwdEntails (h : FwdEntailsSrc es x) : FwdEntails es x :=
  h.mono fun _ _ _ _ hv => .inr hv

/-- Without `F ∪ WE` edges every scope holds. -/
theorem fwdEntailsOn_of_noEdge (h : ∀ a b, ¬ x.δ.edge a b) (scope) : FwdEntailsOn es x scope :=
  fun s t he => absurd he (h s t)

theorem EdgeGen.base {j₀ : Justification} {s t u v : EventId} (h : EdgeGen es x j₀ s t u v) :
    es.fwdBase j₀ u v := by
  rcases h.1 with ⟨-, rfl, rfl, hr⟩ | ⟨-, rfl, rfl, hr⟩
  · exact hr.1.1
  · exact hr.1.1

theorem EdgeGen.sub {j₀ : Justification} {s t u v : EventId} (h : EdgeGen es x j₀ s t u v) :
    ∀ a b, j₀.δ.edge a b → x.δ.edge a b := by
  rintro a b (hf | hw)
  · exact .inl (h.2.1 _ hf)
  · exact .inr (h.2.2 _ hw)

/-- `ψ_δ` entails `ψ_{δ_{j₀}}`. -/
theorem EdgeGen.psi {j₀ : Justification} {s t u v : EventId} (h : EdgeGen es x j₀ s t u v)
    {f : Valuation} (hf : x.δ.psi es f) : j₀.δ.psi es f :=
  fun p hp => hf p (h.2.1 p hp)

/-- **Valid generating predicates make every scope hold**: where each edge
    has a generating `j₀` whose predicate holds under every valuation (no
    Strengthening, no guard), `P_{j₀} ∧ ψ_{δ_{j₀}}` follows from `ψ_δ`, which
    every `P_j ∧ ψ_δ` and `p_combined` contain. -/
theorem fwdEntailsOn_of_valid
    (h : ∀ s t, x.δ.edge s t → ∃ j₀ u v, EdgeGen es x j₀ s t u v ∧ ∀ f, j₀.P.holds f) (scope) :
    FwdEntailsOn es x scope := fun s t he => by
  obtain ⟨j₀, u, v, hg, hv⟩ := h s t he
  exact ⟨j₀, u, v, hg, fun j _ _ f hf => ⟨hv f, hg.psi hf.2⟩, fun f hf => ⟨hv f, hg.psi hf.2.1⟩⟩

/-! ## Every edge has a generating justification -/

/-- Each edge of a generated justification was added against a generated
    justification whose context is part of the final one. -/
theorem generated_edge_gen {Ω : Pred} {j : Justification} (h : es.Generated Ω j) :
    (∀ p ∈ j.δ.f, ∃ j₀, es.Generated Ω j₀ ∧ es.fwdRel j₀ p.1 p.2 ∧
      (∀ q ∈ j₀.δ.f, q ∈ j.δ.f) ∧ (∀ q ∈ j₀.δ.we, q ∈ j.δ.we)) ∧
    (∀ p ∈ j.δ.we, ∃ j₀, es.Generated Ω j₀ ∧ es.weRel j₀ p.2 p.1 ∧
      (∀ q ∈ j₀.δ.f, q ∈ j.δ.f) ∧ (∀ q ∈ j₀.δ.we, q ∈ j.δ.we)) := by
  induction h with
  | pre _ hj _ => rw [δ_of_preJust hj]; exact ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩
  | va _ _ _ _ ih => exact ih
  | str _ _ _ _ _ _ _ ih => exact ih
  | @fwd j₁ _ _ _ _ e₁ e₂ _ _ _ _ hg _ hf _ _ _ _ _ _ ih =>
      refine ⟨fun p hp => ?_, fun p hp => ?_⟩
      · rcases List.mem_append.1 hp with hp | hp
        · obtain ⟨j₀, h₀, hr, hsf, hsw⟩ := ih.1 p hp
          exact ⟨j₀, h₀, hr, fun q hq => List.mem_append_left _ (hsf q hq), hsw⟩
        · simp only [List.mem_singleton] at hp
          subst hp
          exact ⟨j₁, hg, hf, fun q hq => List.mem_append_left _ hq, fun q hq => hq⟩
      · obtain ⟨j₀, h₀, hr, hsf, hsw⟩ := ih.2 p hp
        exact ⟨j₀, h₀, hr, fun q hq => List.mem_append_left _ (hsf q hq), hsw⟩
  | @we j₁ e₁ e₂ hg hwe _ _ ih =>
      refine ⟨fun p hp => ?_, fun p hp => ?_⟩
      · obtain ⟨j₀, h₀, hr, hsf, hsw⟩ := ih.1 p hp
        exact ⟨j₀, h₀, hr, hsf, fun q hq => List.mem_append_left _ (hsw q hq)⟩
      · rcases List.mem_append.1 hp with hp | hp
        · obtain ⟨j₀, h₀, hr, hsf, hsw⟩ := ih.2 p hp
          exact ⟨j₀, h₀, hr, hsf, fun q hq => List.mem_append_left _ (hsw q hq)⟩
        · simp only [List.mem_singleton] at hp
          subst hp
          exact ⟨j₁, hg, hwe, fun q hq => hq, fun q hq => List.mem_append_left _ hq⟩
  | lift _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih₂ => exact ih₂
  | weak _ _ _ _ ih => exact ih

theorem mem_δ_f_of {j : Justification} (hj : j ∈ x.J) {p : EventId × EventId} (hp : p ∈ j.δ.f) :
    p ∈ x.δ.f := by
  obtain ⟨X, J, rf⟩ := x
  simp only [δ] at *
  induction J with
  | nil => cases hj
  | cons j' J ih =>
      simp only [FwdCtx.union, List.foldr_cons]
      rcases List.mem_cons.1 hj with rfl | hj
      · exact List.mem_append_left _ hp
      · exact List.mem_append_right _ (ih hj)

theorem mem_δ_we_of {j : Justification} (hj : j ∈ x.J) {p : EventId × EventId} (hp : p ∈ j.δ.we) :
    p ∈ x.δ.we := by
  obtain ⟨X, J, rf⟩ := x
  simp only [δ] at *
  induction J with
  | nil => cases hj
  | cons j' J ih =>
      simp only [FwdCtx.union, List.foldr_cons]
      rcases List.mem_cons.1 hj with rfl | hj
      · exact List.mem_append_left _ hp
      · exact List.mem_append_right _ (ih hj)

/-- **Every edge of an execution has a generated `j₀` (`EdgeGen`)**: the
    structural part of the condition always holds; only the entailment
    constrains. -/
theorem edgeGen_of_execution {Ω : Pred} (hx : x.IsExecution es Ω) {s t : EventId}
    (he : x.δ.edge s t) : ∃ j₀ u v, EdgeGen es x j₀ s t u v ∧ es.Generated Ω j₀ := by
  rcases he with hf | hw
  · obtain ⟨j, hj, hpj⟩ := mem_δ_f_inv hf
    obtain ⟨j₀, h₀, hr, hsf, hsw⟩ := (generated_edge_gen (hx.generated j hj)).1 _ hpj
    exact ⟨j₀, s, t, ⟨.inl ⟨hf, rfl, rfl, hr⟩, fun q hq => mem_δ_f_of hj (hsf q hq),
      fun q hq => mem_δ_we_of hj (hsw q hq)⟩, h₀⟩
  · obtain ⟨j, hj, hpj⟩ := mem_δ_we_inv hw
    obtain ⟨j₀, h₀, hr, hsf, hsw⟩ := (generated_edge_gen (hx.generated j hj)).2 _ hpj
    exact ⟨j₀, t, s, ⟨.inr ⟨hw, rfl, rfl, hr⟩, fun q hq => mem_δ_f_of hj (hsf q hq),
      fun q hq => mem_δ_we_of hj (hsw q hq)⟩, h₀⟩

/-! ## No crossing against `pred` -/

/-- The two ends of a generated edge are at one location under
    `P_{j₀} ∧ ψ_{δ_{j₀}}`. -/
theorem EdgeGen.loc (hev : LocsEval es) {j₀ : Justification} {s t u v : EventId}
    (h : EdgeGen es x j₀ s t u v) {f : Valuation} (hf : PredOf es j₀ f) :
    locVal es f s = locVal es f t ∧ (locVal es f t).isSome := by
  obtain ⟨-, -, ev₁, ev₂, l₁, l₂, h₁, h₂, hl₁, hl₂, hq⟩ := h.base
  obtain ⟨v₁, hv₁⟩ := Option.isSome_iff_exists.1 (hev u ev₁ l₁ f h₁ hl₁)
  obtain ⟨v₂, hv₂⟩ := Option.isSome_iff_exists.1 (hev v ev₂ l₂ f h₂ hl₂)
  have := hq f hf v₁ v₂ hv₁ hv₂
  subst this
  have hu : locVal es f u = some v₁ := by rw [locVal_eq h₁ hl₁, hv₁]
  have hv : locVal es f v = some v₁ := by rw [locVal_eq h₂ hl₂, hv₂]
  rcases h.1 with ⟨-, rfl, rfl, -⟩ | ⟨-, rfl, rfl, -⟩
  · rw [hu, hv]; simp
  · rw [hu, hv]; simp

/-- Along a chain whose edges' generating predicates `f` satisfies, every
    event is at the location of the image. -/
theorem chain_loc (hev : LocsEval es) {f : Valuation} {a a' : EventId} (h : x.δ.Remap a a')
    (H : ∀ s t, x.δ.edge s t → x.δ.Remap t a' →
      ∃ j₀ u v, EdgeGen es x j₀ s t u v ∧ PredOf es j₀ f) :
    locVal es f a = locVal es f a' := by
  induction h with
  | canon _ => rfl
  | @step q e e' he hr ih =>
      obtain ⟨j₀, u, v, hg, hf⟩ := H q e he (.step he hr)
      rw [← ih H, (hg.loc hev hf).1]

/-- **`pred` refutes a crossing**: an event `c` strictly `⊑`-between the ends
    `u ⊑ v` of an edge generated against `j₀`, at their location under a
    model of `P_{j₀} ∧ ψ_{δ_{j₀}}`, whose image under `δ_{j₀}` is neither end,
    is `≼`-between them in `j₀` (`≼^{P_{j₀}}_{δ_{j₀}}`), so `u` is not an
    immediate predecessor of `v`. -/
theorem no_cross (hev : LocsEval es) {j₀ : Justification} {u v c c₀ : EventId}
    (hb : es.fwdBase j₀ u v) {f : Valuation} (hf : PredOf es j₀ f)
    (huc : es.poR u c) (hcv : es.poR c v) {val : Val} (hc : locVal es f c = some val)
    (hv : locVal es f v = some val) (hr : j₀.δ.Remap c c₀) (hcu : c₀ ≠ u) (hcv' : c₀ ≠ v) :
    False := by
  obtain ⟨⟨⟨⟨u₀, v₀, -, ru, rv⟩, -⟩, hno⟩, -, ev₁, ev₂, l₁, l₂, h₁, h₂, hl₁, hl₂, hq⟩ := hb
  have ru' : j₀.δ.Remap u u := .canon (canon_of_remap ru)
  have rv' : j₀.δ.Remap v v := .canon (canon_of_remap rv)
  have hu : locVal es f u = some val := by
    obtain ⟨v₁, hv₁⟩ := Option.isSome_iff_exists.1 (hev u ev₁ l₁ f h₁ hl₁)
    rw [locVal_eq h₂ hl₂] at hv
    rw [locVal_eq h₁ hl₁, hv₁, hq f hf v₁ val hv₁ hv]
  exact hno ⟨c₀, ⟨⟨u, c, .inr ⟨huc, mayAlias_of hf.1 hu hc⟩, ru', hr⟩, fun h => hcu h.symm⟩,
    ⟨⟨c, v, .inr ⟨hcv, mayAlias_of hf.1 hc hv⟩, hr, rv'⟩, hcv'⟩⟩

/-- **The core: `remap_δ` reverses no `⊑`-pair at one location under a
    valuation that satisfies the generating predicates of the edges on the
    two chains.** No hypothesis on the shape of the chains. -/
theorem noRev_of_edges {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hev : LocsEval es)
    {a b a' b' : EventId} (hab : es.poR a b) (ra : x.δ.Remap a a') (rb : x.δ.Remap b b')
    (hne : a' ≠ b') {f : Valuation} {val : Val}
    (hfa : locVal es f a = some val) (hfb : locVal es f b = some val)
    (H : ∀ s t, x.δ.edge s t → (x.δ.Remap t a' ∨ x.δ.Remap t b') →
      ∃ j₀ u v, EdgeGen es x j₀ s t u v ∧ PredOf es j₀ f) :
    ¬ es.poR b' a' := by
  intro hba
  have hu := hx.fwdWF.uniq
  have hfun := fun {e e₁ e₂ : EventId} => @FwdCtx.Remap.functional x.δ hu e e₁ e₂
  have la : locVal es f a' = some val := by
    rw [← chain_loc hev ra fun s t he h => H s t he (.inl h)]; exact hfa
  have lb : locVal es f b' = some val := by
    rw [← chain_loc hev rb fun s t he h => H s t he (.inr h)]; exact hfb
  have cb : ∀ e, ¬ x.δ.edge e b' := canon_of_remap rb
  rcases remap_stay_up' hx hpo_trans hF rb (c := a) (.inr hab) with
    (heq | hab') | hra | ⟨q, p, hf, hqa, hap, hpb⟩
  · have : x.δ.Remap a b' := heq ▸ (.canon cb : x.δ.Remap b' b')
    exact hne (hfun ra this)
  · -- `a`'s chain enters the up-set of `b'` by a Write Elision edge across `b'`
    have hnot : ¬ (b' = a ∨ es.poR b' a) := by
      rintro (h | h)
      · exact hirr _ (h ▸ hab')
      · exact hirr _ (hpo_trans _ _ _ hab' h)
    rcases remap_enter_up' hx hpo_trans hF ra hnot (.inr hba) with hrb | ⟨q, p, hw, hpb, hbq, hpa⟩
    · exact hne (hfun hrb (.canon cb))
    · have hqp : x.δ.edge q p := .inr hw
      have hqa : x.δ.Remap q a' := remap_inv_step hu hqp hpa
      obtain ⟨j₀, u, v, hg, hf₀⟩ := H q p hqp (.inl hpa)
      have hpq : es.poR p q := we_po hx _ hw
      obtain ⟨hu', hv'⟩ : u = p ∧ v = q := by
        rcases hg.1 with ⟨-, rfl, rfl, hr⟩ | ⟨-, rfl, rfl, -⟩
        · exact absurd (hpo_trans _ _ _ hr.1.1.2.1 hpq) (hirr _)
        · exact ⟨rfl, rfl⟩
      subst u v
      have lq : locVal es f q = some val := by
        rw [chain_loc hev hqa fun s t he h => H s t he (.inl h)]; exact la
      refine no_cross hev hg.base hf₀ hpb hbq lb lq (c₀ := b')
        (.canon fun e he => cb e (hg.sub _ _ he)) (fun h => cb q (h ▸ hqp)) ?_
      rintro rfl
      exact hne (hfun hqa (.canon cb))
  · exact hne (hfun ra hra)
  · -- `b`'s chain leaves the up-set of `a` by a Forwarding edge across `a`
    have hqp : x.δ.edge q p := .inl hf
    have hqb : x.δ.Remap q b' := remap_inv_step hu hqp hpb
    obtain ⟨j₀, u, v, hg, hf₀⟩ := H q p hqp (.inr hpb)
    have hqp' : es.poR q p := fwd_po hx _ hf
    obtain ⟨hu', hv'⟩ : u = q ∧ v = p := by
      rcases hg.1 with ⟨-, rfl, rfl, -⟩ | ⟨-, rfl, rfl, hr⟩
      · exact ⟨rfl, rfl⟩
      · exact absurd (hpo_trans _ _ _ hr.1.1.2.1 hqp') (hirr _)
    subst u v
    have lp : locVal es f p = some val := by
      rw [chain_loc hev hpb fun s t he h => H s t he (.inr h)]; exact lb
    obtain ⟨a₀, ha₀, ha₀'⟩ := remap_prefix hg.sub hu ra
    refine no_cross hev hg.base hf₀ hqa hap hfa lp ha₀ ?_ ?_
    · rintro rfl; exact hne (hfun ha₀' hqb)
    · rintro rfl; exact hne (hfun ha₀' hpb)

/-! ## `DP ∪ ≼ ⊆ ⊑` -/

/-- The part of `NoRevLoc` for pairs with an RMW access, which entailment of
    predicates does not address. It holds where there are no RMWs
    (`noRevRMW_of_nil`), under `NoRevLoc`, and where no `F ∪ WE` edge crosses
    an RMW access (`noRevRMW_of_noCrossRMW`); it does not follow from the
    restrictions (`RMWCross.rmwCross`), and `DP ∪ ≼ ⊆ ⊑` does not need it
    (`dep_po_R`). -/
def NoRevRMW (es : EventStructure) (x : Execution) : Prop :=
  ∀ a b a' b', es.poR a b → x.δ.Remap a a' → x.δ.Remap b b' → (es.RMWAcc a ∨ es.RMWAcc b) →
    ¬ es.poR b' a'

theorem noRevRMW_of_nil (h : es.rmw = []) : NoRevRMW es x :=
  fun _ _ _ _ _ _ _ hr _ => by rcases hr with hr | hr <;> exact es.not_rmwAcc_of_nil h _ hr

theorem noRevRMW_of_noRevLoc (h : NoRevLoc es x) : NoRevRMW es x :=
  fun a b a' b' hab ra rb hr => h a b a' b' hab ra rb (by
    rcases hr with hr | hr
    · exact .inr (.inr (.inr (.inl hr)))
    · exact .inr (.inr (.inr (.inr hr))))

/-- `ppoM_po_T` with the alias part of `NoRevLoc` replaced by a hypothesis on
    the step's own alias predicate. -/
theorem ppoM_po_E {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hR : NoRevRMW es x) (hT : RMWTightR es x)
    {Pa Pr : Pred} {a' b' : EventId}
    (hAl : ∀ a b, es.poR a b → (es.mustAlias a b ∨ es.mayAlias Pa a b) →
      x.δ.Remap a a' → x.δ.Remap b b' → a' ≠ b' → ¬ es.poR b' a')
    (ha' : x.XwF es a') (hb' : x.XwF es b')
    (hA : x.Anchored es a' b') (h : es.ppoM Pa Pr x.δ a' b') : es.poR a' b' := by
  obtain ⟨⟨a, b, hab, ra, rb⟩, hne⟩ := h
  have hfun := fun {e e₁ e₂ : EventId} => @FwdCtx.Remap.functional x.δ hx.fwdWF.uniq e e₁ e₂
  have hbase : es.poR a b := by
    rcases hab with (hs | (⟨w, hs, ent, hm, hw, hr', -⟩ | ⟨r, ⟨ent, hm, hw, hr', -⟩, hs⟩)) | hal
    · exact hs.1
    · subst hw hr'
      rcases hT.1 ent hm a a' ra ha' hs.1 with rfl | h
      · exact absurd (hfun ra rb) hne
      · exact h
    · subst hw hr'
      rcases hT.2 ent hm b b' rb hb' hs.1 with rfl | h
      · exact absurd (hfun ra rb) hne
      · exact h
    · exact hal.1
  rcases anchored_cmp hF hA with h | h | h
  · exact absurd h hne
  · exact h
  · refine absurd h ?_
    rcases hab with (hs | (⟨w, hs, ent, hm, hw, hr', -⟩ | ⟨r, ⟨ent, hm, hw, hr', -⟩, hs⟩)) | hal
    · exact sync_not_back hx hpo_trans hirr hF hs ra rb hne
    · exact hR a b a' b' hbase ra rb (.inr ⟨ent, hm, .inl hr'⟩)
    · exact hR a b a' b' hbase ra rb (.inl ⟨ent, hm, .inr hw⟩)
    · exact hAl a b hbase hal.2 ra rb hne

/-- A model of `P` satisfies every `P_j ∧ ψ_δ`. -/
theorem PJ_of_P {f : Valuation} (h : x.P es f) {j : Justification} (hj : j ∈ x.J) :
    x.PJ es j f :=
  ⟨(h j hj).1, psi_of_P h⟩

/-- **Each step of `≼` lies in `⊑` under `FwdEntailsImg`.** -/
theorem ppoStep_po_E {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hT : RMWTightR es x)
    (hsat : Sat (x.P es)) (hev : LocsEval es) (hE : FwdEntailsImg es x) (hR : NoRevRMW es x)
    {a b : EventId} (h : x.ppoStep es a b) : es.poR a b := by
  obtain ⟨ha, hb, ⟨j, hj, hp, hwa, hwb⟩ | ⟨hs | ⟨hp, hal'⟩, hA⟩⟩ := h
  · refine ppoM_po_E hx hpo_trans hirr hF hR hT ?_ ha hb
      (anchored_of_inWin hx.inX ⟨j, hj, hwa, hwb⟩) hp
    intro a₀ b₀ hab hal ra rb hne
    obtain ⟨f, hf, val, h₁, h₂⟩ : ∃ f, x.PJ es j f ∧ ∃ v, locVal es f a₀ = some v ∧
        locVal es f b₀ = some v := by
      rcases hal with hm | hm
      · obtain ⟨f, hf⟩ := hsat
        exact ⟨f, PJ_of_P hf hj, locVal_of_mustAlias hev hm f⟩
      · exact of_mayAlias hm
    refine noRev_of_edges hx hpo_trans hirr hF hev hab ra rb hne h₁ h₂ fun s t he ht => ?_
    obtain ⟨j₀, u, v, hg, hJ, -⟩ := hE s t he
    refine ⟨j₀, u, v, hg, hJ j hj ?_ f hf⟩
    rcases ht with ht | ht
    · exact ⟨_, ht, hwa⟩
    · exact ⟨_, ht, hwb⟩
  · exact ppoSyncRM_po_T hx hpo_trans hirr hF hA hs
  · refine ppoM_po_E hx hpo_trans hirr hF hR hT ?_ ha hb hA hp
    intro a₀ b₀ hab hal ra rb hne
    obtain ⟨f, hf, val, h₁, h₂⟩ : ∃ f, x.Pm es f ∧ ∃ v, locVal es f a₀ = some v ∧
        locVal es f b₀ = some v := by
      rcases hal with hm | hm
      · obtain ⟨f, hf, -⟩ := of_mayAlias hal'
        exact ⟨f, hf, locVal_of_mustAlias hev hm f⟩
      · exact of_mayAlias hm
    refine noRev_of_edges hx hpo_trans hirr hF hev hab ra rb hne h₁ h₂ fun s t he _ => ?_
    obtain ⟨j₀, u, v, hg, -, hm⟩ := hE s t he
    exact ⟨j₀, u, v, hg, hm f hf⟩

/-- **`DP ∪ ≼ ⊆ ⊑` under `FwdEntailsImg`**: `dep_po_T` with `NoRevLoc`
    replaced by `FwdEntailsImg` and `NoRevRMW`, given a model of `P` (as `φ`
    provides) and locations that evaluate. -/
theorem dep_po_E {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hT : RMWTightR es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b) (hsat : Sat (x.P es)) (hev : LocsEval es)
    (hE : FwdEntailsImg es x) (hR : NoRevRMW es x) {a b : EventId} (h : x.dep es a b) :
    x.poX es a b := by
  rcases h with hp | hd
  · exact ⟨.inl hp.1, .inl hp.2.1,
      ppo_po hpo_trans (fun _ _ h => ppoStep_po_E hx hpo_trans hirr hF hT hsat hev hE hR h) hp⟩
  · exact ⟨.inl hd.1, .inl hd.2.1, hDP a b hd⟩

/-- `dep_po_E` from a consistent execution: `φ` gives the model of `P`. -/
theorem dep_po_E_of_phi {Ω : Pred} (hx : x.IsExecution es Ω) (hphi : x.phi es)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hT : RMWTightR es x)
    (hDP : ∀ a b, x.DP a b → es.poR a b) (hev : LocsEval es)
    (hE : FwdEntailsImg es x) (hR : NoRevRMW es x) {a b : EventId} (h : x.dep es a b) :
    x.poX es a b :=
  dep_po_E hx hpo_trans hirr hF hT hDP (by obtain ⟨-, -, f, hf, -⟩ := hphi; exact ⟨f, hf⟩)
    hev hE hR h

/-- **`FwdEntailsAll` implies `NoRevLoc`** (with its RMW part `NoRevRMW`):
    with every justification's alias queries answered under the generating
    predicates, no `LocLinked` pair is reversed. -/
theorem noRevLoc_of_fwdEntailsAll {Ω : Pred} (hx : x.IsExecution es Ω)
    (hpo_trans : ∀ a b c, es.poR a b → es.poR b c → es.poR a c)
    (hirr : ∀ a, ¬ es.poR a a) (hF : PoForest es) (hsat : Sat (x.P es)) (hev : LocsEval es)
    (hE : FwdEntailsAll es x) (hR : NoRevRMW es x) : NoRevLoc es x := by
  intro a b a' b' hab ra rb hl hba
  by_cases hne : a' = b'
  · subst hne; exact hirr _ hba
  -- the alias part, under a model `f` that every edge's generating predicate holds of
  have main : ∀ f, (∀ s t, x.δ.edge s t → ∃ j₀ u v, EdgeGen es x j₀ s t u v ∧ PredOf es j₀ f) →
      ∀ val, locVal es f a = some val → locVal es f b = some val → False :=
    fun f H val h₁ h₂ =>
      noRev_of_edges hx hpo_trans hirr hF hev hab ra rb hne h₁ h₂ (fun s t he _ => H s t he) hba
  have ofJ : ∀ f, x.P es f → ∀ s t, x.δ.edge s t →
      ∃ j₀ u v, EdgeGen es x j₀ s t u v ∧ PredOf es j₀ f := fun f hf s t he => by
    obtain ⟨j₀, u, v, hg, hJ, -⟩ := hE s t he
    obtain ⟨j, hj, -⟩ : ∃ j ∈ x.J, True := by
      rcases he with h | h
      · obtain ⟨j, hj, -⟩ := mem_δ_f_inv h; exact ⟨j, hj, trivial⟩
      · obtain ⟨j, hj, -⟩ := mem_δ_we_inv h; exact ⟨j, hj, trivial⟩
    exact ⟨j₀, u, v, hg, hJ j hj trivial f (PJ_of_P hf hj)⟩
  rcases hl with hm | hm | ⟨j, hj, hm⟩ | hm | hm
  · obtain ⟨f, hf⟩ := hsat
    obtain ⟨val, h₁, h₂⟩ := locVal_of_mustAlias hev hm f
    exact main f (ofJ f hf) val h₁ h₂
  · obtain ⟨f, hf, val, h₁, h₂⟩ := of_mayAlias hm
    refine main f (fun s t he => ?_) val h₁ h₂
    obtain ⟨j₀, u, v, hg, -, hpm⟩ := hE s t he
    exact ⟨j₀, u, v, hg, hpm f hf⟩
  · obtain ⟨f, hf, val, h₁, h₂⟩ := of_mayAlias hm
    refine main f (fun s t he => ?_) val h₁ h₂
    obtain ⟨j₀, u, v, hg, hJ, -⟩ := hE s t he
    exact ⟨j₀, u, v, hg, hJ j hj trivial f hf⟩
  · exact hR a b a' b' hab ra rb (.inl hm) hba
  · exact hR a b a' b' hab ra rb (.inr hm) hba

end Execution
