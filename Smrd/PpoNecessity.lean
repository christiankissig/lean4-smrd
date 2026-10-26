import Smrd.PpoStability

/-!
# The untruncated `≼` is necessary for `HB_v`-coherence to be RC11's

`coherenceV_iff_coherence` (`Smrd.CoherenceRC11`) makes `HB_v`-coherence,
over `HB_v ≜ (DP ∪ ≼ ∪ SW)⁺`, agree with RC11's coherence axiom, over
`HB ≜ (⊑ ∪ SW)⁺`, under (i) `⊑|loc ⊆ DP ∪ ≼`, (ii) `⊑;[W_rel] ⊆ DP ∪ ≼` and
`[R_acq];⊑ ⊆ DP ∪ ≼` for one direction, and `DP ∪ ≼ ⊆ ⊑` for the other. This
module shows, from RC11's verdicts alone, which of these the paper's
truncated `≼` misses and MoRDor's untruncated one supplies, and where
MoRDor's breaks the other direction.

## (N1) Conditions (i) and (ii) are necessary

One witness per shape of the conditions. For a realisable shape: a program
(computed by `denote`), an execution with `φ` that RC11 forbids (`¬ Coherence`
for every coherence order, or every one the outcome fixes), whose
`HB`-coherence over the truncated `DP ∪ ≼_trunc` holds
(`CoherenceVOver … ((ppoTrunc).union DP)`) and over MoRDor's `DP ∪ ≼` fails.

* R–R, CoRR (`corr_necessary`): `x := 0; (x := 1 ∥ r1 := x; r2 := x)`, the reads
  after the reader's last (absent) write;
* W–R, CoWR (`cowr_necessary`): `x := 0; (x := 1 ∥ x := 2; r := x)`, the read
  after the reader's last write;
* acquire, MP (`mp_necessary`): `x := 0; y := 0; (x := 1; y :rel= 1 ∥
  r1 :acq= y; r2 := x)`, the read after the acquire.

Not realisable: R–W (CoRW), W–W (CoWW), and the release edge `⊑;[W_rel]`
(MP with the release on the writer's side). Each pair ends at a write of `X`,
which is justified unless elided, so the pair lies in that justification's
window and the truncated `≼` contains it already (`trunc_of_poloc_write`,
`trunc_of_po_rel`, for executions without forwarding or elision).

## (N2) The converse needs `DP ∪ ≼ ⊆ ⊑`, which MoRDor's `≼` breaks

`coherenceV_of_coherence` asks `DP ∪ ≼ ⊆ ⊑`. `ppo_cross_thread`:
`x := 0; (x := 1 ∥ x := 2)` with `x := 1` eliding `x := 0` (Write Elision,
`Generated.we`) and no forwarding: MoRDor's `≼` remaps the pair
`(x := 0, x := 2)` of `ppo_loc` to `(x := 1, x := 2)`, across threads and
outside `⊑`. With `CO` `0 < 2 < 1` the execution is RC11-coherent and not
`HB_v`-coherent. The initialising write is an ordinary write in lean4-smrd's
semantics (a sequential prefix of the program), and elidable, so the
counterexample lives in Lean's model as in MoRDor's.
-/

namespace PpoNecessity

open EventStructure PpoKit PpoStability Execution

/-! ## Bounds for simple executions -/

def winB (es : EventStructure) (a w : EventId) : Bool := a == w || es.po.contains (a, w)

/-- The paper's truncated `≼` of a simple execution, bounded. -/
def truncL (es : EventStructure) : List (EventId × EventId) :=
  (syncL es ++ aliasL es).filter fun p =>
    p.1 != p.2 && (preJs es).any fun j => winB es p.1 j.w.id && winB es p.2 j.w.id

theorem winB_of {es : EventStructure} {a w : EventId} (h : a = w ∨ es.poR a w) :
    winB es a w = true := by
  unfold winB
  rcases h with rfl | h
  · simp
  · simp [EventStructure.poR] at h; simp [h]

theorem trunc_mem {es : EventStructure} (hr : es.rmw = []) (hg : GlobLocs es)
    {rf : List (EventId × EventId)} {a b : EventId} (h : (simple es rf).ppoTrunc es a b) :
    (a, b) ∈ truncL es := by
  obtain ⟨j, hj, hp, -, -, hwa, hwb⟩ := h
  refine List.mem_filter.2 ⟨ppo_mem hr hg (noEdge_simple es rf) hp, ?_⟩
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true]
  exact ⟨hp.2, j, hj, winB_of hwa, winB_of hwb⟩

theorem dp_none {es : EventStructure} (hd : ∀ j ∈ preJs es, j.P.syms = [] ∧ j.D = [])
    {rf : List (EventId × EventId)} {a b : EventId} : ¬ (simple es rf).DP a b := by
  rintro ⟨-, -, j, hj, -, h⟩
  obtain ⟨h1, h2⟩ := hd j hj
  rcases h with h | h
  · rw [h1] at h; cases h
  · rw [h2] at h; cases h

def relL (L : List (EventId × EventId)) : Rel := fun a b => (a, b) ∈ L

/-- `FR` over list-given `rf` and `co`. -/
def frL (rf co : List (EventId × EventId)) : List (EventId × EventId) :=
  rf.flatMap fun p => (co.filter fun q => q.1 == p.1).map fun q => (p.2, q.2)

theorem fr_mem {es : EventStructure} {rf co : List (EventId × EventId)} {a b : EventId}
    (h : (simple es rf).fr (relL co) a b) : (a, b) ∈ frL rf co := by
  obtain ⟨w, hrf, hco⟩ := h
  exact List.mem_flatMap.2 ⟨(w, a), hrf, List.mem_map.2 ⟨(w, b),
    List.mem_filter.2 ⟨hco, by simp⟩, rfl⟩⟩

/-- `HB`-coherence over the truncated `DP ∪ ≼` of a simple execution, from
    decidable bounds `H` on `HB` and `E` on `ECO`. -/
theorem coherenceV_trunc {es : EventStructure} (S : Simple es) (hg : GlobLocs es)
    (hd : ∀ j ∈ preJs es, j.P.syms = [] ∧ j.D = [])
    {rf co H E : List (EventId × EventId)}
    (hHsub : ∀ p ∈ truncL es ++ swL es, p ∈ H) (hH : Closed H)
    (hEsub : ∀ p ∈ rf ++ co ++ frL rf co, p ∈ E) (hE : Closed E)
    (hok : ∀ p ∈ H, p.1 ≠ p.2 ∧ (p.2, p.1) ∉ E) :
    CoherenceVOver es (simple es rf) (((simple es rf).ppoTrunc es).union (simple es rf).DP)
      (relL co) := by
  refine coherenceVOver_of (H := H) (E := E) ?_ ?_ hok
  · intro a b h
    refine transGen_mem (fun c d hs => hHsub _ ?_) hH h
    rcases hs with (ht | hdp) | hsw
    · exact List.mem_append.2 (.inl (trunc_mem S.normw hg ht))
    · exact absurd hdp (dp_none hd)
    · exact List.mem_append.2 (.inr (sw_mem hsw))
  · intro a b h
    refine eco_mem (fun c d h => hEsub _ ?_) (fun c d h => hEsub _ ?_) (fun c d h => hEsub _ ?_)
      hE h
    · exact List.mem_append.2 (.inl (List.mem_append.2 (.inl h)))
    · exact List.mem_append.2 (.inl (List.mem_append.2 (.inr h)))
    · exact List.mem_append.2 (.inr (fr_mem h))

theorem X_simple {es : EventStructure} (S : Simple es) {rf : List (EventId × EventId)}
    {e : Event} (he : e ∈ es.events) (hb : e.isBranch = false) (hf : e.isFence = false) :
    (simple es rf).X e.id := cand_of_mem S.nodup he hb hf

theorem ids_of_cand {es : EventStructure} {a : EventId} (h : es.Candidate a) : a ∈ es.ids := by
  obtain ⟨⟨e, he, rfl⟩, -, -⟩ := h
  exact List.mem_map_of_mem he

/-- The frozen predicate of a simple execution holds everywhere. -/
theorem P_simple {es : EventStructure} (S : Simple es) (rf : List (EventId × EventId))
    (f : Valuation) : (simple es rf).P es f := by
  intro j hj
  obtain ⟨w, hw, hj'⟩ := mem_preJs.1 hj
  obtain ⟨-, hδ, hP, -⟩ := preJust_spec hj'
  exact ⟨by rw [hP]; exact S.holds hw f, fun p hp => by rw [hδ] at hp; cases hp⟩

theorem locOf_of_sameLoc {es : EventStructure} (S : Simple es) (hg : GlobLocs es)
    {rf : List (EventId × EventId)} {a b : EventId} (h : (simple es rf).sameLoc es a b) :
    locOf es a = locOf es b := by
  obtain ⟨ea, eb, la, lb, ha, hb, hla, hlb, heq⟩ := h
  obtain ⟨x, rfl⟩ := hg ea (ev_inv ha).1 _ hla
  obtain ⟨y, rfl⟩ := hg eb (ev_inv hb).1 _ hlb
  have := heq (fun _ => .num 0) (P_simple S rf _) _ _ rfl rfl
  cases this
  simp [locOf, ha, hb, hla, hlb]

/-- A coherence order given as a list. -/
theorem coherenceOrder_simple {es : EventStructure} (S : Simple es) (hg : GlobLocs es)
    {rf co : List (EventId × EventId)}
    (hw : ∀ p ∈ co, clsB es Event.isWrite p.1 = true ∧ clsB es Event.isWrite p.2 = true)
    (hirr : ∀ p ∈ co, p.1 ≠ p.2) (htr : Closed co)
    (htot : ∀ a ∈ es.ids, ∀ b ∈ es.ids, clsB es Event.isWrite a = true →
      clsB es Event.isWrite b = true → a ≠ b → locOf es a = locOf es b →
      (a, b) ∈ co ∨ (b, a) ∈ co) :
    (simple es rf).CoherenceOrder es (relL co) where
  writes a b h := by
    obtain ⟨h1, h2⟩ := hw _ h
    exact ⟨cand_of_cls S.nodup (fun e he => wr_nb e (.inl he)) (cls_clsB.2 h1),
      cand_of_cls S.nodup (fun e he => wr_nb e (.inl he)) (cls_clsB.2 h2), cls_clsB.2 h1,
      cls_clsB.2 h2⟩
  irrefl a h := hirr _ h rfl
  trans a b c h₁ h₂ := htr _ h₁ _ h₂ rfl
  total a b ha hb hwa hwb hne hsl :=
    htot a (ids_of_cand ha) b (ids_of_cand hb) (cls_clsB.1 hwa) (cls_clsB.1 hwb) hne
      (locOf_of_sameLoc S hg hsl)

theorem sameLoc_of {es : EventStructure} {x : Execution} {a b : EventId} {ea eb : Event}
    {l : Expr} (ha : es.ev a = some ea) (hb : es.ev b = some eb) (hla : ea.loc = some l)
    (hlb : eb.loc = some l) : x.sameLoc es a b :=
  ⟨ea, eb, l, l, ha, hb, hla, hlb, fun _ _ _ _ h₁ h₂ => by rw [h₁] at h₂; cases h₂; rfl⟩

theorem poX_of {es : EventStructure} {x : Execution} {a b : EventId} (ha : x.X a) (hb : x.X b)
    (h : es.poR a b) : x.poX es a b := ⟨Or.inl ha, Or.inl hb, h⟩

/-- A pair of `ppo_sync` of a simple execution is in MoRDor's `≼`. -/
theorem ppo_of_sync {es : EventStructure} {rf : List (EventId × EventId)} {a b : EventId}
    (hs : es.ppoSyncM a b) (hne : a ≠ b) (ha : (simple es rf).X a) (hb : (simple es rf).X b) :
    (simple es rf).ppo es a b :=
  ⟨ha, hb, .single ⟨.inl ha, .inl hb, .inr (.inl ⟨(FwdCtx.remapRel_of_noEdge
    (noEdge_simple es rf)).2 hs, hne⟩)⟩⟩

/-! ## (N1) CoRR: R–R after the last write -/

def W (i t : Nat) (pc : List Nat) (o : MemOrd) (x : String) (n : Nat) : Event :=
  ⟨i, .write o (Expr.glob x) (Expr.num n) false, ⟨t, pc, []⟩, []⟩
def R (i t : Nat) (pc : List Nat) (o : MemOrd) (x : String) : Event :=
  ⟨i, .read o (Expr.glob x) i false, ⟨t, pc, []⟩, []⟩

/-- `x := 0; (x := 1 ∥ r1 := x; r2 := x)` -/
def corr : Stmt := .seq (st .rlx "x" 0)
  (.par (st .rlx "x" 1) (.seq (ld .rlx "r1" "x") (ld .rlx "r2" "x")))
def esCoRR : EventStructure :=
  ⟨[W 0 0 [0] .rlx "x" 0, W 1 0 [1, 0] .rlx "x" 1, R 2 1 [1, 1, 0] .rlx "x",
    R 3 1 [1, 1, 1] .rlx "x"], [(0, 1), (0, 2), (0, 3), (2, 3)], []⟩

unseal interp in
theorem denote_corr : denote (fun _ => 0) corr = esCoRR := rfl

theorem SCoRR : Simple esCoRR := ⟨by decide, by decide, rfl⟩
theorem gCoRR : GlobLocs esCoRR := globLocs_of (by decide)

/-- The first read reads `x := 1`, the second the initial `x := 0`. -/
def rfCoRR : List (EventId × EventId) := [(1, 2), (0, 3)]
def coCoRR : List (EventId × EventId) := [(0, 1)]
def xCoRR : Execution := simple esCoRR rfCoRR

theorem corr_exec : xCoRR.IsExecution esCoRR (fun _ => True) ∧ xCoRR.phi esCoRR :=
  ⟨isExecution_simple SCoRR (by decide),
   phi_simple SCoRR (by decide) (by decide) (by decide)
     (fun α => if α = 2 then .num 1 else .num 0) (by decide)⟩

/-- RC11 forbids it under every coherence order. -/
theorem corr_rc11 {co : Rel} (hco : xCoRR.CoherenceOrder esCoRR co) :
    ¬ xCoRR.Coherence esCoRR co := by
  intro hcoh
  have X : ∀ e ∈ esCoRR.events, xCoRR.X e.id :=
    fun e he => X_simple SCoRR he (by revert e; decide) (by revert e; decide)
  have X0 := X (W 0 0 [0] .rlx "x" 0) (by simp [esCoRR])
  have X1 := X (W 1 0 [1, 0] .rlx "x" 1) (by simp [esCoRR])
  have X2 := X (R 2 1 [1, 1, 0] .rlx "x") (by simp [esCoRR])
  have X3 := X (R 3 1 [1, 1, 1] .rlx "x") (by simp [esCoRR])
  rcases hco.total 0 1 X0 X1 ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩ (by decide)
    (sameLoc_of rfl rfl rfl rfl) with h | h
  · exact hcoh 2 ⟨3, .single (.inl (poX_of X2 X3 (show (2, 3) ∈ esCoRR.po by decide))),
      .inr (.tail (.single (.inr ⟨0, show (0, 3) ∈ rfCoRR by decide, h⟩))
        (.inl (.inl (show (1, 2) ∈ rfCoRR by decide))))⟩
  · exact hcoh 0 ⟨1, .single (.inl (poX_of X0 X1 (show (0, 1) ∈ esCoRR.po by decide))),
      .inr (.single (.inl (.inr h)))⟩

/-- **CoRR (R–R)**: RC11 forbids the execution; `HB` over the truncated
    `DP ∪ ≼` accepts it; `HB_v` over MoRDor's `DP ∪ ≼` rejects it. -/
theorem corr_necessary :
    xCoRR.IsExecution esCoRR (fun _ => True) ∧ xCoRR.phi esCoRR ∧
    xCoRR.CoherenceOrder esCoRR (relL coCoRR) ∧
    (∀ co, xCoRR.CoherenceOrder esCoRR co → ¬ xCoRR.Coherence esCoRR co) ∧
    CoherenceVOver esCoRR xCoRR ((xCoRR.ppoTrunc esCoRR).union xCoRR.DP) (relL coCoRR) ∧
    ¬ xCoRR.CoherenceV esCoRR (relL coCoRR) := by
  refine ⟨corr_exec.1, corr_exec.2, coherenceOrder_simple SCoRR gCoRR (by decide) (by decide)
    (by decide) (by decide), fun _ h => corr_rc11 h, ?_, ?_⟩
  · exact coherenceV_trunc SCoRR gCoRR (by decide) (H := [(0, 1)])
      (E := [(1, 2), (0, 3), (0, 1), (3, 1), (0, 2), (3, 2)])
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro h
    have X2 : xCoRR.X 2 := X_simple SCoRR (e := R 2 1 [1, 1, 0] .rlx "x") (by simp [esCoRR]) rfl rfl
    have X3 : xCoRR.X 3 := X_simple SCoRR (e := R 3 1 [1, 1, 1] .rlx "x") (by simp [esCoRR]) rfl rfl
    have hel := not_elided_simple esCoRR rfCoRR
    obtain ⟨f, hf⟩ := sat_Pm corr_exec.1 SCoRR hel
    have hp : xCoRR.ppo esCoRR 2 3 := ppo_of_alias hel hf (y := "x") rfl rfl rfl rfl
      (show (2, 3) ∈ esCoRR.po by decide) (by decide) X2 X3
    exact h 2 ⟨3, .single (.inl (.inl hp)), .inr (.tail (.single (.inr
      ⟨0, show (0, 3) ∈ rfCoRR by decide, show (0, 1) ∈ coCoRR by decide⟩))
      (.inl (.inl (show (1, 2) ∈ rfCoRR by decide))))⟩

/-! ## (N1) CoWR: W–R after the last write -/

/-- `x := 0; (x := 1 ∥ x := 2; r := x)` -/
def cowr : Stmt := .seq (st .rlx "x" 0)
  (.par (st .rlx "x" 1) (.seq (st .rlx "x" 2) (ld .rlx "r" "x")))
def esCoWR : EventStructure :=
  ⟨[W 0 0 [0] .rlx "x" 0, W 1 0 [1, 0] .rlx "x" 1, W 2 1 [1, 1, 0] .rlx "x" 2,
    R 3 1 [1, 1, 1] .rlx "x"], [(0, 1), (0, 2), (0, 3), (2, 3)], []⟩

unseal interp in
theorem denote_cowr : denote (fun _ => 0) cowr = esCoWR := rfl

theorem SCoWR : Simple esCoWR := ⟨by decide, by decide, rfl⟩
theorem gCoWR : GlobLocs esCoWR := globLocs_of (by decide)

/-- The read reads `x := 1`, coherence-before the reader's own `x := 2`. -/
def rfCoWR : List (EventId × EventId) := [(1, 3)]
def coCoWR : List (EventId × EventId) := [(0, 1), (0, 2), (1, 2)]
def xCoWR : Execution := simple esCoWR rfCoWR

theorem cowr_exec : xCoWR.IsExecution esCoWR (fun _ => True) ∧ xCoWR.phi esCoWR :=
  ⟨isExecution_simple SCoWR (by decide),
   phi_simple SCoWR (by decide) (by decide) (by decide) (fun _ => .num 1) (by decide)⟩

/-- RC11 forbids it under every coherence order with `x := 2` last, as the
    outcome (`x = 2` finally) fixes. -/
theorem cowr_rc11 {co : Rel} (h12 : co 1 2) : ¬ xCoWR.Coherence esCoWR co := by
  intro hcoh
  have X2 : xCoWR.X 2 := X_simple SCoWR (e := W 2 1 [1, 1, 0] .rlx "x" 2) (by simp [esCoWR]) rfl rfl
  have X3 : xCoWR.X 3 := X_simple SCoWR (e := R 3 1 [1, 1, 1] .rlx "x") (by simp [esCoWR]) rfl rfl
  exact hcoh 2 ⟨3, .single (.inl (poX_of X2 X3 (show (2, 3) ∈ esCoWR.po by decide))),
    .inr (.single (.inr ⟨1, show (1, 3) ∈ rfCoWR by decide, h12⟩))⟩

/-- **CoWR (W–R)**. -/
theorem cowr_necessary :
    xCoWR.IsExecution esCoWR (fun _ => True) ∧ xCoWR.phi esCoWR ∧
    xCoWR.CoherenceOrder esCoWR (relL coCoWR) ∧
    (∀ co, co 1 2 → ¬ xCoWR.Coherence esCoWR co) ∧
    CoherenceVOver esCoWR xCoWR ((xCoWR.ppoTrunc esCoWR).union xCoWR.DP) (relL coCoWR) ∧
    ¬ xCoWR.CoherenceV esCoWR (relL coCoWR) := by
  refine ⟨cowr_exec.1, cowr_exec.2, coherenceOrder_simple SCoWR gCoWR (by decide) (by decide)
    (by decide) (by decide), fun _ h => cowr_rc11 h, ?_, ?_⟩
  · exact coherenceV_trunc SCoWR gCoWR (by decide) (H := [(0, 1), (0, 2)])
      (E := [(1, 3), (0, 1), (0, 2), (1, 2), (3, 2), (0, 3)])
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro h
    have X2 : xCoWR.X 2 := X_simple SCoWR (e := W 2 1 [1, 1, 0] .rlx "x" 2) (by simp [esCoWR]) rfl rfl
    have X3 : xCoWR.X 3 := X_simple SCoWR (e := R 3 1 [1, 1, 1] .rlx "x") (by simp [esCoWR]) rfl rfl
    have hel := not_elided_simple esCoWR rfCoWR
    obtain ⟨f, hf⟩ := sat_Pm cowr_exec.1 SCoWR hel
    have hp : xCoWR.ppo esCoWR 2 3 := ppo_of_alias hel hf (y := "x") rfl rfl rfl rfl
      (show (2, 3) ∈ esCoWR.po by decide) (by decide) X2 X3
    exact h 2 ⟨3, .single (.inl (.inl hp)), .inr (.single (.inr
      ⟨1, show (1, 3) ∈ rfCoWR by decide, show (1, 2) ∈ coCoWR by decide⟩))⟩

/-! ## (N1) MP: the acquire edge -/

/-- `x := 0; y := 0; (x := 1; y :rel= 1 ∥ r1 :acq= y; r2 := x)` -/
def mp : Stmt := .seq (st .rlx "x" 0) (.seq (st .rlx "y" 0)
  (.par (.seq (st .rlx "x" 1) (st .rel "y" 1)) (.seq (ld .acq "r1" "y") (ld .rlx "r2" "x"))))
def esMP : EventStructure :=
  ⟨[W 0 0 [0] .rlx "x" 0, W 1 0 [1, 0] .rlx "y" 0, W 2 0 [1, 1, 0, 0] .rlx "x" 1,
    W 3 0 [1, 1, 0, 1] .rel "y" 1, R 4 1 [1, 1, 1, 0] .acq "y", R 5 1 [1, 1, 1, 1] .rlx "x"],
   [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (4, 5)], []⟩

unseal interp in
theorem denote_mp : denote (fun _ => 0) mp = esMP := rfl

theorem SMP : Simple esMP := ⟨by decide, by decide, rfl⟩
theorem gMP : GlobLocs esMP := globLocs_of (by decide)

/-- The acquire reads the release `y := 1`, the read of `x` the initial `0`. -/
def rfMP : List (EventId × EventId) := [(3, 4), (0, 5)]
def coMP : List (EventId × EventId) := [(0, 2), (1, 3)]
def xMP : Execution := simple esMP rfMP

theorem mp_exec : xMP.IsExecution esMP (fun _ => True) ∧ xMP.phi esMP :=
  ⟨isExecution_simple SMP (by decide),
   phi_simple SMP (by decide) (by decide) (by decide)
     (fun α => if α = 4 then .num 1 else .num 0) (by decide)⟩

theorem sw34 : xMP.sw esMP 3 4 :=
  ⟨.inl ⟨_, rfl, rfl⟩, 3, 3, 4, .inl rfl,
    ⟨⟨_, rfl, rfl⟩, 3, .inl rfl, ⟨_, rfl, rfl⟩, .inl rfl⟩,
    show (3, 4) ∈ rfMP by decide, ⟨_, rfl, rfl⟩, .inl rfl, .inl ⟨_, rfl, rfl⟩⟩

/-- RC11 forbids it under every coherence order. -/
theorem mp_rc11 {co : Rel} (hco : xMP.CoherenceOrder esMP co) : ¬ xMP.Coherence esMP co := by
  intro hcoh
  have X : ∀ e ∈ esMP.events, xMP.X e.id :=
    fun e he => X_simple SMP he (by revert e; decide) (by revert e; decide)
  have X0 := X (W 0 0 [0] .rlx "x" 0) (by simp [esMP])
  have X2 := X (W 2 0 [1, 1, 0, 0] .rlx "x" 1) (by simp [esMP])
  have X3 := X (W 3 0 [1, 1, 0, 1] .rel "y" 1) (by simp [esMP])
  have X4 := X (R 4 1 [1, 1, 1, 0] .acq "y") (by simp [esMP])
  have X5 := X (R 5 1 [1, 1, 1, 1] .rlx "x") (by simp [esMP])
  rcases hco.total 0 2 X0 X2 ⟨_, rfl, rfl⟩ ⟨_, rfl, rfl⟩ (by decide)
    (sameLoc_of rfl rfl rfl rfl) with h | h
  · have hb : xMP.hb esMP 2 5 :=
      .tail (.tail (.single (.inl (poX_of X2 X3 (show (2, 3) ∈ esMP.po by decide)))) (.inr sw34))
        (.inl (poX_of X4 X5 (show (4, 5) ∈ esMP.po by decide)))
    exact hcoh 2 ⟨5, hb, .inr (.single (.inr ⟨0, show (0, 5) ∈ rfMP by decide, h⟩))⟩
  · exact hcoh 0 ⟨2, .single (.inl (poX_of X0 X2 (show (0, 2) ∈ esMP.po by decide))),
      .inr (.single (.inl (.inr h)))⟩

/-- **MP (the acquire edge `[R_acq];⊑`)**. -/
theorem mp_necessary :
    xMP.IsExecution esMP (fun _ => True) ∧ xMP.phi esMP ∧
    xMP.CoherenceOrder esMP (relL coMP) ∧
    (∀ co, xMP.CoherenceOrder esMP co → ¬ xMP.Coherence esMP co) ∧
    CoherenceVOver esMP xMP ((xMP.ppoTrunc esMP).union xMP.DP) (relL coMP) ∧
    ¬ xMP.CoherenceV esMP (relL coMP) := by
  refine ⟨mp_exec.1, mp_exec.2, coherenceOrder_simple SMP gMP (by decide) (by decide)
    (by decide) (by decide), fun _ h => mp_rc11 h, ?_, ?_⟩
  · exact coherenceV_trunc SMP gMP (by decide)
      (H := [(0, 2), (0, 3), (1, 3), (2, 3), (3, 4), (0, 4), (1, 4), (2, 4)])
      (E := [(3, 4), (0, 5), (0, 2), (1, 3), (5, 2), (1, 4)])
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro h
    have X : ∀ e ∈ esMP.events, xMP.X e.id :=
      fun e he => X_simple SMP he (by revert e; decide) (by revert e; decide)
    have X2 := X (W 2 0 [1, 1, 0, 0] .rlx "x" 1) (by simp [esMP])
    have X3 := X (W 3 0 [1, 1, 0, 1] .rel "y" 1) (by simp [esMP])
    have X4 := X (R 4 1 [1, 1, 1, 0] .acq "y") (by simp [esMP])
    have X5 := X (R 5 1 [1, 1, 1, 1] .rlx "x") (by simp [esMP])
    have p23 : xMP.ppo esMP 2 3 :=
      ppo_of_sync ⟨show (2, 3) ∈ esMP.po by decide, .inr ⟨_, rfl, rfl⟩⟩ (by decide) X2 X3
    have p45 : xMP.ppo esMP 4 5 :=
      ppo_of_sync ⟨show (4, 5) ∈ esMP.po by decide, .inl ⟨_, rfl, rfl⟩⟩ (by decide) X4 X5
    exact h 2 ⟨5, .tail (.tail (.single (.inl (.inl p23))) (.inr sw34)) (.inl (.inl p45)),
      .inr (.single (.inr ⟨0, show (0, 5) ∈ rfMP by decide, show (0, 2) ∈ coMP by decide⟩))⟩

/-! ## (N1) Shapes the truncation already covers -/

/-- **R–W and W–W (CoRW, CoWW)**: a `⊑|loc` pair ending at a write of `X` is in
    the truncated `≼`, for executions without forwarding or elision with a
    location model: the write is justified and the pair lies in its window. -/
theorem trunc_of_poloc_write {es : EventStructure} {x : Execution} {Ω : Pred}
    (hx : x.IsExecution es Ω) (hδ : ∀ a b, ¬ x.δ.edge a b) (hirr : ∀ a, ¬ es.poR a a)
    (hm : LocModel es x) {a w : EventId} (hXa : x.X a) (hXw : x.X w)
    (hw : es.cls Event.isWrite w) (h : x.poloc es a w) : x.ppoTrunc es a w := by
  obtain ⟨⟨-, -, hpo⟩, ea, ew, la, lw, hea, hew, hla, hlw, heq⟩ := h
  have hE : es.cls Event.isEffect w := by
    obtain ⟨e, he, h⟩ := hw; exact ⟨e, he, by simp [Event.isEffect, h]⟩
  have hnel : ∀ c, ¬ x.elided c := fun c hc => by
    obtain ⟨b, hb⟩ := (x.elided_iff c).1 hc; exact hδ _ _ hb
  obtain ⟨j, hj, hjw, -⟩ := hx.justified w hXw hE (hnel w)
  obtain ⟨f, hPm, hdef⟩ := hm
  obtain ⟨va, hva⟩ := Option.isSome_iff_exists.1 (hdef a ea la hXa hea hla)
  obtain ⟨vw, hvw⟩ := Option.isSome_iff_exists.1 (hdef w ew lw hXw hew hlw)
  have hv : va = vw := heq f (P_of_Pm hPm) va vw hva hvw
  subst hv
  refine ⟨j, hj, ⟨(FwdCtx.remapRel_of_noEdge hδ).2 (.inr ⟨hpo, ea, ew, la, lw, hea, hew, hla, hlw,
    f, hPm.1 j hj, by simp [Expr.holds, Expr.eval, hva, hvw]⟩), fun h => hirr a (h ▸ hpo)⟩,
    hXa, hXw, .inr (hjw ▸ hpo), .inl hjw.symm⟩

/-- **The release edge `⊑;[W_rel]`** is in the truncated `≼`, for executions
    without forwarding or elision: the releasing write is justified. -/
theorem trunc_of_po_rel {es : EventStructure} {x : Execution} {Ω : Pred}
    (hx : x.IsExecution es Ω) (hδ : ∀ a b, ¬ x.δ.edge a b) (hirr : ∀ a, ¬ es.poR a a)
    {a w : EventId} (hXa : x.X a) (hXw : x.X w) (hw : es.cls Event.isRelW w)
    (hpo : es.poR a w) : x.ppoTrunc es a w := by
  have hE : es.cls Event.isEffect w := by
    obtain ⟨e, he, h⟩ := hw
    refine ⟨e, he, ?_⟩
    obtain ⟨id, k, l, g⟩ := e
    cases k <;> simp_all [Event.isRelW, Event.isEffect, Event.isWrite]
  have hnel : ∀ c, ¬ x.elided c := fun c hc => by
    obtain ⟨b, hb⟩ := (x.elided_iff c).1 hc; exact hδ _ _ hb
  obtain ⟨j, hj, hjw, -⟩ := hx.justified w hXw hE (hnel w)
  have nfb : ∀ c, x.X c → ¬ (es.cls Event.isFence c ∨ es.cls Event.isBranch c) := by
    rintro c hc (h | h)
    · exact (hx.maximal.1 c hc).2.2 h
    · exact (hx.maximal.1 c hc).2.1 h
  refine ⟨j, hj, ⟨(FwdCtx.remapRel_of_noEdge hδ).2
    (.inl (.inl ⟨.inl (.inl ⟨w, hpo, rfl, hw⟩), nfb a hXa, nfb w hXw⟩)), fun h => hirr a (h ▸ hpo)⟩,
    hXa, hXw, .inr (hjw ▸ hpo), .inl hjw.symm⟩

/-! ## (N2) A cross-thread pair from write elision -/

/-- `x := 0; (x := 1 ∥ x := 2)` -/
def ww : Stmt := .seq (st .rlx "x" 0) (.par (st .rlx "x" 1) (st .rlx "x" 2))
def esWW : EventStructure :=
  ⟨[W 0 0 [0] .rlx "x" 0, W 1 0 [1, 0] .rlx "x" 1, W 2 1 [1, 1] .rlx "x" 2], [(0, 1), (0, 2)], []⟩

unseal interp in
theorem denote_ww : denote (fun _ => 0) ww = esWW := rfl

theorem SWW : Simple esWW := ⟨by decide, by decide, rfl⟩
theorem gWW : GlobLocs esWW := globLocs_of (by decide)

def pj (w : Event) : Justification := ⟨w.valres, [], .empty, w⟩
/-- `x := 1`'s pre-justification with `x := 0` elided: `WE = {(1, 0)}`. -/
def jWE : Justification :=
  { pj (W 1 0 [1, 0] .rlx "x" 1) with δ := { (pj (W 1 0 [1, 0] .rlx "x" 1)).δ with we := [(1, 0)] } }
def JWW : List Justification := [jWE, pj (W 2 1 [1, 1] .rlx "x" 2)]
def xWW : Execution := ⟨esWW.Candidate, JWW, fun _ _ => False⟩
def coWW : List (EventId × EventId) := [(0, 2), (2, 1), (0, 1)]

theorem δWW : xWW.δ = ⟨[], [(1, 0)]⟩ := rfl

theorem edge_WW {a b : EventId} (h : xWW.δ.edge a b) : a = 1 ∧ b = 0 := by
  rw [δWW] at h
  rcases h with h | h
  · cases h
  · simp at h; exact h

theorem pre_WW (w : Event) (hw : w ∈ esWW.events) (hk : preJust w = some (pj w)) :
    esWW.Generated (fun _ => True) (pj w) :=
  .pre hw hk ⟨fun _ => .num 0, SWW.holds hw _⟩

/-- `x := 0` is the immediate `≼`-predecessor of `x := 1`, at its location:
    the Write Elision of the paper applies. -/
theorem gen_jWE : esWW.Generated (fun _ => True) jWE := by
  have hpre := pre_WW (W 1 0 [1, 0] .rlx "x" 1) (by simp [esWW]) rfl
  have hδ0 : ∀ a b, ¬ (pj (W 1 0 [1, 0] .rlx "x" 1)).δ.edge a b := by
    intro a b h; rcases h with h | h <;> cases h
  have hppo : ∀ a b, esWW.ppo (pj (W 1 0 [1, 0] .rlx "x" 1)).P.holds
      (pj (W 1 0 [1, 0] .rlx "x" 1)).δ a b → (a, b) ∈ syncL esWW ++ aliasL esWW :=
    fun a b h => ppo_mem rfl gWW hδ0 h
  refine .we (e₁ := 0) (e₂ := 1) hpre ⟨⟨⟨⟨(FwdCtx.remapRel_of_noEdge hδ0).2 (.inr
      ⟨show (0, 1) ∈ esWW.po by decide, _, _, _, _, rfl, rfl, rfl, rfl, fun _ => .num 0,
        SWW.holds (e := W 1 0 [1, 0] .rlx "x" 1) (by simp [esWW]) _,
        by simp [Expr.holds, Expr.eval, Expr.glob]⟩), by decide⟩, ?_⟩,
      _, _, _, _, rfl, rfl, rfl, rfl, fun _ _ _ _ h₁ h₂ => by rw [h₁] at h₂; cases h₂; rfl⟩,
    ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, fun ⟨e, he, hp⟩ => by cases he; simp [W, Event.isVol] at hp⟩ ?_ ?_
  · rintro ⟨e'', h₁, h₂⟩
    have m₁ := hppo _ _ h₁
    have m₂ := hppo _ _ h₂
    have key : ∀ p ∈ syncL esWW ++ aliasL esWW, ∀ q ∈ syncL esWW ++ aliasL esWW,
        p.1 = 0 → q.2 = 1 → p.2 = q.1 → False := by decide
    exact key _ m₁ _ m₂ rfl rfl rfl
  · refine ⟨fun a ha => ?_, fun a b e ha hb => ?_⟩
    · have : ∀ c d, Relation.TransGen
          ({ (pj (W 1 0 [1, 0] .rlx "x" 1)).δ with we := (pj (W 1 0 [1, 0] .rlx "x" 1)).δ.we ++ [(1, 0)] }).edge c d →
          c = 1 ∧ d = 0 := by
        intro c d h
        induction h with
        | single h => rcases h with h | h <;> simp [pj, FwdCtx.empty] at h; exact h
        | tail _ h ih =>
            rcases h with h | h <;> simp [pj, FwdCtx.empty] at h
            obtain ⟨-, rfl⟩ := ih; cases h.1
      have := this a a ha
      rw [this.1] at this; cases this.2
    · rcases ha with h | h <;> simp [pj, FwdCtx.empty] at h
      rcases hb with h' | h' <;> simp [pj, FwdCtx.empty] at h'
      rw [h.1, h'.1]
  · exact ⟨fun _ => .num 0, SWW.holds (e := W 1 0 [1, 0] .rlx "x" 1) (by simp [esWW]) _, trivial⟩

theorem X_WW {a : EventId} : xWW.X a ↔ a = 0 ∨ a = 1 ∨ a = 2 := by
  constructor
  · intro h
    have := ids_of_cand h
    simp [EventStructure.ids, esWW, W] at this
    omega
  · rintro (rfl | rfl | rfl)
    · exact cand_of_mem SWW.nodup (e := W 0 0 [0] .rlx "x" 0) (by simp [esWW]) rfl rfl
    · exact cand_of_mem SWW.nodup (e := W 1 0 [1, 0] .rlx "x" 1) (by simp [esWW]) rfl rfl
    · exact cand_of_mem SWW.nodup (e := W 2 1 [1, 1] .rlx "x" 2) (by simp [esWW]) rfl rfl

theorem elided_WW {a : EventId} : xWW.elided a ↔ a = 0 := by
  constructor
  · intro h; obtain ⟨b, hb⟩ := (xWW.elided_iff a).1 h; exact (edge_WW hb).2
  · rintro rfl; exact ⟨(1, 0), .inr (by rw [δWW]; simp), rfl⟩

theorem isExecution_WW : xWW.IsExecution esWW (fun _ => True) where
  maximal := ⟨fun _ h => h, fun a b _ _ ⟨ea, eb, ha, hb, hn⟩ =>
      hn ⟨fun _ => .num 0, SWW.holds (ev_inv ha).1 _, SWW.holds (ev_inv hb).1 _⟩,
    fun _ hc hn => absurd hc hn⟩
  generated j hj := by
    simp only [xWW, JWW, List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl
    · exact gen_jWE
    · exact pre_WW _ (by simp [esWW]) rfl
  inX j hj := by
    simp only [xWW, JWW, List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl
    · exact X_WW.2 (.inr (.inl rfl))
    · exact X_WW.2 (.inr (.inr rfl))
  consistent := ⟨fun _ => .num 0, fun j hj => by
      simp only [xWW, JWW, List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl <;> simp [jWE, pj, W, Event.valres, Expr.conj, Expr.holds,
        Expr.eval, Expr.tt],
    fun a e _ he => SWW.holds (ev_inv he).1 _⟩
  fwdWF := by
    rw [δWW]
    refine ⟨fun a ha => ?_, fun a b e ha hb => ?_⟩
    · have : ∀ c d, Relation.TransGen (FwdCtx.edge ⟨[], [(1, 0)]⟩) c d → c = 1 ∧ d = 0 := by
        intro c d h
        induction h with
        | single h => rcases h with h | h <;> simp at h; exact h
        | tail _ h ih =>
            rcases h with h | h <;> simp at h
            obtain ⟨-, rfl⟩ := ih; cases h.1
      have := this a a ha
      rw [this.1] at this; cases this.2
    · rcases ha with h | h <;> simp at h
      rcases hb with h' | h' <;> simp at h'
      rw [h.1, h'.1]
  rf_wr _ _ h := h.elim
  rf_func _ _ _ h := h.elim
  justified w hw he hn := by
    rcases X_WW.1 hw with rfl | rfl | rfl
    · exact absurd (elided_WW.2 rfl) hn
    · refine ⟨jWE, by simp [xWW, JWW], rfl, fun j' hj' h' => ?_⟩
      simp only [xWW, JWW, List.mem_cons, List.mem_nil_iff, or_false] at hj'
      rcases hj' with rfl | rfl
      · rfl
      · cases h'
    · refine ⟨pj (W 2 1 [1, 1] .rlx "x" 2), by simp [xWW, JWW], rfl, fun j' hj' h' => ?_⟩
      simp only [xWW, JWW, List.mem_cons, List.mem_nil_iff, or_false] at hj'
      rcases hj' with rfl | rfl
      · cases h'
      · rfl

theorem no_dp_WW {a b : EventId} : ¬ xWW.DP a b := by
  rintro ⟨-, -, j, hj, -, h⟩
  simp only [xWW, JWW, List.mem_cons, List.mem_nil_iff, or_false] at hj
  rcases hj with rfl | rfl <;>
    simp [jWE, pj, W, Event.valres, Expr.conj, Expr.syms, Expr.tt] at h

theorem phi_WW : xWW.phi esWW := by
  refine ⟨fun e h _ => ?_, fun r => ⟨fun ⟨_, h⟩ => h.elim, ?_⟩, fun _ => .num 0, ?_, ?_, ?_, ?_⟩
  · rcases h with ⟨_, h⟩ | ⟨_, h⟩
    · exact h.elim
    · exact no_dp_WW h
  · rintro ⟨hX, e, he, hp⟩
    rcases X_WW.1 hX with rfl | rfl | rfl <;> cases he <;> simp [W, Event.isRead] at hp
  · intro j hj
    simp only [xWW, JWW, List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl
    · exact ⟨by simp [jWE, pj, W, Event.valres, Expr.conj, Expr.holds, Expr.eval, Expr.tt],
        fun p hp => by simp [jWE, pj, FwdCtx.empty] at hp⟩
    · exact ⟨by simp [pj, W, Event.valres, Expr.conj, Expr.holds, Expr.eval, Expr.tt],
        fun p hp => by simp [pj, FwdCtx.empty] at hp⟩
  · intro _ _ _ _ h; exact h.elim
  · intro a e α sz _ he hk
    obtain ⟨hm, -⟩ := ev_inv he
    simp only [esWW, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> cases hk
  · intro a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂ _ _ _ he₁ _ hk₁
    obtain ⟨hm, -⟩ := ev_inv he₁
    simp only [esWW, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> cases hk₁

/-- MoRDor's `≼` orders `x := 1` before `x := 2`: `(x := 0, x := 2)` of
    `ppo_loc`, with `x := 0` remapped onto `x := 1`. -/
theorem ppo_WW : xWW.ppo esWW 1 2 := by
  have X1 : xWW.X 1 := X_WW.2 (.inr (.inl rfl))
  have X2 : xWW.X 2 := X_WW.2 (.inr (.inr rfl))
  have hPm : xWW.Pm esWW (fun _ => .num 0) := by
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · intro p hp; rw [δWW] at hp; cases hp
    · intro a e _ he; exact SWW.holds (ev_inv he).1 _
    intro j hj
    simp only [xWW, JWW, List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl <;> simp [jWE, pj, W, Event.valres, Expr.conj, Expr.holds,
      Expr.eval, Expr.tt]
  have hal : esWW.mayAlias (xWW.Pm esWW) 1 2 :=
    ⟨_, _, _, _, rfl, rfl, rfl, rfl, _, hPm, by simp [Expr.holds, Expr.eval, Expr.glob]⟩
  have r01 : xWW.δ.Remap 0 1 :=
    .step (a := 1) (.inr (by rw [δWW]; simp))
      (.canon fun c h => by have := edge_WW h; cases this.2)
  have r22 : xWW.δ.Remap 2 2 := .canon fun c h => by have := edge_WW h; cases this.2
  exact ⟨X1, X2, .single ⟨.inl X1, .inl X2, .inr (.inr ⟨⟨⟨0, 2, .inr ⟨show (0, 2) ∈ esWW.po by
    decide, .inr ⟨_, _, _, _, rfl, rfl, rfl, rfl, _, hPm, by
      simp [Expr.holds, Expr.eval, Expr.glob]⟩⟩, r01, r22⟩, by decide⟩, hal⟩)⟩⟩

/-- **(N2) `DP ∪ ≼ ⊄ ⊑` with write elision and without forwarding, and the
    converse of `coherenceV_iff_coherence` fails**: the execution of
    `x := 0; (x := 1 ∥ x := 2)` in which `x := 1` elides `x := 0` is an
    execution with `φ`; MoRDor's `≼` orders `x := 1` before `x := 2` across
    threads, outside `⊑`; under `CO = 0 < 2 < 1` it is RC11-coherent (and
    atomic) but not `HB_v`-coherent. -/
theorem ppo_cross_thread :
    xWW.IsExecution esWW (fun _ => True) ∧ xWW.phi esWW ∧ (∀ p ∈ xWW.δ.f, False) ∧
    xWW.ppo esWW 1 2 ∧ ¬ esWW.poR 1 2 ∧ ¬ (∀ a b, xWW.dep esWW a b → xWW.poX esWW a b) ∧
    xWW.CoherenceOrder esWW (relL coWW) ∧ xWW.Coherence esWW (relL coWW) ∧
    xWW.Atomicity esWW (relL coWW) ∧ ¬ xWW.CoherenceV esWW (relL coWW) := by
  have hnr : ¬ esWW.poR 1 2 := by unfold EventStructure.poR; decide
  have hf : ∀ p ∈ xWW.δ.f, False := by intro p hp; rw [δWW] at hp; cases hp
  refine ⟨isExecution_WW, phi_WW, hf, ppo_WW, hnr,
    fun h => hnr (h 1 2 (.inl ppo_WW)).2.2, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun a b h => ?_, fun a h => ?_, fun a b c h₁ h₂ => ?_, fun a b ha hb _ _ hne _ => ?_⟩
    · have hw : ∀ p ∈ coWW, clsB esWW Event.isWrite p.1 = true ∧
          clsB esWW Event.isWrite p.2 = true ∧ (p.1 = 0 ∨ p.1 = 1 ∨ p.1 = 2) ∧
          (p.2 = 0 ∨ p.2 = 1 ∨ p.2 = 2) := by decide
      obtain ⟨h1, h2, h3, h4⟩ := hw _ h
      exact ⟨X_WW.2 h3, X_WW.2 h4, cls_clsB.2 h1, cls_clsB.2 h2⟩
    · have : ∀ p ∈ coWW, p.1 ≠ p.2 := by decide
      exact this _ h rfl
    · have : Closed coWW := by decide
      exact this _ h₁ _ h₂ rfl
    · have key : ∀ a ∈ [0, 1, 2], ∀ b ∈ [0, 1, 2], a ≠ b → (a, b) ∈ coWW ∨ (b, a) ∈ coWW := by
        decide
      have m : ∀ c, xWW.X c → c ∈ [0, 1, 2] := fun c hc => by
        rcases X_WW.1 hc with rfl | rfl | rfl <;> simp
      exact key a (m a ha) b (m b hb) hne
  · -- RC11's `HB` is `⊑` here, which `CO` does not reverse
    refine coherenceVOver_of (D := xWW.poX esWW) (H := [(0, 1), (0, 2)]) (E := coWW) ?_ ?_
      (by decide)
    · intro a b h
      refine transGen_mem (fun c d hs => ?_) (by decide) h
      rcases hs with ⟨-, -, hpo⟩ | hsw
      · exact hpo
      · have := sw_mem hsw
        have : swL esWW = [] := by decide
        simp_all
    · intro a b h
      refine eco_mem (x := xWW) (L := coWW) (fun _ _ h => False.elim h) (fun _ _ h => h)
        (fun _ _ h => by obtain ⟨_, h, _⟩ := h; exact False.elim h) (by decide) h
  · intro r w h; obtain ⟨-, -, ent, hm, -⟩ := h; cases hm
  · intro h
    exact h 1 ⟨2, .single (.inl (.inl ppo_WW)),
      .inr (.single (.inl (.inr (show (2, 1) ∈ coWW by decide))))⟩

end PpoNecessity
