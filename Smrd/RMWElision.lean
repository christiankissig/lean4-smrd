import Smrd.WEAcrossRelease

/-!
# Eliding an RMW access: the lost update

`x := 0; (a := FADD(x, 1); x := 5 ∥ b := FADD(x, 1))`, all accesses relaxed.
RC11 forbids `a = 0 ∧ b = 0`: both FADDs follow `x := 0` in coherence, and
whichever writes first falls between the other's read and write, which
Atomicity forbids (a lost update).

* `rc11_forbids`: every execution with both reads reading `x := 0` breaks
  RC11's `Coherent`, under every coherence order.
* `blind_admitted`: Write Elision without the RMW clause (`weRelBlind` and
  `weNoRel`, both hold) elides the first FADD's write into `x := 5`, and the
  execution satisfies every condition of an execution, `φ`, No-Thin-Air and
  `CoherentT` with `a = 0 ∧ b = 0`. The elided write leaves `X ∖ †`, so no
  coherence order orders it, and Atomicity says nothing about the first FADD.
* `not_generated`, `blind_not_execution`: under the rule that no RMW access is
  elided (`EventStructure.RMWAcc`, MoRDor `docs/DEPARTURES.md` E4) the
  elision is not generated, and the execution above is no execution.
* `forbidden_T`: no execution admits the outcome under `CoherentT`, forwarding
  allowed: no RMW access is elided (`Execution.rmw_not_elided`), so the
  argument of `rc11_forbids` runs over `X ∖ †`.

MoRDor's witness is `litmus-tests/imm/FADD RMW Atomicity.lit`. The `CAS`
variant is not mechanised: its event structure adds branches and guards, and
the rule (`Generated.not_rmwAcc_elided`) excludes it alike.
-/

namespace RMWElision

open EventStructure PpoKit PpoNecessity Execution WEAcrossRelease

/-- `x := 0; (a := FADD(x, 1); x := 5 ∥ b := FADD(x, 1))` -/
def prog : Stmt :=
  .seq (PpoStability.st .rlx "x" 0)
    (.par (.seq (.fadd .rlx .rlx "a" "x" (.num 1)) (PpoStability.st .rlx "x" 5))
      (.fadd .rlx .rlx "b" "x" (.num 1)))

/-- The write of a FADD reading `r`. -/
def FW (i t r : Nat) (pc : List Nat) : Event :=
  ⟨i, .write .rlx (Expr.glob "x") (.bin .add (.sym r) (.val (.num 1))) false, ⟨t, pc, []⟩, []⟩

def e0 : Event := W 0 0 [0] .rlx "x" 0
def e1 : Event := R 1 0 [1, 0, 0, 0] .rlx "x"
def e2 : Event := FW 2 0 1 [1, 0, 0, 1]
def e3 : Event := W 3 0 [1, 0, 1] .rlx "x" 5
def e4 : Event := R 4 1 [1, 1, 0] .rlx "x"
def e5 : Event := FW 5 1 4 [1, 1, 1]

def esL : EventStructure :=
  ⟨[e0, e1, e2, e3, e4, e5],
   [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (2, 3), (4, 5)],
   [⟨1, .val (.bool true), 2⟩, ⟨4, .val (.bool true), 5⟩]⟩

unseal interp in
theorem denote_prog : denote (fun _ => 0) prog = esL := rfl

/-- `esL` without its RMWs, for the value restrictions (all `⊤`). -/
theorem SL0 : Simple { esL with rmw := [] } := ⟨by decide, by decide, rfl⟩

theorem nodupL : (esL.events.map (·.id)).Nodup := SL0.nodup

theorem holdsL {e : Event} (he : e ∈ esL.events) (f : Valuation) : e.valres.holds f :=
  SL0.holds (e := e) he f

theorem gL : GlobLocs esL := globLocs_of (by decide)

theorem po_of {a b : EventId} (h : (a, b) ∈ esL.po) : esL.poR a b := h

/-- No release, acquire or `sc` event: no `ppo_sync`, hence no `ppo_rmw`. -/
theorem syncL_nil : syncL esL = [] := by decide
theorem syncML_nil : syncML esL = [] := by decide

theorem rmw12 : (⟨1, .val (.bool true), 2⟩ : RMWEntry) ∈ esL.rmw := by simp [esL]
theorem rmw45 : (⟨4, .val (.bool true), 5⟩ : RMWEntry) ∈ esL.rmw := by simp [esL]

theorem acc1 : esL.RMWAcc 1 := ⟨_, rmw12, .inl rfl⟩
theorem acc2 : esL.RMWAcc 2 := ⟨_, rmw12, .inr rfl⟩
theorem acc4 : esL.RMWAcc 4 := ⟨_, rmw45, .inl rfl⟩
theorem acc5 : esL.RMWAcc 5 := ⟨_, rmw45, .inr rfl⟩

/-- Every execution contains every event: there are no guards. -/
theorem all_in_X_L {x : Execution} {Ω : Pred} (hX : x.IsExecution esL Ω) {e : Event}
    (he : e ∈ esL.events) : x.X e.id := by
  have nb : ∀ e ∈ esL.events, e.isBranch = false := by decide
  have nf : ∀ e ∈ esL.events, e.isFence = false := by decide
  apply Classical.byContradiction
  intro hn
  obtain ⟨b, -, ea, eb, ha, hb, hns⟩ :=
    hX.maximal.2.2 e.id (cand_of_mem nodupL he (nb e he) (nf e he)) hn
  exact hns ⟨fun _ => .num 0, holdsL (ev_inv ha).1 _, holdsL (ev_inv hb).1 _⟩

theorem rmwRel_of {x : Execution} {ent : RMWEntry} (hm : ent ∈ esL.rmw)
    (hc : ent.cond = .val (.bool true)) (hr : x.X ent.r) (hw : x.X ent.w) :
    x.rmwRel esL ent.r ent.w :=
  ⟨hr, hw, ent, hm, rfl, rfl, by
    rw [hc]; intro _ _ _ _ h₁ h₂; simp only [Expr.tt] at h₂; rw [h₁] at h₂; cases h₂; rfl⟩

/-- Every event of `esL` is at `x`. -/
theorem locL : ∀ e ∈ esL.events, e.loc = some (Expr.glob "x") := by decide

/-! ## The lost update, over any coherence order

Both FADD writes are coherence-after `x := 0`, which `⊑`-precedes them; the
one coherence-first then lies between the other's read and write. -/

theorem lost_update {x : Execution} {co : Rel} {hb : Rel}
    (h01 : x.rf 0 1) (h04 : x.rf 0 4)
    (htot : co 0 2 ∨ co 2 0) (htot' : co 0 5 ∨ co 5 0) (htot'' : co 2 5 ∨ co 5 2)
    (hb02 : hb 0 2) (hb05 : hb 0 5)
    (hcoh : ∀ a, ¬ ∃ b, hb a b ∧ (b = a ∨ x.eco co b a))
    (hat12 : ¬ ∃ w', x.fr co 1 w' ∧ co w' 2) (hat45 : ¬ ∃ w', x.fr co 4 w' ∧ co w' 5) : False := by
  have c02 : co 0 2 := htot.resolve_right fun h => hcoh 0 ⟨2, hb02, .inr (.single (.inl (.inr h)))⟩
  have c05 : co 0 5 := htot'.resolve_right fun h => hcoh 0 ⟨5, hb05, .inr (.single (.inl (.inr h)))⟩
  rcases htot'' with h | h
  · exact hat45 ⟨2, ⟨0, h04, c02⟩, h⟩
  · exact hat12 ⟨5, ⟨0, h01, c05⟩, h⟩

/-! ## RC11 forbids the outcome -/

/-- **RC11 forbids `a = 0 ∧ b = 0`**: every execution in which both FADDs
    read `x := 0` breaks `Coherent`. -/
theorem rc11_forbids {Ω : Pred} {x : Execution} (hx : x.IsExecution esL Ω)
    (h01 : x.rf 0 1) (h04 : x.rf 0 4) : ¬ x.Coherent esL := by
  rintro ⟨co, hco, hcoh, hat⟩
  have X0 := all_in_X_L hx (e := e0) (by simp [esL])
  have X1 := all_in_X_L hx (e := e1) (by simp [esL])
  have X2 := all_in_X_L hx (e := e2) (by simp [esL])
  have X4 := all_in_X_L hx (e := e4) (by simp [esL])
  have X5 := all_in_X_L hx (e := e5) (by simp [esL])
  have tot : ∀ a b (ea eb : Event), ea ∈ esL.events → eb ∈ esL.events → ea.id = a → eb.id = b →
      x.X a → x.X b → ea.isWrite = true → eb.isWrite = true → ea.loc = eb.loc → a ≠ b →
      co a b ∨ co b a := by
    rintro a b ea eb ha hb rfl rfl Xa Xb wa wb - hne
    exact hco.total _ _ Xa Xb ⟨_, PpoKit.ev_of_mem nodupL ha, wa⟩
      ⟨_, PpoKit.ev_of_mem nodupL hb, wb⟩ hne
      (sameLoc_of (PpoKit.ev_of_mem nodupL ha) (PpoKit.ev_of_mem nodupL hb) (locL _ ha)
        (locL _ hb))
  have m0 : e0 ∈ esL.events := by simp [esL]
  have m2 : e2 ∈ esL.events := by simp [esL]
  have m5 : e5 ∈ esL.events := by simp [esL]
  exact lost_update (hb := x.hb esL) h01 h04
    (tot 0 2 e0 e2 m0 m2 rfl rfl X0 X2 rfl rfl rfl (by decide))
    (tot 0 5 e0 e5 m0 m5 rfl rfl X0 X5 rfl rfl rfl (by decide))
    (tot 2 5 e2 e5 m2 m5 rfl rfl X2 X5 rfl rfl rfl (by decide))
    (.single (.inl (poX_of X0 X2 (po_of (by decide)))))
    (.single (.inl (poX_of X0 X5 (po_of (by decide)))))
    hcoh (hat 1 2 (rmwRel_of rmw12 rfl X1 X2)) (hat 4 5 (rmwRel_of rmw45 rfl X4 X5))

/-! ## Under the rule the elision is not generated -/

/-- **No generated justification elides an access of either FADD**, in
    particular not the first FADD's write into `x := 5`. -/
theorem not_generated {Ω : Pred} {j : Justification} (h : esL.Generated Ω j) :
    (3, 2) ∉ j.δ.we ∧ ∀ p, (p ∈ j.δ.f ∨ p ∈ j.δ.we) → p.2 ≠ 1 ∧ p.2 ≠ 2 ∧ p.2 ≠ 4 ∧ p.2 ≠ 5 := by
  have hn := Generated.not_rmwAcc_elided esL h
  refine ⟨fun hp => hn _ (.inr hp) acc2, fun p hp => ⟨?_, ?_, ?_, ?_⟩⟩ <;> intro he <;>
    apply hn p hp <;> rw [he] <;>
    first | exact acc1 | exact acc2 | exact acc4 | exact acc5

/-- **Under the rule no execution admits `a = 0 ∧ b = 0` under `CoherentT`**,
    forwarding and elision allowed: no RMW access is elided, and `x := 0` is
    read from, so the lost-update argument runs over `X ∖ †`. -/
theorem forbidden_T {Ω : Pred} {x : Execution} (hx : x.IsExecution esL Ω) (hphi : x.phi esL)
    (h01 : x.rf 0 1) (h04 : x.rf 0 4) : ¬ x.CoherentT esL := by
  rintro ⟨co, hco, hcoh, hat⟩
  have X0 := all_in_X_L hx (e := e0) (by simp [esL])
  have X1 := all_in_X_L hx (e := e1) (by simp [esL])
  have X2 := all_in_X_L hx (e := e2) (by simp [esL])
  have X4 := all_in_X_L hx (e := e4) (by simp [esL])
  have X5 := all_in_X_L hx (e := e5) (by simp [esL])
  have n0 : ¬ x.elided 0 := hphi.1 0 (.inl ⟨1, h01⟩)
  have n2 : ¬ x.elided 2 := fun h => rmw_not_elided hx h acc2
  have n5 : ¬ x.elided 5 := fun h => rmw_not_elided hx h acc5
  have tot : ∀ a b (ea eb : Event), ea ∈ esL.events → eb ∈ esL.events → ea.id = a → eb.id = b →
      x.XT a → x.XT b → ea.isWrite = true → eb.isWrite = true → ea.loc = eb.loc → a ≠ b →
      co a b ∨ co b a := by
    rintro a b ea eb ha hb rfl rfl Xa Xb wa wb - hne
    exact hco.total _ _ Xa Xb ⟨_, PpoKit.ev_of_mem nodupL ha, wa⟩
      ⟨_, PpoKit.ev_of_mem nodupL hb, wb⟩ hne
      (sameLoc_of (PpoKit.ev_of_mem nodupL ha) (PpoKit.ev_of_mem nodupL hb) (locL _ ha)
        (locL _ hb))
  have m0 : e0 ∈ esL.events := by simp [esL]
  have m2 : e2 ∈ esL.events := by simp [esL]
  have m5 : e5 ∈ esL.events := by simp [esL]
  exact lost_update (hb := x.hbT esL) h01 h04
    (tot 0 2 e0 e2 m0 m2 rfl rfl ⟨X0, n0⟩ ⟨X2, n2⟩ rfl rfl rfl (by decide))
    (tot 0 5 e0 e5 m0 m5 rfl rfl ⟨X0, n0⟩ ⟨X5, n5⟩ rfl rfl rfl (by decide))
    (tot 2 5 e2 e5 m2 m5 rfl rfl ⟨X2, n2⟩ ⟨X5, n5⟩ rfl rfl rfl (by decide))
    (.single (.inl ⟨poX_of X0 X2 (po_of (by decide)), n0, n2⟩))
    (.single (.inl ⟨poX_of X0 X5 (po_of (by decide)), n0, n5⟩))
    hcoh (hat 1 2 (rmwRel_of rmw12 rfl X1 X2)) (hat 4 5 (rmwRel_of rmw45 rfl X4 X5))

/-! ## Without the rule: elided, and admitted by `CoherenceT` -/

/-- `≼` with `δ` empty, bounded by the alias pairs: no `ppo_sync`. -/
theorem ppo_memL {P : Pred} {δ : FwdCtx} (hδ : ∀ a b, ¬ δ.edge a b) {a b : EventId}
    (h : esL.ppo P δ a b) : (a, b) ∈ aliasL esL := by
  obtain ⟨hab, -⟩ := h
  rcases (FwdCtx.remapRel_of_noEdge hδ).1 hab with (hs | ⟨⟨y, hs, -⟩ | ⟨y, -, hs⟩, -⟩) | ⟨hpo, hal⟩
  all_goals first
    | exact mayAlias_mem gL hpo hal
    | (have := ppoSync_mem hs; rw [syncL_nil] at this; cases this)

/-- MoRDor's `≼`, remapped by a function `f`, bounded by the alias pairs. -/
theorem ppoM_memL {Pa Pr : Pred} {δ : FwdCtx} {f : EventId → EventId}
    (hf : ∀ a a', δ.Remap a a' → a' = f a) {a b : EventId} (h : esL.ppoM Pa Pr δ a b) :
    (a, b) ∈ (aliasL esL).map (fun p => (f p.1, f p.2)) := by
  obtain ⟨⟨a₀, b₀, hab, ra, rb⟩, -⟩ := h
  have base : (a₀, b₀) ∈ aliasL esL := by
    rcases hab with (hs | (⟨y, hs, -⟩ | ⟨y, -, hs⟩)) | ⟨hpo, hm | hal⟩
    all_goals first
      | exact mustAlias_mem gL hpo hm
      | exact mayAlias_mem gL hpo hal
      | (have := ppoSyncM_mem hs; rw [syncML_nil] at this; cases this)
  exact List.mem_map.2 ⟨_, base, by rw [hf _ _ ra, hf _ _ rb]⟩

/-- `x := 5`'s pre-justification. -/
def jB : Justification := pj e3
/-- `x := 5`'s justification with the first FADD's write elided: `WE = {(3, 2)}`. -/
def jWE : Justification := { jB with δ := { jB.δ with we := jB.δ.we ++ [(3, 2)] } }
/-- The second FADD's pre-justification, depending on its read. -/
def j5 : Justification := ⟨e5.valres, [4], .empty, e5⟩
def JB : List Justification := [pj e0, jWE, j5]
def rfB : List (EventId × EventId) := [(0, 1), (0, 4)]
/-- The execution eliding the first FADD's write into `x := 5`, with
    `a = 0 ∧ b = 0`. -/
def xB : Execution := ⟨esL.Candidate, JB, fun w r => (w, r) ∈ rfB⟩
def coB : List (EventId × EventId) := [(0, 5), (5, 3), (0, 3)]

theorem δB : xB.δ = ⟨[], [(3, 2)]⟩ := rfl

theorem edge_B {a b : EventId} (h : xB.δ.edge a b) : a = 3 ∧ b = 2 := by
  rw [δB] at h
  rcases h with h | h
  · cases h
  · simp at h; exact h

theorem elided_B {a : EventId} : xB.elided a ↔ a = 2 := by
  constructor
  · intro h; obtain ⟨b, hb⟩ := (xB.elided_iff a).1 h; exact (edge_B hb).2
  · rintro rfl; exact ⟨(3, 2), .inr (by rw [δB]; simp), rfl⟩

/-- `remap_δ` moves the first FADD's write to `x := 5` and fixes the rest. -/
def fB (a : EventId) : EventId := if a = 2 then 3 else a

theorem remap_B {a a' : EventId} (h : xB.δ.Remap a a') : a' = fB a := by
  induction h with
  | @canon e hno =>
      unfold fB
      split
      · subst_vars; exact absurd (show xB.δ.edge 3 2 from .inr (by rw [δB]; simp)) (hno 3)
      · rfl
  | step he hr ih =>
      obtain ⟨rfl, rfl⟩ := edge_B he
      cases hr with
      | canon _ => rfl
      | step he' _ => exact absurd (edge_B he').2 (by decide)

theorem X_B {a : EventId} : xB.X a ↔ a ∈ esL.ids := by
  constructor
  · exact ids_of_cand
  · intro h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    exact cand_of_mem nodupL he (by revert e; decide) (by revert e; decide)

theorem pre_L {w : Event} {j : Justification} (hw : w ∈ esL.events) (hk : preJust w = some j) :
    esL.Generated (fun _ => True) j :=
  .pre hw hk ⟨fun _ => .num 0, holdsL hw _⟩

/-- Write Elision without the RMW clause elides the first FADD's write into
    `x := 5`: it is the immediate `≼`-predecessor of `x := 5` at its location. -/
theorem blind_we : esL.weRelBlind jB 2 3 := by
  have hδ0 : ∀ a b, ¬ jB.δ.edge a b := by
    intro a b h; rcases h with h | h <;> cases h
  refine ⟨⟨⟨⟨(FwdCtx.remapRel_of_noEdge hδ0).2 (.inr
      ⟨po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl, fun _ => .num 0,
        holdsL (e := e3) (by simp [esL]) _,
        by simp [Expr.holds, Expr.eval, Expr.glob]⟩), by decide⟩, ?_⟩,
      po_of (by decide), _, _, _, _, rfl, rfl, rfl, rfl, fun _ _ _ _ h₁ h₂ => by rw [h₁] at h₂; cases h₂; rfl⟩,
    ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, fun ⟨e, he, hp⟩ => by cases he; simp [e2, FW, Event.isVol] at hp⟩
  rintro ⟨e'', h₁, h₂⟩
  have m₁ := ppo_memL hδ0 h₁
  have m₂ := ppo_memL hδ0 h₂
  have key : ∀ p ∈ aliasL esL, ∀ q ∈ aliasL esL, p.1 = 2 → q.2 = 3 → p.2 = q.1 → False := by
    decide
  exact key _ m₁ _ m₂ rfl rfl rfl

/-- The release restriction holds: no release. -/
theorem weNoRel_23 : esL.weNoRel 2 3 := weNoRel_of (by decide) (by decide)

/-- **The RMW clause alone refutes the elision.** -/
theorem not_weRel {j : Justification} : ¬ esL.weRel j 2 3 := fun h => h.2.2 acc2

theorem wf_we : FwdCtx.WF { jB.δ with we := jB.δ.we ++ [(3, 2)] } := by
  refine ⟨fun a ha => ?_, fun a b e ha hb => ?_⟩
  · have : ∀ c d, Relation.TransGen
        ({ jB.δ with we := jB.δ.we ++ [(3, 2)] } : FwdCtx).edge c d → c = 3 ∧ d = 2 := by
      intro c d h
      induction h with
      | single h => rcases h with h | h <;> simp [jB, pj, FwdCtx.empty] at h; exact h
      | tail _ h ih =>
          rcases h with h | h <;> simp [jB, pj, FwdCtx.empty] at h
          obtain ⟨-, rfl⟩ := ih; cases h.1
    have := this a a ha
    rw [this.1] at this; cases this.2
  · rcases ha with h | h <;> simp [jB, pj, FwdCtx.empty] at h
    rcases hb with h' | h' <;> simp [jB, pj, FwdCtx.empty] at h'
    rw [h.1, h'.1]

theorem mem_JB {j : Justification} (hj : j ∈ JB) : j = pj e0 ∨ j = jWE ∨ j = j5 := by
  simpa [JB] using hj

/-- Every justification of `xB` holds everywhere, none forwards, and only
    `j5` depends, on the second FADD's read. -/
theorem J_B {j : Justification} (hj : j ∈ JB) : (∀ f, j.P.holds f) ∧ j.δ.f = [] ∧
    j.P.syms = [] ∧ (j.D = [] ∨ j = j5) := by
  rcases mem_JB hj with rfl | rfl | rfl <;>
    exact ⟨fun _ => by simp [jWE, jB, j5, pj, e0, e3, e5, W, FW, Event.valres, Expr.conj,
      Expr.holds, Expr.eval, Expr.tt], by simp [jWE, jB, j5, pj, FwdCtx.empty],
      by simp [jWE, jB, j5, pj, e0, e3, e5, W, FW, Event.valres, Expr.conj, Expr.syms, Expr.tt],
      by simp [jWE, jB, pj]⟩

theorem P_B (f : Valuation) : xB.P esL f := fun j hj =>
  ⟨(J_B hj).1 f, fun p hp => by rw [(J_B hj).2.1] at hp; cases hp⟩

theorem dp_B {a b : EventId} (h : xB.DP a b) : a = 4 ∧ b = 5 := by
  obtain ⟨-, -, j, hj, hw, h⟩ := h
  rw [(J_B hj).2.2.1] at h
  rcases (J_B hj).2.2.2 with hD | rfl
  · rw [hD] at h; rcases h with h | h <;> cases h
  · rcases h with h | h
    · cases h
    · simp [j5] at h; exact ⟨h, hw.symm⟩

theorem rfOK_B : RfOK esL rfB := by decide

/-- **Were the elision generated, `xB` would be an execution**: every other
    condition of `IsExecution` holds. -/
theorem isExecution_B (hg : esL.Generated (fun _ => True) jWE) :
    xB.IsExecution esL (fun _ => True) where
  maximal := ⟨fun _ h => h, fun a b _ _ ⟨ea, eb, ha, hb, hn⟩ =>
      hn ⟨fun _ => .num 0, holdsL (ev_inv ha).1 _, holdsL (ev_inv hb).1 _⟩,
    fun _ hc hn => absurd hc hn⟩
  generated j hj := by
    rcases mem_JB hj with rfl | rfl | rfl
    · exact pre_L (w := e0) (by simp [esL]) rfl
    · exact hg
    · exact pre_L (w := e5) (by simp [esL]) rfl
  inX j hj := by
    rcases mem_JB hj with rfl | rfl | rfl <;> exact X_B.2 (by decide)
  consistent := ⟨fun _ => .num 0, fun j hj => (J_B hj).1 _,
    fun a e _ he => holdsL (ev_inv he).1 _⟩
  fwdWF := by
    rw [δB]
    refine ⟨fun a ha => ?_, fun a b e ha hb => ?_⟩
    · have : ∀ c d, Relation.TransGen (FwdCtx.edge ⟨[], [(3, 2)]⟩) c d → c = 3 ∧ d = 2 := by
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
  rf_wr w r h := by
    obtain ⟨h₁, h₂⟩ := rfOK_B.1 _ h
    have hw := cls_clsB.2 h₁
    have hr := cls_clsB.2 h₂
    exact ⟨hw, hr, cand_of_cls nodupL (fun e he => wr_nb e (.inl he)) hw,
      cand_of_cls nodupL (fun e he => wr_nb e (.inr he)) hr⟩
  rf_func w w' r h h' := rfOK_B.2 _ h _ h' rfl
  justified w hw he hn := by
    have hids : ∀ w ∈ esL.ids, clsB esL Event.isEffect w = true → w ≠ 2 →
        w = 0 ∨ w = 3 ∨ w = 5 := by decide
    have hw' := hids w (X_B.1 hw) (cls_clsB.1 he) (fun h => hn (elided_B.2 h))
    have uniq : ∀ j j', j ∈ JB → j' ∈ JB → j.w.id = j'.w.id → j' = j := by
      intro j j' hj hj' h
      rcases mem_JB hj with rfl | rfl | rfl <;>
        rcases mem_JB hj' with rfl | rfl | rfl <;>
        first | rfl | (simp [jWE, jB, j5, pj, e0, e3, e5, W, FW] at h)
    rcases hw' with rfl | rfl | rfl
    · exact ⟨pj e0, by simp [xB, JB], rfl, fun j' hj' h => uniq _ _ (by simp [JB]) hj' h.symm⟩
    · exact ⟨jWE, by simp [xB, JB], rfl, fun j' hj' h => uniq _ _ (by simp [JB]) hj' h.symm⟩
    · exact ⟨j5, by simp [xB, JB], rfl, fun j' hj' h => uniq _ _ (by simp [JB]) hj' h.symm⟩

/-- Under the rule `xB` is no execution. -/
theorem blind_not_execution {Ω : Pred} : ¬ xB.IsExecution esL Ω := by
  intro hx
  exact (not_generated (hx.generated jWE (by simp [xB, JB]))).1
    (by simp [jWE, jB, pj, FwdCtx.empty])

/-- The outcome: both FADDs read `0`. -/
def fOut : Valuation := fun _ => .num 0

theorem phi_B : xB.phi esL := by
  refine ⟨fun e h hel => ?_, fun r => ⟨?_, ?_⟩, fOut, P_B fOut, ⟨?_, ?_, ?_⟩⟩
  · rw [elided_B] at hel; subst hel
    rcases h with ⟨r, hr⟩ | ⟨b, hb⟩
    · have : ∀ p ∈ rfB, p.1 ≠ 2 := by decide
      exact this _ hr rfl
    · exact absurd (dp_B hb).1 (by decide)
  · rintro ⟨w, hw⟩
    obtain ⟨-, h₂⟩ := rfOK_B.1 _ hw
    exact ⟨X_B.2 (clsB_id h₂), cls_clsB.2 h₂⟩
  · rintro ⟨hX, hr⟩
    have key : ∀ r ∈ esL.ids, clsB esL Event.isRead r = true → ∃ p ∈ rfB, p.2 = r := by decide
    obtain ⟨p, hp, rfl⟩ := key r (X_B.1 hX) (cls_clsB.1 hr)
    exact ⟨p.1, hp⟩
  · intro w r ew er h hw hr
    have key : ∀ p ∈ rfB, ∀ ew ∈ esL.events, ∀ er ∈ esL.events, ew.id = p.1 → er.id = p.2 →
        ew.loc.map (·.eval fOut) = er.loc.map (·.eval fOut) ∧
        ew.val.map (·.eval fOut) = er.val.map (·.eval fOut) := by decide
    have := key (w, r) h ew (ev_inv hw).1 er (ev_inv hr).1 (ev_inv hw).2 (ev_inv hr).2
    refine ⟨fun lw lr h₁ h₂ => ?_, fun vw vr h₁ h₂ => ?_⟩
    · have := this.1; rw [h₁, h₂] at this; exact Option.some.inj this
    · have := this.2; rw [h₁, h₂] at this; exact Option.some.inj this
  · intro a e α sz _ he hk
    obtain ⟨hm, -⟩ := ev_inv he
    simp only [esL, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> cases hk
  · intro a₁ a₂ e₁ e₂ α₁ α₂ s₁ s₂ _ _ _ he₁ _ hk₁
    obtain ⟨hm, -⟩ := ev_inv he₁
    simp only [esL, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> cases hk₁

/-- A rank `DP ∪ ≼ ∪ rf` increases along. -/
def rkB (a : EventId) : Nat :=
  match a with
  | 0 => 0 | 1 => 1 | 4 => 1 | 3 => 2 | 5 => 2 | _ => 0

theorem ntaB : xB.NoThinAir esL := by
  have hstep : ∀ a b, xB.ppoStep esL a b → rkB a < rkB b := by
    intro a b h
    have hne : a ≠ b := by
      obtain ⟨-, -, ⟨j, -, hp, -⟩ | ⟨hs | ⟨hp, -⟩, -⟩⟩ := h
      · exact hp.2
      · exact hs.2
      · exact hp.2
    obtain ⟨Pa, Pr, hp⟩ := ppoStep_ppoM h
    have hm := ppoM_memL (fun a a' h => remap_B h) hp
    have key : ∀ p ∈ (aliasL esL).map (fun p => (fB p.1, fB p.2)),
        p.1 ≠ p.2 → rkB p.1 < rkB p.2 := by decide
    exact key _ hm hne
  have mono : ∀ {R : Rel}, (∀ a b, R a b → rkB a < rkB b) →
      ∀ a b, Relation.TransGen R a b → rkB a < rkB b := by
    intro R hR a b h
    induction h with
    | single h => exact hR _ _ h
    | tail _ h ih => exact Nat.lt_trans ih (hR _ _ h)
  have hedge : ∀ a b, ((xB.dep esL).union xB.rf) a b → rkB a < rkB b := by
    rintro a b ((⟨-, -, hp⟩ | hd) | hrf)
    · exact mono hstep a b hp
    · obtain ⟨rfl, rfl⟩ := dp_B hd; decide
    · have key : ∀ p ∈ rfB, rkB p.1 < rkB p.2 := by decide
      exact key _ hrf
  intro a h
  exact Nat.lt_irrefl _ (mono hedge a a h)

theorem locOf_B {a b : EventId} (h : xB.sameLoc esL a b) : locOf esL a = locOf esL b := by
  obtain ⟨ea, eb, la, lb, ha, hb, hla, hlb, heq⟩ := h
  obtain ⟨x, rfl⟩ := gL ea (ev_inv ha).1 _ hla
  obtain ⟨y, rfl⟩ := gL eb (ev_inv hb).1 _ hlb
  have := heq (fun _ => .num 0) (P_B _) _ _ rfl rfl
  cases this
  simp [locOf, ha, hb, hla, hlb]

theorem coherenceOrderT_B : xB.CoherenceOrderT esL (relL coB) where
  writes a b h := by
    have hw : ∀ p ∈ coB, clsB esL Event.isWrite p.1 = true ∧ clsB esL Event.isWrite p.2 = true ∧
        p.1 ∈ esL.ids ∧ p.2 ∈ esL.ids ∧ p.1 ≠ 2 ∧ p.2 ≠ 2 := by decide
    obtain ⟨h1, h2, i1, i2, n1, n2⟩ := hw _ h
    exact ⟨⟨X_B.2 i1, fun h => n1 (elided_B.1 h)⟩, ⟨X_B.2 i2, fun h => n2 (elided_B.1 h)⟩,
      cls_clsB.2 h1, cls_clsB.2 h2⟩
  irrefl a h := by
    have : ∀ p ∈ coB, p.1 ≠ p.2 := by decide
    exact this _ h rfl
  trans a b c h₁ h₂ := by
    have : Closed coB := by decide
    exact this _ h₁ _ h₂ rfl
  total a b ha hb hwa hwb hne hsl := by
    have key : ∀ a ∈ esL.ids.filter (· != 2), ∀ b ∈ esL.ids.filter (· != 2),
        clsB esL Event.isWrite a = true →
        clsB esL Event.isWrite b = true → a ≠ b → locOf esL a = locOf esL b →
        (a, b) ∈ coB ∨ (b, a) ∈ coB := by decide
    exact key a (List.mem_filter.2 ⟨X_B.1 ha.1, by simpa using fun h => ha.2 (elided_B.2 h)⟩)
      b (List.mem_filter.2 ⟨X_B.1 hb.1, by simpa using fun h => hb.2 (elided_B.2 h)⟩)
      (cls_clsB.1 hwa) (cls_clsB.1 hwb) hne (locOf_B hsl)

/-- A bound on `ECO`. -/
def EB : List (EventId × EventId) :=
  [(0, 1), (0, 4), (0, 5), (5, 3), (0, 3), (1, 5), (1, 3), (4, 5), (4, 3)]

theorem coherenceT_B : xB.CoherenceT esL (relL coB) := by
  have hH : ∀ a b, xB.hbT esL a b → (a, b) ∈ esL.po := by
    intro a b h
    refine transGen_mem (fun c d s => ?_) (by decide) h
    rcases s with ⟨⟨-, -, hpo⟩, -⟩ | ⟨hs, -⟩
    · exact hpo
    · have := sw_mem hs
      have hsw : swL esL = [] := by decide
      rw [hsw] at this; cases this
  have hE : ∀ a b, xB.eco (relL coB) a b → (a, b) ∈ EB :=
    fun a b h => eco_mem (fun a b h => by
        have : ∀ p ∈ rfB, p ∈ EB := by decide
        exact this _ h)
      (fun a b h => by
        have : ∀ p ∈ coB, p ∈ EB := by decide
        exact this _ h)
      (fun a b h => by
        have : ∀ p ∈ frL rfB coB, p ∈ EB := by decide
        obtain ⟨w, hrf, hco⟩ := h
        exact this _ (List.mem_flatMap.2 ⟨(w, a), hrf, List.mem_map.2 ⟨(w, b),
          List.mem_filter.2 ⟨hco, by simp⟩, rfl⟩⟩))
      (by decide) h
  have hok : ∀ p ∈ esL.po, p.1 ≠ p.2 ∧ (p.2, p.1) ∉ EB := by decide
  rintro a ⟨b, hab, rfl | hba⟩
  · exact (hok _ (hH _ _ hab)).1 rfl
  · exact (hok _ (hH _ _ hab)).2 (hE _ _ hba)

/-- Atomicity holds: the first FADD's write is in no coherence order of
    `X ∖ †`, and nothing lies between `x := 0` and the second FADD's write. -/
theorem atomicity_B : xB.Atomicity esL (relL coB) := by
  rintro r w ⟨-, -, ent, hm, rfl, rfl, -⟩ ⟨w', ⟨w₀, hrf, hco⟩, hco'⟩
  have key : ∀ ent ∈ esL.rmw, ∀ p ∈ rfB, ∀ q ∈ coB, ∀ s ∈ coB,
      p.2 = ent.r → q.1 = p.1 → s.1 = q.2 → s.2 = ent.w → False := by decide
  exact key ent hm (w₀, ent.r) hrf (w₀, w') hco (w', ent.w) hco' rfl rfl rfl rfl

theorem coherentT_B : xB.CoherentT esL :=
  ⟨relL coB, coherenceOrderT_B, coherenceT_B, atomicity_B⟩

/-- **Without the RMW clause, `CoherenceT` admits the lost update.** Write
    Elision under its other conditions (`weRelBlind`, `weNoRel`) elides the
    first FADD's write into `x := 5` (`jWE` from the pre-justification `jB` of
    `x := 5`); the RMW clause refutes it (`¬ weRel`); everything else an
    execution asks holds (`isExecution_B`), and so do `φ`, No-Thin-Air and
    `CoherentT`, with both FADDs reading `x := 0`. -/
theorem blind_admitted :
    (esL.Generated (fun _ => True) jB ∧ esL.weRelBlind jB 2 3 ∧ esL.weNoRel 2 3 ∧
      FwdCtx.WF { jB.δ with we := jB.δ.we ++ [(3, 2)] } ∧
      Sat (Pred.and jB.P.holds fun _ => True)) ∧
    ¬ esL.weRel jB 2 3 ∧
    (esL.Generated (fun _ => True) jWE → xB.IsExecution esL (fun _ => True)) ∧
    xB.phi esL ∧ xB.NoThinAir esL ∧ xB.CoherentT esL ∧ xB.rf 0 1 ∧ xB.rf 0 4 :=
  ⟨⟨pre_L (w := e3) (by simp [esL]) rfl, blind_we, weNoRel_23, wf_we,
    ⟨fun _ => .num 0, (J_B (j := jWE) (by simp [JB])).1 _, trivial⟩⟩,
   not_weRel, isExecution_B, phi_B, ntaB, coherentT_B,
   show (0, 1) ∈ rfB by decide, show (0, 4) ∈ rfB by decide⟩

end RMWElision
