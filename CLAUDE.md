# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Commands

```bash
# Build the project
lake build

# Build a specific target
lake build Smrd

# Check a single file (interactive/incremental in an editor, but CLI-wise via lake)
lake build Smrd.Types

# Run the executable
lake exe lean4-smrd
```

CI runs `leanprover/lean-action@v1` on push/PR, which calls `lake build` by default.

Lean version is pinned in `lean-toolchain`: `leanprover/lean4:v4.28.0`.

## Architecture

This project mechanises the **SMRD (Symbolic Modular Relaxed Dependencies)** memory model
(Richards et al., OOPSLA 2025), in the form restated in Appendix A of the episodic loops paper
(`../episodic-loops-paper`), which refines it: effectful events (writes, allocations,
deallocations) are justified, `≼_rmw` is asymmetric for conditional RMWs, and loops carry per-loop
step-counters and iteration labels. Docstrings cite that paper's LaTeX labels (`def:freeze`, …).

The paper's own results (restricted predicates, futures and episodicity, the γ argument) are
mechanised downstream, on top of this library. Anything episodicity-specific belongs there, not
here.

No Mathlib: sets and relations are predicates (`EvSet`, `Rel` over `EventId`), predicates are
semantic (`Pred := Valuation → Prop`), and syntactic predicates are `Expr`s denoting one via
`Expr.holds`. Symbols are event ids (`origin α = α`).

### Module dependency order

```
Smrd.Types                        expressions, values, events, event structures, relations
├── Smrd.Conjuncts                `conj(P)`, predicates read up to their conjuncts (par:conj)
├── Smrd.EventStructureSemantics  program syntax, CPS semantics ⟨P⟩_{n ρ κ φ} (∥ joins: κ runs once, after both threads), per-loop step-counters
│     ├── Smrd.Fresh            `denote_ids_nodup`: the events of ⟨P⟩_n have distinct ids; `interp_invR` (invariants with RMW entries added as `RMWShapeR`: read ⊑ write, one location)
│     └── Smrd.Monotonicity     `denote_mono`: ⟨P⟩_n embeds into ⟨P⟩_{n'} for n ≤ n' (l:es-mono)
└── Smrd.Forwardingcontext        δ = (F, WE), ψ_δ, remap_δ
      └── Smrd.Ppo                ≼_sync, ≼_rmw, ≼_alias, ≼^P_δ, pred, dependence on P
            ├── Smrd.PpoMordor        MoRDor's ppo templates (ppo_sync, ppo_loc, ForwardingContext.ppo)
            └── Smrd.Justifications  (+ Smrd.Conjuncts) pre-justifications, elaborations, `Generated` (𝕁), Write Elision's release restriction (`weNoRel`), no RMW access elided (`RMWAcc`, `Generated.not_rmwAcc_elided`)
                  └── Smrd.Executions  (+ PpoMordor) executions, freeze (DP, ≼ = MoRDor's freeze_ppo cut to anchored pairs, ppoTrunc, ppoWin, φ), NTA, RC11 coherence, atomicity, UAF (sMRD `nta`, RC11 `ntaRC11`), RC11 no-thin-air (`NoThinAirRC11`), `Frozen`
                        └── Smrd.CoherenceRC11  preserved coherence and HB_v, reduced to RC11's axiom (FenceFree)
                              └── Smrd.PpoTail  MoRDor's ≼: ≼ ⊆ ⊑ without forwarding (elision allowed, `NoCross`), conditions (i)/(ii) off elided events, NTA same as ppoWin
                                    ├── Smrd.CoherenceT  sMRD's coherence over X ∖ † (`CoherenceT`, `CoherentT`, `ConsistentT`); with Write Elision's release restriction (`weNoRel`, MoRDor #207) and Forwarding's acquire restriction (`fwdNoAcq`, MoRDor #210) remap(ppo_sync) ⊆ ⊑ with forwarding (`sync_not_back`); no RMW access elided (`rmw_not_elided`, `atomicityT_iff`); `DP ∪ ≼ ⊆ ⊑` under `NoRevLoc` (not implied by the restrictions, `Smrd.FwdAcrossAlias`); and `CoherenceT` ⇔ HB_v-coherence (no acquire read forwarded, `NoRevLoc`)
                                    ├── Smrd.PpoEval  ≼ computed for global-location executions (`ppoEval_iff`), for `smrd-es` / scripts/ppo_diff.py
                                    └── Smrd.PpoKit  (+ Monotonicity) concrete executions, list bounds on ≼, sw, eco
                                          └── Smrd.PpoStability  truncated ≼ unstable (A), untruncated local/stable (B), no NTA change (C)
                                                ├── Smrd.PpoNecessity  untruncated ≼ needed for HB_v = RC11 (N1: CoRR, CoWR, MP); no cross-thread ≼ under elision (N2), HB_v ⇏ RC11 at an elided write (N3)
                                                │     └── Smrd.WEAcrossRelease  (+ CoherenceT) MoRDor's WE-across-release.lit: RC11 forbids, CoherenceT admits under blind elision, the release restriction forbids; `coww_elided` over X ∖ †
                                                │           ├── Smrd.FwdAcrossAcquire  MoRDor's RSE-across-acquire.lit: RC11 forbids, CoherenceT admits under blind Forwarding across an acquire, the acquire restriction forbids
                                                │           └── Smrd.RMWElision  lost update `x := 0; (FADD; x := 5 ∥ FADD)`: RC11 forbids, CoherenceT admits when the FADD's write is elided, the RMW rule forbids
                                                └── Smrd.DPPast  (+ CoherenceT) DP ⊆ ⊑ (`Generated.past`, `Execution.dp_po`) from Strengthening's and Lifting's origins before the write, given `SymWF` and the store-store forwarding window (`FwdWin`); the `DP ⊆ ⊑` hypotheses of `noThinAir_iff_*`, `dep_po_T` derived (`*_past`)
                                                      ├── Smrd.LiftCross  (+ PpoNecessity) `r := y; if r = 0 then x := 1 ∥ x := 1`: the paper's Lifting lifts the guard into the other thread, DP against ⊑ in an execution; `LiftPast` fails, the restriction on Lifting forbids
                                                      ├── Smrd.FwdAcrossAlias  (+ PpoNecessity) `r0 := *p2; r1 := *p; r2 := x` with `r2` forwarded from `r0` under `p2 = &x ∧ p ≠ &x`, and a justification strengthened by `p ≠ p2` only: consistent, every hypothesis of `dep_po_T` but `NoRevLoc` holds, `NoRevLoc` and `DP ∪ ≼ ⊆ ⊑` fail
                                                      │     └── Smrd.FwdEntails  (CoherenceT + RoutineHyps; its examples import FwdAcrossAlias) `FwdEntailsOn`: each F ∪ WE edge has a generating j₀ (`EdgeGen`, always available: `edgeGen_of_execution`) with P_j ∧ ψ_δ ⊨ P_{j₀} ∧ ψ_{δ_{j₀}} for the j in scope, and p_combined ⊨ it; scope = window ∋ remap_δ(e₂) (`FwdEntailsImg`) gives `DP ∪ ≼ ⊆ ⊑` (`dep_po_E`, with `NoRevRMW`, `Sat P`, `LocsEval`), scope = all of J gives `NoRevLoc` (`noRevLoc_of_fwdEntailsAll`); valid generating predicates satisfy every scope (`fwdEntailsOn_of_valid`)
                                                      │           ├── Smrd.FwdEntailsCheck  the execution of FwdAcrossAlias violates every scope; PpoNecessity's `xWW`, `xC` satisfy every scope
                                                      │           ├── Smrd.FwdPastWindow  FwdAcrossAlias with `z := 1` before `r2`: consistent, `FwdEntails` (window ∋ e₂) holds, `≼ ⊄ ⊑`
                                                      │           ├── Smrd.FwdChain  chain `r3 ↦ r2 ↦ r0`: consistent, `FwdEntailsSrc` (window ∋ e₁ or e₂) holds, `≼ ⊄ ⊑`; `FwdEntailsImg` fails
                                                      │           └── Smrd.FwdEntailsRMW  `NoRevRMW` dropped: the ppo_rmw pairs are not reversed under the restrictions, `pred` and `RMWWF` (read ⊑ write, one location), so `dep_po_R` = `dep_po_E` with `RMWWF` for `NoRevRMW`; `NoCrossRMW` (no F ∪ WE edge crosses an RMW access) implies `NoRevRMW` and, with `FwdEntailsAll`, `NoRevLoc`
                                                      │                 └── Smrd.RMWCross  (+ FwdEntailsCheck, RMWElision) `y := 0; x := 1; FADD_rlx(y, 1); x := 2`, `x := 1` elided across the FADD: consistent, `FwdEntailsAll`, `NoRevRMW`/`NoRevLoc` fail, `≼ ⊆ ⊑` holds; `x := 1; FADD_rel(x, 1)`: `pred` refuses eliding `x := 1` into the FADD's write (`not_weRel_fadd`)
                                                      └── Smrd.SymWFDenote  (+ Fresh) ⟨P⟩_n introduces symbols ⊑-before their uses (`denote_symWF`)
Smrd.Labels  (Fresh + Monotonicity + Executions) labels are unique in P̄: distinct events of ⟨P⟩_n with one label conflict (`labels_unique`, `conflictFree_label_inj`), for distinct loop ids
Smrd.RoutineHyps  (Fresh + PpoTail) ⊑ of ⟨P⟩_n a strict order (`denote_po_trans`, `denote_po_irrefl`); sameLoc (under P ∧ φ_rf, as partial values) transitive and ⊇ rf outright (`sameLoc_trans`, `rfLoc` in CoherenceRC11); locations of ⟨P⟩_n Total for programs that do not compute pointers (`denote_totalLocs`, `Stmt.PtrWF`), so LocModel from a model of P ∧ valres_X ∧ φ_rf (`locModel_of_denote`); with constant offsets `*(r + c)`, `*(r + rc)` (`Stmt.PtrOffWF`, RCU's `rcu1_ptrOffWF`) from a model that also types the offset bases as non-booleans (`AddrTypedAt`, `locModel_of_denote_off`; needed: `locModel_of_offset_false`); counterexamples to LocModel from φ alone
Smrd.RMWWFDenote  (RoutineHyps + FwdEntailsRMW) ⟨P⟩_n is `RMWWF` (`denote_rmwWF`); `dep_po_R_denote`, `dep_po_R_of_phi_denote` drop `RMWWF` and ⊑'s transitivity and irreflexivity (`PoForest` stays: false for `(a ∥ b); c`)
      └── Smrd.FwdAcrossJoin  (+ DPPast, PpoNecessity) `z := 0; (r1 :=_acq z ∥ x := 1); r2 := x; y := r2`, `r2` forwarded from `x := 1` across the join: consistent, every hypothesis of `dep_po_R_of_phi_denote` and `dep_po_T` but `PoForest` holds, `≼` relates `r1` and `x := 1` (⊑-incomparable), `DP ∪ ≼ ⊄ ⊑`
```

`Smrd.Basic` re-exports all of the above and is the library root (`Smrd.lean` imports it).
Each module header lists its deviations from the paper (the relational `remap_δ`, …).

Renaming or changing the signature of a definition here can break downstream developments that
depend on `main`; check them before merging such a change.
