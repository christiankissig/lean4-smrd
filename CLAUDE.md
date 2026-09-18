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

`../lean4-episodic-loops` builds on this library (a Lake git dependency on `main`) for the paper's
own results: restricted predicates, futures and episodicity, and the γ argument. Anything
episodicity-specific belongs there, not here.

No Mathlib: sets and relations are predicates (`EvSet`, `Rel` over `EventId`), predicates are
semantic (`Pred := Valuation → Prop`), and syntactic predicates are `Expr`s denoting one via
`Expr.holds`. Symbols are event ids (`origin α = α`).

### Module dependency order

```
Smrd.Types                        expressions, values, events, event structures, relations
├── Smrd.EventStructureSemantics  program syntax, CPS semantics ⟨P⟩_{n ρ κ φ}, per-loop step-counters
│     ├── Smrd.Fresh            `denote_ids_nodup`: the events of ⟨P⟩_n have distinct ids
│     └── Smrd.Monotonicity     `denote_mono`: ⟨P⟩_n embeds into ⟨P⟩_{n'} for n ≤ n' (l:es-mono)
└── Smrd.Forwardingcontext        δ = (F, WE), ψ_δ, remap_δ
      └── Smrd.Ppo                ≼_sync, ≼_rmw, ≼_alias, ≼^P_δ, pred, dependence on P
            └── Smrd.Justifications  pre-justifications, elaborations, `Generated` (𝕁)
                  └── Smrd.Executions  executions, freeze (DP, ≼, φ), NTA, coherence, UAF, `Frozen`
```

`Smrd.Basic` re-exports all of the above and is the library root (`Smrd.lean` imports it).
Each module header lists its deviations from the paper (strict `⊑`, …).

Renaming or changing the signature of a definition here can break `lean4-episodic-loops`. It
sees a change only once pushed to `main`, after `lake update lean4-smrd` there; run that and
`lake build` in `../lean4-episodic-loops` before merging such a change.
