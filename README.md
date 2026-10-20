[![Lean Action CI](https://github.com/christiankissig/lean4-smrd/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/christiankissig/lean4-smrd/actions/workflows/lean_action_ci.yml)

# Summary

Lean4 Formalisation of Symbolic Modular Relaxed Dependencies per 
["Symbolic MRD: Dynamic Memory, Undefined Behaviour, and Extrinsic Choice" by Jay Richards, Daniel Wright, Simon Cooksey, Mark Batty](https://2025.splashcon.org/details/OOPSLA/104/Symbolic-MRD-Dynamic-Memory-Undefined-Behaviour-and-Extrinsic-Choice).

The definitions follow the restatement of SMRD in Appendix A of *Episodic Loops*, and
[lean4-episodic-loops](../lean4-episodic-loops) builds that paper's results on this library.

# Differential testing against MoRDor

`smrd-es` runs the event structure semantics `denote` on a program given as JSON and prints the
event structure as JSON (see the header of `EsExport.lean` for both formats):

```bash
lake build smrd-es
.lake/build/bin/smrd-es program.json 2      # per-loop step-counter 2
```

`scripts/es_diff.py` compares it with [MoRDor](../mordor) on MoRDor's litmus tests. It takes each
program from `mordor parse --output-mode isa` and translates it to `smrd-es`'s input. It takes
MoRDor's event structure from `mordor interpret --output-mode json`. It then compares the two
program-order forests up to the renaming of event ids and symbols:

```bash
python3 scripts/es_diff.py --bound 2 ../mordor/litmus-tests ../mordor/programs/episodicity
```

It needs a MoRDor build (`dune build` in `../mordor`, or `--mordor PATH`). Each test comes out as
`agree`, `equiv` (expressions differ only syntactically), `pruned` (agree once events MoRDor does
not generate are dropped: those on an unsatisfiable path, and branches the path decides),
`value` (an expression is not equivalent), `differ`, `branches` (agree on every event but the
branch events, which MoRDor elides where the path decides them, unevenly), `cut` (see below),
`ub-model` (a difference under one of MoRDor's
UB-optimising models, `UB11`, `RC11UB` or `IMMUB`, which fold `e / !r` to `e` and `denote` does not),
or `skip` (a construct this library's syntax
lacks: non-atomics, locks, strong RMWs, RMWs on pointers, statements after a parallel block).
Registers read before they are assigned are unknowns in MoRDor, and `smrd-es` starts each of them
out holding a symbol of its own.

Loops are bounded differently. When a loop's counter runs out, `denote` generates nothing
(`⟨while b P⟩ ≜ ∅`, as in the paper), and that path ends. MoRDor instead generates one more loop
head (its `Blocked` check) and leaves the loop on its exit outcome. MoRDor's bound n is therefore
`denote`'s bound n + 1 with each loop's last body removed, and the test compares loop programs in
that form (status `cut`). `do B while c` is translated as `B; while c B`.
