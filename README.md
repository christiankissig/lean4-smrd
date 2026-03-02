# lean4-smrd

A Lean 4 formalisation of the **Symbolic Memory Recurrence Diagram** (SMRD)
semantics for weak memory concurrency.

## Background

The MRD semantics was introduced in:

> Christian Kissig, "A Denotational Semantics for Weak Memory Concurrency",
> *ESOP 2020*.
> <https://link.springer.com/chapter/10.1007/978-3-030-44914-8_22>

It provides a denotational semantics for concurrent programs that:

- **avoids thin-air reads** by tracking true data-flow dependencies,
- **gives DRF-SC** (sequentially consistent semantics to data-race-free
  programs), and
- **supports compositional refinement** for validating compiler optimisations.

The original implementation is available as an OCaml simulator at
<https://github.com/kent-weak-memory/mrder>.

This Lean 4 project provides a *symbolic* formalisation: memory locations,
stored values and register names are kept as **abstract type parameters**
(`Loc`, `Val`, `Reg`), so every result holds for any concrete instantiation of
those domains.

## Structure

| File | Contents |
|------|----------|
| `SMRD/Basic.lean` | Memory access orderings, event labels. |
| `SMRD/EventStructure.lean` | Labeled Event Structures (LES), product, coproduct, relabeling. |
| `SMRD/Properties.lean` | Well-formedness, configurations, structural lemmas. |
| `SMRD.lean` | Top-level import. |

## Building

Requires [Lean 4](https://leanprover.github.io/) and
[Lake](https://github.com/leanprover/lake) (bundled with Lean):

```bash
lake build
```