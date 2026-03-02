/-!
# Lean4 Formalisation of Symbolic MRD

This library contains a Lean 4 formalisation of the Symbolic Memory Recurrence
Diagram (SMRD) semantics for weak memory concurrency, based on the MRD semantics
described in:

> Christian Kissig, "A Denotational Semantics for Weak Memory Concurrency",
> ESOP 2020.  <https://link.springer.com/chapter/10.1007/978-3-030-44914-8_22>

The formalization is "symbolic" in the sense that memory locations, values and
register names are kept as abstract type parameters (`Loc`, `Val`, `Reg`), so
that all results hold over any instantiation of those domains.

## Module structure

* `SMRD.Basic`          – memory access orderings and event labels.
* `SMRD.EventStructure` – labeled event structures (LES) and their operations.
* `SMRD.Properties`     – well-formedness conditions and key structural lemmas.
-/

import SMRD.Basic
import SMRD.EventStructure
import SMRD.Properties
