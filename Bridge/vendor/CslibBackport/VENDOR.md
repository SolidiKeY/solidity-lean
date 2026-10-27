# CslibBackport

Six files of CSLib (<https://github.com/leanprover/cslib>, Apache-2.0, `LICENSE`)
at commit `c7944a9fb44c3298f1a960a5e574ab23a6ab8ed5` (2026-05-26, Lean 4.30),
backported to Lean 4.24: CSLib's own v4.24 release (`e1fea78`, the one this
package requires) predates its proof theory.

| File | Upstream |
|---|---|
| `Foundations/Logic/InferenceSystem.lean` | [Cslib/Foundations/Logic/InferenceSystem.lean](https://github.com/leanprover/cslib/blob/c7944a9fb44c3298f1a960a5e574ab23a6ab8ed5/Cslib/Foundations/Logic/InferenceSystem.lean) |
| `Foundations/Logic/LogicalEquivalence.lean` | [Cslib/Foundations/Logic/LogicalEquivalence.lean](https://github.com/leanprover/cslib/blob/c7944a9fb44c3298f1a960a5e574ab23a6ab8ed5/Cslib/Foundations/Logic/LogicalEquivalence.lean) |
| `Foundations/Syntax/Context.lean` | [Cslib/Foundations/Syntax/Context.lean](https://github.com/leanprover/cslib/blob/c7944a9fb44c3298f1a960a5e574ab23a6ab8ed5/Cslib/Foundations/Syntax/Context.lean) |
| `Foundations/Syntax/Congruence.lean` | [Cslib/Foundations/Syntax/Congruence.lean](https://github.com/leanprover/cslib/blob/c7944a9fb44c3298f1a960a5e574ab23a6ab8ed5/Cslib/Foundations/Syntax/Congruence.lean) |
| `Logics/Propositional/Defs.lean` | [Cslib/Logics/Propositional/Defs.lean](https://github.com/leanprover/cslib/blob/c7944a9fb44c3298f1a960a5e574ab23a6ab8ed5/Cslib/Logics/Propositional/Defs.lean) |
| `Logics/Propositional/NaturalDeduction/Basic.lean` | [Cslib/Logics/Propositional/NaturalDeduction/Basic.lean](https://github.com/leanprover/cslib/blob/c7944a9fb44c3298f1a960a5e574ab23a6ab8ed5/Cslib/Logics/Propositional/NaturalDeduction/Basic.lean) |

The changes are mechanical: the module system's `module`, `public import` and
`@[expose] public section` dropped, `Cslib.Init` replaced by
`Mathlib.Tactic.Common`, and imports renamed to `CslibBackport.*`.  The
declarations keep their names (`Cslib.Logic.InferenceSystem`, …), so moving
to Lean 4.30 means deleting this directory and importing CSLib's modules.
