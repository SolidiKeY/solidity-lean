# Proposed registration only

No generated root, module map, Lake configuration, axiom pin or owned original
was changed. The coordinator must approve any area registration.

Suggested optional audit library configuration (not applied):

```toml
[[lean_lib]]
name = "H62AuditLanguage"
srcDir = "tests/h62/item2/audit-language"
roots = ["FeatureWitness", "IndependentWitness", "AbiEntryWitness", "FullTelescopeWitness", "FixedPointWitness"]
weakLeanArgs = ["--tstack=131072", "-j1"]
```

The reflection helper imports `Lean` and belongs above the dependency-free
intrinsic core. None of these test modules should enter the core import graph.
Proposed language-area fragment rows, pending owner approval:

| Audit module | What it checks |
|---|---|
| `tests/h62/item2/audit-language/FeatureWitness.lean` | Shared feature/exclusion feasibility and inhabited diagnostic clients. |
| `tests/h62/item2/audit-language/IndependentWitness.lean` | Simultaneous lattice/arithmetic hypotheses and actual overflow-boundary client. |
| `tests/h62/item2/audit-language/AbiEntryWitness.lean` | Actual nonzero boolean decode, failure/fuel/allocation boundaries and error-only decoder controls. |
| `tests/h62/item2/audit-language/FullTelescopeWitness.lean` | Fifteen kernel-checked complete telescope certificates, exact association receipts and mismatch refusal. |
| `tests/h62/item2/audit-language/FixedPointWitness.lean` | All 36 reference-semantics statements with leading arguments: full imported telescope certificates, intrinsic range/overflow/divisor premises and mismatch refusal. |
