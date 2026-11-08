# Audit language

The [checker](../../scripts/h55/module-times/language_audit_controls.py) and
[fixtures](../../tests/h62/item2/audit-language/) define the scope and limitations.

## Validation boundaries

The historical ownership snapshot with SHA256
`7f5d40d46d386ed17731db55ed87f0564f5c9e667bddee00c0f12b28772f9cce`
and its full portable evidence are **UNVERIFIABLE** under H151. Historical replay
remains unproven; current registries are not substitutes. Fresh source recovery
must leave historical owners unknown and must not imply kernel or witness credit.

Use `scripts/h62/item2/audit-language/source_only.py` for fresh frozen-source
recovery and `scripts/h62/item2/audit-language/source_roles.py` for lexical roles;
`--refine` reuses frozen definition refinements while retaining range constraints.
Write bulk output outside the checkout and archive evidence privately under H145.
The original authenticated-ownership checks remain strict.
Run `scripts/h62/item2/audit-language/source_acceptance.py --census EXTERNAL_JSON`
for fresh source-only reconciliation. It does not run or replace historical
ownership acceptance, imported telescope checks or witness certification.

For a named law family, run
`scripts/h62/item2/audit-language/family_coverage.py --source SOURCE --witness WITNESS`
and separately kernel-check the witness module. Source accounting cannot certify
Lean telescope compatibility. Imported telescope witnesses establish only local
joint feasibility, not compiler totality, historical replay or full audit coverage.

Repeat `--family SOURCE WITNESS` to check several complete named families
together; duplicate target and resolved witness identities are refused. This
remains source accounting. Freshly compile the witness objects before checking
`tests/h62/item2/audit-language/FixedPointWitnessSuite.lean` for import composition.

Closed counterexamples must be recorded separately from input-tuple certificates.
`#verify_closed_theorem` checks theorem/Prop status and absence of leading
parameters; an explicit statement guard must establish the counterexample's
meaning. Expected telescope-mismatch errors remain negative tests, never
positive associations or grounds to weaken an original premise.

For eager-bytes outcome checks, freshly compile
`tests/h62/item2/audit-language/AbiDynamicWitness.lean` before kernel-checking
`tests/h62/item2/audit-language/AbiBytesSpec.lean`. Keep the swapped-failure
control: exact success alone does not certify panic/revert distinctions. These
are decoder reference contracts, not compiler or EVM gas contracts.

Check `tests/h62/item2/audit-language/AbiBytesEntry.lean` after freshening the
bytes-specification object when auditing its entry consumer. Preserve the outer
head-size/offset checks and extra fuel layer when substituting a decoder.

Freshen the entry witness object before checking
`tests/h62/item2/audit-language/AbiBytesEntrySpec.lean`. Its zero/one-fuel clauses
are necessary alongside sufficiently fueled outcomes; success preservation alone
does not certify failure priority.

Use `scripts/h62/item2/audit-language/witness_plan.py` with repeated `--witness`
module paths and new external `--output`/`--index` paths to plan fresh accounting.
It grants source-plan credit only. Freshen the listed witness objects and
`tests/h62/item2/audit-language/WitnessAccounting.lean` before checking generated
code; also check `tests/h62/item2/audit-language/WitnessAccountingControls.lean`.
Keep raw leading-binder categories and closed schemas separate. This does not
replace historical ownership acceptance or semantic interface classification.
