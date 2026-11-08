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

For a named law family, run
`scripts/h62/item2/audit-language/family_coverage.py --source SOURCE --witness WITNESS`
and separately kernel-check the witness module. Source accounting cannot certify
Lean telescope compatibility. Imported telescope witnesses establish only local
joint feasibility, not compiler totality, historical replay or full audit coverage.

Repeat `--family SOURCE WITNESS` to check several complete named families
together; duplicate target and resolved witness identities are refused. This
remains source accounting. Freshly compile the witness objects before checking
`tests/h62/item2/audit-language/FixedPointWitnessSuite.lean` for import composition.
