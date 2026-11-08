# Audit theories

The [checker](../../scripts/h55/module-times/theories_audit_witnesses.py) and [fixtures](../../tests/h62/item2/audit-theories/) define the current scope and limitations.

For portable historical evidence, use [paired_evidence.py](../../scripts/h62/item2/audit-theories/paired_evidence.py) and its [corruption controls](../../scripts/h62/item2/audit-theories/check_paired_evidence.py). Certificate designation comes from the committed witness registry; archive integrity checks do not rerun Lean or establish full assignment acceptance.

Missing historical receipts can be reconstructed with [rebuild_frozen_evidence.py](../../scripts/h62/item2/audit-theories/rebuild_frozen_evidence.py). Supply fresh off-git checkout/evidence paths and the toolchain pinned by the original frozen tree. This runs bounded serial checks and census replay; final integration gates remain separate.

[Path premise roles](../../scripts/h62/item2/audit-theories/path_input_roles.py) preserve all 41 frozen telescopes and validate designated joint packets. [Rehashed corruption controls](../../scripts/h62/item2/audit-theories/check_path_role_controls.py) check binder, type and source/owner provenance refusal. These 41 records are separate from the legacy 44-record acceptance snapshot; their disjoint specification union has 85 names.
