# Audit theories

The [checker](../../scripts/h55/module-times/theories_audit_witnesses.py) and [fixtures](../../tests/h62/item2/audit-theories/) define the current scope and limitations.

For portable historical evidence, use [paired_evidence.py](../../scripts/h62/item2/audit-theories/paired_evidence.py) and its [corruption controls](../../scripts/h62/item2/audit-theories/check_paired_evidence.py). Certificate designation comes from the committed witness registry; archive integrity checks do not rerun Lean or establish full assignment acceptance.

Missing historical receipts can be reconstructed with [rebuild_frozen_evidence.py](../../scripts/h62/item2/audit-theories/rebuild_frozen_evidence.py). Supply fresh off-git checkout/evidence paths and the toolchain pinned by the original frozen tree. This runs bounded serial checks and census replay; final integration gates remain separate.
