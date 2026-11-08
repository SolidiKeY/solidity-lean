# Audit theories

The [checker](../../scripts/h55/module-times/theories_audit_witnesses.py) and [fixtures](../../tests/h62/item2/audit-theories/) define the current scope and limitations.

For portable historical evidence, use [paired_evidence.py](../../scripts/h62/item2/audit-theories/paired_evidence.py) and its [corruption controls](../../scripts/h62/item2/audit-theories/check_paired_evidence.py). Certificate designation comes from the committed witness registry; archive integrity checks do not rerun Lean or establish full assignment acceptance.

Missing historical receipts can be reconstructed with [rebuild_frozen_evidence.py](../../scripts/h62/item2/audit-theories/rebuild_frozen_evidence.py). Supply fresh off-git checkout/evidence paths and the toolchain pinned by the original frozen tree. This runs bounded serial checks and census replay; final integration gates remain separate.

[Path premise roles](../../scripts/h62/item2/audit-theories/path_input_roles.py) preserve all 41 frozen telescopes and validate designated joint packets. [Rehashed corruption controls](../../scripts/h62/item2/audit-theories/check_path_role_controls.py) check binder, type and source/owner provenance refusal. These 41 records are separate from the legacy 44-record acceptance snapshot; their disjoint specification union has 85 names.

[Memory-mirror premise roles](../../scripts/h62/item2/audit-theories/mirror_input_roles.py) distinguish logical heap prefixes, universal preservation and selected mirrors. [Corruption controls](../../scripts/h62/item2/audit-theories/check_mirror_role_controls.py) preserve late inputs and premise kinds. These 13 records remain separate from the prior 85 specifications.

[Clean-tail witnesses](../../tests/h62/item2/audit-theories/CleanTailWitnesses.lean) include admitted deployment/entry/write and real transient-reset observations. [Occurrence-based roles](../../scripts/h62/item2/audit-theories/clean_tail_input_roles.py) preserve both same-named anonymous hypotheses and private identity; [corruption controls](../../scripts/h62/item2/audit-theories/check_clean_tail_role_controls.py) reject collapsed or altered inputs.

[Historical acceptance refresh](../../scripts/h62/item2/audit-theories/refresh_history_acceptance.py) regenerates derived ledgers and snapshots from checked proof inputs in a fresh directory. It links no prior summary reports and performs no new Lean proof.

[Reachable-mode witnesses](../../tests/h62/item2/audit-theories/ReachableModeWitnesses.lean) supply whole invariant and persistent-call laws alongside real admitted entries. [Premise accounting](../../scripts/h62/item2/audit-theories/reachable_mode_input_roles.py) and [corruption controls](../../scripts/h62/item2/audit-theories/check_reachable_mode_role_controls.py) preserve all11 original telescopes, including private reset identity.
