# Audit theories

The [checker](../../scripts/h55/module-times/theories_audit_witnesses.py) and [fixtures](../../tests/h62/item2/audit-theories/) define the current scope and limitations.

For portable historical evidence, use [paired_evidence.py](../../scripts/h62/item2/audit-theories/paired_evidence.py) and its [corruption controls](../../scripts/h62/item2/audit-theories/check_paired_evidence.py). Certificate designation comes from the committed witness registry; archive integrity checks do not rerun Lean or establish full assignment acceptance.

Missing historical receipts can be reconstructed with [rebuild_frozen_evidence.py](../../scripts/h62/item2/audit-theories/rebuild_frozen_evidence.py). Supply fresh off-git checkout/evidence paths and the toolchain pinned by the original frozen tree. This runs bounded serial checks and census replay; final integration gates remain separate.

[Path premise roles](../../scripts/h62/item2/audit-theories/path_input_roles.py) preserve all 41 frozen telescopes and validate designated joint packets. [Rehashed corruption controls](../../scripts/h62/item2/audit-theories/check_path_role_controls.py) check binder, type and source/owner provenance refusal. These 41 records are separate from the legacy 44-record acceptance snapshot; their disjoint specification union has 85 names.

[Memory-mirror premise roles](../../scripts/h62/item2/audit-theories/mirror_input_roles.py) distinguish logical heap prefixes, universal preservation and selected mirrors. [Corruption controls](../../scripts/h62/item2/audit-theories/check_mirror_role_controls.py) preserve late inputs and premise kinds. These 13 records remain separate from the prior 85 specifications.

[Clean-tail witnesses](../../tests/h62/item2/audit-theories/CleanTailWitnesses.lean) include admitted deployment/entry/write and real transient-reset observations. [Occurrence-based roles](../../scripts/h62/item2/audit-theories/clean_tail_input_roles.py) preserve both same-named anonymous hypotheses and private identity; [corruption controls](../../scripts/h62/item2/audit-theories/check_clean_tail_role_controls.py) reject collapsed or altered inputs.

[Historical acceptance refresh](../../scripts/h62/item2/audit-theories/refresh_history_acceptance.py) regenerates derived ledgers and snapshots from checked proof inputs in a fresh directory. It links no prior summary reports and performs no new Lean proof.

[Reachable-mode witnesses](../../tests/h62/item2/audit-theories/ReachableModeWitnesses.lean) supply whole invariant and persistent-call laws alongside real admitted entries. [Premise accounting](../../scripts/h62/item2/audit-theories/reachable_mode_input_roles.py) and [corruption controls](../../scripts/h62/item2/audit-theories/check_reachable_mode_role_controls.py) preserve all11 original telescopes, including private reset identity.

[Leaf-extension packets](../../tests/h62/item2/audit-theories/LeafProgressWitnesses.lean) preserve full all-horizon premises and distinguish builtin source success from configuration-only emit/error/effect inputs. [Certificate refusal controls](../../scripts/h62/item2/audit-theories/check_leaf_progress_controls.py) require the designated whole-law packet.

[Frozen leaf premise roles](../../scripts/h62/item2/audit-theories/leaf_progress_input_roles.py) run against original history and pin both all-horizon laws. [Rehashed corruption controls](../../scripts/h62/item2/audit-theories/check_leaf_role_controls.py) reject selected-horizon substitutions and altered type, configuration or owner metadata.

[Tuple-progress packets](../../tests/h62/item2/audit-theories/TupleProgressWitnesses.lean) retain exact constructor-required fit proofs alongside slot/fragment and all-lower-horizon laws. [Certificate controls](../../scripts/h62/item2/audit-theories/check_tuple_progress_controls.py) require the complete declaration packet.

[Tuple premise roles](../../scripts/h62/item2/audit-theories/tuple_progress_input_roles.py) distinguish ordinary joint inputs from intentional H69 type separation. [Rehashed controls](../../scripts/h62/item2/audit-theories/check_tuple_role_controls.py) preserve duplicate anonymous hypotheses and late data, and keep classification independent of supplied coverage labels.
