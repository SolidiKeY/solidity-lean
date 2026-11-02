# P8a partial schema and resource checkpoint

Revision: this document's commit; the sealed handoff records the full SHA.
Published integration base: `63d3f9232416629146ab2f0a40d756dc9be43845`.
The H12 frozen interface is unchanged. This is not a `P8a.Producer`, a
`SourceSpec` instance, full admission, operational failure semantics, or an
EVM adequacy result.

## Source interfaces and provenance

The coordinator explicitly transferred V16's P8 implementation at
`01f8d3545570304e72bdb8d6b67db762dfefc075`. V07 `Scalar` and
`DeclarationGraph`, P8 `ScalarSchema`, `ShapeSchema`, their controls and
`FieldAdmission` are reused byte-for-byte. No later P6/P9 code is consumed.
The relayed GraphSchema drafts are completed locally, with explicit equality
transport and an explicit find predicate fixing elaboration. Their controls
add memory/storage positives for a fixed wrapper around a dynamic self-node.
The checksum handoff distinguishes exact peer files, adapted files and drafts.

`scalarStruct`, `shapeStruct` and `graphStruct` construct certified singleton
schemas from actual source declaration fields; they do not accept a desired
target certificate as an input. The source declaration must have kind struct.
The result certifies actual declaration identity, lookup, ordered fields and
guarded layout. The producer checks nonempty/distinct fields and a computed
rank. Dynamic recursive nodes and guarded fixed wrappers have positive
controls; inline/fixed-inline self recursion, wrong scope/identity, unresolved
nodes, duplicate fields and memory mappings have negative controls.

`fields_lookup_none`, `fields_distinct_iff` and
`graph_source_fields_distinct` preserve lookup/distinctness through actual
`GraphFieldsRel`. `duplicate_cannot_be_graph_fields` exposes a limitation of
current core well-formedness; it does not redefine the approved profile.
Unsupported producer shapes remain open obligations, not new exclusions.
Multiple-node extraction, general declarations, heap/value execution and G01
lowering correctness remain separate. V16 owns P8b/G01.

`Source.FailureResources.Bound` is the canonical low-level horizon/failure
pair. P8 `FailureResource` aliases it and reuses the projection/replacement
laws. The initial unpublished resource structure is preserved in evidence;
its replacement does not change the frozen H12 signatures. The low-level
module imports only Roadmap.Evm, avoiding a Source-to-P8-to-Session cycle.
`NoFail` characterizes all request/frame schedules, retaining arbitrary
post-fee balances. `no_horizon_retraction` is axiom-free.

`unmodified_forward_obstruction` uses the actual published source language,
whose Forward defaults to True, to refute packaging it unchanged with full
failure replacement and even the necessary clear-frame consequence. This is
an obstruction proof, not an implementation: the evaluator still consumes a
Nat horizon and does not consult these failure points.

The earlier local typed observation traversal is included unchanged in scope:
it covers expression/statement children and supplied roots, not callee closure,
all features, specification observations or whole-program execution roots.
See [admission checkpoint](p8-admission.md) and
[checked syntax/settings](p8a-checked-syntax.md).

## Checks and reviews

All native checks use Lean 4.24.0, Lake 5.0.0-src+797c613, LEAN_NUM_THREADS=1,
explicit -j1, a hard whole-group 12 GiB cap, no swap, and authorized 4 GiB
available-host reserve. Native terminal receipts and logs are retained in
`/workspace/p8a-implementation-20261102-evidence`.

- `timeout 300 lake build Solidity.Lowering.P8.GraphSchemaControls`: exit 0,
  42 jobs, 3.321 s, peak aggregate RSS 731545600 bytes.
- `timeout 300 lake build Solidity.Lowering.P8.ResourceBoundary Solidity.Frontend.Admission.Controls`:
  exit 0, 32 jobs, 3.839 s, peak aggregate RSS 515485696 bytes.
- Final touched targets GraphSchemaControls, FieldAdmission, ResourceBoundary,
  Controls: exit 0, 55 jobs, 4.084 s, peak aggregate RSS 727687168 bytes.
- `timeout 300 lake env lean --tstack=131072 /workspace/p8a-implementation-20261102-evidence/CheckpointAudit.lean`:
  exit 0; only propext, Classical.choice and Quot.sound occur. The horizon
  obstruction and resource replacement laws are axiom-free. Parse soundness
  and settings obstruction use propext only.

Failed missing-import/elaboration attempts remain failed in exclusive logs;
no resource stop occurred in these focused checks. Independent read-only
finder and skeptic used no Lean/server/builds. Their concrete documentation
findings are corrected: current serial Source ownership, exact/adapted peer
provenance, and separate historical/current evidence. Their review is not
final all-gates approval.

H12 defers full end-of-lane gates to lane checkpoints. These focused targets
are not full/root/import, combined TrustAudit, TestSuite or corpus success.
The earlier full run interrupted for H12 remains nonpassing. Historical
documentation failures are not relabeled passed. No source/EVM observations
or semantic/proof/resource budgets changed.

## Still required

Complete execution/observation-root and feature extraction, exact settings and
resolution/admission coverage, public compiler routing or importer agreement,
actual operational failure hooks and rollback/resource consistency, hash/slot
preimage tracing, and a SourceSpec realization remain open P8a work. Parser
completeness/uniqueness and full multi-unit resolution are not supplied here.
S02-IMMUT, SS-CP5-HASHED and SS-NEW remain queued. The persistent goal is not
reset or completed. No worker push or master integration is claimed.
