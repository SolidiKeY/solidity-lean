# P8a component metadata composition

Partial checkpoint: checked component composition is implemented, with
nontrivial inheritance control glue delegated under H14. It is not full G15,
G00 approved-profile classification, global imported-name typing or SourceSpec.
The frozen H12 interface remains byte-identical. Revision is this document's
commit; the sealed handoff supplies the exact revision and cumulative exports.

## Typed interface and exact claims

`Solidity.Lowering.P8.SourceMetadata` exports `UnitOK`, `unitCheck`,
`strict_iff`, `unitCheck_iff`, `unitSet`, `ComponentOK`, `metadata`,
`metadata_iff`, `checker`, `metadata_complete`, `checkInput`, `input_sound`,
`every_unit_checked`, and `parsed_units_preserved`.

`UnitOK` is exactly the EXISTING `(WellFormed and InProfileSyntax)`, `StaticOK`
and `InheritanceOK` conjunction. `unitCheck` consumes the existing
`strictMetadataChecker` and `inheritanceChecker`; it changes none of their
judgments or definitions. `strict_iff`/`unitCheck_iff` establish exact decision
for these components. `ComponentOK` adds admitted settings, selected main
membership, `UnitsOK` at empty remappings, and every unit's `UnitOK`.
`metadata_iff`/`metadata_complete` are exact for that conjunction only.

`unitSet` reconstructs source trees from actual packet resolutions.
`parsed_units_preserved` reuses checked resolution uniqueness to prove this
roster is exactly the original checked parser's roster, with order and names.
Standalone metadata does not prove a packet's source origin or environment
coherence. The composed `input_sound` retains raw validity, original-byte
parsing and actual Source.Resolves' before adding the metadata result.
No arbitrary replacement tree/environment can be justified by metadata alone.
No remapping field exists in current raw Input; empty remappings is the
existing component input, not a new source-language exclusion.

`UnitsOK` certifies existing file-level import/name-scope conditions. It does
not make per-unit typing global imported-name typing. No theorem that G00
InProfile implies this check, or that this check is complete admission, is
provided. Existing component checks may be stronger/different from the still
unimplemented whole profile. Do not turn component refusals into silent new
profile exclusions or a public compiler admission theorem.

## Controls and incomplete obligations

The original byte/parse fixtures pass all composed stages under both
pipelines; the two-unit A.sol/B.sol original-byte chain also passes metadata.
The owning frontend's timestamp constant fixture is S01 well formed but is
refused by the existing stricter compile-time constant judgment; its proofs
are reused, not re-proved. A missing import passes exact per-unit resolution
but fails component metadata. Duplicate unit names and an absent main fail.
These are kernel source/metadata controls, not external EVM observations.

Review identified a remaining control gap: nontrivial inheritance success and
an isolated inheritance refusal are not yet exercised by this module. Human
H14 delegates this routine work as M01–M03 in the lane's TERRA-TODO list (not on master),
with exact proposed statements over published InheritanceExamples fixtures.
The strict-before-refusal candidate is UNVALIDATED; do not claim it passed.
The generated `SourceMetadataObligations.lean` contains typed proposition
aliases and a `PendingControls` structure with explicit unimplemented proof
fields. No inhabitant, proved routine control, sorry or axiom is exported.
This is an accurate partial checkpoint, not all-controls or full-lane approval.

Remaining producer obligations: complete approved profile/feature/type/spec
and independent execution/observation-root coverage; global typing/public
checked frontend or importer correspondence; actual executed-target adequacy;
operational failure hooks/rollback/resource consistency, hash/slot preimages
and SourceSpec realization; all mandatory final gates. V16 retains P8b/G01.
S02-IMMUT, SS-CP5-HASHED and SS-NEW remain queued.

## Validation, H14 and handoff

Base: fetched published `91d7b7e60eaf7efb815a9441fafcfb1b0ab2aec0`, which adds P9 override controls and
Source progress proofs. No P8a replacement was present. The helper branch was
rebased, retaining published imports/module map and protected checkpoint
`52b2ca000d32c0de04a39a712d87bf753603f9a2` under
`refs/recovery/p8a/resolutions-52b2ca00`; every older seal is retained.

`timeout 300 lake build Solidity.Lowering.P8.SourceMetadataControls` passed
61 jobs, 4.354 seconds, peak aggregate RSS 800026624 bytes. The new module and
controls reported 1.5/2.3 seconds. No OOM/resource stop. Printed headlines
use only propext, Classical.choice and Quot.sound; no new axiom, native
shortcut, weaker statement or raised proof/test/time/resource budget.
Earlier failed proof elaborations remain failed in exclusive receipts.

The producer proofs were completed before H14 arrived. After H14, no new
manual routine proofs were added. The pending routine signature interface is generated by
`scripts/generate-p8a-metadata-obligations.py`; its typecheck passed 56 jobs,
1.036 seconds, peak aggregate RSS 630603776 bytes. This validates types only,
not truth or inhabitation of the three proposed goals. A failed generated
namespace-alias draft and its exact source remain preserved.
The module registrations are generated by
`scripts/register-p8a-modules.py` under the repository writer lock; model
review checks the generated diff. No new interface freeze was introduced.
Neither Lean MCP/multi-attempt nor `${VM_WORKSPACE}/coord-tools` was available at
checkpoint preparation; no attempted automation is fabricated. Use the
coordinator toolkit once supplied. Routine inheritance controls are relayed
via the lane's TERRA-TODO list and typed explicit obligations, not unproved theorem stubs.

Lean 4.24.0 / Lake 5.0.0-src+797c613, LEAN_NUM_THREADS=1 and explicit -j1,
hard whole-group 12 GiB/no swap, authorized 4 GiB host reserve. Native touched
module checking is the available diagnostic fallback. H12/H14 end-of-lane
full/root/import, combined TrustAudit, TestSuite, corpus, strict/docs/sort
gates remain required; these focused passes do not replace them. Historical
full interruption and documentation failures remain nonpassing.

Independent read-only finder/skeptic used no Lean/server/builds. They found no
source proof/coherence defect; finder requested the still-pending inheritance
controls. Final artifact accuracy review does not approve completion.
Evidence: `${VM_WORKSPACE}/p8a-implementation-20261102-evidence`. No persistent
goal reset/completion, worker push, default-branch edit or controller
integration is claimed. Consumers: V07/V08/V09/V16/V17/VY5.
