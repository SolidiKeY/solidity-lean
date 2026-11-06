# H55 shared fixtures: preparatory census

Status: migration is blocked pending coordinator notices naming current owners,
accepted handoffs and exact transferred files. The original source-path list is
an inventory of inputs, not a write lease. No production migration is claimed.

At base `4d3790eadb8a5212233bc7d5e345817476b2f590`, four V08 controls
(`CreationSuccess`, `Handler`, `LibraryHandler`, `Prefix`) have textually
identical private `extract_failure` proofs. A candidate shared lemma must retain
the exact type and each existing use; its location and imports require owner
agreement and an affected-file timing comparison. `fitting` declarations occur
in many StorageOps controls but their individual contexts and proofs differ:
name matching alone is not evidence that they can share a fixture.

Run `python3 scripts/h55/shared-fixtures/census.py` for a reproducible lexical
inventory of named candidates in V08, backend and lowering StorageOps, and G19 controls. This is a
lead list, not scope-complete acceptance: it does not resolve aliases, compare
statements, discover every near-copy or establish any proof. The initial census omitted `Solidity/Lowering/StorageOps`; that area contains
multiple `uintSyntax` declarations and the Bool/Int/Signed near-copy families.
Its files also require explicit transfer before migration. Each case must
be checked against the original declarations, observations, refusals and
premises; no theorem or case may be dropped to fit a shared abstraction.

The Readonly owner should inspect `run_bind` near-copies in CaptureFailures,
PrimitiveReads, JournalLeaves, EnvironmentCredit, CapturePhases and
EnvironmentSteps. The Yul owner should inspect `capacity_exact` in
ArithmeticVisitorShapesControls, StatementVisitorShapesControls,
WordVisitorShapesControls, ExpressionShapesControls and ShapeCapacityControls,
among other Yul controls. These are outside this lane's current permissions.

Next: obtain exact transferred files and owner agreements, establish identical
bounded pre-change timings, complete each queue item with all affected-module
checks and independent finder/skeptic reviews, then commit the item and export
proof evidence, patch and cache pack. Queue items 2 and 3, reuse/equivalence
backfill, and all production gates remain open. H58 HOLD remains in force.

## Unapplied owner proposal

`scripts/h55/shared-fixtures/extract-failure-owner.patch` is an exact-base
proposal for the four V08 `extract_failure` copies. Its generator checks every
original file byte-for-byte against the base and refuses to run if the proposed
helper already exists. The patch proposes a new same-area helper and edits four
existing controls; neither action is authorized until the coordinator provides
an owner agreement and transfers the exact files. `git apply --check` only
confirms textual applicability. The proposal has not been applied, Lean checked,
timed, reviewed, registered or accepted, and is not a completed queue item.
The declaration inventory is a candidate finder, not the requested
scope-complete acceptance tool; such a tool and owner packets for the other
families remain to be built.
