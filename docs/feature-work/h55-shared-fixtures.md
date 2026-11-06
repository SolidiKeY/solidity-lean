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

`python3 scripts/h55/shared-fixtures/extract_failure_packet.py` emits an exact-base
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

## Conservative baseline audit

`python3 scripts/h55/shared-fixtures/baseline_audit.py PATH...` hashes and
compares every byte of each explicitly named Lean input with the pinned Git
base. It exits nonzero on any difference or invalid input. Identical bytes
cover the whole named file; a changed file requires a separate declaration and
case comparison, kernel checks and independent reviews. This tool does not
infer the assigned scope or establish that a changed statement is equivalent.
It is deliberately incapable of approving a migration by itself.

The Bool/Int deletion examples include distinct encoded values, including
negative signed values; the Bool/Signed copy examples also have differently
sized case sets. A parameterisation needs explicit acceptance for each original
observation and refusal, including empty, short-fuel and static executions.
These examples are leads, not a claim that the family census is complete.

## Full-file review aids

`change_ledger.py` inventories every baseline Lean file in the four areas by
default and partitions all old and current lines into equal, added, deleted or
changed spans with hashes. It exits nonzero if any byte differs. Empty ranges
represent insertions or deletions; line ranges are one-based inclusive and an
empty range has its start one greater than its end. The ledger accounts for
all source lines but does not parse Lean, prove unchanged theorem types, match
cases or approve a migration. Those checks remain required.

`family_inventory.py` scans all baseline Lean files in those areas for the
listed helper, storage, Source execution, declaration and branch signals. It
reports every file, even files with no matching signals, with file hashes and
line locations. It is a lexical lead inventory: comments can match and names
or semantic near-copies can be missed. Full family review and exact case
acceptance remain open. Neither script substitutes for the affected-module Lean
checks or independent finder and skeptic reviews.

H70: V08 world-lowering and V10 storage-operations accepted the owner ticket
relays. Review of the unapplied extract-failure packet is still requested from
those owners; no original-file transfer follows from the relay.

## Uint syntax owner proposal

`uint_syntax_packet.py` emits an unapplied exact-base proposal for 22 identical
private `uintSyntax` definitions in lowering StorageOps, plus a proposed new
same-area helper. It retains each local name and declared type by delegating
its body to the helper; public definitions and non-identical variants are not
included. The generator enumerates the entire baseline directory, verifies
current file bytes and requires exactly 22 textual matches. The proposed helper
and every consumer require owner approval and exact file transfers. The packet
has passed only `git apply --check`; no Lean check, full case acceptance,
performance comparison, registration or independent review has occurred.
It is a proposal for a subset, not completion of the family.

## Storage near-copy case census

`storage_case_census.py` emits baseline file hashes and declaration-block
locations for Bool/Int array deletion, Bool/Signed dynamic copy, and Bool fixed
copy source/target controls. The Bool deletion controls contain theorems named
`word_agrees` and `false_and_absent` that the Int file does not. The census
reports all matched theorem names and asymmetries for the selected pairs;
common names do not establish equal statements or cases. It is a lexical
review aid, not a complete semantic census or acceptance of the family.

## Snapshot initial owner proposal

`snapshot_initial_packet.py` emits an unapplied exact-base proposal for the
identical private `initial` definitions in PrimitiveSnapshotDependent,
PrimitiveSnapshotRepeat and PrimitiveSnapshotSequence controls, with a
parameterised same-area helper. Local declared types and the bodies of the
fixtures are retained in the proposal. The generator checks original bytes;
`git apply --check` is textual only. The helper, consumer files, import,
proof reducibility, timing and registration all need owner agreement and Lean
checks. No completeness claim is made for other initial/frame fixtures.

## Array deletion semantic review (partial)

Manual reading of the Bool and Int array-deletion controls identifies these
original public observations that any shared parameterisation must preserve:

| Declaration | Original cases or observations to retain |
|---|---|
| `certificate` | Ordered Source child clears and header clear, actual EVM run, representation and transport, all listed target/source words, and query readbacks. Bool and Int instantiate different primitive types. |
| `ordered` | Complete Source, graph, numeric and target before/after vectors, including retained older elements and journal length 4. Int retains the encoded negative values; Bool retains its true values. |
| `full_target_context` | Exact equality of the full target context before and after. |
| `empty_retained` | Already-empty Source and target run, retained before/after vectors and journal length 2. |
| `fuel_static` | Short fuel times out with the specified partial Source view and journal length 1; a static delete reverts with the initial state. |
| `live_alias_restore` | Live alias read after deletion, out-of-bounds reindexing and exact panic bytes, plus rollback to the original state. |
| `wrong_extent` | Actual wrong-header target execution, complete correct/wrong target vectors and mismatch with the retained Source value. |
| `readbacks_presence` | Source header and retained-element reads, absent storage cells, and actual target read execution. |
| Bool `false_and_absent` | Distinguishes an explicitly stored false from absence after partial deletion, while retaining true at another position. There is no theorem of this name in the Int controls. |

This is a review of those named public statements only. Private helper facts,
all other declarations, full signed-copy/fixed-copy families, proofs, and
exact statement equivalence after a migration remain to be audited. The case
matrix is not an acceptance result.
