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

## Dynamic storage-copy semantic review (partial)

Manual reading of the public Bool and Signed dynamic-copy controls gives the
following original obligations. These remain separate statements and cases
unless a later, checked migration preserves each one exactly.

| Declaration | Original observations to preserve |
|---|---|
| `certificate` | Ordered Source copy log, actual target run, represented overlay and numeric transport, every listed Source/target cell and query readback. Bool and Signed instantiate different element types. |
| `ordered` | Complete Source, graph, numeric and target before/after vectors and journal length 4, including the retained older element. The Signed vector contains negative encoded words. |
| `full_target_context` | Exact equality of target context before and after the target run. |
| `grow_certificate`, `empty_certificate` | Actual Source and target executions for growth and empty source, with the header and all four specified element comparisons. |
| `varied_ordered` | Complete Source and target vectors for growth and empty-source cases, including journal lengths 4 and 5 and retained older words. |
| `bad_old_agreements` | Two actual target runs independently distinguish an incorrect retained older word and an incorrect payload word, both before and after the copy. Signed uses wrong positive magnitudes against negative encodings. |
| `readbacks` | Actual Source header and element reads and actual target reads for header, copied, cleared and retained positions. |
| Bool `absent_and_false` | Raw absence versus explicitly present false, typed default read and canonical false/true words. |
| Bool `fuel_static` | Timeout retains the specified partial write prefix and journal length 1; static execution reverts at the initial state. The theorem does not claim rollback for the timeout. |
| Bool `live_alias` | Alias remains readable after copy while a fresh index operation fails with the exact index-panic data. |
| Signed `signed_words_presence` | The two negative words have values `2^256-17` and `2^256-71`; preserve absent zero, explicitly stored zero, cleared absence and the retained negative read. |

This covers the named public statements in these two files only. It does not
review every private fact, all related files, or an actual replacement proof;
it is not scope-complete acceptance.

## Fixed Bool storage-copy semantic review (partial)

The following records the named public statements in the Bool fixed-copy
Source and target control files. Their shared names are not evidence of equal
statement types, and every original observation remains an acceptance obligation.

| File and declaration | Original observations to preserve |
|---|---|
| Source `certificate`, `ordered`, `source_context` | Actual Source copy log, complete before/after views with journal length 3, and exact Source context equality. |
| Source `no_dynamic_header` | Both fixed roots have absent cells and no words; dynamic length reads and the wrong dynamic interpretation fail with the stated stuck result. |
| Source `live_fixed_alias` | The same live fixed alias reads true before and false after copy; index 3 reverts with exact panic data, while direct read of retained position 3 remains true. |
| Source `fuel_static` | Timeout preserves the specified partial view with journal length 2; static copy reverts with initial state. |
| Source `malformed_source` | Missing-value and wrong-cell-type failures retain their distinct stuck messages and initial state. |
| Source `snapshot_order` | Actual memory load followed by captured versus fresh copies yields the two specified complete views, each with journal length 4. |
| Source `same_path`, `explicit_restore` | Self-copy succeeds unchanged even under static mode; explicit rollback of the ordinary copy restores the initial state. |
| Source `false_presence` | Preserve absent versus present false cells and the alias's before/after true-to-false reads. |
| Target `certificate`, `source_ordered` | Actual Source log and target execution, selected word agreements, complete Source before/after views and Source context equality. |
| Target `target_ordered`, `selected_ordered`, `root_presence` | Complete target vectors and non-store context, selected-order readbacks including repeats and outside positions, and fixed roots with no Source words. |
| Target `required_old_agreements`, `wrong_execution`, `wrong_ordered` | Independently refute wrong old source and retained-position agreements; execute both target cases and preserve their complete old/result target vectors and Source mismatches. |
| Target `false_presence` | Source absence and present false remain distinct while both selected target words are zero. |

This matrix covers named public statements in these two controls only. Private
facts, other families, all replacement proofs and exact statement comparison
remain open; the matrix is not a proof or scope-complete acceptance.

## Literal-failure Source/static semantic review (partial)

Manual review of three V08 controls identifies the following original public
facts and distinct static-frame behavior. The list records preservation
obligations, not proof of a proposed shared fixture.

| Control and declarations | Original observations and premises to retain |
|---|---|
| BoolPrefix `member`, `typed`, `related`, `lookups`, `expression_lookups`, `fields` | Declaration membership and typing, argument/heap lookups and StringBytes/representation witnesses; `fields` retains its explicit heap lookup premise. |
| BoolPrefix `actual_error`, `actual_expression` | The same heap premise yields the exact custom-error revert packet and unchanged state, versus successful ABI expression allocation at memory reference 4 with the specified `afterLiteral` state. |
| BoolPrefix `retained`, `older`, `unused_third`, `fresh` | Preserve represented fields after allocation, the older bytes object, the unused third string, the new object at 4 and cursor 5. |
| BoolPrefix `alias_error`, `timeout`, `dangling_error`, `dangling_expression`, `wrong_cursor` | Preserve the aliased first-string packet, timeout at fuel 1, distinct stuck dangling-reference outcomes for statement and expression, unchanged states, and cursor inequality. |
| BoolPrefix `static_error` | With `static := true`, this pure custom-error statement still reverts with the exact packet and unchanged state; it is not a generic static-write refusal. |
| BoolPrefix `packed_bool`, `packed_uint`, `packed_unequal` | Actual packed Bool and uint encodings remain distinct. |
| MixedEncoding `represented`, `arguments_run`, `body_return`, `extracted` | Keep the four-field representation and exact argument/tuple-return states; `arguments_run` and `body_return` quantify over both values of `static`. |
| MixedEncoding `encoding`, `transport`, `finite_fits`, `finite_transport` | Encoding applies at arbitrary frame/fuel; transport retains its explicit `Failure.Fits 8` premise, and the finite witness uses the 256-byte packet and physical world journal. |
| MixedEncoding `old_alias`, `repeated_alias` | Preserve the old return-slot reference and the repeated dynamic reference with its duplicated bytes representation. |
| MixedEncoding `wrong_order`, `first_offset`, `second_offset`, `empty_encoding`, `wrong_head` | Preserve the unequal order control, concrete offsets 128 and 192, empty encoding, and rejected head offset 64. The five `packets` and printed observations are separate original controls. |
| ScalarOverflow `overflow_bound`, `populated` | Maximum plus one reaches the 256-bit bound; the actual checked Source `evalE` and guarded scalar execution both fail with arithmetic panic for either `static` value, retaining the stated Source state. |
| ScalarOverflow `retained_operands`, `raw_zero`, `positive_baseline`, `no_success_on_overflow` | Retain the test stack operands, distinguish the unchecked raw zero body from the guarded failure, preserve the positive 1+1 result and the explicit no-success observation. |

This is not a review of all Source/static families or of every original
private declaration and emitted observation. It does not establish exact
statement preservation or discharge any Lean gate.

## Transient emit Source/static semantic review (partial)

The following records the named public statements in SourceTransientEmit and
SourceTransientEmitPanic controls. Pipeline and fuel quantifiers, frame updates,
reached states and exact failure data are part of the original obligations.

| Control and declarations | Original observations to preserve |
|---|---|
| Emit `assignment_statement`, `arguments_reached`, `encoding_reached`, `emit_reached`, `sequence_complete` | Actual transient-write prefix, argument evaluation, encoding, direct emit and full item sequence, including the false local and reached intermediate states. Argument/encoding facts quantify over `static`. |
| Emit `direct_static`, `prefix_static_refusal`, `static_boundary_contrast` | Direct static emit runs its arguments and encoding then reverts at `afterArgs`; the static prefix refuses at `opening`. Heap cursors differ, 2 versus 1. |
| Emit `zero_horizon`, `direct_argument_timeout`, `prefix_argument_timeout` | Distinct timeout horizons and exact states: zero remains at opening, direct argument timeout stays written, prefixed argument timeout reaches written. |
| Emit reordered argument, encoding, emit and sequence theorems; `wrong_actual_order` | Preserve the actual reordered reached states and the inequality of original versus reordered execution. |
| Emit `complete_vector`, `payload_observation` | Preserve all specified account balances, storage/transient reads, journal/heap fields, events, log payload and local fields; retain selector plus exact hash/word encoding. |
| Emit `erased_execution`, `erased_not_opening` | Log erasure yields the stated reached state but not opening; heap allocation remains observable. |
| Emit `rollback_execution_component`, `rollback_logged`, `rollback_static`, `wrong_automatic_rollback` | Preserve explicit journal rollback equations and the negative automatic-rollback control. Source heap and logs are not claimed to roll back. |
| Emit `end_fields`, `end_reads` | End-execution clears the journal and transient reads for both owners while preserving the specified world, heap, event, log and local fields. |
| Panic `arguments_reached`, `direct_panic`, `items_panic`, `intrinsic_payload` | Argument failure occurs after the reached write/hash prefix, with exact division-by-zero panic bytes and `afterArgs`; direct failure holds for either static flag. |
| Panic `decoder_observation`, `wrong_empty_payload`, `wrong_assert_payload` | Decoder observes code `0x12`; empty and assertion panic payloads are distinct. The decoder is an observation, not a Source catch or frame adequacy theorem. |
| Panic `prefix_static_refusal`, `zero_timeout`, `wrong_before_hash` | Static prefix refuses at opening; zero horizon times out at opening; direct panic cannot be replaced by the pre-hash written state. |
| Panic `complete_vector`, `rollback_after_panic`, `end_fields`, `end_reads`, `erased_failure` | Preserve the complete reached account/transient/heap/log vector, explicit journal-only rollback, end-execution fields and reads, and erased-log failure observation. No automatic rollback or EVM log adequacy is asserted. |

This is a partial manual review of named public statements in two controls;
other Source/static files, private declarations, exact post-migration
statements and all Lean gates remain open.

## H82 retirement handoff

H82 permits statement-preserving proof-only, additive, split, import and
prose changes without exact-file owner agreement. The previous requests for
such agreement are withdrawn. Owner review remains necessary before changing
an existing statement, a definition body on which a statement depends, an
interface, budget, axiom set or exclusion; H57 versioning applies to frozen
interfaces. The proposed `uintSyntax` and snapshot-initial packets replace
existing definition bodies used by statements and therefore still require the
relevant owner decision. No original source migration has been applied.

The serial V08 baseline build started under the writer lock with Lean `-j1`,
`LEAN_NUM_THREADS=1`, no swap and a 10 GiB virtual-memory bound, and was
interrupted for the retirement instruction. Its partial log is not a passing
baseline or timing gate. All original queue items and backfill, complete
semantic acceptance, proof and timing checks, independent finder/skeptic
reviews, and registration fragments remain outstanding. The surviving lane
is `solidity-h62-2-20261106/audit-readonly-calls`.
