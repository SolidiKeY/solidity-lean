# H55 shared fixtures: preparatory census

**Current status:** The coordinator resumed this lane after the H82 retirement
handoff and master integration. The V08 `extract_failure` proof-only subset is
now implemented as described at the end of this document; earlier owner-lease
and unapplied-packet notes below are historical. Independent review and the
rest of the ordered queue remain open.

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


## Resumed V08 extract-failure subset (review pending)

At integrated baseline `5f14596531efea2be64f1a5e7a83afa5e151e865`, four
V08 controls contained identical private `extract_failure` proofs. They now
use `Solidity.Lowering.V08.SharedFailureFixture.extract_failure`. For each
file, removing the added import, restoring the original unqualified proof
references, and removing the original private helper from the baseline leaves
every remaining byte identical. This includes all public statements and
observations, but does not complete the broader shared-fixtures item.

Lean 4.24.0 / Lake 5.0.0, one Lean process, `-j1`, `LEAN_NUM_THREADS=1`,
10 GiB virtual-memory limit and no swap were used. KeySort passed. The
changed import chain and all four full affected files passed. Baseline/after
wall times in seconds: Handler 7.130/6.922; LibraryHandler 5.970/5.954;
CreationSuccess 5.333/5.432; Prefix 30.985/30.059. No measured file exceeded
10% slowdown. Existing printed diagnostics and axiom reports were identical
before/after after removing timing lines; the shared helper reports no axioms.
These are kernel Lean checks, not external behavioral tests. Evidence hashes
are in `tests/h55/shared-fixtures/extract-failure-evidence.sha256`; the logs
remain off Git on the VM. A missing cached KeySort OLean caused the first
direct baseline attempt to fail before elaboration; four missing OLeans were
restored from hashes in Lake traces before the passing checks.

Central integration registration fragments (do not edit generated roots/maps):

```lean
import Solidity.Lowering.V08.SharedFailureFixture
```

```markdown
| `Lowering/V08/SharedFailureFixture.lean` | Shared failure extraction for V08 control proofs. |
```

Independent read-only finder and skeptic reviews, complete axiom audit and the
full item-1 census/acceptance remain pending. No milestone or whole-goal
completion is claimed. Later queue items, backfill and final gates also remain
open. H82 owner decisions remain required for proposed changes to definition
bodies on which statements depend.

## Fitting helper attempt: return to Sol

An exploratory generic `fitsBool` helper checked root, data and hash key
bounds; its first probe failed because `Bool.and_eq_true.mp` is not a lemma,
then a corrected probe using `Bool.and_eq_true_iff.mp` passed, including a
mixed root/data/hash example. Four original snapshot controls and their
baseline timings passed. The attempted helper in the nested production
namespace then failed to build because unqualified `Loc` resolved to
`Solidity.Loc` rather than `Solidity.Storage.Loc`. Lean's `sorry` warnings in
that error log are elaborator recovery diagnostics; no source `sorry` was
introduced. Treating the two failed probes/build attempts conservatively under
the Terra two-failure rule, return this fitting attempt to Sol. The attempted
consumer diff and helper are preserved off Git as
`/workspace/h55-shared-fixtures-evidence/fitting-failed-consumers.patch` and
`/workspace/h55-shared-fixtures-evidence/fitting-failed-helper.lean`; all four
uncommitted consumer edits and the helper were removed from the worktree. The
prior extract-failure checkpoint is unaffected. No fitting proof, after timing,
review or acceptance is claimed.

## Extract-failure equivalence backfill

`tests/h55/shared-fixtures/ExtractFailureEquivalence.lean` retains the original
proof locally, applies the shared theorem at the exact original statement and
proves equality of the two proofs by proof irrelevance for arbitrary inputs.
`lake env lean -j1 --tstack=131072` passed with Lean 4.24.0; both public
backfill theorems reported no axioms. This is a kernel check of this helper's
reuse and proof equivalence, not an external behavioral test, independent
review or full-scope acceptance of item 1. Evidence remains off Git at
`/workspace/h55-shared-fixtures-evidence/extract-equivalence.log`.

### Extract-failure declaration comparison

`ExtractFailureDeclarationAudit.lean` inventories every kernel constant
belonging to the four affected modules, including private and generated
constants. Each record includes its elaborated type expression, universe
parameters, axiom dependencies and safety flags. The exact baseline modules
were compiled in a separate artifact overlay using the original sources and
unchanged dependency OLeans. `compare_extract_declarations.py` compared these
against the changed modules: 608 original constants, 604 changed constants,
exactly four removed private `extract_failure` constants, no additions and no
other changed records. The shared replacement separately reports no axioms and
its original statement/proof-equivalence controls passed. This checks all
kernel constants in these four modules, not every module or family in item 1;
independent finder/skeptic reviews and the broader item acceptance still remain.
Large inventories are off Git and hashed in the evidence manifest.

The declaration comparator pins per-module baseline and changed counts for this
exact baseline and rejects duplicate or missing rows. Its negative controls
confirmed rejection of altered elaborated types, changed axiom sets, removed
rows and duplicate rows; the real inventories pass. Counts must be re-derived
from the compiled baseline if the underlying source scope changes.

## Source ABI entry semantic review (partial)

Manual review of the public statements in `SourceAbiEntryControls.lean`
records these obligations for any shared Source/static fixture. They concern
entry decoding and exact reached Source state; they do not assert general ABI
adequacy or injectivity of the mixed byte observation.

| Declarations | Original observations and premises to preserve |
|---|---|
| `observeResult_injective`, `observeBytes_injective` | Injectivity of the two explicitly defined observation functions over their stated result types. |
| `binary_eager`, `empty_eager`, `long33_eager`, `input_sizes` | Eagerly decode the exact binary, empty and 33-byte inputs; their selector-inclusive input sizes are 100, 68 and 132 respectively. |
| `binary_lazy`, `empty_lazy`, `long33_lazy`, `binary_reference` | Preserve existential lazy references and actual lazy reads for all three inputs; the concrete binary reference is `(68,3)`. |
| `binary_source_entry` | For either pipeline and either static value, preserve the actual Source expression result, memory reference 1, exact allocated heap bytes, eager decoding and lazy reference/read witness. |
| `shifted_head`, `truncated_data`, `wrong_decoded_bytes`, `wrong_reference` | Preserve the shifted-head and wrong-value inequalities, actual truncation revert, and exclusion of reference `(36,3)`. |
| `mixed_entry`, `mixed_input_bytes`, `mixed_heap_object`, `mixed_effects_and_entry` | Preserve the three-branch decoder observation, exact selector-stripped bytes and allocated heap object; the combined Source/decoder fact includes reached effects and quantifies over both static values. |
| `mixed_second_reference`, `wrong_argument_order`, `packed_not_entry` | Preserve the `(260,33)` reference, distinguish reversed argument order, and retain the actual revert verdict for packed data interpreted as canonical entry data. |

The selected file's named public statements are reviewed here; other ABI and
Source/static families, private/generated declarations, exact migrated
statements, independent reviews and all broader acceptance gates remain open.

## Source ABI expression semantic review (partial)

The public statements in `SourceAbiControls.lean` cover several related
families; any future shared frame fixture must retain their original quantified
pipeline/static/packing inputs and exact reached states.

| Declarations | Original observations to preserve |
|---|---|
| `literal_complete`, `literal_vector`, `empty_binary_unaligned_lengths`, `literal_cases` | Actual Source evaluation for arbitrary bytes and both static/packed flags; complete world, transient, journal and heap vector; empty, binary and 33-byte cases with standard lengths 64, 96 and 128. |
| `arguments_execute`, `digest_word`, `digestWord_eq`, `encoding_execute`, `mixed_complete`, `mixed_vector` | Reached local assignment and hash/allocation effects, exact digest word, packed/standard encoding, result reference 2 and complete final vector. |
| `reversed_execution`, `complete_offset_words`, `mixed_standard_offsets`, `reversed_standard_offsets`, `different_ordered_bytes` | Actual reversed execution and distinct ordered bytes, including offset words 160, 224 and 256. |
| `insufficient_after_effects`, `wrong_stale_pointer`, `wrong_skipped_hash`, `wrong_returned_locals`, `actual_different_order`, `actual_different_packing`, `mixed_lengths` | Timeout after the local effect, distinct wrong pointers/effects/locals, actual order and packing inequalities, and standard/packed lengths 320 and 70. |
| `selector_value_bytes`, `selector_drop`, `selector_byte_at`, selector/signature argument and completion facts | Exact selector bytes and indexed prefix behavior; actual selector/signature Source executions preserve reached argument effects and output reference 2 for either static value. |
| `empty_signature_prefix`, `prefixed_complete_vector`, `prefixed_offsets_and_length`, `prefixed_values_encoding` | Preserve the checked empty-hash prefix, complete prefixed vector, total length 324 and specified offsets, and the encoding equation at arbitrary horizon. |
| `prefixed_timeout_after_effects`, `prefixed_zero_horizon`, `wrong_selector_bytes`, `wrong_signature_prefix`, `prefixed_wrong_pointer`, `prefixed_skipped_effects` | Distinguish the reached-effect timeout from zero-horizon timeout and retain each negative selector, signature, pointer and skipped-effect control. |
| `memory_signature_arguments`, `memory_signature_complete`, `memory_signature_vector`, `selector_reversed_complete`, `actual_prefixed_different_order`, `memory_signature_wrong_pointer` | Preserve the additional signature-memory allocation and reference 3, its complete vector, reordered selector behavior and wrong-pointer/order inequalities. |
| `selector_argsOK`, `signature_argsOK`, `memory_signature_argsOK`, `overlong_selector_not_argsOK` | Preserve the three accepted typing observations and the explicit overlong-selector rejection. |
| `source_transient_write`, `source_transient_read`, `source_transient_read_end`, `source_transient_rollback`, `source_transient_static_after_effect`, `source_transient_zero_horizon`, `source_transient_complete_vector` | Preserve actual Source write/read/reset and explicit undo, static refusal after the RHS local effect, timeout, and complete account/journal/heap/event/log vector. |
| `intrinsic_transient_write`, `intrinsic_transient_reset`, `intrinsic_selected_reset`, `wrong_source_stale_transient`, `wrong_intrinsic_stale_transient`, `wrong_transient_payload` | Retain intrinsic write/reset observations, the generic typed-path reset instantiation and the three negative controls; no canonical Source-to-contract layout relation is inferred. |

This matrix records named public statements in this one file. It does not
establish the complete cross-family census, private/generated case acceptance,
or any post-migration proof or independent review.

### Source ABI kernel declaration baseline

`tests/h55/shared-fixtures/SourceAbiDeclarationAudit.lean` inventories every
kernel constant owned by `SourceAbiControls` and `SourceAbiEntryControls`,
including private/generated constants, elaborated type expressions, universe
parameters, axiom dependencies and safety flags. The serial Lean 4.24.0 run
at integrated baseline `5f14596531efea2be64f1a5e7a83afa5e151e865` recorded 131
and 52 constants respectively. Those two source files are unchanged from the
original base. The off-Git JSONL and the exact source/OLean inputs are hashed in
`tests/h55/shared-fixtures/source-abi-evidence.sha256`. This establishes a
comparison baseline for these modules only; it is not a migrated-source check,
case-equivalence proof, independent review or complete original-scope census.

### V08 Source-execution candidate declaration baseline

`source_exec_inventory.py` selects the 74 original V08 `*Controls.lean` files
containing lexical `execS` or `evalE` references, and verifies each selected
source byte-for-byte against the original base. All 74 candidate modules built
serially under Lean 4.24.0. `generate_source_exec_audits.py` generated ten
small serial Lean batches, which recorded 3,103 owned kernel constants (2,083
theorems), with elaborated type expressions, universe parameters, axiom
dependencies and safety flags. `summarize_source_exec_audits.py` verified all
74 modules are present without duplicate declaration rows. No declaration was
flagged unsafe or as an axiom. Two original generated declarations have the
`partial` flag: `BoolErrorControls.parameters._unsafe_rec` and
`LiteralFailureDynamicListErrorControls.parameters._unsafe_rec`; both recorded
empty axiom lists. These are baseline observations, not newly introduced facts.

The batch sources, JSONL outputs, build log and module inputs are off Git and
hashed in `tests/h55/shared-fixtures/source-exec-evidence.sha256`. This lexical
candidate set can include comments and miss indirect execution calls. It is
not the entire original Source family, semantic case review, a comparison with
future migrations, independent review or completion of any queue item.

The second Source-execution inventory additionally records elaborated bodies
of 1,020 non-theorem constants, so a later comparison can detect changed
existing definitions as well as declaration types, universe parameters,
axioms and safety flags. `compare_source_exec.py` checks the pinned 3,103-row
baseline and 74-module coverage, rejects removed or modified original records
and newly added unsafe/partial/axiom declarations, and reports safe additions.
Its negative controls exercise changed types, definition bodies and axiom sets,
removals and an unsafe addition; its self-comparison passed. This is an exact
kernel-record comparison for this lexical candidate set, not semantic case
acceptance for all assigned families or approval of owner-sensitive changes.

## Fitting declaration census: resource stop

`fitting_inventory.py` selected 34 original StorageOps controls with a named
`fitting` declaration (26 backend, 8 lowering), and verified their source bytes
against the original base. All 34 original modules built serially. An
8-module Lean declaration/body audit then failed with `INTERNAL PANIC: out of
memory` under the existing 10 GiB virtual-memory cap. Reducing to one module
allowed the first two audits to pass, but `FreshDefaultPushControls` also ran
out of memory at the same cap. Both failures are preserved off Git and the cap
was not raised. The first two per-module outputs are partial census evidence;
32 selected modules remain unaudited by this harness. Conservatively return
this resource-limited fitting census to Sol under the two-failure rule, along
with the earlier failed fitting implementation attempt. This is not a proof,
performance pass, source migration or scope-complete acceptance. No unchanged
failing configuration should be rerun. The off-Git logs, generated audit
sources and successful outputs are hashed in
`tests/h55/shared-fixtures/fitting-census-evidence.sha256`.

## Transient dynamic-bytes and mixed-rethrow review (partial)

The named public statements in `SourceTransientBytesEmitControls` and
`SourceTransientMixedRethrowControls` retain the following distinct Source
execution and static-frame observations.

| Control and declarations | Original observations to preserve |
|---|---|
| Bytes emit `bytes_event_member`, `arguments_reached`, `memory_reached`, `encoding_reached`, `emit_reached`, `sequence_complete` | Actual event membership, argument allocation at reference 1, exact old/new heap objects, ABI encoding, direct emit and prefixed sequence for arbitrary bytes. Argument/encoding facts quantify over static mode. |
| Bytes emit `direct_static`, `prefix_static_refusal`, `static_boundary_contrast` | Direct static emit allocates its argument then reverts at `afterArgument`; the static prefix refuses at `opening`; their heap cursors are 2 and 1. |
| Bytes emit `zero_timeout`, `prefix_argument_timeout` | Preserve zero-horizon timeout at opening and argument timeout after the prefix at written. |
| Bytes emit `payload_transport`, `complete_vector`, `boundary_cases`, `boundary_lengths`, `actual_payload` | Preserve selector plus ABI head/length/padding, complete account/transient/journal/heap/log vector, actual empty/binary/33-byte executions and lengths 64/96/128. |
| Bytes emit `wrong_length`, `wrong_padding`, `wrong_byte_order`, `stale_reached`, `fresh_not_stale`, `wrong_reference`, `dangling_error` | Preserve each wrong-payload inequality, valid stale reference 0 versus fresh reference 1, wrong-reference inequality and the explicit malformed dangling-reference failure for either static flag. |
| Bytes emit `erased_execution`, `rollback_logged`, `wrong_automatic_rollback`, `end_fields`, `end_reads` | Preserve log erasure, explicit journal rollback, negative automatic-rollback observation and end-execution field/read behavior; no automatic heap/log rollback is inferred. |
| Mixed rethrow `arguments_reached`, `encoding_reached`, `expression_reached`, `declaration_reached`, `sequence_complete` | Preserve argument effects at the reached transient state, packed/standard encoding, allocated reference 2, declaration state and exact rethrown bytes. |
| Mixed rethrow `static_before_arguments`, `argument_timeout`, `sequence_timeout` | Static prefix refuses at opening; the argument and sequence timeout cases retain their distinct written/local states. |
| Mixed rethrow `complete_vector`, `rollback_complete_state`, `end_fields`, `transient_reads` | Preserve complete account/transient/journal/heap/log vector, explicit journal rollback and actual pre/post end-execution reads for both owners. |
| Mixed rethrow `wrong_original_base`, `wrong_reversed_payload` | Preserve the negative controls distinguishing the reached journal base and reversed standard-encoding payload. |

This matrix covers the named public statements of these two files only;
private/generated declarations, the rest of the Source families and exact
post-migration acceptance remain open.

### G19 execution candidate declaration baseline

The exact G19 original assignment list remains unestablished. As a read-only
superset lead, `g19_exec_inventory.py` selected 18 original G19 controls with
lexical `execS`/`evalE` references and verified their source bytes against the
original base. All 18 modules built serially. One-module audit batches recorded
240 owned kernel constants, 128 theorems and 112 non-theorem values, including
elaborated types, definition bodies, universes, axiom dependencies and
safety flags; none were flagged unsafe, partial or axiom declarations.
`compare_g19_exec.py` self-comparison and negative controls for changed type,
body and axiom sets, removal and unsafe addition passed. The build, generated
batches, records and module inputs are hashed off Git in
`tests/h55/shared-fixtures/g19-exec-evidence.sha256`. This is not an exact G19
scope determination, semantic case review, migrated-code acceptance or
independent review. All original G19 scope and final gates remain open.

## Source custom-error semantic review (partial)

The named public statements in `SourceCustomErrorControls` and
`SourceCustomErrorFailureControls` preserve these actual Source observations;
all stated pipeline, static and horizon parameters remain part of the facts.

| Declarations | Original observations to preserve |
|---|---|
| Custom-error `populated_snapshot`, `error_member`, `assign_false`, `read_false` | Complete initial account/transient/journal/heap/event/log snapshot, declaration membership, and actual local assignment/read for arbitrary state and static mode. |
| `arguments_execute`, `encoding_execute`, `signature_utf8`, `signature_bytes` | Reached local/hash effects, exact converted values and encoding, and exact UTF-8 signature bytes. |
| `actual_execution`, `intrinsic_selector_payload`, `encoded_length`, `exact_payload_length`, `complete_machine` | Actual custom-error revert and reached state for either static mode, intrinsic selector transport, 96-byte body and 100-byte payload, and retained machine/heap observations. |
| `zero_horizon`, reversed argument/encoding/execution facts, `wrong_argument_order`, `static_is_not_plain_revert`, `argument_timeout`, `panic_before_payload` | Preserve distinct timeout, reordered-value inequality, nonempty static custom-error payload and division-by-zero panic before error-payload construction. |
| Failure `converted_hash_head`, `changed_local_tail_failure`, `argument_prefix_then_failure`, `argument_failure_boundary`, `observed_argument_failure`, `wrong_argument_reset` | Preserve the hash allocation and changed local before panic, actual statement boundary and `EM.attempt` observation, and inequality from the original unallocated state. |
| Failure `nested_panic_execution`, `nested_timeout`, `nested_intrinsic_panic_bytes`, `rethrow_binary`, `observed_rethrow`, `wrong_truncated_selector`, `rethrow_not_panic` | Preserve nested panic versus timeout, intrinsic panic code 0x12 bytes, actual binary rethrow and attempt observation, truncated-selector inequality and the rethrow/panic distinction. No catch-dispatch claim is added. |
| Failure `record_populated_snapshot`, `record_members`, `record_arguments`, `record_encoding_failure`, `record_execution_failure`, `record_complete_state` | Preserve the record environment and membership, reached local/heap effects, exact stuck `not ABI-encodable` result, and all recorded state and heap objects. |
| Failure `wrong_encoding_rollback`, `encoding_failure_not_plain_revert`, `record_zero_horizon` | Preserve the negative automatic-reset and plain-revert controls, and zero-horizon timeout at the initial state. |

This records named public statements in these two controls only, not the
complete cross-family census, all private/generated cases or any migrated
statement acceptance. The existing kernel Source candidate inventories remain
baseline evidence, not independent review.

### Complete original V08 control-file baseline partition

`verify_v08_coverage.py` checks that all 106 original V08 `*Controls.lean`
files partition into the 74 lexical Source-execution candidates, 28 other
unchanged controls, and the four extract-failure controls compared before and
after. The 28 unchanged controls built and were inventoried one module at a
time: 999 owned kernel constants, 604 theorems and 395 non-theorem values;
none were flagged unsafe, partial or axiom declarations. The generated
`compare_v08_remaining.py` self-comparison and type/body/axiom/removal/unsafe
addition negative controls passed. Build and audit files remain off Git, hashed
in `tests/h55/shared-fixtures/v08-remaining-evidence.sha256`.

This establishes a kernel declaration/body baseline across the 106 original
V08 control files, with the four changed files compared separately. It is not
semantic review of all cases, the whole assignment's exact scope, independent
review, or acceptance of future changes; non-control modules and other areas
remain outside this particular partition.

## Remaining backend control census: resource stop

`backend_remaining_inventory.py` selected 58 original backend controls outside
the 26 named fitting candidates and checked their source bytes against the
original base. All 58 modules built serially. Their one-module kernel
expression audits then passed for 20 modules, but `GraphRetainedCycleControls`
and `LifecyclePathControls` independently hit `INTERNAL PANIC: out of memory`
under the unchanged 10 GiB virtual-memory cap. The run stopped after the two
failures; 36 candidates were not audited. No cap was increased and neither
failed configuration should be rerun unchanged. Return this backend-census
remainder to Sol alongside the fitting census and implementation attempts.
The successful partial outputs, failure logs, generated batch files and build
log are off Git and hashed in
`tests/h55/shared-fixtures/backend-remaining-evidence.sha256`. This is not a
complete backend semantic census, full declaration audit, performance pass or
acceptance of any migration.

## Source emit semantic review (partial)

The named public statements in `SourceEmitControls` retain the following
Source behavior for their stated pipeline, static and horizon parameters:

| Declarations | Original observations to preserve |
|---|---|
| `populated_snapshot`, `event_member`, `assign_false`, `read_false` | Complete initial world/transient/journal/heap/event/log snapshot, event membership and actual local assignment/read for arbitrary state and static mode. |
| `arguments_execute`, `encoding_execute`, `emit_execute` | Ordered converted arguments, local and hash-allocation effects, exact encoded bytes and actual successful emit with its reached logged state. |
| `static_after_effects`, `retained_after_static`, `erased_success_retains_effects`, `wrong_static_snapshot` | Direct static emit refuses only after the actual argument/encoding effects; preserve the reached heap and other state fields, the log-erasure observation and the inequality from the original populated snapshot. |
| `zero_horizon`, `argument_timeout` | Distinct zero-horizon and positive-horizon argument timeouts at the stated initial state. |
| `reordered_arguments_execute`, `reordered_encoding_execute`, `exact_ordered_bytes`, `wrong_argument_order`, `reordered_emit_execute`, `wrong_ordered_execution` | Preserve changed argument order and the exact zero/one word ordering, plus inequality of the actual logged executions. |
| `panic_arguments`, `panic_before_static`, `intrinsic_panic_observation`, `nonempty_panic` | Division-by-zero argument failure is reached before static refusal for either static value, carries intrinsic panic code 0x12 bytes and is not an empty revert. |
| `digest_word`, `encoded_intrinsic` | Preserve the digest-word equality and exact intrinsic hash/zero-word payload observation. |
| `dangling_arguments_execute`, `dangling_encoding_execute`, `encoding_failure_before_static`, `wrong_encoding_halt` | Preserve the explicitly malformed pointer-99 fixture, its successful argument evaluation followed by stuck dangling-reference encoding failure, and its distinction from a plain static revert. It is not an admitted SourceSpec machine. |

This is a partial semantic census of one control file, not a complete
cross-family acceptance, proof of a replacement or independent review.

## Source call-phase semantic review (partial)

The named public statements in `SourceCallPhaseControls` distinguish raw
callee outcomes from caller-side return demand under an inherited static frame.
Any later fixture consolidation must preserve the following original cases:

| Declarations | Original observations to preserve |
|---|---|
| `actual_raw`, `actual_capture`, `actual_prefix` | Actual code-present raw call for arbitrary outcomes preserves ordered input bytes and inherited static mode; capture observes the reached state; the prefixed expression changes the caller local before that call. |
| `retained` | Preserve the old heap object and cursor, account, transient state, journal, function locals and logs separately from the new call/answer history. |
| `one_byte_caller_failure`, `no_demand_success` | One-byte successful callee output reverts under the declared uint return demand but succeeds as unit under an empty demand. The two demands are not interchangeable. |
| `revert_payload`, `unfinished`, `static_value_refusal` | Preserve the exact callee revert bytes, zero-horizon timeout at the initial state, and nonzero-value static refusal at the initial state. |
| `wrong_order`, `wrong_mode`, `wrong_outcome` | Preserve the explicit byte-order, inherited-static and success-versus-revert inequalities. |

This is a partial manual census of one control file, not an ExtCall edit,
full Source-family acceptance, a replacement proof or independent review.

## G19 assignment and loop semantic review (partial)

The exact original G19 assignment list remains unestablished. Read-only review
of three broad candidate controls records these original obligations; it does
not assert that these are the only assigned G19 cases.

| Control and declarations | Original observations to preserve |
|---|---|
| AssignmentBlocks `maps`, `initial`, `joined` | Preserve the typed slot map and relation for both flags, arbitrary write lists/pipelines/fuel/checked mode, actual Source and target runs, the post relation and unchanged target global state. |
| AssignmentBlocks `observed`, `repeated_observed`, `reversed_observed`, `reverse_refused` | Preserve complete four-slot observations, repeated-write behavior, reversed-order result and explicit inequality. |
| AssignmentBlocks `untouched`, `self_alias_observed` | Preserve the unrelated uint value 77, target heap/global fields and the actual same-slot observation. |
| AssignmentWhileReset `initial`, `entry`, `joined`, `checked`, `observed` | Preserve the mapped initial relation, simulation entry, actual Source and target loop results, machine execution, both false local words, untouched memory cell 3 and stack `[77]`. |
| AssignmentWhileReset `omitted_checked`, `omitted_observed`, `omitted_loop_refused`, `self_alias` | Preserve the separate omitted-body target run and its true word, the inequality with the actual loop, and the same-slot Source/target case. |
| WhileReturn `yes`, `no`, `same_slot` | Preserve return versus normal Source outcomes and actual target/mapping relations for both checked modes; retain the self-aliased slot case. |
| WhileReturn `captured_true`, `true_not_fallthrough`, `false_not_return`, `nontrivial_input` | Preserve the actual captured target true value, both explicit wrong-outcome inequalities and the live memory/storage input observations. |

These are named public statements in three candidate files only. Private and
generated declarations, all other G19 cases, the exact assigned scope and
independent review remain open; this matrix is not a migration acceptance.

## G19 break/continue/return candidate review (partial)

The exact original G19 list remains unestablished. Read-only review of the
following broad candidates records their named public control observations.

| Control family | Original observations to preserve |
|---|---|
| AssignmentWhileBreak `yes`, `no`, `same_slot`, `write_seen`, `skip_refused`, `reference_frame` | Actual mapped Source/target results for true, false and alias cases; condition write cannot become skip; preserve global state and live memory/storage references. No physical StateRepr is asserted. |
| AssignmentForBreak `yes`, `no`, `same_slot`, `post_is_effectful`, `post_write_refused`, `non_boolean_post_skipped` | Preserve the mapped initializer writes for arbitrary optional post expressions, the skipped effectful post under break, and the non-Boolean post case. |
| AssignmentDoWhileBreak `yes`, `no`, `same_slot`, `condition_is_effectful`, `trailing_write_refused` | Preserve the actual body write while the arbitrary trailing condition is skipped, including the explicit effectful-condition negative control. |
| AssignmentDoWhileContinue `yes`, `no`, `same_slot`, `suffix_is_effectful`, `dead_suffix_refused`, `declaring_suffix_skipped` | Preserve actual mapped outcomes and skipped suffix, including an effectful suffix and one extending the typed context. |
| AssignmentWhileContinue `joined`, `body_tail_skipped`, `donor_observed`, `wrong_donor_refused`, `observed`, `omitted_loop_refused` | Preserve the continue result, donor value zero, wrong-donor and omitted-loop inequalities, related Source/target result and exact machine memory/stack observations. |
| AssignmentForContinue `joined`, `body_donor_observed`, `no_post_timeout`, `post_omission_refused`, `observed` | Preserve donor value one, the required post's effect, timeout when post is omitted, the actual inequality and machine memory/stack observations. |
| AssignmentForReturn `yes`, `no`, `same_slot`, `captured_true`, `true_not_fallthrough`, `false_not_return`, `nontrivial_input` | Preserve return versus normal cases, aliasing, captured true and both wrong-outcome controls, plus live memory/storage inputs. |
| AssignmentDoWhileReturn `joined`, `observed`, `wrong_return_flag_refused`, `trailing_condition_writes`, `trailing_write_refused`, `return_not_normal`, `same_slot` | Preserve actual returned Source/target relation, four-Boolean observation, distinct return flag, skipped effectful condition and alias case. |

These are partial manual case notes, not an exact G19 scope determination,
complete private/generated declaration review, proof of a migration or
independent review.

### Remaining G19 lexical execS/evalE candidate cases

The following is a read-only statement census, not a proof of fixture equivalence or a determination of the original G19 scope. Together with the preceding G19 tables it covers the 18 lexical candidate control files; declarations and cases outside those candidates still need scope identification and acceptance.

| Control | Original obligations to preserve |
| --- | --- |
| AssignmentReturnFlag | For every pipeline, fuel and checked flag, true assignment returns and false assignment continues normally, with source/target related; same-slot alias runs normally. Captured true, stale guard and wrong map refusals, and live memory/storage input are separate obligations. |
| ConditionalReturn | Every pipeline, fuel, flag and checked setting yields source return, target reachability and related environments. Observe `[true,true,flag,true]`; wrong donor and wrong return flag are refused; return is not normal. |
| ConditionalReturnContinuation | Same quantified joined return and relation with a tail; normal observation `[true,true,flag,true]`, eager tail `[true,false,flag,true]`, refusal for both flags, and evidence that the skipped tail actually writes. |
| ConditionalStatement | Both choices, arbitrary pipeline and fuel preserve normal source/target runs and relation; source and target snapshots distinguish branch values. Refuse stale condition; preserve aliased reached relation and `[false,false,true]` snapshot. |
| ConditionalSequence | Both choices and arbitrary pipeline/fuel preserve normal source/target runs and relation with subsequent assignment; source and target snapshots agree, wrong scope index is refused. Heterogeneous Boolean/numeric fixture has reached relation and `[1,1,7]` snapshot. |
| ReturnPair | Arbitrary pipeline, fuel and flag: source returns on true and continues on false, target reaches related environment. Observe `[flag,!flag,true,true]`; refuse stale second donor and omitted second write; preserve captured-false/caller-true witness. |
| ReturnTail | Both choices and arbitrary pipeline/fuel preserve return versus normal outcome, related target and captured flag; preserve source/target snapshots and eager-tail refusal. Aliased initial relation, reached relation, `[false,true,true,false]` snapshot and clobbered-flag refusal are independent obligations. |
