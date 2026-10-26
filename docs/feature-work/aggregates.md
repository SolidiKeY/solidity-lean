# Aggregate milestone, 2026-10-25

Integration status (2026-10-26): included in the shared checkout. Current
combined validation is tracked in [integration.md](integration.md).
Worker handoff statuses and isolated validation results below are historical;
they neither report the current combined checks nor establish full source support.

Inline array expressions now allocate fixed memory before evaluating and
storing each element in source order. Type inference starts at the first
mobile element type and folds Solidity implicit common types, independently
of the target (`[1,256]` is `uint16[2]`; a `uint16[2]` memory target does not
make `[1,2]` cease being `uint8[2]`). Numeric, Boolean, fixed-byte, finite nested-array and struct
elements are exercised by native and compiler-imported examples. Storage
reference elements copy at each element's evaluation; memory references alias.

`Src.fixedCopyMem` retains the typed `MPath` and `FixedCopy` witness. Its
value and lower term compose memory-to-storage copying with the existing
fixed-shape conversion; `Src.lower_valueT`, weakening, hereditary invariants,
clean tails and sound save/push integration cover the new source. Mapping
freedom comes from the indexed memory path. Generic fixed-copy adapters remain
Lean-only. The conservative KeY fragment and EVM compiler explicitly exclude
the adapter, as they already exclude storage fixed-copy adapters.

Fixed memory snapshots may copy into compatible dynamic or longer fixed
storage arrays, including reference pushes and deferred getter receivers.
Storage value copies may widen numeric element widths; aliases and memory
bindings retain exact element shapes. Byte-width widening is not modeled by
this conversion because it requires shifting values. Snapshot evaluation
stays after the receiver's effects when the native receiver statement defers it.

Local memory and storage-alias tuple targets capture all RHS references before
rebinding. Multiple nonlocal targets, effectful/dependent targets and duplicate
targets retain their restrictions. Calldata read-only propagation now includes
nested assignment roots and computes a finite fixed point, so tuples and
array elements cannot create untracked writable aliases.

Slice bases are captured before endpoints and remain stable through source
rebinding. Nonconstant bounds are read once. Relative bounds are checked before
adding outer offsets. Inline reads, lengths and decoding open at the actual
expression position. Relative indices are captured once; invalid indices use
the base's out-of-range index, preserving bounds Panic(0x32) without evaluating
an overflowing offset. Endpoint range failures retain Solidity's ordinary
revert. The source reference is Solidity 0.8.38 commit
`1835d247de183f23e7b0e2bc4a50732af525b77c`,
`YulUtilFunctions::calldataArrayIndexRangeAccess`.

## Review

A read-only finder and an independent skeptic reviewed both source/core and
frontend areas without calling Lean. Confirmed issues fixed in this milestone:

- Nested RHS reference assignments escaped calldata taint; propagation now
  includes those roots and reaches a finite fixed point. Regression checks
  include a five-link reverse alias chain and a nested tuple rebinding and container-element assignment.
- Literal-lvalue rejection also rejected legal literals inside index
  expressions. It now rejects only a whole literal target; indexed temporary elements
  remain writable, with write/delete/increment regressions.
- Import scalar casts were applied to reference elements of nested arrays.
  Scalar context is now applied only to immediate scalar element types; an
  imported narrow nested-array regression covers the affected path.
- Slice test expectations now distinguish legacy right-first and via-IR
  left-first schedules. A catchable-code test distinguishes Panic(0x32) from
  Panic(0x11). Ordinary declarations also shadow the virtual view table.

Reference pushes also validate captured source widths against the direct
receiver or the deferred getter return metadata, rejecting narrowing through
a literal.

The broad examples also caught inline slice decoding entering generic call
admission. Private descriptors now retain whole-base checking, and tuple
assignments/declarations resume the ABI decoder after opening the stable
view. Both existing `Hashing` examples and a new tuple-decode case pass the
expanded 246-job focused build.

The final axiom audit of `Src.lower_valueT`, `Src.valueT_wk` and the new
literal/imported/slice/Panic32/via-IR headline proofs lists only `propext`,
`Classical.choice` and `Quot.sound`. No additional trusted assumption,
dependency or heartbeat override was added.

## Validation

The initial 181-job targeted core build passed. Per-file checks passed for the
new native and compiler-imported array examples and the slice effect suite.
The pinned-fixture JavaScript regression passes on the host: the imported
literal assertion is proved and the false assertion stays pending. It could
not launch its process group inside the sandbox (EPERM). Frozen TestSuite
static audit: 552 derived, 11 refuted, zero pending. Layering: 126 core
modules, zero elaborator reachability. Feature audit: 211 features and 783
upstream symbols. Automation gate: 491 automatic plus 61 budgeted, 11 refuted,
zero pending.

One profiler sample per declaration, with other build work running, measured:

| Proof | Before (s) | After (s) |
|---|---:|---:|
| Fixed storage shape copy | 0.095 | 0.071 |
| Simple slice read | 0.425 | 0.438 |
| Nested slice read | 0.902 | 1.057 |

These are indicative timings, not a controlled benchmark. The nested slice
cost increased with the stable captures and relative checks; no heartbeat
limits changed.

Final `./run-lean.sh` passed: 587 library jobs, 243 TestSuite jobs and the
frozen `473da8944c` sort gate (377 taclets, 131 read-bearing annotations,
zero mismatches). The existing `Examples/Decision.lean` checked in 852 s.
The frozen corpus passed all 774 obligations with no verdict or generated
output drift. The default-compiler testing API also proves the new literal
property; the committed AST remains generated by the exact 0.8.38 compiler.
The final fixture import was rechecked after its compatible pragma update.

`git diff --check`, layering, feature audit and the automatic gate pass.
Orphan/doc-path checks report the same 33 pre-existing scratch orphans and
13 pre-existing missing vendor/external document paths, with no new finding.
The temporary timing module was removed. Source changes remain uncommitted
for shared-checkout integration.

## Remaining interfaces

This is a checked implementation milestone, not completion of every aggregate
feature in the catalog. The integrated [primitive slice-copy continuation](../calldata-slice-copies.md)
now supplies materialization, internal passing/returns, hashing and existing
storage-copy consumers. Reference-element slices, general writable whole-calldata
copies and external calls with reference arguments remain limited. Nominal
enum/UDVT and function-valued element identities belong to the type/function
groups; recursive shapes belong to recursive-types. Scalar captures retain
address and fixed-byte source markers. Heterogeneous reference-return
tuples remain a function-return interface. The feature catalog remains partial.

## Group 07 upstream repair (2026-10-26)

This lane starts at `006fcd593f5beeb540e7adf2bc76de4638566924` on
`group07-tuples-references`. The historical corpus reports remain unchanged.
All eleven assigned fixtures were reproduced independently before editing,
with `--batch-size 1`, their full snapshot paths, and separate output directories.
Every fixture still had frontend gaps in both required source pipelines.
The attached managed executor passed Lean 4.24.0, Lake 5.0.0 and
`lake build Solidity.KeySort`; the archive verified all 11,622 files.

The lowering now uses existing intrinsic statements for tuple conditionals,
reference-valued empty push operands, discarded unary expressions and scalar
local deletion. Literal-string conditionals use a fresh memory binding and evaluate only the
selected literal branch. Tuple RHS values are captured before primitive overlapping
writes, whose order is right to left. The new overlapping-target path accepts
only names, fields and literal indices; general dependent/effectful LHS
locations still need typed location captures. Reference alias restrictions and
mixed storage/memory conditional rejection remain explicit. Per-component
capture declarations and assignments retain width/shape admission.

Generated push aliases retain complete element shape metadata. A pushed-member
store from a scalar stack local is admitted only when its receiver is pure;
receiver mutation, ordinary calls and callback-capable expressions remain
unsupported there. No runtime representation, calculus rule, core dependency,
axiom, search budget or heartbeat limit changed. These are frontend emissions
of existing statements and their existing soundness theorems.

The upstream replay adapter now resolves generated public getters by source
getter identity and ABI signature. Signature normalization preserves the source
function name byte for byte. Every original stateful observation, constructor,
rollback and required pipeline remains in the runner; unsupported observations
and resource exhaustion retain their original inconclusive treatment.

`Calls.duplicateCallTarget`, `Calls.duplicateStorageTarget` and `Calls.lazyTuple`
prove emitted-program properties for arbitrary typed states, including false
alternative output controls and an untaken division. `Checked.lean` pins tuple
reference-width rejection. The separately compiled `tests/solc/Group07.sol`
uses the SHA-checked 0.8.38 compiler; `tests/upstream/Group07.lean` kernel-checks
its emitted programs, including lazy discarded tuple branches, checked rejection,
unchecked negation, overlapping memory writes, owned strings and push aliases.
Its standalone checked-narrow control uses the existing ordinary-revert guard;
it does not certify Solidity's ABI Panic(0x11) encoding. Its effectful push
receiver remains explicitly unsupported. These certificates
are not a universal source/compiler correctness theorem. Runtime agreement is
observational evidence only.

The read-only finder identified generated push prefixes escaping discarded
components/branches. `localStmt` now isolates and drains each prefix at its
operand position. The independent skeptic confirmed this fix and identified
three further boundaries: getter names containing ABI type spellings, receiver
mutation before reading a local RHS, and nominal/string metadata on fresh push
aliases. All were fixed and inspected again without opening Lean workers.
Getter identity and model-alias rejection are pinned in `Replay.lean`.

Validation and exact per-fixture provenance are recorded in
[`tests/upstream/group07-validation.json`](../../tests/upstream/group07-validation.json).
Long logs are retained under `/workspace/.setup/logs/group07-*` in the managed
executor. Early overlapping build runs produced bus errors and out-of-date
artifact failures; they are inconclusive, not passing checks or demonstrated
model failures. Final validation is serialized over the final source state.

Final isolated fixture results (each row requires both legacy and via-IR):

| Path under `test/libsolidity/semanticTests/` | Before | After |
|---|---|---|
| `array/push/push_no_args_struct.sol` | broken | working |
| `builtinFunctions/erc7201_param_ternary_operator.sol` | broken | working |
| `expressions/conditional_expression_storage_memory_2.sol` | broken | explicit unsupported mixed-reference join |
| `expressions/conditional_expression_tuples.sol` | broken | working |
| `expressions/tuple_from_ternary_expression.sol` | broken | working |
| `variables/mapping_local_tuple_assignment.sol` | broken | working |
| `viaYul/comparison_functions.sol` | broken | working |
| `viaYul/conditional/conditional_tuple.sol` | broken | working |
| `viaYul/local_tuple_assignment.sol` | broken | working |
| `viaYul/negation_bug.sol` | broken | working |
| `viaYul/tuple_evaluation_order.sol` | broken | working |

None was already fixed on the starting master. The mixed-reference row remains
`broken` with its explicit frontend gap in the runner, not passing or silently
excluded. There are no adapter/resource-blocked rows in the final isolated run.
Earlier resource/artifact failures remain in their separate output directories.
The final isolated commands took 3.04–4.75 seconds per fixture, including both
pipelines, with unchanged 120-second process limits and loop fuel 1,000. These
are wall observations, not a controlled before/after performance benchmark.

The lane has no dependency on unpublished group changes. Integration touches
shared frontend/elaborator files and the narrow getter lookup in
`Tools/Upstream.lean`; adjacent edits to tuple admission, ternary hoisting or
source-signature lookup require ordinary merge review. The optional Bridge and
obsolete SolKey reader are unchanged. No pushes or merges to master are made.

The native indexed-push control uses `(rows[i++].push)()` and proves that
`i` increments once. The importer's unparenthesized indexed push-call spelling
remains an explicit printer gap; its unsupported report is pinned separately.
Six kernel-certificate headlines and all three universal tuple theorems have
only `propext`, `Classical.choice` and `Quot.sound` in their axiom sets. The
trust inventory's full 25-finding list is identical to starting master. Lean
MCP diagnostics are unavailable; configured per-file Lean commands use
`--tstack=131072`. A refreshed fixture run after updating the obsolete source
rejection pin took 5.88–10.78 seconds per fixture with the broad build running;
its source/model hashes are the final hashes in the validation JSON.
