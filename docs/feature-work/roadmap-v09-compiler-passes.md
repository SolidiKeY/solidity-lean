# V09 compiler-pass components (G24–G31)

Backend pass components over the existing memory compiler
(`Backend/Passes/`). Headline results are
parameterised over any `Compilation`/`CompiledVal` with explicit link or
budget premises (`MappedBoundaryLink`, `ReachedMappedLink`, reached-cost
budgets), and controls instantiate them (`LinkedControls.concrete_link`,
`terminal_reflection_inhabited`, the `HeapBoundary` links).

## Components

- Values: `ValueCertificate` (`CompiledVal` success/revert over a saved tail),
  `ValueSequence*`, `SharedPair`, `ValueContext*`, `StatefulValues`
  (`binary`/`unary`: checked, division, modular and power operands),
  `ResolvedMetadata*`.
- Captures: `Capture*`, `CapturedValueStability`, `ReferenceCapture*`,
  `ReferenceObjectCertificate`, `ConditionalReferenceCapture`;
  `RuntimeReturnCapture*` (the P1 V3 primitive-return emitter followed by a
  capture, with `NoAliasPromotion` as a premise).
- Heap and allocation: `HeapBoundary*` (branch-indexed physical heap links),
  `HeapPrefix`, `ReindexedMemory`, `MemoryCompilerSequence`, `Allocating*`,
  `AllocatorPreservation`, `PreservedAllocator*`, `TripleAllocation`.
- Composition: `TripleSuffix`, `TripleFailures`, `TerminalReflection`
  (`compilation_{mapped,triple}_reflect_success`), `Reframed*`.
- Divergence and faults: `DivergenceWitness` (`*_fault_witness_iff`),
  `TailDivergence`, `Spin`, `FaultReached`, `FaultTail`.
- Calls and loops: `MemoryCall*`, `LoopCall*`,
  `LoopCallsBoundary.loops_budgeted_memoryCalls_link`, `LoopAllocatingSuffix`.
- Widths and Booleans: `WidthApplication`, `SignedWidthGuard`,
  `SignedWidthCapture`, `ShortCircuitBoundary`, `FixedBoolean*`,
  `FreshBoolean*`, `EntryReception*`.
- `*Pins` modules hold `#guard_msgs` axiom guards only.

About 26 modules (for example `EntryReception`, `ReachedHash`,
`FreshBoolean*`, `FixedBoolean*`, `HeapApplication`,
`PreservedAllocatorApplication`, `TripleSuffix`, `TripleFailures`) are
observations on the single `CompileExamples` fixture, not general pass
results. `WidthApplication`, `ShortCircuitBoundary`,
`ConditionalReferenceCapture` and `ReferenceCaptureCertificate` have private regression controls outside the published integration; they
are not claimed as default-root controls here.

## Integration checks

`CompilerProofChecks` also imports the restored axiom-pin modules. Their
expected messages are generated from the current kernel reports; only
`propext`, `Classical.choice` and `Quot.sound` are permitted, with exact
axiom-free and smaller sets retained. No theorem statement or premise changes.

`ReframedTripleWrongOrder.block_code_split` uses accepted compiler join and
single-block certificates instead of unfolding the whole concrete compiler.
The default heartbeat budget, failure behavior and complete ordered vectors
are unchanged. The `RuntimeReturnFailure*` and `AssignedBareRevert*`
applications remain registered.

`P8Admission` and `CheckedCallBoundary` were not integrated and are not on
master; neither supplied an inhabited source-admission or whole-source result.

## Void-call heap effects followed by capture

[RuntimeVoidCapture](../../Solidity/Backend/Passes/RuntimeVoidCapture.lean)
consumes the published ordinary void-call return certificate. Its original
physical entry, alias guard, actual source success, reached value evaluation
and fresh-local bound remain explicit. The reached machine, address map and
captured word precede every saved tail; each tail retains the receiving
`Input`, full `MappedOutput`, both stage runs and their joined execution.

[Controls](../../Solidity/Backend/Passes/RuntimeVoidCaptureControls.lean)
observe an actual array mutation from 7 to 37 before capture. The complete
12-cell vector retains the old scalar, three aliases, array lengths and all
three payloads, runtime cursor and protected word. Premature capture reads 7;
body bounds failure skips capture. Saved-head and insufficient-private-frame
controls retain their original scope. The fixture uses `b = 0` and a
nonallocating call; its conditional allocator law proves no positive-cost
application. It is ordinary void-call transport, not recursive or approved
source-profile adequacy. Independent finder and skeptic reviews found no
remaining source defect. Exact standard-only guards are generated from the
actual kernel output; no proof budget or expected observation was changed.

## Reached allocation budgets before failure

[PositiveAllocationFailure](../../Solidity/Backend/Passes/PositiveAllocationFailure.lean)
inhabits the positive-base allocator premise. A real assignment changes the
size local from 0 to 2, so the selected allocating block costs 3 instead of 1.
A full empty-heap allocator at cursor 64 supplies the exact reached capacity.
The source allocation succeeds before its index-at-length read reverts.

[Controls](../../Solidity/Backend/Passes/PositiveAllocationFailureControls.lean)
retain full assignment output, reached runtime input and actual joined revert
for every saved stack. At the same reached state and header `W - 3`, the stale
one-word estimate fits but the correct three-word demand is refused. Skipping
the assignment loses representation. The complete assignment-prefix vector
observes its scalar, heap cursor, runtime cursor and protected word. No target
post-allocation vector or post-failure machine is asserted. Independent
finder and skeptic reviews found no source defect; the exact standard-only
axiom guards are generated from the focused kernel output.

## Exact terminals of checked void calls

[RuntimeVoidReflection](../../Solidity/Backend/Passes/RuntimeVoidReflection.lean)
derives terminal cases without assuming source success. It exposes the real
capture prefix, its full typed representation, frame bound and transported
allocator input. Target revert reflects exactly intrinsic ordinary revert;
success reflects the actual final machine and selected address map. Typed
fault exclusion is proved before applying saved-tail transport.

[Controls](../../Solidity/Backend/Passes/RuntimeVoidReflectionControls.lean)
separate argument-read failure from callee failure after successful arguments.
Both retain every cell of the 22-cell capture window, including saved payload,
advanced cursor, aliases and heap contents. Successful mutation is reflected.
A panic is an actual distinct source outcome whose selector is refused; the
loop control proves selector refusal only. These results cover the accepted
finite call certificate under its original physical entry and alias guard,
not arbitrary calls, public ABI bytes, recursion or session resource adequacy.
Independent finder and skeptic reviews found no source defect.

## Effectful Source short circuit

[EffectfulShortCircuit](../../Solidity/Backend/Passes/EffectfulShortCircuit.lean)
connects the published V07 Boolean assignment fragment to actual accepted
compiler code. `execution` retains pointwise initial Source alignment, Boolean
reflection, all four position certificates and the original physical compiler
Input. It derives independent Source and intrinsic runs and reached caller
alignment; the actual output machine and full selected map precede every saved
tail. This uses no P8 producer or assumed preservation conclusion.

[Controls](../../Solidity/Backend/Passes/EffectfulShortCircuitControls.lean)
instantiate an accepted memory compilation at positive base with an untouched
scalar, allocator cursor and two protected cells. The RHS reads the local
written by the left assignment. One emitted program per operator handles both
runtime Booleans. Complete Source locals and eight target cells plus the full
stack are observed. Actual eager and reversed programs discriminate skipped
RHS effects and stale alias reads; frame and corrupted-tail controls remain
separate. Twenty-two generated guards pin actual standard-only axiom sets.
Independent finder and skeptic reviews requested executed alternate programs
rather than only wrong-value comparisons; those controls are now included.
These are typed internal symbolic instructions, not external EVM tests or
SourceSpec, admission, ABI, world or session/resource adequacy.

## Effectful reference-pair capture

[EffectfulReferencePair](../../Solidity/Backend/Passes/EffectfulReferencePair.lean)
consumes V07's actual reference assignment/read pair. Both initialized selected
reads, the independent address/reference relation and its alias equivalence
remain premises. Source evaluation and intrinsic execution select the pipeline's
actual old/new captures; the compiled machine and full output map precede every
saved tail, under the original physical Input. No P8 producer is required.

[Controls](../../Solidity/Backend/Passes/EffectfulReferencePairControls.lean)
use two live Source byte objects and the existing represented intrinsic heap.
Both actual pipeline programs are accepted and executed. Complete thirteen-cell
vectors retain both arrays, all old locals, both captured pointers and the stack.
Wrong-pipeline capture, an old alias following the rebind, corrupted tail and
insufficient frame are discriminated. This base-zero, nonallocating application
makes no allocator-header or global Source heap/world adequacy claim.

## Width-aware Source value application

[SourceNarrowingValue](../../Solidity/Backend/Passes/SourceNarrowingValue.lean)
consumes the published unchecked unsigned subtraction transport for all valid
widths from eight through 256. The original integer-local family, range/read
premises, unchecked Source frame and actual value certificate/representation
remain explicit. Independent Source and intrinsic runs retain the numeric
relation; one representing output word works before all saved tails, with every
non-stack machine component unchanged. This reuses arithmetic certificates.

[Controls](../../Solidity/Backend/Passes/SourceNarrowingValueControls.lean)
compile uint8 zero minus one to 255 over an inhabited positive-base physical
input. Actual checked subtraction instead reverts. Complete six-cell and stack
observations retain the allocator cursor and protected words; wrong width,
unmasked word, operand order and corrupted-tail controls discriminate results.
This fragment application is not general frontend width lowering, primitive
byte execution, panic ABI encoding, or public resource/session adequacy.

## Capture and failure packaging

The four previously deferred routine statements are now implemented by V09:
[CapturedReadback](../../Solidity/Backend/Passes/CapturedReadback.lean),
[ShortCircuitWitness](../../Solidity/Backend/Passes/ShortCircuitWitness.lean),
[ConditionalReferenceInput](../../Solidity/Backend/Passes/ConditionalReferenceInput.lean)
and [RuntimeCaptureReflection](../../Solidity/Backend/Passes/RuntimeCaptureReflection.lean).
Their exact original signatures retain the two actual value certificates,
physical representations, capacity, branch fragments and arbitrary saved tails.
Joined readback uses actual successful capture/update execution. Revert witnesses
expose immediate or reached operand runs. Conditional Input derives the real
frame bound and zero cost. Capture reflection consumes the full original Input
and actual typed value alternatives, without a raw fault-tail law.

[Controls](../../Solidity/Backend/Passes/QueueCompletionControls.lean) inhabit
success, immediate/reached/skipped failure, conditional reference capture and
frame refusal over the existing populated heap. All eleven listed cells and the
full saved stack are retained. The wrong-readback control is a cell inequality,
not another emitted execution. Independent finder and skeptic reviews found no
proof or premise defect. These close the routine statements, not public Source,
ABI, world or resource/session adequacy.

## Reference-call sequencing

The following completed components consume the published memory/tuple return
producer with its original `Form`, full `Entry`, `NoAliasPromotion`, actual
intrinsic call outcome and exact frame/allocation premises.

- [ReferenceCallReadback](../../Solidity/Backend/Passes/ReferenceCallReadback.lean)
  derives the receiving capture/update Input from the actual returned map and
  full representation. Map and operand words precede every saved tail. Exact
  cost, allocator growth, cursor and private-frame words are retained. The
  mixed tuple client allocates a default object, returns the old array alias,
  captures 7, updates the old scalar to 9 and reads back 7; stale-map and frame
  refusals are checked.
- [ReferenceCallCaptureFailure](../../Solidity/Backend/Passes/ReferenceCallCaptureFailure.lean)
  retains the actual successful call prefix before a failed returned-alias
  read. It derives each tailed capture Input and joined target revert iff the
  operand ordinarily reverts. No post-failure state or map is supplied. The
  next free physical cell contains pointer 128 before declaration, then 7
  after successful capture; no zero-initialization premise is assumed.
- [ReferenceCallArgumentFailure](../../Solidity/Backend/Passes/ReferenceCallArgumentFailure.lean)
  and [Prefix](../../Solidity/Backend/Passes/ReferenceCallArgumentPrefix.lean)
  use one emitted tuple call: runtime index zero succeeds with reached cost
  one, while index two fails in its first argument with cost zero despite a
  true static allocation flag. Actual save execution, full representation,
  zero prefix allocator growth and arbitrary saved tails are proved. The
  heap cursor stays 130 while the private save pointer advances to 22.

The controls retain complete ordered selected-cell vectors and full stacks.
They are intrinsic/symbolic-word results, not independent Source, recursive
call, approved-profile, public ABI or session-resource adequacy.

## Source assignment arithmetic

[AssignmentSubtractionPass](../../Solidity/Backend/Passes/AssignmentSubtractionPass.lean)
connects the independent V07 Source clause for `(i = a) - i` to actual compiled
capture-prefix and subtraction execution. Original Source/target reads,
integer and result ranges, `fuel + 4`, frame, Input and value certificates
remain explicit. A canonical machine, selected map and word precede every
saved tail; full prefix MappedOutput and joined code execution are derived.

For `a = 9`, `i = 7`, both Source and emitted code give legacy 2 versus via-IR
0, while retaining `i = 9` and the old array, allocator and sentinel. Reversed
operand code actually reverts; stale RHS, frame and saved-tail corruption are
rejected. This is local integer/result correspondence and physical target
preservation, not a global Source-heap/world relation, general overflow or
narrow wrapping theorem. No P8 producer is assumed.

## Unchecked unsigned addition

[SourceAdditionValue](../../Solidity/Backend/Passes/SourceAdditionValue.lean)
consumes the published V07 addition transport and an actual `CompiledVal`.
Valid widths, Source integer-local alignment, operand ranges and reads, the
explicit unchecked frame, `fuel + 3` and full target `StateRepr` remain premises.
It derives independent Source/intrinsic results and their value relation, then
chooses one representing word before every saved tail. Successful emitted code
preserves every non-stack machine component.

[Controls](../../Solidity/Backend/Passes/SourceAdditionValueControls.lean) use
actual accepted code: uint8 `255 + 1` gives 0, the same code on `1 + 1` gives 2,
and emitted unmasked full-word addition gives 256 on the first input. All six
fixture cells and the full stack are observed; wrong unmasked value and saved
tail controls discriminate the results. Exact standard-only axiom guards are
in [Pins](../../Solidity/Backend/Passes/SourceAdditionValuePins.lean). Independent
finder/skeptic reviews requested the nonzero and actual unmasked controls;
both were added. This is a local arithmetic/value application, not effectful
assignment sequencing, general Source heap/world or byte-level EVM adequacy.

## Open

General source/world/backend composition remains open. Concrete intrinsic
whole-program acceptance, such as `FreshBooleanCompilation.public_whole`,
is not general Source closure. G24 requires the actual Source/Lowering/world
and full public Cert producers. G24.01 also retains the abstract slot/root/hash/
data/offset interface and state/decode export; G24.03 retains its statement
freeze obligation. G25/G26 retain their stated scalar, general
source-admission and execution prerequisites. G31 belongs to VY4. ABI entry
premises do not close G24.03 by themselves. Whole-lane completion still
requires the original combined validation and producer obligations.
