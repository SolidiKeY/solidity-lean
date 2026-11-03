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

## Open

General source/world/backend composition remains open. Some concrete intrinsic whole programs are accepted, as proved
by `FreshBooleanCompilation.public_whole`; this is not general source closure.
Remaining G25/G26 obligations stay explicit; G31 is owned by VY4.

### Reference-call capture and readback

`Backend/Passes/ReferenceCallReadback.lean` consumes the published memory/tuple
return producer with its original `Form`, `Entry`, `NoAliasPromotion` and actual
intrinsic call success. `execution` derives the receiving capture/update Input
from the actual returned full representation. Returned map and operand words
precede the saved-tail quantifier; the result retains BaseExtends, exact call-cost
allocator growth, full suffix MappedOutput, cursor and every protected private-frame
word. `call_revert` absorbs an unreachable suffix without a suffix Input.

The controls instantiate a real mixed tuple call: default allocation costs one
word, the returned reference aliases the old array, capture saves 7, and the
old scalar becomes 9 before readback returns 7. All five final locals, both heap
objects, fourteen selected target cells, allocator cursor and full saved stack
are observed. The original map cannot represent the newly allocated default
object; frame 15 cannot admit private pointer 16; argument index 2 reaches body
revert. Wrong recapture is an inequality of reached cells, not execution of an
alternative compiler. These are intrinsic/symbolic execution results, not
independent Source evaluation, frontend correspondence, external EVM validation,
public ABI or session/resource adequacy.

Separate read-only finder and skeptic reviews found no confirmed defect.
Thirteen generated guards pin the actual standard-only axiom reports.

### Reached capture failure after a reference return

`Backend/Passes/ReferenceCallCaptureFailure.lean` retains the actual successful
memory/tuple call output, selected address map, full representation, exact
allocation cost, cursor and private frame before every saved tail. It derives
the receiving capture Input at each tailed machine and proves joined emitted
revert iff the reached operand ordinarily reverts. The intrinsic joined
call/capture program also reverts when that operand does. No post-failure state
or map is constructed.

The controls return the old array alias after default allocation, then actually
read index one of its length-one array during capture. Both intrinsic and target
joined executions revert; a local receiver read still returns seven at that same
reached representation. All fourteen selected prefix cells and the full saved
stack are observed. The next physical local slot contains the old pointer 128
before declaration, not zero; `wrong_zero_capture_cell` refutes the false zero
assumption from an unvalidated draft. The earlier post-capture vector, whose
same cell contains seven, is unchanged. No failed-machine observation, Source
frontend correspondence or public resource/session claim follows. Separate
read-only finder and skeptic source reviews found no confirmed defect.

### Runtime argument failure before return allocation

`Backend/Passes/ReferenceCallArgumentFailure.lean` uses one checked tuple call
for both runtime cases. Its first primitive argument reads the old array at the
caller index. Index zero succeeds and reaches default return allocation with
exact cost one; index two fails in that argument with exact reached cost zero,
even though the emitted program's static allocation flag is true. Original
Entry, frame and capacity predicates remain intact. The emitted first-value
prefix precedes its parameter store and the return/body suffix. The successful
return retains the old array alias and the distinctive primitive seven.

`Backend/Passes/ReferenceCallArgumentPrefix.lean` consumes the published context
capture certificate to derive actual save execution, full caller representation
and zero allocator growth. The argument then reverts under that reached
representation for every saved tail and arbitrary unreachable suffix. All
fourteen selected prefix cells and the complete stack are observed; the heap
cursor remains 130 while the private save pointer advances to 22. A successful
branch of the same emitted call refutes an always-revert claim. These are
intrinsic/symbolic-word results, not independent Source or public ABI/resource
adequacy. Separate read-only finder and skeptic reviews found no confirmed defect.

### Independent Source arithmetic effects and emitted captures

`Backend/Passes/AssignmentSubtractionPass.lean` consumes the published V07
`assignment_subtraction_transport` for `(i = a) - i`. It retains original
Source/target reads, integer ranges, result-range guard, frame and `fuel + 4`
quantification, actual accepted memory-prefix certificate/Input and compiled
subtraction value. It derives the reached value through the existing arithmetic
proof, then retains full prefix MappedOutput and actual joined code execution
with one canonical machine, selected map and result word before every saved tail.
No P8 producer or desired-preservation premise is introduced.

The controls align Source locals `a = 9`, `i = 7` with a represented target
containing an independent old array. Both Source and emitted code yield legacy
result two versus via-IR zero, while both retain `i = 9`. All eleven selected
target cells, the allocator, old array, sentinel and full saved stack remain
observed. Executing the reversed operand code after the actual legacy prefix
reverts; stale RHS, corrupted tail and insufficient frame are rejected. This is
a local integer/result correspondence plus physical target preservation, not a
global Source-heap/world relation or general overflow/wrapping/ABI adequacy.
Separate independent finder and skeptic source reviews found no confirmed defect.
