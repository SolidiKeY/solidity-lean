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

## Effectful assignment and unchecked addition

[AssignmentAdditionPass](../../Solidity/Backend/Passes/AssignmentAdditionPass.lean)
extends the local-value application to `(i = a) + i` using the published Source
assignment transport and actual captured operand order. It retains valid
widths, initial integer-local alignment/reads/ranges, unchecked frame and fuel,
original compiled-prefix Input and actual operand certificate. The theorem
derives post-assignment local alignment and chooses the canonical machine,
selected address map and result word before all saved tails. Each tail retains
the full reached MappedOutput, prefix execution, operand execution and joined
execution. No wrapped result-range premise is required.

[Controls](../../Solidity/Backend/Passes/AssignmentAdditionControls.lean) inhabit
both pipelines with `a = 255`, `i = 1`: legacy returns 0, via-IR returns 254,
and both retain `i = 255`, all eleven fixture cells, old array, allocator,
sentinel and full saved stack. Stale RHS, insufficient frame and corrupted
tail are refused. The difference comes from assignment/capture effects, not
from swapping commutative addition operands. Exact guards are in
[Pins](../../Solidity/Backend/Passes/AssignmentAdditionPins.lean). Independent
finder and skeptic reviews found no defect. This remains local Source integer
alignment plus intrinsic/physical execution, not Source heap/world or public
resource/session adequacy.

## Effectful assignment and unchecked multiplication

[AssignmentMultiplicationPass](../../Solidity/Backend/Passes/AssignmentMultiplicationPass.lean)
uses the published V07 multiplication transport with the actual assignment
capture prefix and compiled operand. It retains the original width/range,
Source-local alignment, unchecked frame/fuel and full compiler Input premises.
It derives post-assignment alignment and full reached MappedOutput, choosing
the machine, map and word before all saved tails and joining both actual runs.
Existing arithmetic and compiler producers supply the soundness arguments.

[Controls](../../Solidity/Backend/Passes/AssignmentMultiplicationControls.lean)
use `a = 255`, `i = 1`: legacy gives 255 while via-IR wraps `255 * 255` to 1.
All eleven existing fixture cells and the full saved stack are preserved.
The same reached via-IR prefix followed by actual accepted unmasked multiplication
gives 65025, distinguishing omitted narrowing. Stale RHS, frame and saved-tail
controls remain explicit. [Pins](../../Solidity/Backend/Passes/AssignmentMultiplicationPins.lean)
guard the actual standard axiom sets. Independent finder and skeptic reviews
found no defect. This is local numeric/effect correspondence and physical
intrinsic execution, not public Source heap/world, checked-overflow, ABI or
resource/session adequacy. H22 external-call construction is untouched.

## Memory scope exit and local-slot reuse

[MemoryScopeBoundary](../../Solidity/Backend/Passes/MemoryScopeBoundary.lean)
adds physical transport beyond structural block compilation: the existing
block certificate keeps its exact emitted code, allocation cost and original
Input. Scope exit restricts the actual output fragment and drops only typed
locals, retaining the full heap relation, selected map, old-reference identities
and allocator growth. The canonical machine and map precede every saved tail.
Exact intrinsic `THalt` reflection keeps revert, panic and divergence distinct;
target observation transport is equality of the actual code. Here source
means intrinsic `Prog.run`, not independent `Solidity.Source` semantics.

[Controls](../../Solidity/Backend/Passes/MemoryScopeControls.lean) drop two
capture locals, then derive a fresh declaration's Input at the actual shortened
context. Both actual maps precede all tails; full prefix and final MappedOutput,
joined intrinsic execution and emitted execution are retained. The declaration
reuses cell 4; all twelve listed cells and the full saved stack are observed.
Accepted code for the wrong extended context writes cell 6 instead; that raw
code contrast is not a valid typed joined program. Cell 5 retains its old 255,
so scope exit does not claim physical erasure. A reached revert follows the
actual successful capture prefix, with no post-failure state invented.

[Allocation](../../Solidity/Backend/Passes/MemoryScopeAllocation.lean) independently
inhabits positive cost: an accepted zero-length array allocation consumes one
cell and transports actual selected allocator ownership from cursor 64 to 65
across all tails, despite dropping its reference binder. No heap deallocation
is inferred. [Pins](../../Solidity/Backend/Passes/MemoryScopePins.lean) guard the
observed standard axiom sets. Independent finder and skeptic source reviews
found no defect. Public Source/world/ABI/session adequacy remains open; H22
external-call construction is untouched.

## Expanded-call scope and old-alias consumption

[MemoryCallScopeBoundary](../../Solidity/Backend/Passes/MemoryCallScopeBoundary.lean)
transports the separate `Memory.Calls.Program` branch through the published
block/sequence constructors. It retains the original push-free witness, exact
reached cost and maximum of the private call need and caller context length.
Original and scoped Inputs are equivalent; the full output heap/map/allocator
relation survives dropping the extra caller locals. Checked projection lemmas
keep large concrete certificates from being unfolded during client proofs.

[Controls](../../Solidity/Backend/Passes/MemoryCallScopeControls.lean) consume an
actual allocating memory-return call, drop its return/capture locals, and derive
an old-alias consumer Input from the same reached map. All three actual maps
and machines precede saved tails; all three MappedOutputs and both intrinsic
source/code associations are retained. The private-frame underestimate remains
refused. [Observations](../../Solidity/Backend/Passes/MemoryCallScopeObservations.lean)
include all four heap objects, both elements of the owned array, caller/private
cells, sentinel, allocator and two saved stack words: 11 intrinsic fields and
18 target words (two stack plus 16 selected memory words). Correct code updates
the old object to 8 while retaining the dropped object's 33; raw code compiled
for the old extended context changes that 33 to 42. It is not a valid typed
joined consumer. Skipped suffix and corrupted-tail observations are refused.

[Failures](../../Solidity/Backend/Passes/MemoryCallScopeFailures.lean) retain the
actual successful allocation prefix and scoped failing-stage Input. Argument
failure costs 0; reached body failure costs 1. Both associations revert without
requiring an Input or run for the typed unreachable suffix, and no failed-state
map is invented. [Pins](../../Solidity/Backend/Passes/MemoryCallScopePins.lean)
guard observed standard axiom sets. Independent finder and skeptic reviews
found no defect. These are intrinsic/symbolic-word internal-call results;
independent Source/world, public ABI/session and general recursion adequacy
remain open. H22 external-call construction is untouched.

## Public selection of the scoped call

[CompilerCallScopeRecognition](../../Solidity/Backend/Passes/CompilerCallScopeRecognition.lean)
uses the actual value returned by public `Compiler.compile` for the scoped-call
fixture. Its exact acceptance equation and memoryCalls tag are checked. Fragment
and private-frame projections are checked, as is reached allocation cost 6 at
the stated intrinsic entry state. The Input equivalence varies level, frame,
map and machine at that fixed state; it is not an all-state cost theorem.
A generic output adapter accounts for all eleven constructors and preserves
the complete memoryCalls fragment, heap, old-map and reached-cost relations.

The consumer is reindexed only by the proved fragment equality. Physical links
then derive its Input from the actual returned certificate, retaining all three
selected maps before tails, full outputs and both emitted-code associations.
[Controls](../../Solidity/Backend/Passes/CompilerCallScopeControls.lean) execute
the public selector's actual code and check the complete original 18-word
vector, skipped consumer, corrupted tail and private-frame refusal.
[Pins](../../Solidity/Backend/Passes/CompilerCallScopePins.lean) guard observed
standard axiom sets. Independent finder and skeptic source reviews found no
defect. Equality with the earlier manually packaged complete certificate was
not proved and is not a premise. This proves recognition of the middle scoped
stage, not public recognition of the whole three-stage join or independent
Source/world/ABI adequacy. H22 external-call construction is untouched.

## Whole scoped-call fixture recognition

[CompilerWholeScope](../../Solidity/Backend/Passes/CompilerWholeScope.lean)
closes the preceding fixture's middle-only recognition limit: public
`Compiler.compile` accepts the entire fixed allocation/scoped-call/consumer
program from the empty intrinsic context. The actual returned certificate's
private frame and reached allocation cost 8 supply its initial Input. Actual
execution and full MappedOutput share a selected map before all tails; exact
allocator ownership advances from 256 to 264 and all four objects remain.

A generic compiler-code association lemma follows typed syntax equality.
It is kept separate from execution correctness; the physical result follows
from independent intrinsic program execution and the actual certificate.
[Controls](../../Solidity/Backend/Passes/CompilerWholeScopeControls.lean) check
the complete original 18-word vector, corrupted tail and private-frame refusal.
A separately typed, publicly accepted unscoped program returns the different
context and changes the owned value from 33 to 42. It is not another association
of the scoped program. [Pins](../../Solidity/Backend/Passes/CompilerWholeScopePins.lean)
guard observed standard axiom sets. Independent finder and skeptic source
reviews found no defect. This is one inhabited intrinsic program family;
general compiler coverage, independent Source/world and bytecode adequacy
remain open. H22 external-call construction is untouched.

## Whole scoped-call failure recognition

[CompilerScopedFailure](../../Solidity/Backend/Passes/CompilerScopedFailure.lean)
uses the actual public compiler results for the complete allocation/scoped-call/
unreachable-consumer programs. Argument and body failures are inhabited by the
existing independent intrinsic runs, with exact reached costs 2 and 3. The
unreachable allocating suffix remains in the program and contributes no reached
cost. Original initial representation, private frame and allocator premises
supply Input. Typed compiler transport proves ordinary target revert for every
saved stack; source panic/divergence and target fault are separately excluded.
No post-failure state/map or ABI bytes are inferred. These fixed fixtures extend
the existing reached-prefix certificates rather than proving general Source or
compiler coverage. [Pins](../../Solidity/Backend/Passes/CompilerScopedFailurePins.lean)
retain exact observed standard-only axiom sets.

## Effectful conditional-expression consumer

[EffectfulConditionalAssignment](../../Solidity/Backend/Passes/EffectfulConditionalAssignment.lean)
consumes V07's published `ConditionalAssignments.transport` and the same intrinsic
assignment/capture/conditional program. Initial heterogeneous context alignment,
Boolean reflection, all six slot mappings, the actual memory compilation Input
and the result-value certificate remain explicit. Independent Source execution
and the full caller post-relation compose with emitted execution, full
MappedOutput and result readback. The machine, selected map and result word are
chosen before all saved tails. No P8 producer or desired final relation is assumed.

[Controls](../../Solidity/Backend/Passes/EffectfulConditionalControls.lean)
instantiate one emitted program for both runtime Booleans. The selected true arm
overwrites the caller's original condition while the fresh snapshot stays true.
Complete observations include all five original locals, both captures, allocator
cursor, independent sentinels and stack. Actual compiled eager and recapture/
re-evaluation suffixes produce different complete vectors. Joined readback,
saved tails and insufficient-frame refusal are checked.
[Exact axiom guards](../../Solidity/Backend/Passes/EffectfulConditionalPins.lean)
use only observed standard axioms. These are kernel and symbolic-word results,
not public admission, world/ABI or external compiler/EVM adequacy.

The changed-tree checkpoint attempt stopped at its original 300-second bound
while checking the pre-existing Source/Horizon dependency; later global gates
were not reached. The exact published conditional producer and these consumer
files pass separate serial per-file checks against their checked imports.
The failed combined attempt remains a failure, not a substituted passing gate.

## Context-correlated memory-reference capture

[RelatedMemoryCapture](../../Solidity/Backend/Passes/RelatedMemoryCapture.lean)
consumes V07's published `related_memory_capture`. Independent initial context
alignment derives the selected Source-reference relation, both context-extension
relations and exact caller recovery after dropping the temporary. The actual
memory certificate's original Input supplies emitted execution and full
MappedOutput with one selected map and machine before all tails. Pointer
readback uses that selected map; identity with the original reference address
follows from BaseExtends. It is not assumed as an output relation.

[Controls](../../Solidity/Backend/Passes/RelatedMemoryCaptureControls.lean)
inhabit the context relation with two live Source objects, two aliased old
intrinsic locals and an independent reference. Complete eleven-cell observations
retain all caller locals, the fresh capture, an independent cell, both array
lengths and every element, plus saved stack words. Actual wrong-reference and
skipped-capture runs differ; an incorrect initial reference relation is refused.
[Guards](../../Solidity/Backend/Passes/RelatedMemoryCapturePins.lean) pin the
observed standard axiom sets. The concrete client is nonallocating with base
zero; it does not claim positive-base allocator growth. The general theorem
retains the original branch allocator obligations. Extended Source locals
classify the returned reference; no Source declaration execution, general heap
content relation, admission/world or bytecode theorem follows.

## Plain storage-alias capture

[RelatedStorageCapture](../../Solidity/Backend/Passes/RelatedStorageCapture.lean)
consumes the paired published `related_storage_capture` through the existing
core compilation branch. The original `inFragP` certificate, plain `.ok` alias
fragment fact and full core Input remain explicit. Initial Sim.aliases supplies
the typed reference, symbolic Slot and PathSlot witness before all saved tails.
The exact existing load/store code and its actual successful execution derive
fresh-cell capture and appended pointer readback with full core MappedOutput.
Core Sim is not upgraded to memory ownership.

[Controls](../../Solidity/Backend/Passes/RelatedStorageCaptureControls.lean)
inhabit two distinct typed storage roots, the independent Source-local context
relation and original core representation. Public compiler option-code equality
recognizes the actual instructions; it is not a claim of dependent certificate
record equality. Complete selected-cell and stack observations distinguish real
wrong-alias and skipped-capture runs, and symbolic `.slot` from numeric `.val`.
[Exact guards](../../Solidity/Backend/Passes/RelatedStorageCapturePins.lean)
retain the observed standard-only axiom sets. This bounded application covers
plain aliases, not the separate fragile-alias case. It proves neither Source
declaration execution nor general storage contents, hashing/layout, decoding,
resource/session or world-to-bytecode adequacy.

## H21/H22 published synchronization

The lane rebased its twelve private checkpoints onto public
`603eef898f3a4a058a59e8fa7331b77f8cf6ec05`, including H22's explicit external-call
mode and invocation metadata. Existing pass source files were unchanged and
construct no core ExtCall values; no static-mode or provenance interpretation
is claimed. Pre-sync commits and their seals remain preserved separately.

H21 roots are regenerated by `scripts/coord-tools/register.sh`; new rows live
in the compiler-transport area map. Two unpublished, untracked V09 prototypes
were reversibly relocated outside the production source tree, retaining bytes,
inodes, sizes and timestamps. They remain private and were not resubmitted.
No checker exclusion, language profile or proof premise changed.

The cold post-sync import attempt stopped at the existing 300-second bound.
Separate published MemoryCompile and Compiler prerequisites then passed under
the same bound. The Source capture prerequisite, KeySort and the storage-capture
closure with thirteen exact guards also passed on the rebased tree. The broader
changed-module import attempt stopped at its unchanged 300-second bound and
remains incomplete. Two further old untracked scratch drafts were preserved
outside the production tree, resolving the orphan findings without an allow-list.
These checks do not establish the final combined lane gates or discharge the
remaining Source/world/resource producers.

## Open

General source/world/backend composition remains open. Concrete intrinsic
whole-program acceptance, such as `FreshBooleanCompilation.public_whole`,
is not general Source closure. G24 requires the actual Source/Lowering/world
and full public Cert producers. G24.01 also retains the abstract slot/root/hash/
data/offset interface and state/decode export; G24.03 remains unfrozen under C7; these adapters do not authorize its final
interface freeze. G25/G26 retain their stated scalar, general
source-admission and execution prerequisites. G31 belongs to VY4. ABI entry
premises do not close G24.03 by themselves. Whole-lane completion still
requires the original combined validation and producer obligations.
