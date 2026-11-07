# G38 failure statement paths

The initial interface uses the existing indexed `Source.RStmt`, actual
`Source.execS` execution and checked `Backend.Failure.Slice` execution.
`StatementReverts` records the reached state, including dirty writes; it does
not claim that an evaluator revert rolls back a caller. `Emits` retains the
existing byte-span and stack bounds and observes immutable bytes before unwind.
No complete EVM, gas, call convention or production compiler theorem follows
from the terminal slice interface.

## Producer boundaries

`Premises.EncodingAt` requires actual `Source.encodeVals` execution. The published
`Backend/AbiWorld/ErrorLayout` and `ErrorRoundtrip` discharge Error(string)
packet layout and decoder roundtrip in `ReasonCodec`. Their scope does not
prove general runtime custom-error or return encoding, so `EncodingAt` remains
explicit for those values. `InternalBareRevert` is the existing P1 interface; internal-frame
transport stays with v12-flow-calls. `IncompleteAt` retains source timeout and
does not turn resource exhaustion into revert (VY5 H16). `TransientRestored` is
only a source projection: physical transient representation/reset/rollback
remains VY4 P7's `Backend/Transient`. No unavailable producer instance is
postulated. These are explicit remaining obligations, not axioms.

## Checked statement increment

`Statements.compileStatement` is an executable partial selector over the existing
indexed `RStmt`. Its expression arm reuses G21 literal recognition: bare revert,
revert with a literal reason, false require (bare or literal reason), and false
assert with exact Panic(1) bytes. The other arm reuses G21's indexed Boolean
literal custom-error selector. It does not add another argument elaborator or
ABI encoder. True guards, effectful arguments and other statements are refused
by this helper; this does not reject their source semantics.

`compiled_statement` proves that **every successful decision** has an actual
`Source.execS` failure at an explicit sufficient finite horizon, with the same
payload as checked target-slice execution. It does not replace a timeout at a
smaller horizon. `expression_statement` retains the reached state for arbitrary
expression failures. Source failure class is its existing `Halt.revert payload`;
no extra distinction can be inferred solely from possibly equal payload bytes.
Panic origins other than the literal assert arm are not selected by this compiler.

`WorldUnwind.literal_world_unwind` executes the failure statement after arbitrary
real source journal operations. It separately proves the source caller rollback
and the existing local checkpoint execution, with bytes captured before restoring
persistent/transient projections and caller byte memory/stack. It does not
compile the supplied dirty prefix, identify the byte checkpoint with physical
world storage, or restore source heap/events/logs by implication.

`Returns.encoded_return` consumes actual upstream `encodeVals` execution. It
proves exact payload emission and the successful commit branch, retaining reached
store projections instead of the caller checkpoint. `boolean_encoding`
discharges the encoder premise for arbitrary Boolean lists and source states.
This is a return-payload boundary theorem, not compilation of arbitrary source
return statements.

`Controls` inhabits the statement/compiler simulations with a populated source
state, nonempty heap/events/journal, nonempty target stack/memory and an ignored
suffix. Kernel controls cover require/reason, assert, Boolean custom errors,
dirty persistent and transient journal rollback, true/effectful/skip refusal,
timeout retention, actual Boolean encoding, successful return after a dirty
prefix, and different outcomes for return/revert with identical bytes. Executable
observations run source require, assert, bare revert and custom errors in both
legacy and viaIR modes, plus target code and the actual return encoder. These
are checked-slice observations, not solc/EVM differential or whole-program tests.

## Validation and limitations

A direct statement proof failed before unfolding the hypothesis's `ExceptT.run`;
the shared scratch-tactic workflow found the retained proof. Further syntax,
instantiation and diagnostic import-map failures are retained as failures in the
external checkpoint evidence. Plain per-file `lake env lean` initially could not
locate content-addressed fetched artifacts; diagnostics use the matching actual
Lake setup file, without copying artifacts or forging traces.

Printed axioms of the new simulation theorems are only `propext`,
`Classical.choice`, `Quot.sound`. Independent read-only finder and skeptic
reviews found no confirmed defect in the checked increment, while explicitly
retaining the source/physical and return-statement boundaries above. Full
end-of-lane gates remain for a completed G38 checkpoint; none is asserted passed
by this focused increment.

Remaining G38 work includes general runtime condition/argument and nonliteral return
statement lowering, general G41 payload encoding, v12 internal-frame failure
transport, H16 resource/exhaustion points, and physical transient composition.
P7's published implementation has been consumed; its nonempty REVERT refusal
remains intact. G38 and G39 are not complete.

## P7 empty-failure composition

`TransientUnwind.empty_code` proves that `Failure.emit 0 .empty` is exactly
P7's published empty emitter. `paired_bare_failure` executes an actual source
transient write and the actual compiled bare-revert statement, alongside P7's
actual framed TSTORE/REVERT execution. It derives target caller restoration,
source journal rollback and the selected post-write cell relation. It supplies
no full initial source/physical state relation. `source_restored` restores the
whole source state only for this executed transient-only prefix, whose other
fields were unchanged. This replaces a P7 assumption in the supported case.

The inhabited controls use P7's nonempty journals, caller stack, memory, heap,
events, logs and persistent state. Both source pipelines and the target execute
empty failures. A separate executed nonempty emitter reports `unsupported` and
retains its dirty transient write. `no_current_payload_transport` kernel-refutes
`Premises.TransientPayloadAt` for the current nonempty emitter/adapter, for every
proposed byte machine and selected word-frame set. The residual predicate states
actual checked byte execution, actual P7 frame execution, and an explicit finite
word/byte relation. No instance is assumed, and no positive theorem consumes it.
It is not a universal source/world representation.

The remaining exact producer boundaries are:

- G41, v13-abi-world: the published `Backend/AbiWorld/ErrorLayout` and
  `ErrorRoundtrip` packet laws are consumed by `ReasonCodec` below. Their
  presence does not discharge general runtime value encoding:
  `Premises.EncodingAt` still specifies the actual upstream execution needed
  for those values. The packet modules themselves are not a missing dependency.
- v12-flow-calls: `InternalFlow/RuntimeFrameInterfaceV1.BareRevertClaim` explicitly
  excludes payload, panic and exhaustion. General internal-frame failure
  transport must come from that owner; G38 does not edit those modules.
- VY5 H16: source resource/exhaustion points remain outside `IncompleteAt`'s
  literal timeout equation. No timeout is reclassified as a completed revert.
- P7, VY4: `Transient.Instructions.step` refuses MSTORE8 and nonempty REVERT.
  Its current target cannot discharge the residual nonempty-payload contract.
  A payload-aware producer/interface is needed before general byte/transient
  unwind and G39 composition can be claimed; the source modules remain read-only.

The sealed pre-publication checkpoint retained the authorized relay and all
integration attempts. The active shared edit is the script-generated
`Solidity.lean` registration; no P7 implementation or shared documentation is
changed by the task range. Both independent reviewers found no confirmed issue
in the empty-failure composition or residual typed boundary. Printed axioms
remain only the three standard axioms (empty-code identity uses only `propext`).
Full G38 completion and its full end-of-lane gates remain outstanding.

## Published-base related-state check

`TransientUnwind.simulates_bare_failure` additionally requires the genuine
initial P7 `Represents` relation and proves that same selected-cell relation
after actual source caller rollback and actual target frame restoration.
`TransientControls.restored_relation` supplies the real inhabited initial
relation on P7's nonempty prefixes. The earlier execution-pair theorem remains
unconditional; it is not mistaken for a general initial-state simulation.
Neither `callback_load`, `callback_then_reset` nor the arbitrary-target
`SourceCallback.source_target` is used as a simulation premise.

Core source, P1, existing Failure and V11 dependencies and the toolchain were
unchanged across the published-base update. Independent finder and skeptic
reviews found no confirmed defect in the related-state theorem, its inhabited
control or the additive compatibility diff. General payload and whole-program
completion claims remain outside this checkpoint.

## Return signatures and literal Boolean return statements

`Parametric.compile` removes the original helper's void-return restriction.
For any return-type list and parameter count, it selects the same G21 literal
failure or Boolean custom-error code. `expression_tag` and `error_tag` prove
actual `execS` equality at every horizon, including timeout, for only those two
constructors. This is not general AST erasure or an internal return convention.
`selected_correct` derives actual source failure and checked target execution
for every successful decision. Inhabited controls use a reference-returning
body whose hidden return slot points at an actually allocated byte object;
its literal/custom failures run in both pipelines. Reference-return compilation
itself is not implied.

`BooleanReturn.compile` separately recognizes literal Boolean `retVal` statements
in a body with one Boolean hidden return slot, zero parameters and no additional
locals. Its successful-decision theorem proves actual slot overwrite, actual
`retVals` extraction from that returned slot, actual `encodeVals`, and checked
RETURN bytes under the unchanged fit/stack gates. The observer encodes in the
actual reached state. Both Boolean values have source/target executions in
both pipelines. A runtime-local return succeeds in source and remains explicitly
refused by this literal helper. Other signatures, runtime return expressions,
internal-frame transport and full function/world/EVM refinement remain open.
The old encoder-only theorem remains a separate boundary result.

The return matcher is polymorphic in contexts and uses G21's polymorphic literal
view, with syntax evidence eliminated only into its Prop certificate. This
avoids indexed `declTuple`/call-result elimination without changing Source ASTs,
representations or budgets. Failed direct attempts and successful scratch syntax
transport checks are retained. Printed axioms remain standard only. Both
independent reviewers found no confirmed defect; neither review promotes these
statement boundaries to frontend or whole-program support.
## Published Error(string) codec consumer

`ReasonCodec.layout` derives the Source packet offset, length word and exact
payload from the published G41 codec laws. `roundtrip` derives the decoder's
word-representability bound from the existing emission `Fits` premise.
`compiled_readback` connects actual parametric Source statement execution,
checked emission and decoder readback from the resulting byte memory, without
an assumed layout, successful emission or roundtrip. The controls use an
allocated reference return slot, both Source pipelines, boundary bytes and a
malformed-selector refusal. This discharges packet laws, not general runtime
ABI encoding, caller transport or full EVM correspondence. Independent finder
and skeptic reviews found no confirmed issue.

## Selected G39 sharing and reset composition

`TransientSharing.observed` executes the existing framed P7 body and captures
its stack head before `finish` restores the caller. `self_share` requires an
initial selected-slot relation and equal owner addresses, then proves actual
Source read/write/read and observed target values. `execute` sequences actual
framed store and read bodies. Static Source refusal and target `staticWrite`
remain distinct, and wrong-owner observations are discriminated.

`writeReset` performs an actual callback before reset. `reset_relation` links
actual Source `endTx` and target reset while preserving Source world/heap and
the complete ordinary target machine. `TransientComposition.mixed` executes
P7's ordinary persistent/memory instructions between transient store/read;
`mixedReset` then clears the bank/journal and preserves the reached persistent
and memory writes. These mixed target results do not provide Source lowering
for those ordinary instructions or a G24 state relation.

`TransientCallback.cell_port` consumes the registered Source callback fixture
with an initial relation and actual before/after readback; it retains the
fixture's Source memory invariants. The target code is its local store body,
not the complete CALL protocol. Arbitrary outer result bytes are the supplied
Source environment strategy answer, not the fallback's output or target-store
returndata. G42 code/account/strategy admission and full EVM correspondence
remain explicit boundaries. Neither weak `callback_load` nor the no-callback
`callback_then_reset` law is used. Inhabited and refusal controls execute
nonempty caller prefixes and both Source callback pipelines. Independent
finder and skeptic reviews found no confirmed issue.


## Framed payload emission

`FramedEmission` consumes the published physical byte-store producer.
`preserve_bytes` extends its untouched-word law to an entire actual payload
write. Its explicit sufficient separation premise puts the emitted byte interval
before or after every live complete word. It relates the reached bytes to the
same numeric memory observations; it does not refine an overlapping abstract
word store.

`emitter` derives the checked emitted program's reached slice, exact terminal
outcome, saved slice stack and word frame. No successful execution or final
frame is supplied as a premise. `compiled_reason` joins this with existing
public literal-statement selection, actual Source failure and decoder readback
from that same reached slice. The exact Error packet is locally generalized
with its defining equality retained to avoid eager byte-prefix normalization;
the statement and default proof limits are unchanged.

`FramedEmissionControls` inhabits a nonempty represented word and saved stack.
Both Source pipelines execute the reason-failure consumer, including an
allocated reference return slot. Writes immediately before and after the word
preserve it. A checked overlapping emission still reverts but invalidates the
old word frame, so separation is not silently waived. The Boolean-return client
also uses the existing public selector, actual hidden-slot overwrite, `retVals`,
`encodeVals`, successful checked emission and reached word frame. Printed axioms
are standard only. Independent finder and skeptic reviews found no confirmed
defect.

These are component-local byte-emitter and frame results. `WordFrame` alone
supplies no Source/world or stack correspondence. General runtime encoding,
internal-frame payload/panic/exhaustion transport, P7 nonempty rollback, gas,
allocation and full bytecode/EVM adequacy remain separate. The existing emitter,
compiler selections, refusals and overlapping-store counterexamples are
unchanged. Focused validation:

```
LEAN_NUM_THREADS=1 lake -f lakefile.g38.toml build Solidity.Backend.FailurePaths.FramedEmissionControls
```

The temporary config supplies Lean `-j1` and `Elab.async=false`; the inherited
resource guard remains required. The focused consumer passed in 3.039 seconds
with 902,086,656 bytes peak aggregate RSS. Its printed axioms are only
`propext`, `Classical.choice` and `Quot.sound`. The bounded full checkpoint
remained incomplete: timeout at 300.064 seconds, 1,830,236,160 bytes peak,
with `Yul.DirectUpdates` last logged complete. This is not a full-gate pass or
an attribution of the timeout to that module. All failed elaboration and build
receipts are retained in the handoff.


## Runtime bare Boolean-local guards

`FailurePaths.RuntimeGuard` connects an actual Source `require(local)` expression
statement to `Evm.Memory.compileStmt` selecting the intrinsic bare-require
statement. General Boolean operands are related by explicit initial local reads
and the existing full `Memory.StateRepr`, including its heap/base-map conditions.
No compiled certificate, desired execution or final representation is assumed.
The selected instructions are exactly the local MLOAD followed by `assertTop`.
The actual run returns the entire initial machine on true and bare revert on
false. The actual Source run retains all state and caller locals, returning
normally on true or reverting with empty bytes on false, at horizon `n+7`.
Zero horizon still times out.

`RuntimeGuardControls` inhabits the physical layout for both Boolean values and
either Source pipeline, with saved stack word 77 and nonempty source log and
function-local state. It distinguishes false from success, evaluates assert to
its panic bytes, and retains refusal of a runtime local by the older literal
statement selector. This is a relation between the supplied indexed Source and
intrinsic nodes; automatic frontend lowering, arbitrary guard expressions,
message-bearing require, assert compilation, bytecode/EVM execution, reverted
target poststate and internal-frame payload transport remain outside this leaf.
The instruction machine supplies no failure post-machine or payload bytes.

Focused check:

```
LEAN_NUM_THREADS=1 lake -f lakefile.g38.toml build Solidity.Backend.FailurePaths.RuntimeGuardControls
```

With serial Lean `-j1`, `Elab.async=false` and the existing inherited guard, this
passed in 2.763 seconds, peak aggregate RSS 818,483,200 bytes. Printed axioms are
only `propext`, `Classical.choice` and `Quot.sound`. Independent read-only finder
and skeptic reviews found no confirmed soundness or vacuity defect. The earlier
300.064-second full checkpoint timeout remains failed; this focused check does
not discharge it. No unchanged full retry was made for this leaf.


## Runtime relational guards

`FailurePaths.RelationalGuard` extends the bare-require result to `<`, `<=`,
`>` and `>=` of two signed256 or unsigned256 locals. It consumes the published
primitive comparison packet, including its exact operand order and signed
instructions. `public_selection` proves that the public checked memory statement
compiler selects the comparison instructions followed by `assertTop`.
`agreement` derives both actual executions from initial Source/intrinsic local
read correspondence and the full initial `Memory.StateRepr`; no selected
certificate, successful run or poststate is supplied as a premise. At horizon
`n+7`, Source returns normally or reverts with empty bytes and preserves all
state and caller locals. The selected target run either preserves the entire
machine, including the saved stack, or produces bare revert.

`RelationalGuardControls` inhabits the comparison fixture for arbitrary allowed
operands and both pipelines. Named controls cover equality for all relations,
signed sign boundary and extrema, maximum unsigned operands, equality failing
strict less-than, negative signed less-than succeeding, maximum unsigned
less-than zero reverting, zero-horizon timeout and the older literal selector
still refusing these runtime conditions. This is a proof about related supplied
indexed nodes, not an automatic frontend lowering. Arbitrary expressions,
message-bearing require, assert payload compilation, bytecode/EVM behavior,
reverted target poststate and internal-frame failure transport remain separate.
The instruction machine does not expose revert payload bytes or a post-machine.

Focused validation:

```
LEAN_NUM_THREADS=1 lake -f lakefile.g38.toml build Solidity.Backend.FailurePaths.RelationalGuardControls
```

The serial guarded check passed in 3.653 seconds with 814,166,016 bytes peak
aggregate RSS. All printed axioms are `propext`, `Classical.choice` and
`Quot.sound`. Independent read-only finder and skeptic reviews found no
confirmed defect. The prior full-checkpoint timeout is still failed; this
increment supplies no changed full-gate condition, and it was not retried.


## Runtime logical guards

`FailurePaths.LogicalGuard` connects `require(a && b)` and `require(a || b)`
over Boolean locals to public checked memory statement selection. It uses the
existing Source short-circuit evaluator and the compiler's `binaryCode`, with
its conditional jump around the second load, followed by `assertTop`.
`agreement` proves actual Source and selected target runs from initial operand
read correspondence and the full initial `Memory.StateRepr`. True preserves
the whole target machine and saved stack; false produces bare revert. Source
retains all state and caller locals and returns normally or reverts with empty
bytes at horizon `n+7`. No selected certificate or desired run is an input.

`LogicalGuardControls` inhabits all Boolean combinations and both pipelines,
including saved stack word 77. It retains the older literal-selector refusal
and zero-horizon timeout. Separate target-only controls deliberately put a
slot-tagged word in the right Boolean cell, outside `StateRepr`: evaluating it
as a guard faults and is proved not to revert. True OR skips it and returns the
whole machine; false AND skips it while evaluating the condition, pushing false.
The AND control does not claim successful require execution. These malformed
machine controls establish no additional Source correspondence.

This remains a relation between supplied indexed Source and intrinsic nodes.
Automatic frontend lowering, arbitrary or effectful operands, message/assert
payload compilation, reverted target state, internal-frame transport and full
bytecode/EVM adequacy remain separate. The target instruction machine exposes
no revert bytes or post-machine. No existing selector, failure outcome or
allocation-input policy changed.

Focused validation:

```
LEAN_NUM_THREADS=1 lake -f lakefile.g38.toml build Solidity.Backend.FailurePaths.LogicalGuardControls
```

The serial guarded check passed in 2.947 seconds with 820,215,808 bytes peak
aggregate RSS. Printed axioms are only `propext`, `Classical.choice` and
`Quot.sound`. Independent read-only reviews checked the source and the corrected
fault-versus-revert control. Failed initial proof attempts are retained. The
previous full checkpoint timeout remains failed and was not retried unchanged.


## Executable selection of Boolean-local guards

`FailurePaths.LocalGuardSelection.compile` inspects an actual indexed Source
statement and accepts bare `require(local)` for a Boolean local. Its dependent
view retains the source type, local index and statement equality. The caller
supplies an explicit Boolean-local context map; the selector constructs the
intrinsic guard and invokes public `Evm.Memory.compileStmt`. It does not accept
a supplied target node, compiled certificate or desired execution.

`selected_correct` proves both actual runs for every successful decision, from
initial local correspondence and full initial `Memory.StateRepr`. The Boolean
value is obtained from the recognized source local. At horizon `n+7`, Source
returns normally or reverts with empty bytes, preserving its state and caller
locals; selected target code preserves the whole machine on true or produces
bare revert on false. The public compiler selection is also part of the result.

`LocalGuardSelectionControls` consumes that success theorem with inhabited
memory, saved stack word 77, both Boolean values and both Source pipelines.
Literals, assert and message-bearing require are refused by this selector;
these are fragment refusals, not Source-language rejection. A separate negative
control refutes an incorrect initial local correspondence; the selector does
not check runtime values. Zero source horizon still times out. Existing literal
and other guard compilers and their refusal boundaries are unchanged.

This closes executable Source selection for this narrow indexed-statement leaf.
Constructing the context map, frontend/unit lowering, general conditions,
message/assert payload compilation, target failure poststate and bytecode/EVM
adequacy remain outside it. The target machine exposes no revert bytes or
post-machine; no internal-frame failure transport follows.

Validation target is `Solidity.Backend.FailurePaths.LocalGuardSelectionControls`.
The serial guarded check passed in 8.208 seconds with 1,053,290,496 bytes peak
aggregate RSS. Printed axioms are only `propext`, `Classical.choice` and
`Quot.sound`. Independent read-only finder and skeptic reviews found no
confirmed defect. Failed initial dependent-pattern/type-check attempts remain
in the handoff. The earlier full-checkpoint timeout remains failed and was not
retried unchanged.


## Executable selection of logical guards

`FailurePaths.LogicalGuardSelection.compile` recognizes bare indexed Source
`require(a && b)` and `require(a || b)` when both operands are Boolean locals.
It reuses the existing Boolean-local recognizer and retains actual operand,
type, operator and statement equalities. The selected Source indices pass
through an explicit context map, and compilation invokes public checked
`Memory.compileStmt`; callers supply neither an intrinsic target node nor a
successful target run.

`selected_correct` proves actual Source execution, public compiler selection
and selected target execution for every successful decision. Initial local
correspondence and full `Memory.StateRepr` are explicit. At horizon `n+7`,
Source preserves its state and caller locals and either returns normally or
reverts with empty bytes. Target code preserves the entire machine on true or
produces bare revert on false. The target instruction machine exposes no revert
payload or post-machine.

`LogicalGuardSelectionControls.success_client` consumes this theorem on an
inhabited layout with saved stack word 77 for both operators, all Boolean values
and both pipelines. Separate exact observations check the expected logical
result. The selector refuses local-only guards (handled by the separate local
selector), literal operands, assert and message forms. These are selector
boundaries, not Source-language errors. A negative control refutes incorrect
initial correspondence; compilation performs no runtime-value check. Zero
Source horizon still times out.

Context-map construction, whole-unit/frontend lowering, general or effectful
operands, message/assert payload compilation, internal-frame failure transport
and bytecode/EVM adequacy remain outside this result. No existing selector,
syntax representation or halt/allocation policy changed.

Validation target is `Solidity.Backend.FailurePaths.LogicalGuardSelectionControls`.
The serial guarded check passed in 3.043 seconds with 833,429,504 bytes peak
aggregate RSS. Printed axioms are only `propext`, `Classical.choice` and
`Quot.sound`. Independent read-only finder and skeptic reviews found no
confirmed defect. The failed initial dependent-rewrite attempt is preserved;
explicit evaluator congruence resolves it without changing the theorem. The
earlier full-checkpoint timeout remains failed; focused checks do not establish
a full build on the expanded published base.


## Executable selection of relational guards

`FailurePaths.RelationalGuardSelection.compile` recognizes bare indexed Source
require over `<`, `<=`, `>` or `>=` of two integer locals. Recognition checks
actual width 256 and retains signedness, local indices, operator and Source
syntax equality. It constructs the intrinsic guard through an explicit typed
integer context map and invokes public checked `Memory.compileStmt`.

`selected_correct` covers every successful decision. It obtains the integer
operands and their ranges from the recognized Source locals, uses explicit
initial read correspondence and full `Memory.StateRepr`, and derives actual
Source execution, public compiler selection and selected target execution.
No supplied target node, compiled certificate, desired run or poststate is a
premise. Source returns normally or reverts with empty bytes at horizon `n+7`,
retaining state and caller locals. Target preserves the whole machine on true
or produces bare revert on false, with no exposed revert bytes or post-machine.

`RelationalGuardSelectionControls.success_client` consumes this theorem on
inhabited full-width inputs for all four relations, either signedness, arbitrary
in-range operands and both pipelines. Exact controls also cover equality, the
signed sign boundary and maximum unsigned value, with saved stack word 77.
The fixture's structural integer-index map preserves indexed types; its semantic
read relation is proved separately for the full-width fixture. It is not a
whole-program lowering producer.

Narrow integers, nonlocal operands, assert and message forms are refused by
this selector. An actual uint8 Source guard succeeds in both pipelines while
remaining refused, so the width boundary is not Source-language rejection.
Zero source horizon still times out. Existing selectors and policies remain
unchanged. General operands, whole-unit/frontend lowering, context-map
construction, payload compilation, internal-frame transport and bytecode/EVM
adequacy remain outside this result.

Validation target is `Solidity.Backend.FailurePaths.RelationalGuardSelectionControls`.
The serial guarded check passed in 4.069 seconds with 827,912,192 bytes peak
aggregate RSS. Printed axioms are only `propext`, `Classical.choice` and
`Quot.sound`. Independent read-only finder and skeptic reviews found no
confirmed defect. The uint8 control required explicit pipeline cases; its failed
initial proof and scratch automation are retained. The earlier full-checkpoint
timeout remains failed; these focused checks do not establish a full build.


## Unified checked guard entry point

`FailurePaths.CheckedGuards.compile` dispatches actual indexed Source statements
to the local-Boolean, logical-local and full-width relational-local selectors.
It invokes those existing public-memory-compiler paths without introducing an
AST or interpreter. `Maps` and `Related` group their existing typed index
functions and initial read premises. They do not construct or replace a
whole-program context/position/origin/alias relation.

`selected_correct` proves actual Source and target execution for every successful
dispatch from the grouped initial read relation and full `Memory.StateRepr`.
It returns a Boolean observation: at horizon `n+7`, Source preserves state and
caller locals and either returns normally or reverts with empty bytes; target
code preserves the whole machine on true or produces bare revert on false.
`selected_public_compiler` separately derives an actual intrinsic target and
checked certificate, public `Memory.compileStmt` selection, and exact equality
of the returned code. No target, certificate or desired run is supplied as an
input to either theorem.

`CheckedGuardsControls` uses one inhabited mixed context with two Boolean and
two unsigned256 locals, exactly reserved frame 4 and saved stack word 77.
The same maps, initial read relation and full representation support all three
unconditional source selections. Each branch consumes unified correctness and
exact public compiler provenance. Further controls distinguish OR success, AND
revert and relational outcomes, preserve zero-horizon timeout, refuse literals,
assert and message forms, and refute incorrect initial correspondence. Selector
refusal is not Source-language rejection; the existing literal-failure compiler
remains separate and unchanged.

This is the union of the three narrow pure guard fragments. General or effectful
conditions, argument/body/whole-unit lowering, context-map construction, payload
compilation, target failure poststate, internal-frame transport and bytecode/EVM
adequacy remain outside it. The target machine exposes no revert bytes or
post-machine. No existing source, compiler, syntax or halt/allocation policy
changed.

Validation target is `Solidity.Backend.FailurePaths.CheckedGuardsControls`.
The serial guarded check passed in 5.273 seconds with 856,449,024 bytes peak
aggregate RSS. Printed axioms are only `propext`, `Classical.choice` and
`Quot.sound`. Independent read-only finder and skeptic reviews checked execution,
public-code provenance and inhabited branch clients without confirmed findings.
The initial equality-substitution name error and scratch automation are retained.
The earlier full-checkpoint timeout remains failed; focused checks do not
establish a full build on the expanded published base.


## Computable intrinsic guard lowering

`FailurePaths.GuardLowering.lower` produces an existing intrinsic `Stmt` directly
from the three admitted indexed Source guard views. It does not extract data
from an existential proof or introduce another AST. Its compiler stage calls
public `Memory.compileStmt` once on the computed target. `compile_eq_checked`
proves exact equality with the prior checked dispatcher for every Source input,
including unsupported forms, so code and refusal boundaries are unchanged.

`lowered_require` characterizes every successful target as a Boolean require;
`lowered_compiles` derives actual public checked compilation success for every
lowered target. `selected_correct` derives actual Source and compiled runs from
successful executable selection, initial typed read correspondence and full
`Memory.StateRepr`. `lowered_correct` is the typed consumer: its lowering and
public compiler equations must hold, and it then derives the same runs. Neither
consumer assumes a desired execution or poststate.

`GuardLoweringControls` computes all three targets in the inhabited mixed
Boolean/integer context, proves their public compiler choices and exact code,
and consumes the typed lowering theorem in both Source pipelines. Literal,
assert and message refusals remain explicit; general refusal equivalence is
also proved. The old context-map, range, frame, source horizon and target failure
observation limits are retained. This is productive statement lowering for the
existing guard leaves, not body/program/whole-unit lowering, a context-map
producer, payload or internal-frame transport, or bytecode/EVM adequacy.

Validation target is `Solidity.Backend.FailurePaths.GuardLoweringControls`.
The serial guarded check passed in 5.418 seconds with 830,263,296 bytes peak
aggregate RSS. Printed axioms are only `propext`, `Classical.choice` and
`Quot.sound`. Independent read-only finder and skeptic reviews found no
confirmed defect. The historical full-checkpoint timeout remains failed;
focused checks do not establish a full build on the expanded published base.

## Finite guard sequences

`FailurePaths.GuardSequences` lowers finite lists of the admitted indexed
Source guards to the existing intrinsic `Prog`. Its `items` function builds
existing Source `RItems`; this entry point does not recognize arbitrary source
blocks or add an intermediate language. The compiler calls public
`Memory.compileProg` on the computed program. `lowered_public` derives public
compilation success and the unchanged fragment for every successful lowering.

`lowered_correct` and `selected_correct` derive actual Source `execItems` and
selected instruction execution with horizon `n + statements.length + 7`.
Each normal guard preserves the locals, Source state and full target machine,
so the next guard uses the original read and representation premises. The first
failure short-circuits the suffix and propagates empty Source revert and bare
target revert. Supplied maps, typed read correspondence and full `StateRepr`
remain necessary; no execution, desired poststate or compiler witness is
assumed by the executable-selector theorem.

`GuardSequencesControls` compiles a mixed three-guard list through the public
compiler, proves its exact concatenated instructions and instantiates the
general theorem in both Source pipelines. `source_run` and `target_run` identify
the result as the conjunction of the three conditions, including unchanged
state/machine on success. Controls distinguish success, first/middle/last
failure, equality rejection by `<`, empty compilation, zero-horizon timeout
and static refusal of a literal guard in the suffix. General effectful bodies,
Source block recognition, payload/internal-frame transport and physical
bytecode/EVM correspondence are outside this result.

The focused serial check passed in 4.872 seconds with 1,082,912,768 bytes peak
aggregate RSS. All printed new theorem axioms are standard only. A failed
recursive simplifier attempt reached the existing heartbeat limit; replacing
it with one evaluator rewrite discharged the same claim without raising limits.
Earlier failed full-checkpoint validation remains failed, and this focused
sequence result does not establish a full build on the expanded published base.

## Direct indexed Source-items selection

`FailurePaths.GuardBodySelection` accepts existing indexed Source `RItems`
directly. Its executable structural `view` recognizes expression-statement
sequences and records their unchanged output context and exact reconstruction
from existing statements. This structural view alone does not admit arbitrary
expressions as guards: the downstream `GuardSequences` compiler still checks
each statement against the same three guard families. Assignments, for example,
are structurally expression statements but their compilation is refused.

`compile` uses that computed view and the public memory program compiler.
`selected_public` derives its exact intrinsic program, public compiler choice,
unchanged fragment and code. `selected_correct` derives actual execution of the
original Source items, using reconstruction rather than a supplied statement
list or desired run. Its horizon is `n + admitted.statements.length + 7`; the
admitted witness is computed by `view`, not a new execution premise. Typed maps,
initial read correspondence and full `StateRepr` remain explicit. The view is
general over existing Source indices to permit structural recursion; the
compiler entry point still takes equal input/output contexts, no declared
returns, no modifier and the body statement context.

`GuardBodySelectionControls` passes a nonempty mixed Boolean/integer Source
items body to the new entry point, proves its exact public-selected code and
consumes the correctness theorem in both pipelines. Exact Source and target
observations reuse the checked three-condition result. Empty selection,
zero-horizon timeout, skip/unchecked/context-growth structural refusals and
assignment/literal-guard compiler refusals are explicit. These are scope
refusals, not claims that Source rejects those programs. Root `.block` statement selection is handled separately below. General
effectful bodies, context-map construction, internal-frame payload transport
and physical bytecode/EVM adequacy are not supplied here.

The focused serial check passed in 2.944 seconds with 837,017,600 bytes peak
aggregate RSS and no new source warnings. All sixteen printed theorem reports
use only `propext`, `Classical.choice` and `Quot.sound` (or subsets). No proof
budget was raised. Earlier failed full-checkpoint validation remains failed;
focused selector checks do not establish the outstanding full build.

## Root guard-block statements

`FailurePaths.GuardBlockSelection` recognizes an actual root Source `.block`,
computes its existing structural body view and lowers the admitted guards to
an intrinsic `.block` program. It invokes public `Memory.compileStmt` on that
statement. `block_public` proves the actual public block-arm choice;
`selected_public` derives both program and statement compiler provenance and
exact returned code. `compile_of_view` proves equality with the established
sequence compiler for every recognized block, including downstream refusals.
The selected statement fragment is the public compiler’s restricted inner
fragment; the code is exactly the inner program code.

`restore_self` and `close_normal` prove the actual Source local-restoration
operations. `body_correct` composes the checked sequence execution with
`Out.close`; `selected_correct` derives original Source statement execution at
`n + admitted.admitted.statements.length + 8` and selected instruction execution.
The extra horizon step is the root block. Initial typed maps/read correspondence
and full `StateRepr` remain explicit; normal completion restores the same locals
and Source state and preserves the complete target machine. Empty Source revert
and bare target revert propagate unchanged. No target post-failure machine,
execution oracle or supplied desired certificate is assumed.

`GuardBlockSelectionControls` consumes the root selector in the inhabited mixed
context in both Source pipelines. Concrete joint Source/target controls cover
success and first/middle/last failure; exact general observations are also
proved. Zero and one horizon retain timeout. Empty blocks compile; bare guards
at this block-only entry point, skip/unchecked/declaration bodies and assignment
bodies are refused. The other guard entry points retain their own behavior.
This closes root-block selection for the existing unchanged-context pure guard
sequence, not general nested/effectful bodies, frontend admission, internal-call
failure transport or physical bytecode/EVM correspondence.

The serial focused control check passed in 4.558 seconds with 823,193,600 bytes
peak aggregate RSS and no new source warnings. All twenty-six printed theorem
axiom reports use only `propext`, `Classical.choice` and `Quot.sound` or subsets.
Earlier full-build timeout and the published calculus-plan doc-path failure
remain open; this result does not turn either failed gate into a pass.


The RelationalGuard pair now guards all fifteen existing axiom reports with
exact expected messages. Every report retains only propext, Classical.choice
and Quot.sound. The theorem statements, proof terms and existing controls are
unchanged. A deliberately incorrect empty expected inventory is rejected;
both guarded modules pass. Independent read-only finder and skeptic reviews
found no confirmed defect. This inventory follow-up changes no correspondence
claim or failure boundary.

The LogicalGuard pair also guards all nineteen existing axiom reports against
their actual output, including the smaller two-axiom representation report.
The generated g07 inventory records those nineteen and the preceding fifteen
RelationalGuard entries, without changing or removing any recorded pin.
Both guarded modules pass, and an incorrect empty expected inventory is
rejected. Short-circuit and poisoned-right observations, theorem statements
and proof terms are unchanged. Read-only finder and skeptic reviews found no
confirmed defect; the pin check reports zero errors and no unrecorded changes.

## Local custom-error arguments under explicit producer contracts

EncodedError derives a real singleton local argument evaluation and custom-error
statement run from the existing Premises.EncodingAt equation. Argument type and
implicit identity conversion remain intrinsic. Parameter count and return
signature are retained, and selector bytes come from the actual Source global.
No completed statement run or target run is assumed as the encoder premise.

Emission derives actual checked byte execution, exact readback, saved-stack
preservation, terminal suffix absorption and a disjoint numeric/byte WordFrame.
That frame is not a whole Source/world representation. World unwind separately
derives Source journal rollback and local checkpoint restoration from an
explicit actual operation-list witness. It does not restore Source heap, logs,
events or function locals implicitly.

| Consumer | Explicit fact | Producer or discharge |
|---|---|---|
| source_run, emitted_frame, world_unwind | Existing Premises.EncodingAt for the actual value and reached state | G41 general encoder; Boolean controls discharge it |
| source_incomplete | Existing Premises.IncompleteAt for the actual encoder | H16 failure-point producer; no general instance supplied |
| arguments_incomplete | Existing Premises.IncompleteAt for the actual arguments and reached state | H16; actual zero-fuel local control supplies an instance |
| world_unwind | reached.ex = caller.ex.run ops | Caller operation-list witness; dirty-journal control discharges it |
| transient_transport | Existing Premises.TransientPayloadAt | P7 nonempty transport remains an explicit hypothesis |

Boolean controls quantify over both pipelines, using populated Source state,
a nonempty physical frame and saved stack. They derive nonempty custom failures
from local values, distinguish bytes, reject a false encoder equation, preserve
zero/one-horizon timeout and prove timeout is not revert. A dirty persistent
and transient journal is actually unwound by the component checkpoint.
The old literal selector still refuses this local argument, and the existing
P7 nonempty-adapter counterexample remains.

This is an encoder/emitter-boundary consumer, not new public compiler admission,
frontend lowering, whole Source/physical/world adequacy or internal-call frame
transport. The P7 theorem supplies no nonempty producer instance. The journal
components do not establish Source/target dirty-prefix correspondence.
All 21 theorem inventories are guarded against actual standard-only reports.
Independent read-only finder and skeptic reviews found no confirmed defect.
Registration and pin proposals are left for coordinator-owned shared files.

The final guarded general module passed in 18.468 seconds and its control module
in 2.854 seconds, with 1,220,100,096 bytes peak aggregate RSS. Neither owned
module exceeded 60 seconds. The checks use one Lean thread and unchanged proof
budgets; these focused results do not assert that the full lane gates pass.

## Nonhalting encoder prefixes and terminal failure

`PrefixFailure` derives checked execution of a REVERT suffix from an actual
nonhalting checked prefix, its offset/length stack layout, payload readback,
and existing capacity bounds. It preserves reached memory and restores the
saved stack; later instructions are absorbed by the terminal outcome.
`source_terminal` combines this with the local Source error evaluation under
the existing explicit encoding premise. It does not assume the completed
terminal run. The public writes/PUSH emitter supplies an inhabited prefix
witness, and `public_emitter` identifies its code with the existing emitter.

The G41/V11 adapter must supply a runtime encoder's actual prefix execution,
layout and readback; G41 supplies Source encoding. Automatic runtime compiler
selection, initial Source/target representation, dirty-prefix world coherence,
bytecode adequacy and internal-frame failure transport remain open. These
results do not construct those producers.

Both-pipeline controls retain populated Source state, a saved stack and a
disjoint live word. They reject early terminal prefixes, unsupported instructions
and swapped offset/length operands, and preserve timeout and compiler refusals.
All 21 theorem axiom reports are guarded; only the existing standard axioms occur.
Independent read-only finder and skeptic reviews found no confirmed defect.
The final general and control checks passed in 1.94 and 1.42 seconds respectively
under the unchanged serial resource/proof limits; full-lane completion is not claimed.

The generated Solidity library root now imports EncodedError,
EncodedErrorControls, PrefixFailure and PrefixFailureControls. All 42 axiom
reports across these modules are guarded, including every PrefixFailure report.
Fresh per-file elaboration executes these guards and the controls successfully.
Registration is checked with the repository generator; no proof statement,
producer boundary, execution result or refusal changes in this repair.
