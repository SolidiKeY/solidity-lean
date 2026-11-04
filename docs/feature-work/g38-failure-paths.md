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
