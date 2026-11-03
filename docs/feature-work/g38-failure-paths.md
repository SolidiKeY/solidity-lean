# G38 failure statement paths

The initial interface uses the existing indexed `Source.RStmt`, actual
`Source.execS` execution and checked `Backend.Failure.Slice` execution.
`StatementReverts` records the reached state, including dirty writes; it does
not claim that an evaluator revert rolls back a caller. `Emits` retains the
existing byte-span and stack bounds and observes immutable bytes before unwind.
No complete EVM, gas, call convention or production compiler theorem follows
from the terminal slice interface.

## Producer boundaries

`Premises.EncodingAt` requires actual `Source.encodeVals` execution. General
custom-error and return encoding remains G41, v13-abi-world's
`Backend/AbiWorld/ErrorLayout` and `ErrorRoundtrip` (not on this published base).
`InternalBareRevert` is the existing P1 interface; internal-frame transport stays
with v12-flow-calls. `IncompleteAt` retains source timeout and does not turn
resource exhaustion into revert (VY5 H16). `TransientRestored` is only a source
projection: physical transient representation/reset/rollback remains VY4 P7's
`Backend/Transient`. It is consumed from published master (`e80eae28`, base `24149fd5`)
for the supported empty-failure case below. No unavailable producer instance is
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

The same managed VM reports Lean 4.24.0 and Lake 5.0.0-src+797c613. The runtime
`lake -f lakefile.g38.toml build Solidity.KeySort` passed (0.304 s, peak group
RSS 48,553,984 bytes). All Lean checks use one thread, explicit `-j1` and the
unchanged 300-second bound under the authorized `bounded.py` fallback: hard
12 GiB per-process address space, sampled 10 GiB group-RSS and 12 GiB whole-VM
stops, existing 16 GiB VM cgroup and actual disabled swap. This is not a writable
12 GiB group-cgroup guarantee.

The initial interface build failed on two namespace qualifications after
150.077 s and 988,758,016 bytes peak RSS; the corrected build passed. A direct
statement proof failed before unfolding the hypothesis's `ExceptT.run`; the
shared scratch-tactic workflow found the retained proof. Further syntax,
instantiation and diagnostic import-map failures are retained as failures in the
external checkpoint evidence. Plain per-file `lake env lean` initially could not
locate content-addressed fetched artifacts; diagnostics use the matching actual
Lake setup file, without copying artifacts or forging traces.

The final affected target command is
`lake -f lakefile.g38.toml build Solidity.Backend.FailurePaths.Controls`:
exit 0, 5.257 s, peak group RSS 920,707,072 bytes. Printed axioms of the new
simulation theorems are only `propext`, `Classical.choice`, `Quot.sound`.
Independent read-only finder and skeptic reviews found no confirmed defect in
the checked increment, while explicitly retaining the source/physical and
return-statement boundaries above. Full end-of-lane gates remain for a completed
G38 checkpoint; none is asserted passed by this focused increment.

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

- G41, v13-abi-world: general upstream ABI/error encoding via
  `Backend/AbiWorld/ErrorLayout` and `ErrorRoundtrip` is absent from this base.
  `Premises.EncodingAt` specifies the actual upstream execution needed.
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
integration attempts. The active branch is rebased onto published `24149fd5`,
which contains P7 as `e80eae28`; the relay dependency commits are absent from the
active task range. P7 differs from `55c76891` only in three corrected docstrings.
The active shared edit is the script-generated `Solidity.lean` registration;
no P7 implementation or shared documentation is changed by the task range. The remaining P7 dependency targets (`SourceCallback`, `Mixed`,
`WordControls`) built successfully in this VM: 5.958 s, peak group RSS
725,331,968 bytes. The final owned typed-refusal target passed in 2.736 s,
peak group RSS 884,117,504 bytes. Both independent reviewers found no confirmed
issue in the empty-failure composition or residual typed boundary. Printed
axioms remain only the three standard axioms (empty-code identity uses only
`propext`). Full G38 completion and its full end-of-lane gates remain outstanding.

## Published-base related-state check

`TransientUnwind.simulates_bare_failure` additionally requires the genuine
initial P7 `Represents` relation and proves that same selected-cell relation
after actual source caller rollback and actual target frame restoration.
`TransientControls.restored_relation` supplies the real inhabited initial
relation on P7's nonempty prefixes. The earlier execution-pair theorem remains
unconditional; it is not mistaken for a general initial-state simulation.
Neither `callback_load`, `callback_then_reset` nor the arbitrary-target
`SourceCallback.source_target` is used as a simulation premise.

The published-base affected command built both
`Solidity.Backend.FailurePaths.TransientControls` and
`Solidity.Backend.FailurePaths.Controls`: exit 0, 16.672 s, peak group RSS
918,130,688 bytes. Core source, P1, existing Failure and V11 dependencies and the
toolchain were unchanged across the published-base update. Independent finder
and skeptic reviews found no confirmed defect in the related-state theorem,
its inhabited control or the additive compatibility diff. General payload and
whole-program completion claims remain outside this checkpoint.

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
transport checks are retained. The combined Boolean-return-control/parametric
compiler build passed in 6.269 s (peak group RSS 903,401,472 bytes); the parametric
reference controls passed in 3.031 s (908,365,824 bytes). Printed axioms remain
standard only. Both independent reviewers found no confirmed defect; neither
review promotes these statement boundaries to frontend or whole-program support.
