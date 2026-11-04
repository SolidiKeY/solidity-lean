# Inline assembly VY4: Yul world interface

`Yul/World/**`, from the vy4-world lane. It builds on master's Source world
(`Source/Observe`, `Source/World`) and backend byte constants.

- `Raw`: RETURNDATACOPY windows, call output prefix, CREATE/CREATE2 addresses
  (`overwrite` ignores its old argument, so `overwrite_last` is definitional).
- `Observations`: logs, observations and rollback of traces;
  `ObservationAgreement` has only the identity instance.
- `Frames`, `Adapters`, `ByteMemory`: frame completion, `callAdapter`,
  `logAdapter`, `copyReturndata`, a `BytePort` over backend memory.
  `WorldPort`/`FrameAnswer` are interfaces: on success they accept arbitrary
  operations (including caller-storage writes under STATICCALL); the only
  producer here is a scripted one in the checks.
- `AdapterRules`, `ReturnSize`, `CreationFrames`, `CreationRules`,
  `CreationAddressing`: step rules; each takes the adapter equation that
  defines its `Step`, so they are determinism lemmas.
- `Lifecycle`, `LifecycleAdapter`: the EIP-6780 SELFDESTRUCT lifecycle.
- `*Checks`: controls.

Logs (G01): log entries are observations recorded with the frame and rolled
back with it.

Open: real port producers (physical completion, caller frames, effectful emit
rollback, static environment invocation), the P7 transient target (TLOAD/TSTORE
consumers), port laws for the step rules.

## Returndata bridge and target-call output (sched 2026-11-03)

- `SolidityBridge.YulWorld.Returndata` (Bridge) consumes the frozen P10 API and
  `ReturnCopyBounds`: successful gate/operand facts give the copy-source bounds,
  the `Raw.returnWindow` bytes and the charged native successor; rejected
  windows fail only after both gas checks. No byte readback, padding or
  source/compiler origin. `ReturndataControls` holds the populated controls.
- The six equation-premised port lemmas are renamed `copy_step_eq`,
  `call_step_eq`, `log_step_eq`, `size_step_eq`, `initcode_step_eq`,
  `addressed_step_eq` (statements unchanged): determinism from an adapter
  equation, not source reachability or Yul/G51 soundness. The in-module
  `#print axioms` lines were dropped.
- `TargetCallMemory.call_output_exact` / `call_output_readback` /
  `call_output_frame`: input loading plus a supplied producer invocation, the
  target output store, the copied prefix and every byte outside it, for success
  and revert. `TargetCallRules.call_output_box` derives the normal-return `Box`
  from preflight, output extent, input loading and the invocation equation (not
  from the desired `CallStep`). `TargetCallControls` is a registered module instantiating all four laws on
  the existing `AdapterChecks` fixture. Explicit success/revert witnesses and
  live Box applications retain the full observer, output prefix and arbitrary
  outside-byte framing. The producers remain scripted, not reachable-callee
  or static-world certificates.

Open: actual callee/initcode execution, the full-slot carrier (needs
`OwnedBoolFrame` and its storage closure, not in the published Views), common
source emit/G01, compiler returndata noninterference, the scripted `WorldPort`
static-write weakness.

## Source-compatible physical consumer input

Actual frame calldata is retained through `sourceFrameOfCall` and source entry.
Ordinary success, nonempty error, static and low-fuel helpers quantify calldata
without changing their bodies, results or horizons. Original failed checks are
retained; affected rechecks and source/object identities cover the original
273-module request plus its added actual input adapter. The generated scoped
audit checks 527 declarations and 351 standard-only theorem axiom reports.
Source and producer files are unchanged. This private input is not published
world/allocator/G01/compiler or final calculus adequacy.

The registered target-control audit separately checks 15 declarations and 11
theorem axiom reports. Both checkpoints have independent read-only finder and
skeptic reviews with no findings. Full lane/joint gates remain open.

G07 still exits1 on an unrecorded `foo []` pin in the preserved external Mathlib
test cache; the official collector/compare yields the same finding on that exact
integration base with the same cache. This equality is not G07 passage or an
original pinned-base comparison. Historical failures remain retained separately.

## Selected delegate consumer compatibility

Calldata-parameterized body helpers preserve old empty defaults and use actual
input at entry. The selected registered code executes its real typed persistent
write at caller storage, with inherited sender/value and no transfer. Existing
success, nonempty revert, pending timeout, static write-refusal, full-carrier
rollback and bounded output controls pass. Their code/classification/depth,
representation, shared-world and memory premises remain explicit; no desired run
or outcome premise is introduced.

The generated audit checks 363 declarations and 250 standard-only theorem
axiom reports. Source and VY2 definitions and all budgets are unchanged;
normalizing only the frame term avoids the retained heartbeat failures.
Independent read-only finder/skeptic reviews found no issues. The immutable
private package includes the required output-transport dependency and verifies
all checked source hashes against its committed tree. It is a development
input, not universal delegate/environment, allocation/G01/compiler/resource,
intrinsic G51 or final joint adequacy. Original work/backfill queues remain
partial and the persistent goal is unchanged.

Their twenty fresh file checks pass; the scoped audit checks 207 declarations
and 106 standard-only theorem reports. All 287 transitive source identities
match the committed tree. Reused objects are bound by exact source/object pairs
to prior verified seals, not modification times alone. Independent reviews are
clear. Local-only arguments, formatting/placement premises and selected
execution scope remain explicit; universal G01/allocator/world and final
calculus/compiler adequacy are not established. Peer agreement consumers remain
separate work.

Eleven additional files and the generated 17-declaration/12-theorem audit pass.
These are concrete byte transport, typed account framing and journal laws;
creation outcomes remain scripted. No initcode or callback reachability,
Source/compiler/static/world adequacy follows. Actual intrinsic world-builtin
binding and G51 effect closure remain owned/open work; executable creation still
requires V08 P15 CTOR/SS-NEW and VY5 H16. The original goal is unchanged.

## Intrinsic LOG leaf

`LogBuiltin.logBuiltin` consumes the existing arity-indexed `Builtin a 0` and
already evaluated `Fin a` word operands. LOG0 through LOG4 use offset/size at
positions0/1 and topics in positions2onward, without cleaning high bits.
The actual frame supplies emitter/storage address and static status. Existing
logAdapter/emitObserved carry the full world, returndata and ordered trace.
Other constructors return none because this partial leaf does not handle them;
this is not admission refusal or an exceptional-halt certificate.

Five exact binding laws and the static guard kernel-check. Registered controls
cover all arities, a topic above2^255, wrong topic order, actual delegated emitter,
static and missing-byte refusals, and complete failed-frame observation rollback.
Generated audit:26declarations/17standard-only theorem reports. Independent
read-only finder/skeptic reviews are clear. No Yul AST, source, admission or
producer definitions change. Operand evaluation order, full runner integration,
Source/G01/compiler/resource adequacy and G51 remain open.

## Layout-aware transient target port

`World/TransientTargetPort` imports VY2's actual `TransientSlots` and the
local P7 target executor without changing either producer. `store` first
executes the checked physical Source/residual operation and retains its full
result, then executes the target callback in the supplied real Source frame.
Preparation failure returns `none`; it is not an EVM exceptional halt or
Source timeout. When static preparation succeeds, it returns the producer's unchanged
Source/residual result carrying `.revert []`, paired with the local target's
`.staticWrite` error and unchanged target. These distinct verdicts are kept.

`load_assuming_view_agreement` observes the actual loaded target word before restoring the
caller machine and requires pointwise agreement with `transientSlotLoad`.
`store_exact` derives the actual paired target run from checked physical
preparation and a nonstatic frame. `store_readback` uses VY2's real
`transientSlot_load_store` law and finite separation to establish full-word
agreement at the written slot. It does not claim preservation of every other
physical slot or a whole-bank representation invariant. `reset_readback_zero`
uses actual typed default/codec zero facts to relate every slot after both
transaction resets. No new world, layout or caller-reachability assumption is
introduced; the matching-view premise is explicit and remains to be derived
at universal source/compiler boundaries.

`TransientTargetControls` instantiates the actual declared uint16 transient
cell with dirty complementary bytes, a persistent caller prefix, two prior
Source/residual journal entries, and a distinct-owner target journal entry.
Actual store changes the cell to `0xabcd`, retains complement `0xb6b60000`,
and extends both physical journals to length three. Full raw readback is not
silently cleaned to the logical low uint16. Controls also cover static refusal
with complete carriers, another target owner/key and unowned-slot reset.
Kernel controls remain separate from the retained finite solc/EVM evidence.

Original queue: Y07.01 (including V08 P15/SS-NEW and VY5 H16 creation/initcode),
Y07.02 general known/environment/delegate/lifecycle/common emit/G01 adequacy,
Y09.03 G51 embedding and joint closure, and Backfill A/B universal integration
remain partial. Available VY2 Views are used here, not reported absent.
Compiler last-source-frame returndata noninterference, resource and allocation
adequacy and final mandatory lane gates remain open. This port certifies local
physical/target effects only, not full Yul admission or compiler correctness.

Validation: the 128-module combined import closure reused 49 exact-source
objects and serially compiled 79 modules. The port, seven new controls and
complete 15-declaration signature/axiom report pass per-file checks. Reports
use no custom axioms or `sorryAx`. Independent read-only finder/skeptic reviews
found no semantic issues; the static-availability wording was clarified.
Layering, generated root reachability, doc paths and trust pass. Failed reset
normalization, missing output-directory and dependent-value decision attempts
remain retained. These isolated CLI checks do not replace final Lake/full
build, TestSuite/strict, runtime KeySort or original joint-lane gates;
historical G07 failures remain failures.

## Full transient caller-prefix rollback

`TransientTargetRollback.store_rollback` consumes the actual checked physical
operation used by `TransientTargetPort.store`. It derives the executed target
callback and proves that rollback at the actual Source/residual entry and the
target entry journal length restores the complete `(Source.EMState, residual,
target)` tuple. Heap, intrinsic locals, function locals, events and legacy
logs are retained from the real operation, not projected away or assumed
unchanged. The proof extracts the checked packed plan, uses the producer's
nonstatic Source execution and paired rollback, and reuses target rollback.

`store_two_outer_rollback` derives both actual coupled stores and restores the
same full tuple after both successful effects when the enclosing entry is
rolled back. Its premises are the two checked preparations and a nonstatic
frame; neither an outcome nor a desired source-run equality is supplied.
Arbitrary existing source, residual and target journal prefixes are retained.
This is local effect sequencing and rollback, not a G42 callback-reachability
or transaction/world adequacy theorem.

`TransientTargetRollbackControls` uses a caller with nonempty intrinsic bool
locals, bytes heap, function locals, events, logs and all three histories.
The actual typed uint16 write and unowned raw-slot write extend Source and
residual prefixes from two to four entries, then the general theorem restores
the exact decorated caller and complete target. A wrong-mark control retains
the mutation, showing that restoration depends on the real frame-entry mark.
The port does not consume the separate unified Yul observation trace or the
owned-bool encoding carrier; it claims no rollback theorem for omitted inputs.
Original Y07/G01/G51/compiler/resource/final joint obligations remain open.

Both new rollback modules and the combined ten-declaration signature/axiom
audit pass serial per-file checks; all axiom reports are standard-only.
Independent read-only finder and skeptic found no confirmed findings.
Failed direct automation and preparation-normalization tactics are retained;
no theorem premise, expected value or proof budget was changed to pass.
Structural layering/reachability/doc-path/trust checks pass. These checks
remain distinct from pending full Lake/TestSuite/strict/runtime KeySort and
final joint closure; historical global G07 failures are not relabelled.

## Intrinsic LOG success inversion

`World/LogSuccess.logAdapter_success_iff` derives the exact nonstatic guard,
actual memory-load witness and complete emitted state from successful adapter
execution, and proves the converse from those real premises.
`logBuiltin_success` applies inversion to every existing arity-indexed builtin
with zero results: success implies a nonstatic frame and precisely one full
log at the frame's emitter appended through `emitObserved`. Non-LOG constructors
cannot succeed in this leaf. The five earlier binding laws still determine
exact topic/data encodings; the new generic law keeps the complete ordered
state, rather than only an event/log projection.

`logBuiltin_not_identity` proves that this successful leaf cannot return its
entry unchanged: the full trace gains one observation even for LOG0 with no
topics and empty data. `LogSuccessControls` executes that empty LOG0 against
the actual memory port, retaining the caller execution, existing observation
prefix and nonempty return buffer `[0xfa,0,0xbc]`. Missing memory-port output
and static execution remain refusals even for zero-length data.

This is a local intrinsic-builtin effect/inversion theorem, not G51 calculus
embedding or a full Yul runner theorem. Operand evaluation, Source emit/G01
encoding, physical allocation/view and world/compiler/resource adequacy remain
open, alongside original Y07.01/Y07.02/Y09.03 and Backfill A/B joint closure.
Creation/initcode still requires V08 P15/SS-NEW and VY5 H16. No finite compiler/
EVM run was added; previous external evidence remains separate.

Validation: both new modules and the complete eleven-declaration signature/
axiom audit pass serial per-file checks. No custom axioms or `sorryAx` occur.
Independent read-only finder and skeptic reviews found no confirmed findings.
Failed automation and branch-discrimination attempts remain retained. Layer,
root reachability, doc-path and trust checks pass. Final full Lake/TestSuite/
strict/runtime KeySort and joint gates remain pending; historical G07 failures
are retained, not relabelled passes. No proof or execution budget was raised.

## Composed SELFDESTRUCT lifecycle leaf

`World/SelfDestruct.selfDestruct` composes the existing `destructTransfer`
(balance transfer or self-beneficiary burn) and `Lifecycle.schedule`, with
static refusal before either operation. It introduces no new account/storage
semantics. `selfDestruct_success_iff` recovers the actual successful transfer,
nonstatic guard and exact complete returned lifecycle record. Known-beneficiary
funding/overflow conditions remain those of the existing typed transfer;
`none` is adapter refusal, not an EVM halt or a callee revert certificate.

`selfDestruct_rollback` applies the real entry mark to the **actual returned
execution**, restoring the entire execution and journal prefix. It does not
restore lifecycle metadata by itself: frame completion must also restore its
saved creation/deletion flags. `selfDestruct_finish_fresh` derives account
emptying after actual scheduling from `created a = true`;
`selfDestruct_finish_old` preserves the post-transfer account at finalization
when `created a = false`. No account-creation reachability follows from a
supplied creation flag. Callee termination and common observations are not
inputs to this local leaf and are not certified by it.

Controls use three funded accounts with distinct code/nonce and typed storage,
a two-entry caller journal, old/fresh self-beneficiaries, old/fresh distinct
beneficiaries, deferred code/storage deletion, final deletion/retained credit,
actual burn rollback, static refusal and known-beneficiary overflow refusal.
The prior both-pipeline transaction-runner evidence remains separate; no new
external/compiler test is claimed here.

Original Y07.01 creation/initcode still requires V08 P15/SS-NEW and VY5 H16;
general Y07.02 execution/lifecycle/common Source emit/G01 and physical/world
adequacy, Y09.03 G51 embedding, Backfill A/B universal integration, allocation,
resource, compiler returndata noninterference and final joint gates stay open.

Validation: both modules, eight controls and all twenty declaration signatures/
axiom reports pass serial per-file checks, standard axioms only. Independent
read-only finder and skeptic found no confirmed findings. Failed automation,
record-layout and implicit-state proof attempts are retained. Layering,
generated reachability, doc-path and trust checks pass; these are not the
pending full Lake/TestSuite/strict/runtime KeySort or final joint gates.
Historical global G07 failures remain retained. No budgets or verdicts changed.

## Complete lifecycle snapshot framing

`World/LifecycleFrames.rollbackLifecycle` restores the saved creation/deletion
maps while applying the existing `CallFrame.rollback` to the actual returned
execution at the actual entry journal mark. It consumes existing typed
`Lifecycle` records, not a second world/state representation.
`rollbackLifecycle_selfDestruct` proves full record restoration for an actual
successful SELFDESTRUCT leaf. `selfDestruct_journaled` derives its journal
operations from the actual transfer/burn result; operation lists are conclusions,
not requested scripts or adequacy premises.

`rollbackLifecycle_two_committed` derives both actual journal sequences and
uses `run_append`, the real identity `CallFrame.commit`, and `rollback_run` to
restore the entire lifecycle after two successful leaves and enclosing rollback.
Arbitrary existing execution/journal and metadata prefixes remain intact.
This closes the local metadata-snapshot obligation from the preceding leaf;
it does not establish reachable G42 frames, physical-carrier coupling, common
observations or source/compiler/world transaction adequacy.

Controls first execute a prior caller burn/schedule (three journal entries and
a prior deletion flag), then an actual distinct-beneficiary credit and a second
self-beneficiary burn (six entries total). Full rollback restores the entry,
retaining the prior caller deletion but removing the child deletion flags.
An execution-only rollback counter-control leaks a deletion flag and deletes
an account at finalization that survives after proper snapshot restoration.
Creation flags remain supplied preparation inputs; no initcode reachability is
inferred. Existing finite transaction-runner evidence is separate.

Y07.01 still needs V08 P15/SS-NEW and VY5 H16 creation/initcode; Y07.02 universal
execution/physical/lifecycle/common emit/G01, Y09.03 G51 embedding, Backfill A/B
universal integration, compiler returndata noninterference/resource/allocation
and final joint gates remain open. No owner implementation or budget changed.

Validation: both modules and fifteen complete declaration/axiom reports pass
serial per-file checking, standard axioms only. Independent read-only finder
and skeptic reviews found no confirmed findings. Failed automation and actual
control attempts remain retained; no budget/premise/verdict was changed.
Layering, generated root reachability, doc paths and trust pass. Full Lake,
TestSuite/strict/runtime KeySort and original joint gates remain pending;
historical G07 failures are retained, not reported as passes.

## Constructive normal-return LOG port rules

`World/LogPortRules` supplies `AdapterRules.log_loaded_continuation` and
`log_loaded_box` from an actual payload read and nonstatic guard. Unlike the
older equation-indexed `log_step_eq`, neither takes a completed adapter/Step
equation as a premise. The first constructs the actual normal continuation;
the second guarantees equality of the **complete** emitted observer and
unchanged producer memory for every such continuation. `log_missing_box`
proves that a failed memory read gives no normal continuation; it does not
classify a Source/EVM exception or drop its required rollback behavior.

Registered controls instantiate both constructive existence and the box for
LOG4 with a topic above 2^255 and exact payload bytes. The missing-memory case
has no normal step. A wrong-topic-order step to the expected observer is
refused using the complete ordered trace, not event/log projections. These
are Lean-only port rules, listed separately in the rule map under YQ5;
they are not `Logic.Rule`, printed `dl{}` rules or a G51 source embedding.

Original Y07.01 V08 P15/SS-NEW plus VY5 H16 creation/initcode, universal Y07.02
execution/lifecycle/common Source emit/G01/physical adequacy, Y09.03 intrinsic
G51 embedding and Backfill A/B universal integration remain open. Allocation,
resources, compiler returndata noninterference and final joint gates remain
unproved. Kernel port laws are separate from finite external EVM evidence.

Both modules and ten complete declaration/axiom reports pass serial per-file
checks, standard axioms only. Independent read-only finder and skeptic found
no confirmed findings. Failed automation/control attempts remain preserved.
Layering, generated root reachability, doc paths and trust pass. Full Lake,
TestSuite/strict/runtime KeySort and final joint checks remain pending;
historical global G07 failures are retained. No proof or execution budget changed.

## Intrinsic returndata leaf

`World/ReturndataBuiltin.returndataBuiltin` consumes the existing intrinsic
builtin arities and already-evaluated operands. RETURNDATASIZE returns the
existing `Source.toWord` representation of the caller-local last-buffer length
and the identical configuration. `returndatasize_word_exact` states the real
`length < 2^256` premise for equality with the natural length; physical/world
producers still owe valid buffer extent. No new conversion or size refusal is
introduced. Unsupported constructors are simply outside this partial leaf,
not new admission exclusions or EVM exceptional-halt verdicts.

RETURNDATACOPY delegates to the actual existing `copyReturndata`, returning
zero result words and the updated memory with the **entire observer unchanged**.
The binding rule requires an actual bounded source window and successful
producer destination store. Out-of-source bounds refuse even zero length.
Target-memory readback and every-byte outside framing follow from the existing
concrete byte-memory producer under explicit source/destination bounds. These
do not establish logical heap ownership/writeback or universal allocation.

Controls use explicit supplied frame-outcome preparation, not a reachable
callee: a nonempty old buffer is overwritten by four distinct revert bytes.
Actual intrinsic copy crosses addresses31–32, retains full last returndata,
and reads both untouched neighboring bytes. Stale-buffer output is refused;
exact-end zero succeeds, out-of-source zero refuses, and destination overflow
refuses independently of source validity. No new compiler/EVM run is claimed.

Actual source-frame origin, compiler last-call noninterference, operand
execution, reachable world/initcode (V08 P15/SS-NEW and VY5 H16), G01/common
emit, physical/source/allocator/resource adequacy, G51 embedding and final
joint closure remain original Y07/Y09 and Backfill A/B obligations.

Both modules and twenty-one complete declaration/axiom reports pass serial
per-file checks, standard axioms only. Independent read-only finder/skeptic
found no confirmed findings. Failed automation and Source.SPath elaboration
attempts are retained. Layering, generated root reachability, doc paths and
trust pass. Full Lake/TestSuite/strict/runtime KeySort and original final joint
gates remain pending; historical G07 failures remain failures. No budget,
expected verdict, observation or producer implementation changed.

## Intrinsic CALL-family binding

`World/CallBuiltin.callBuiltin` maps the existing arity-indexed CALL,
STATICCALL and DELEGATECALL operands to `callAdapter`: seven operands for CALL,
six for the others, with no value operand invented for those instructions.
Callee address is the low160 bits of the raw word; source locals are not cleaned.
Gas words are forwarded opaquely, with no gas/resource correctness claimed.
`childContext` supplies the existing sender/value/storage/static inheritance.
The generic caller-side static/nonzero-value refusal is derived independently
of any producer outcome.

The result remains the full `CompletedCall`, including outcome, full observer,
full returndata and optional output-memory write. `callContinuation` is a
separate optional normal view returning the one-word flag and configuration
only when copied memory exists. A completed callee success/revert with refused
memory remains `some CompletedCall` and has no normal continuation; it is not
recoded as a callee revert or silently dropped. The enclosing physical/source
fault and rollback adapter remains open.

Guarded outcome fixtures check the actual forwarded gas, target outside the
precompile range, raw input and child sender/value/storage/static coordinates.
They test CALL and STATICCALL success, DELEGATECALL revert, copied prefix with
untouched tail, full returndata and caller observation prefix. Dirty upper
address bits remain distinct from the low address. A refusing output store
retains completion. A static/nonzero-value negative uses an unconditional
fixture with a matching nonstatic positive, isolating preflight from context
guards. Wrong raw input is refused by the guarded fixture. A separate nonmutating
fixture also checks parent-static DELEGATECALL retains its storage/sender/value
while inheriting the static flag.

These are interface/binding controls, **not** reachable known/environment code
certificates. An arbitrary `WorldPort` may still supply illegal operations in
static context: this leaf does not certify those operations or discard that
obligation. G01/G51, creation/initcode (V08 P15/SS-NEW and VY5 H16), compiler
last-call interference, allocator/resource and final joint adequacy remain open
across the original Y07/Y09 and Backfill A/B queues.

Validation: final modules and thirty-one complete declaration/axiom reports
pass serial per-file checks, standard axioms only. Independent read-only
finder/skeptic found no confirmed findings, including the added parent-static
delegate control. Layering, generated root reachability, doc paths and trust
pass. These are interface/port checks, not full Lake/TestSuite/strict/runtime
KeySort or final source/joint gates; historical G07 failures are retained.
No budget, expected observation or producer implementation changed.

Review correction: `load_assuming_view_agreement` transports an assumed
pointwise physical-read/target-bank relation. `reset_readback_zero` reads zero
after both resets for any prior target; neither constructs an initial view
agreement. `stored_load_readback` instead derives the written-slot physical
read and executed target read from the actual checked store, nonstatic frame
and producer separation fact, with no initial agreement premise. Its control
starts mismatched and invokes that law explicitly after the write. The three
LOG port-rule controls now use direct `exact` law calls, with no `rfl` fallback.

The intrinsic terminal leaf binds STOP/RETURN/REVERT to exact loaded bytes,
with missing-memory refusal kept distinct from a genuine revert. It only
produces an outcome; interpreter exit, frame completion and Source/G51
integration remain open. Registered controls cover cross-word, empty and
refused payloads.

`selfDestruct` and `rollbackLifecycle` are compatibility abbreviations for the
pre-existing `Lifecycle.destructKnown` and `Lifecycle.rollbackDestruction`.
Their existing public proofs retain their premises; local lifecycle snapshot
rollback was already implemented, not a newly closed adequacy obligation.

Review-fix validation: explicit LOG law controls, actual mismatched-entry store
readback and affected consumers pass. Combined 25-declaration signature/axiom
audit is standard-only; independent finder/skeptic report no findings.
No initial view or universal adequacy claim is added. Full lane gates remain
open; earlier failed separation-decision attempt and historical gates are retained.

## Intrinsic SELFDESTRUCT binding

`SelfDestructBuiltin` binds the existing one-operand intrinsic builtin to
`Lifecycle.destructAtFrame`, reusing the shared low160 address projection.
It derives the actual lifecycle result, empty-success tag, local snapshot
rollback and full non-endpoint account preservation from existing laws.
The tag is not an interpreter-exit proof; `none` is not a callee revert.

Controls cover dirty beneficiary bits, delegated storage owner versus a
separate funded code target, old/fresh self/other beneficiary behavior,
deferred deletion, complete code-target preservation, static refusal and
actual-result rollback. They are typed context/metadata preparations, not
code/creation reachability certificates. Environment credit, physical/G01/G51,
compiler/resource and original Y07/Y09/Backfill A/B joint closure remain open.

Both modules and twenty signature/axiom reports pass serial per-file checks;
standard axioms only. Independent finder/skeptic report no findings. Failed
scratch automation/layout attempts are retained. Layering, reachability,
doc paths and trust pass; mandatory full lane gates remain pending.

## H22/H21 reconciliation

The lane is rebased onto H22's Core call-mode/invocation metadata and H21's
build rules. Owned World/P7 code constructs no Core `ExtCall`; the inspected
World leaf closure does not import `Syntax/Scoped`. No static/provenance
interpretation of the new fields is claimed. Generated roots were regenerated
and checked after rebasing; existing area-map coverage includes the carried
modules. Original Source/world/G01/G51/resource and final obligations remain open.

## Published dependency reconciliation

The lane adopts published integration `059eb83d`; carried World/P7 source
bodies are unchanged. The earlier library checkpoint stopped at the disk
reserve and remains failed. Its axiom-pin failure is also retained. With the
published nested-cache collection fix, the new inventory check passes with
6,252 pins, zero errors and zero unrecorded changes; this is not full-library
or lane completion. H24's declaration-graph companion is present but supplies
no concrete admission inhabitant or creation/initcode executor. Original
world/G01/G51/compiler/resource and joint obligations remain open.

## Terminal builtin G0 repair

`terminalBuiltin` uses `Builtin.casesOn` with a motive generalizing both arities
and the operand function, replacing the indexed executable match rejected at
review. Its public signature, existing laws and complete control module are
unchanged. RETURN/REVERT retain full loaded bytes, STOP ignores memory, and
missing memory or unhandled builtins still return `none`. This mechanical
repair adds no interpreter, Source/G01/G51 or compiler adequacy claim.
