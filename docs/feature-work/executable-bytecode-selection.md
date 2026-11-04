# Executable bytecode selection

`Solidity/Backend/Selection/**` states the G45 obligations for turning the
compiler IR into executed bytecode. At the initial checkpoint the interface modules were
statements only: certificate fields are obligations, and no inhabitant or
theorem is claimed by declaring a structure.

## Interface

`Interface.lean` fixes the contracts for instruction selection (with physical
operand refusal), frame preservation over every untouched suffix, finite
structured execution of the existing `Block`, execution at a real assembled
byte placement, and composition that ties assembly, encoding and behaviour to
the same emitted program. `FrameCertificate.prefixes` is conditional on `Scalar.stackBound` and follows
from the existing `Scalar.prefix_capacity`, so it does not yet impose the
G45.02 physical capacity; V1 must not supply a G45.02 physical-capacity result. V2 below supplies the stronger contract.
`StructuredExec` uses the existing numeric
evaluator for leaves and conditions, records the actual intermediate stacks
and covers arbitrary finite loop bodies. It does not classify divergence or
change Source evaluation horizons. A decoder roundtrip alone is never treated
as executable behaviour.

| Item | Existing result reused | Remaining obligation |
|---|---|---|
| G45.01 | `Scalar.selectUnary`, `selectBinary`, `selectChecked`; `Scalar/Typed.lean` certificates, `Scalar/Values.lean` composition | Selection from `Evm.Instr` with explicit unsupported instructions |
| G45.02 | `Scalar.step_frame`, `run_frame`; `Scalar.Heights`; `LabelExec.arity_domain` | DUP/SWAP/POP index translation, frame expansion, physical capacity |
| G45.03 | `Block.expand`, `LabelExec.Assembly`, `Loops.loop_header`/`loop_backedge`, `Boundaries` | Whole branch/sequence execution at true byte offsets |
| G45.04/.05 | `assemble`, `assemble_eq`, `assemble_pushTag`, `decode_encode` | Composition of these, without equating roundtrip with execution |
| G45.06 | The layers above | Same-program control/assembly/bytes composition |

The relayed scalar-sequence proofs are now ported under Selection (below).
The constructor-artifact results remain unported; no theorem is attributed
to an unintegrated Executable module.

## Premises

`Premises.lean` names the external inputs as typed parameters, never axioms:
G24.03 source-to-IR preservation, G45.05-BR reachable-state decoder agreement
(an empty reachable set cannot discharge it, since the entry is reachable),
and the G49.02 runtime-consumer statement on the exact composed bytes. The
consumer statement is not a G49 proof.

## Interface V2: non-vacuous obligations

The V1 frame-prefix field does not certify physical capacity. In particular, the
empty tail must be admitted. The original uniform gasless frame law is retained,
without claiming capacity for larger tails. No G45.02 capacity result may rely
on the V1 frame contract.

PremisesV2.lean requires a nonempty compiler observation relation. Its runtime
consumer also requires an admitted numeric-stack/frame witness with an actual
successful Evm.run equation, independently
of its implication premises. Thus relation := False cannot make either V2
contract trivially inhabited. Nonemptiness alone is not source-evaluation
coverage: the concrete source observation relation and its preservation are
still the G24.03 producer's responsibility. The decoder and exact-byte control
contracts are reused, and no G49.02 theorem is proved here.

The relayed scalar-sequence proofs below are ported into Selection; no theorem is attributed to the unintegrated Executable modules.

V2 signature finder/skeptic reviews confirmed empty-tail admission and rejection
of relation := False. Skeptic additionally found that a bare relation witness
could name an incorrect final IR stack; strengthened it with the actual IR-run
equality. A usable runtime result still requires the explicit compiler/decoder
premises; neither a witness nor nonemptiness proves source-evaluation coverage.

### V2 kernel consequences and controls

FrameCapacityV2.lean derives actual empty-tail capacity, capacity of every
admitted prefix, and final output bounds from the required V2 fields. Its
identity and DUP1 certificates are inhabited and preserve arbitrary protected
tails; DUP's physical room domain includes its extra word.

InterfaceV2Controls.lean constructs the exact old defect: 1025 actual PUSH0
instructions satisfy the V1 gasless frame contract. Boundary controls check DUP
at heights 1023 and 1024. Nonempty no-op compiler and valid IR-witness controls,
false compiler/runtime relations, and the incorrect final-IR-state control cover
the premise changes. They are not a G24.03 or G49.02 theorem.

Limits (review): `peak` need not be least, so a certificate with
`peak := 1024 - input.length` claims capacity only for the empty tail.
The constructed `CompilerPremise` V2 example `identityCompiler` uses a
source-independent relation; nonemptiness is not coverage. The contract does
not exclude source-dependent preserving relations. No `RuntimeConsumer` V2
instance exists yet; `runtime_witness_inhabited` shows only that its witness
domain is nonempty.

## Relayed scalar-sequence port

ScalarSequence.lean, ScalarSequenceResources.lean and ScalarSequenceControls.lean
port the corresponding scalar sequence, resources and checks from the verified
relay commit 22a1b53ecd0d50272d26e2758bafaead52bf247d. Only namespace/import
renaming and scoped axiom-report scaffolding change; the proof bodies are reused.
They establish actual staged scalar behavior, selected opcode/byte order, typed
protected caller words and exact physical peaks (+3 and +6). Controls include
wrong operand order, insufficient intermediate capacity and full emitted bytes.

The port itself reuses a proved scalar consumer; it does not establish
compiler-IR instruction selection or fetched runtime execution. The typed caller-frame producer and
G24.03/G45.05-BR obligations remain explicit; no source coverage or runtime
consumer instance is claimed. The accepted V2 limits above remain unchanged.

ScalarSequenceFrames.lean consumes the relayed formulas through V2 with actual
peaks 3 and 6, including both typed caller words. ScalarSequenceFrameControls
instantiates both certificates on populated frames with nonempty physical
tails, rejects a corrupted protected word and excludes intermediate overflow
even where final height fits. No V1 capacity field or runtime producer is used.


## Compiler-IR literal component

LiteralSelection.lean constructs the existing InstructionCertificate for every
IR numeric PUSH literal. Numeric-stack injectivity makes the success equivalence
exact for every output stack; actual IR execution preserves all nonstack machine
fields and agrees with Scalar.run of an actual PUSH32. Fault/None correspondence
is also proved. The common 256-bit bound is used explicitly.

LiteralSelectionControls checks a populated suffix and arbitrary complete caller
machine frame, all 33 big-endian bytes of a two-byte value, incorrect value/byte
order, corrupted tails and symbolic-literal component refusal. selectLiteral is
only this component: None does not classify another IR constructor's execution
or a complete compiler's verdict. Physical admission still needs V2 capacity.
The numeric and sequence components below extend this literal component.
General stack/frame lowering, whole labelled control and assembly composition
remain open.

## H21/H22 compatibility review

Independent finder and skeptic reviews confirmed that the Selection proof
sources are unchanged after the H21/H22 integration rebase. No Selection
module constructs an ExtCall, so the explicit call mode and invocation fields
require no adapter here. The finder identified module-map rows detached from
the table during migration; the owned rows now share its existing header.
The pre-rebase validation applies to its original head; post-rebase checks
are recorded separately. No coverage or certificate premise changed.

## Numeric arithmetic component

ArithmeticSelection.lean extends the existing InstructionCertificate with
actual compiler-IR ADD, MUL, SUB and EXP selection to one Osaka opcode each. A complete
IR-step equation constructs success and refusal equivalences, using the
existing injective numeric-stack representation. Both operations preserve all
nonstack machine fields and refuse operand underflow. No capacity claim follows
from the gasless step certificate; physical admission still requires V2.

Controls execute wraparound at the 256-bit boundary with arbitrary suffixes,
transport it to arbitrary complete IR caller frames, reject missing operands,
wrong results and corrupted tails, and check the emitted opcode bytes.
selectArithmetic covers only ADD/MUL/SUB/EXP; absence for another instruction does not
classify its source execution. Further numeric and sequence components are
described below; general stack/control lowering and assembly composition
remain open.

Independent read-only finder and skeptic reviews passed the ADD/MUL component
and controls without confirmed findings. Both checked actual runner equality,
non-vacuous input cases, modular bounds, complete-frame preservation and the
separation from capacity, symbolic-slot behavior and checked source arithmetic.

SUB and EXP extend the same certificate constructor and numeric representation.
SUB matches the IR natural subtraction residue with the physical word operation;
EXP keeps the actual IR base on top and reduces its final natural power.
Controls include negative subtraction residue, exponentiation wraparound,
arbitrary suffixes and full caller frames, both operand shortages, swapped
operand results, corrupted suffixes and the actual SUB/EXP opcode bytes.
These are gasless numeric IR operations, not checked source overflow guards.

Independent read-only finder and skeptic reviews also passed the SUB/EXP
extension and controls. The documentation and map row now state the four-op
component scope, addressing the skeptic's scope-description finding. No
capacity, checked-source, or whole-selector result is inferred.

## Bitwise and unsigned comparison component

BitwiseSelection.lean reuses the existing instruction-certificate constructor
for numeric AND/OR/XOR/NOT, unsigned LT/GT, EQ and ISZERO. Word and Boolean
representation lemmas relate the actual IR operations to Scalar steps over
the common intrinsic 256-bit words. Each certificate proves success and
operand-underflow equivalence while retaining every nonstack machine field.
Symbolic slots, checked source arithmetic and physical capacity are not
covered by these numeric-step certificates; capacity remains a V2 obligation.

Each operation has executed positive, arbitrary-suffix, complete-caller-frame,
underflow and wrong-result controls. Additional controls distinguish unsigned
high-bit comparisons, full-width complement and both Boolean outcomes, reject
corrupted suffixes and check all eight opcode bytes. A local ADD absence is
paired with its existing arithmetic selection, so component absence is not
presented as a whole-selector or source refusal. The components below cover division, shifts and signed operations. The sequence component below extends this numeric coverage; the remaining
stack/control/composition queue is still open.

Independent read-only finder and skeptic reviews passed this component and
its controls without confirmed findings, including unsigned ordering, flag
conversion, complement width, all input lengths and the component boundaries.

Per-file lint cleanup removed unused LT/GT rewrite arguments and a redundant
NOT-bound fact. Both reviewers confirmed unchanged statements and controls.

## Unsigned division and logical shifts

UnsignedSelection.lean reuses the existing certificate constructor for numeric
DIV/MOD and SHL/SHR. Quotient/remainder bounds follow from the intrinsic
dividend; divisor zero produces word zero in both actual runners, with no
nonzero-divisor premise. Shifts retain the entire top-of-stack count, return
zero at counts at least 256, discard high bits for SHL and never sign-extend
SHR. The certificates preserve all nonstack IR fields and reflect operand
shortages. These results do not establish checked source guard/panic behavior
or physical capacity; V2 admission remains separate.

Controls cover ordinary and zero-divisor execution, arbitrary physical tails
and complete IR caller frames, empty/singleton operands, wrong operand order,
full-width unsigned values, counts 0/255/256/maximum, SHL overflow, logical SHR,
corrupted suffixes and all four opcode bytes. Component absence is paired with
another component's supported selection. Independent read-only finder and
skeptic reviews passed without confirmed findings; no hidden divisor, count,
capacity or source-coverage premise was introduced. Signed and sequence selection are described below; the
stack/control/composition queue remains open.

## Signed numeric component

SignedSelection.lean selects SLT/SGT/SDIV/SMOD against the actual numeric IR
step. It reuses Scalar.sgn_word and Scalar.toWord_ofInt together with the
published Evm signed-range theorems. The division-result range is the wider
word interval, so minimum divided by negative one is included and wraps as
raw EVM SDIV does. The SMOD nonzero-divisor case discharges its range proof
inside the certificate; divisor zero is separately proved to return zero.
No nonzero-divisor or minimum-integer exclusion is a caller premise.

Controls distinguish signed from unsigned ordering, truncation from floor
division, dividend-signed remainder from Euclidean remainder, and raw overflow
from checked source refusal. They execute zero divisors, negative divisors,
minimum words, arbitrary suffixes and complete IR caller frames, reject both
operand shortages, wrong results and corrupted tails, and check all four
opcode bytes. Physical capacity, checked source guard/panic execution, source
adequacy and byte-runtime correspondence remain separate obligations.

Independent read-only finder and skeptic reviews passed this component and
controls without confirmed findings, including local discharge of every range
obligation and inclusion of zero divisors and raw minimum-word overflow.

## Numeric instruction sequences

NumericSequence.lean dispatches the numeric PUSH and all twenty numeric
operation constructors to their existing certificates. A support predicate
characterizes this component over the frozen IR type; it is not a source
refusal predicate. compileNumeric concatenates the actual expansions in IR
order. A total equation of the existing Evm.run and Scalar.run runners proves
both successful execution with every nonstack IR field preserved and faults
at any instruction position. The existing StructuredExec code case then
yields an inhabitant of LoweringCertificate for the selected straight-line
code, with no assumed target result or new evaluator.

Controls instantiate a nonempty five-instruction, 101-byte lowering and run it
over arbitrary suffixes and complete caller machines. Wrong-order results,
corrupted tails and both early and late underflows are rejected. A component
refusal paired with an actual IR revert keeps these observations distinct.
These are numeric straight-line certificates: stack-manipulation lowering,
physical capacity, structured branch/loop realization, source adequacy and
executable-byte composition remain separate obligations.

Independent read-only finder and skeptic reviews passed the selector, total
sequence equation, existing-contract inhabitant and controls without findings.
They checked actual intermediate stacks, zero skips, frame threading, early
and late faults, and separation from capacity and fetched-byte execution.

## Native stack selection and physical frames

StackSelection.lean relates numeric-stack IR POP, DUP1--DUP16 and SWAP1--SWAP16
steps to their existing physical operations, including operand refusal and
complete nonstack IR-frame preservation. The one-based IR indices are
translated explicitly to Fin16 opcode indices; SWAP16 reaches word17. An
exchange lookup/set lemma connects the existing two implementations without
introducing another evaluator. Index zero really faults in the IR; a larger
index can succeed in the IR while this native component returns None, so no
global source refusal or deep-index lowering is inferred.

V2 frame constructors use actual peaks1 for DUP and0 for SWAP/POP. They
preserve every external suffix and prove capacity for every arithmetically
admitted suffix, including the always-admitted empty suffix. Composition
uses the actual intermediate stack length and the maximum of both declared
peaks after height adjustment. Existing successful step-height/frame laws
yield a generic successful-program consumer with conservative peak equal to
instruction count; this need not be minimal and can restrict its room domain.
Native constructors retain tight peaks, admitting full-height SWAP/POP. No
legacy conditional capacity field is used.

Controls cover native depth16, arbitrary caller machines, protected nonempty
tails, both end opcode bytes, wrong indices, shortages and corrupted tails.
DUP at input height1023 and SWAP/POP at1024 are inhabited. Overfull results
are excluded for any V2 certificate. A DUP/POP trace whose final height fits
but whose intermediate height is1025 cannot have a V2 certificate for that
code, regardless of its declared peak. Safe composition supplies every-prefix
bounds, and the generic consumer inhabits a numeric-compiler frame certificate.
Mixed numeric/stack sequence integration, larger-index lowering, structured
control and executable-byte composition are not established by this module.

The existing compileNumeric remains numeric-only; these native certificates do
not silently extend its coverage. The generic ofRun constructor consumes an
actual successful Scalar.run proof, rather than proving compiler correctness
on its own. Independent read-only finder and skeptic reviews found no semantic
defect. The finder requested an explicit proposition type for one local bound
in the overflow rejection; that proof-style annotation has been added.

## Mixed numeric/native-stack sequences

The existing sequence compiler and runner proof are factored over their
instruction-certificate selector. compileNumeric and its named contracts
remain numeric specializations with unchanged types and controls; no second
compiler or evaluator is introduced. MixedSelection adds numeric-priority
native-stack fallback, retaining every previous numeric selection. A theorem
proves exact emitted-code equality for every previously compiled numeric
program. All Fin16 native cases have explicit selection theorems.

Mixed lowering and fault reflection specialize the same actual-runner theorem.
Controls compile six IR instructions combining PUSH, DUP, SWAP, DIV and POP
to 70 bytes and preserve arbitrary complete IR caller machines and suffixes.
An existing V2 ofRun consumer supplies conservative peak6 (not the least peak),
capacity on its declared room domain and all-prefix bounds. Late native
shortage is reflected into an actual IR fault. Index17 still returns None
while its raw IR execution can succeed; no larger-index lowering or source
refusal claim follows. Structured control and executable-byte composition
remain open.

Both independent read-only reviews found the original final-result negative
did not discriminate order errors because POP discarded DIV's result. It was
renamed as a wrong-result control. Explicit IR/code prefix equalities now
identify the boundary before POP; its actual run retains results3 and5.
Executed wrong-DUP1 and omitted-SWAP mutants produce1 and0 instead of3, and
inequalities distinguish both on the same populated tail. Both reviewers
confirmed this control repair. The compiler and runner proofs had no semantic
finding. The announced factoring checked file history and undid no earlier
checking-speed optimization.

## Stack checkpoint handoff

Native frames/capacity are committed at d21aae49; shared compiler and mixed
lowering at de20c672. Both checkpoints pass the library, touched-module, trust,
roots, orphans, layers, documentation-path and axiom-pin gates; scoped per-file
checks and KeySort pass, with only standard axioms in the scoped reports.
Consumers can use selectScalar, compileScalar, scalarLowering, the exact
numeric-code compatibility theorem, and V2 native/compose/ofRun frame
constructors. Conservative peaks retain their explicit room conditions.
Native indices above16 need another lowering; source compiler adequacy and
Bridge agreement remain typed producer boundaries. Whole structured control
and executable-byte composition remain open; these passes are not a runtime
gate or whole-assignment completion.


## Placed code and sequential control

ExecutionTrace proves finite execution in the existing LabelExec.advance
machine, with a 1024-word bound at every reached instruction boundary. Safe
is a predicate over that machine, not another evaluator. Scalar success and
actual stackBound evidence execute encoded instructions at byte PCs through
arbitrary surrounding bytes. Assembly equality transports this result to
arbitrary item-prefix/suffix placement. Existing CodeShape determines the
height of the actual result; StructuredExec conditions may overwrite lower
words, and no protected-value assumption is inferred from height.

The frozen ControlCertificate now has codeCertificate and seqCertificate
constructors. Sequence execution uses its actual intermediate stack and the
first certificate's derived result height; it joins actual instruction counts
and every prefix bound. No reached-body or favorable-PC premise is supplied.
Controls instantiate both constructors in a nonempty sequence after PUSH32:
entry33, exit38, actual result12 with protected word23. Wrong item-index PC,
wrong result, corrupted tail and actual ADD shortage are rejected. A condition
control explicitly preserves the existing lower-word-overwrite behavior.

This checkpoint covers code and sequence. Conditional branches, general loop
body reachability/backedges and whole assembly/encoding composition remain
open. Counts are instruction boundaries, not gas or Source budgets; LabelExec
has no memory/storage/account or terminal semantics. Source compiler adequacy
and decoder Bridge agreement remain the existing typed producer premises.


Independent finder and skeptic reviews passed the code/sequence proofs and
placement controls without semantic findings. The shortage control supplies a
one-word state directly at ADD; it is not a fault reached from the sample's
normal entry. Both reviews explicitly retain the open branch/loop and full
composition obligations and used neither builds nor the Lean server.


The code/sequence implementation checkpoint7583709c passes all eight
checkpoint gates and both scoped per-file checks. KeySort passes under
Lean4.24.0/Lake5.0.0-src+797c613. The scoped reports contain only standard
axioms. These are checkpoint checks, not the unfinished assignment's full
runtime gate. The following documentation-only handoff records this result;
its Lean sources are identical to the gated implementation commit.


## Bounded assembled control packets

ControlPackets adds capacity to the existing assembled JUMP, JUMPI and
ISZERO/PUSH/JUMPI packets. Actual assembly supplies target resolution and the
scanner's validity proof. Actual fetched PUSH determines the intermediate
operand stack. The two-step packet splitter derives its second step from the
complete packet and the independently fetched first step; no favorable next
state is assumed. JUMP needs one temporary word; conditional tests need two
above their actual tail. ISZERO replaces its input word and does not add one.
The final JUMPDEST is itself executed. Item indices are converted through the
actual assembled byte sizes.

Controls construct an actual assembler output with the published assembler
existence theorem, then derive both bounded conditional arms, a bounded jump
and the destination's own step. Independent literal byte vectors pin the
PUSH32-prefix entry33, zero destination39 and nonzero fallthrough37. They do
not claim equality with the assembler's exact minimal-width output. The
literal test admits a real1024-word peak and rejects its hidden1025-word peak
for every alleged finish state. Wrong PCs, results and tails are rejected.
A corrupted taken target lies in PUSH data and is refused by the scanner;
the same corrupted target remains unused on the untaken arm.

The first monolithic whole-branch draft exceeded the unchanged200000
heartbeat budget during layout normalization. It is preserved outside the
registered source for decomposition into smaller lemmas. No heartbeat budget
was increased, and no branch or general-loop control certificate is claimed
by these packet results. Whole body reachability, general-loop realization
and assembly composition remain open.


Both read-only packet reviews confirmed the proof scope but found that the
initial corrupt-target control's non-JUMPDEST payload did not isolate the
scanner's instruction-boundary check. It now targets a payload byte0x5b:
the byte equals JUMPDEST, an explicit InPushData witness proves it is inside
PUSH data, and the scanner rejects it. Taken execution fails and untaken
execution succeeds. This is a strengthened control, not a semantics change.

Both independent reviewers confirmed the embedded0x5b repair. Packet proofs
received no semantic finding; the remaining branch draft is not registered
and is not part of the passing code.


## Control checkpoint handoff

Placed code/sequence realization is committed at7583709c (documentation
handoffb60e023c), and bounded control packets at2b1d3227. Each passes all eight
checkpoint gates and its two scoped per-file checks, with only standard
axioms in the exact scoped report sets. KeySort passes under the recorded
Lean4.24.0/Lake5.0.0-src+797c613 serial toolchain. This documentation-only
handoff retains identical Lean sources to the gated packet implementation.
Consumers may use codeCertificate, seqCertificate, bounded jump/jumpi/test
and placed tag execution; they may not infer a branch or loop certificate.
The unproved branch draft needs smaller static layout and execution lemmas
within the existing proof budget. General loops and G45.06 remain open, with
no current producer blocker to those proof steps. These checkpoint passes do
not constitute the assignment's final full gate or Source/Bridge agreement.


## Whole conditional execution

BranchExecution.iteCertificate implements every field of the original frozen
ControlCertificate for an existing Block.ite. It derives the selected body's
entry from actual condition execution and the generated test, executes that
body through its proved certificate, and executes the required join jump and
final JUMPDEST. The true and false paths retain their actual instruction
counts and stack bounds at every boundary, including temporary label pushes.
Condition code may overwrite lower words. Output room explicitly reserves
the true arm's join operand; no condition-only capacity assumption replaces it.

BranchLayout.Placement records prefix views of the same existing expansion;
items_eq and block_prefix prove their equality to Block.expand. It is neither
a compiler nor an execution language. Generic adapters hold the whole item
list abstract while transporting existing scalar/packet/control proofs through
explicit list equalities. Separating these lemmas avoids elaborating symbolic
assembler expressions inside the whole proof. The unchanged200000 heartbeat
budget suffices; the earlier monolithic draft is superseded for branches.

Controls construct real assembler outputs after PUSH32, exercise distinct
nonempty true/false bodies over a populated tail, and reject the wrong-arm
result and corrupted tail for the same actual run. A condition replaces42
with99 and chooses the false body; whole byte execution then observes106,
rather than assuming preservation of the original operand. A separate static
negative retains the required room above a1024-word branch output. These are
kernel proof controls, not external EVM tests or exact minimal-width claims.
General loops and G45.06 composition remain open.


Independent finder and skeptic reviews passed all four branch modules without
material findings. Both confirmed actual body reachability, byte coordinates,
changed condition-stack handling, join and tag execution and prefix capacity.
The join-overflow control is static ExpansionRoom rejection; it does not claim
an independently executed byte-overflow witness. Successful assembly, finite
StructuredExec and child control certificates remain explicit inputs. The
reviews used no edits, builds or Lean server.


The whole-branch implementationa777de49 passes all eight checkpoint gates
and all four per-file checks. Exact scoped reports contain only standard
axioms; KeySort passes under Lean4.24.0/Lake5.0.0-src+797c613. This following
documentation-only handoff preserves every Lean source from that checked
implementation. Consumers may construct conditional control certificates from
certified children and the stated test/join room. General-loop realization,
G45.06 and the assignment's full final gate remain open.


## General structured loops

LoopExecution proves one actual iteration of an arbitrary certified structured
body through the generated head tag, condition, test, body and backedge. It
needs no remaining-loop execution premise. The backedge returns to the real
placed head byte PC, rather than item count or byte zero. A zero condition
executes the exit JUMPDEST. finite_loop inducts the existing finite
StructuredExec derivation and joins these traces; no fixed body-step bound,
favorable reached-body fact or byte-jump oracle is supplied. The condition's
actual lower stack may change values. Shape evidence derives only its length.

loopCertificate implements every frozen control-certificate field. The test's
n+2 room also provides the backedge's n+1 room, while each body certificate
retains its own prefix bounds. StructuredExecution.structuredCertificate now
constructs control realization for every existing BlockShape together with
ExpansionRoom, including nested branches/loops and arbitrary sequences.
Sequence composition uses the explicit intermediate shape/room witnesses.
Static loop prefix views are proved equal to Block.expand and reuse the same
fixed-whole-items adapters; no additional evaluator or compiler is introduced.

Controls construct actual assembly for a loop whose nonempty body is itself
a conditional decrement. Two iterations take2 to1 to0 with a protected word23
and repeated backedges to byte33 after PUSH32. A zero-entry execution exits,
and an independent one-iteration witness needs no remaining-loop premise.
Wrong head zero, final result and corrupted tail are rejected. Reusing the
existing changed-condition control, whole loop exit returns99 from input42.
Header overflow is static control-certificate rejection, not an independently
executed overflow witness. Independent finder/skeptic reviews passed all five
modules without findings and used no edits, builds or Lean server. Finite
StructuredExec is a finite-execution premise, not a termination proof. These
results cover the frozen structured fragment; source adequacy, gas and Bridge
agreement remain separate. G45.06 composition remains open.


The general-loop/all-shapes implementation1314ed5e passes all eight checkpoint
gates and five per-file checks, with only standard axioms in the exact scoped
reports. KeySort passes under Lean4.24.0/Lake5.0.0-src+797c613. This following
documentation-only handoff preserves the checked Lean sources. Whole control
realization for the frozen shaped fragment is available; G45.06 IR-to-byte
composition and the assignment's final full gate remain open.


## Assembly composition: proved flat instance and remaining structured lowering

Composition.compose binds a proved lowering certificate, existing shape/room,
actual assembled program and decoder roundtrip for that same program.
CompositionCertificate.execute derives finite byte execution and every stack
bound from actual IR success and the proved control realization. It does not
infer executable behavior from decoder roundtrip. execute_bridge transports
each actual step and prefix through the unchanged G45.05-BR DecoderPremise,
including its nonempty entry and reachability closure requirements.

scalarComposition supplies its own scalarLowering from the existing mixed
selector and constructs actual assembly using the master assembler theorem;
its caller supplies no unproved lowering certificate. The resulting code is
proved equal to the selected native program. Controls instantiate six mixed
IR instructions,70 encoded bytes and a populated tail. Actual IR success
preserves the complete caller frame; an independent six-step byte run reaches
PC70 and result5. A validly encoded literal mutant reaches6 and decodes to a
different artifact. Tail corruption, empty decoder reachability and a decoder
step that always refuses are rejected. An identity adapter only tests the
conditional transport and is not an implementation of Bridge agreement.

Independent finder and skeptic reviews found no soundness defect, but both
confirmed an original scope obligation remains: no producer here constructs
LoweringCertificate for actual compiler IR relative jump/jumpi patterns or
recursive loop instructions. Generic compose requires that proved component;
whole Block/StructuredExec realization does not supply IR-to-block lowering.
That is required local lane work, not a G24 or decoder-agreement premise and
not an authorized exclusion. Consequently this checkpoint completes concrete
flat numeric/native composition, while G45.06 and the whole assignment remain
partial. Neither Source adequacy, arbitrary IR outcomes, gas, termination nor
G49 is claimed. Both reviews used no edits, builds or Lean server.


The concrete-composition implementation567b238d passes all eight checkpoint
gates and both per-file checks. Exact scoped axiom sets are standard only,
and KeySort passes under the recorded Lean4.24.0/Lake5.0.0-src+797c613 toolchain.
This following documentation-only handoff preserves its checked Lean sources.
The required local structured-IR lowering producer remains open; the full
assignment gate and whole-lane completion are therefore still pending.


## Recursive lowering reflection interface

FramedLoweringInterface adds only a signature extending LoweringCertificate.
The original success equivalence is retained. The new reflection field must
recover the numeric stack, unchanged complete caller frame and zero pending
skip from any actual successful IR result. This supplies the information
needed to inspect intermediate branch/loop machines without assuming their
frame or silently normalizing escaping skips. It does not classify faults,
reverts or divergence, alter observations/budgets, or create another evaluator.
The field is a required local proof, not a new foreign premise. No instance
or recursive lowering proof is claimed by this signature-only checkpoint.


Independent finder and skeptic signature reviews confirm this strictly
strengthens the existing contract, with no evaluator or foreign premise.
A registration presentation finding was fixed by joining the new and earlier
owned module rows into the existing contiguous Markdown table. Programs with
escaping skips or nonstack effects cannot satisfy this normal-return/frame
contract merely by discarding those observations; eventual producers must
prove their domain. Signature-only status remains explicit.


The signature checkpointfb1fddbe passes all eight checkpoint gates and its
per-file check, with axiom-free signature/projection reports and zero warnings.
KeySort passes under Lean4.24.0/Lake5.0.0-src+797c613. This documentation-only
handoff preserves the checked Lean source. The interface is now committed
before any framed lowering proof; the original recursive lowering obligation
and final assignment gates remain open.
