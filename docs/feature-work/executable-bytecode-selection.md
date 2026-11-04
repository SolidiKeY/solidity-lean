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
