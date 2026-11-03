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
Other numeric IR operations, sequence selection, general stack/frame lowering,
whole labelled control execution and assembly composition remain open.

## H21/H22 compatibility review

Independent finder and skeptic reviews confirmed that the Selection proof
sources are unchanged after the H21/H22 integration rebase. No Selection
module constructs an ExtCall, so the explicit call mode and invocation fields
require no adapter here. The finder identified module-map rows detached from
the table during migration; the owned rows now share its existing header.
The pre-rebase validation applies to its original head; post-rebase checks
are recorded separately. No coverage or certificate premise changed.

## Numeric ADD/MUL component

ArithmeticSelection.lean extends the existing InstructionCertificate with
actual compiler-IR ADD and MUL selection to one Osaka opcode each. A complete
IR-step equation constructs success and refusal equivalences, using the
existing injective numeric-stack representation. Both operations preserve all
nonstack machine fields and refuse operand underflow. No capacity claim follows
from the gasless step certificate; physical admission still requires V2.

Controls execute wraparound at the 256-bit boundary with arbitrary suffixes,
transport it to arbitrary complete IR caller frames, reject missing operands,
wrong results and corrupted tails, and check the emitted opcode bytes.
selectArithmetic covers only ADD/MUL; absence for another instruction does not
classify its source execution. Remaining arithmetic operations, instruction
sequences, general stack/control lowering and assembly composition remain open.

Independent read-only finder and skeptic reviews passed the ADD/MUL component
and controls without confirmed findings. Both checked actual runner equality,
non-vacuous input cases, modular bounds, complete-frame preservation and the
separation from capacity, symbolic-slot behavior and checked source arithmetic.
