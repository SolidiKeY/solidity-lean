# Executable bytecode selection

`Solidity/Backend/Selection/**` implements G45.01, G45.02, the remaining
whole-control part of G45.03 and G45.06 for the numeric/native-stack and
structured IR fragment described below. The recursive IR branch/loop producer
gap identified during composition review is now implemented and passes its
checkpoint gates. The required full lane gate remains incomplete; declaring a
certificate structure never proves it.

## Contracts and proof boundary

`Interface.lean` retains the instruction, lowering, whole-control and
same-artifact composition contracts. The instruction contract includes actual
IR success/refusal and complete nonstack caller-frame preservation.
`StructuredExec` uses the existing `Backend.Block` and `Scalar.run`; it records
actual intermediate stacks and arbitrary finite loop bodies. It is a finite
specification, not another source evaluator or a termination proof.

V1 `FrameCertificate.prefixes` is conditional on `Scalar.stackBound` and
follows from `Scalar.prefix_capacity`; it cannot certify G45.02 capacity.
`InterfaceV2.lean` requires actual prefix capacity on an inhabited peak/room
domain, admits the empty tail and retains uniform protected-tail behavior.
V2 peaks are sufficient bounds, not necessarily least: a maximal peak can
admit only the empty tail. No capacity result here relies on V1.

`FramedLoweringInterface.lean` extends the unchanged lowering equivalence with
reflection of every actual successful IR final machine/skip. The output must
be numeric, the complete nonstack caller frame unchanged and the pending skip
zero. Its signature was committed first at fb1fddbe. The new fields are proved
locally by the constructors below, not supplied as foreign premises. A
successful escaping skip cannot be silently reclassified as a normal return.

## Selection and stack lowering

LiteralSelection, ArithmeticSelection, BitwiseSelection, UnsignedSelection and
SignedSelection construct actual opcode certificates against Backend.Scalar
for numeric PUSH, arithmetic, comparisons, bitwise operations, shifts and signed
operations present in the compiler IR. Numeric PUSH emits PUSH32. Zero divisors,
wraparound, signed minimum overflow, full shift counts, physical underflow and
actual operand order retain the existing raw IR/Osaka semantics. Source-level
checked arithmetic and guards are separate compiler obligations.

NumericSequence supplies the existing selector-parametric compileWith runner
proof and numeric specialization. MixedSelection adds native POP/DUP/SWAP
selection through that same compiler, with exact compatibility for previously
compiled numeric programs. DUP/SWAP cover native indices1 through16; index17
can return component None while raw IR execution succeeds. Component None is
not a Source refusal or an IR fault. Unsupported memory, storage, account,
terminal and symbolic-slot instructions are not coerced into this fragment.

StackSelection proves native frame transformations with tight peaks, actual
intermediate-capacity composition and the conservative V2.ofRun consumer.
Heights include every prefix and the1024 bound, not merely the final stack.
The conservative code-length peak is not asserted minimal.

## Existing and relayed results reused

The implementation reuses Backend.Scalar numeric/stack step semantics, frame
laws, stack-height/prefix-capacity results and signed bridges. Existing
Backend.Control supplies expansion and labels; Backend.LabelExec supplies
fetched-byte effects, resolved assembler packets, placement and scanned jump
destinations. Backend.Assembler and Opcode supply checked assembly and
encoding/decoding. No read-only semantic module is changed.

ScalarSequence, ScalarSequenceResources and ScalarSequenceControls port proof
bodies from the verified relay22a1b53ecd0d50272d26e2758bafaead52bf247d with only
namespace/import renaming and scoped axiom scaffolding. ScalarSequenceFrames
and ScalarSequenceFrameControls consume those formulas through V2 with actual
peaks3 and6 and populated protected tails. No theorem is attributed to an
unintegrated Executable module, and unported constructor artifacts are not
claimed. No second lowering framework, compiler AST or evaluator is introduced.

## Whole labelled execution

ExecutionTrace.Safe is a proposition over existing LabelExec.advance. Actual
Scalar.run plus actual stackBound yields encoded-byte execution through
arbitrary surrounding bytes. Successful assembly transports this trace to
item-prefix/suffix placement at real byte PCs. Sequence composition uses its
actual intermediate stack and derives its height from existing shape evidence.

BranchExecution derives selected-body entry, executes the certified body and
executes the join and final JUMPDEST. Conditions may overwrite lower words;
shape gives their length, not value equality with the original stack. The
header needs n+2 room and the true-arm join needs m+1 room.

LoopExecution derives head/condition/test/body/backedge execution for arbitrary
certified bodies. One iteration needs no remaining-loop execution premise.
Finite StructuredExec induction joins actual iterations and the final exit
JUMPDEST; it does not assume termination. The n+2 header room also supplies the
n+1 backedge PUSH room. StructuredExecution constructs ControlCertificate for
every existing BlockShape plus ExpansionRoom, including nested branches/loops.
Static prefix views are proved equal to the original Block.expand.

## Actual structured IR lowering and byte composition

FramedLowering constructs scalar and sequence reflection from the actual
existing selector equation and Evm.exec_append. IRBranchLowering constructs
both directions for the existing StructuredFlow.Branch.emit relative-jump
shape, with arbitrary numeric condition words. Its packet law retains the
actual escaping-skip continuation; selected normal-return children prove their
skip zero rather than assuming it.

IRLoopLowering handles actual recursive Evm.Instr.loop. Forward finite
structured execution supplies actual loopIterN witnesses. Conversely an actual
successful loopRun result yields a finite witness from its definition, and
induction recovers each actual numeric intermediate machine, unchanged caller
frame and StructuredExec body/rest. Empty conditions, faults and reverts are
not relabelled as successful results. No whole-loop lowering, reached-body or
termination oracle is a premise. Scalar, sequence, relative branch and loop
constructors recursively extend the same LoweringCertificate framework.
Branch and loop conditions must lower to `.code code`; these constructors do
not accept arbitrary structured condition blocks.

Composition binds the proved lowering, proved control, actual assembler output
and decoder roundtrip to the same program. execute derives finite encoded-byte
behavior and every prefix bound from actual IR success, ending at size of that
actual code. Decoder roundtrip is not treated as executable behavior.
StructuredIRComposition supplies a checked assembly factory for the recursively
constructed lowering; assembler refusal is retained. Concrete nested IR loops
with a relative-branch body now compose all the way to actual bytes without a
caller-supplied whole-program correspondence premise.

## Controls and reviews

Controls inhabit selection, protected frames, both branch outcomes, nonzero
byte-prefix placement, repeated backedges and zero exits. Negative controls
include source/target underflow, actual hidden1025-word peaks despite fitting
outputs, corrupt tails/results, wrong operand order and wrong byte/item PCs.
A target byte0x5b inside PUSH data is proved invalid despite matching JUMPDEST;
taken and untaken paths retain distinct behavior. Static header/join-capacity
rejections are not described as executed overflow witnesses.

StructuredIRControls constructs a branch inside a loop inside another actual
IR loop. Named IR turn witnesses use prior scalar semantics and the actual
loopTurn/loopIterN laws without invoking the whole-loop lowering producer.
The independent false-arm check reuses the existing G36 branch law. Changing
the relative distance skips the else arm and demonstrably changes its result.
An escaping successful skip is rejected by the framed contract; selected POP
still faults on underflow. Complete caller fields and protected word23 are
retained in the composed examples. These are Lean kernel controls, not external
solc/geth tests or claims about the assembler's least widths.

Independent finder/skeptic reviews are required at each checkpoint. Earlier
confirmed control findings were repaired: POP had hidden an operand-order
mistake, and a corrupt target with a non-JUMPDEST byte had not isolated boundary
scanning. Discriminating prefix mutants and the embedded0x5b witness resolve
those findings. The signature review's Markdown table break was also repaired.
Independent finder and skeptic reviews found no soundness defect and confirmed
that the actual new producers resolve the previous local recursive-lowering
gap for this fragment. The finder requested the explicit scalar-condition
restriction above; it is now recorded. Large concrete interpreter
reductions were replaced by abstract turn-composition lemmas, without increasing
proof budgets. Runtime measurements and VM recovery details live in sealed
handoff evidence, not in the semantics.

## External premises and explicit limits

Premises and PremisesV2 retain typed G24.03 source-to-IR preservation from
v09-compiler-passes and G45.05-BR reachable-state decoder agreement from
v15-evm-agreement. execute_bridge transports through that named agreement;
identity adapters in controls are not the actual Bridge implementation. Entry
reachability prevents using an empty reachable set.

V2 compiler nonemptiness excludes relation=False but is not source-evaluation
coverage; its identityCompiler example is source independent. No RuntimeConsumer
V2 instance or G49.02 proof is constructed. Source observations, Fml.inTarget,
refusals and budgets remain with their original interfaces and producers.

The result concerns successful finite numeric-stack execution and its complete
caller frame. It is not arbitrary unstructured-jump graph lowering, native
stack spilling beyond16, memory/storage/account/terminal behavior, Source
adequacy, gas equivalence, divergence classification or termination. It adds no
authorization to exclude an original obligation. Final completion requires the
required reviews, full lane gate, standard-axiom audit and sealed handoff.

## Structured IR checkpoint validation and handoff

The signature-first interface is committed at fb1fddbe; recursive producer,
composition and control proofs at c5c0ba36, with unused-simp cleanup at effc78df.
Independent finder/skeptic source reviews pass, including the explicit scalar
condition restriction. All eight checkpoint gates and seven per-file checks
pass on effc78df; the seven files have no warnings. All 465 scoped Selection
axiom reports match their source declarations and use only standard axioms.
Earlier modules retain their existing unused-argument warnings.

The full lane gate was interrupted by its RAM-reserve guard while checking an
existing decision-hash example. It has not passed and was not retried unchanged.
The local structured IR implementation is ready for review, but final validation
remains open. The sealed handoff records actual commands, source bindings,
resource evidence and the ownership approval needed to resolve that blocker.
No RUNTIME_GATE_PASS or whole-assignment completion is claimed.

## Published master adoption

The lane adopts published master 6f3eedf0788ee1f8a3bcf230558c712ecdca04d5.
Its accepted Selection increment imports only LiteralSelection and its controls
from producer effc78df; it does not integrate or validate the remaining lane.
All local Selection source files are unchanged by this adoption. Generated
roots are regenerated and the area map retains each module exactly once.
The imported nonvacuity audit is historical at its frozen input, not an audit
of these later producers. The source/Bridge premises and full lane validation
obligations above remain open. Cache delivery was pending at this adoption
checkpoint; the subsequent source-key check is recorded below.

Fresh validation on adoption commit63deee119a84320f18a99c4d9917c130116019da
passes all eight checkpoint gates and nine per-file checks, including the two
newly published literal modules. The nine files have no warnings and61 scoped
standard-only reports; the library replays all465 exact Selection reports.
Independent finder/skeptic adoption reviews pass. This is fresh dependency
validation, not reuse of old-head gates. The full gate is still outstanding,
and shared-cache reclamation remains unauthorized.

## Confirmed transport and exact cache-key check

The coordinator confirms successful H21 transport/mapping delivery for6f3eedf0.
The cache-only query of `Solidity.Examples.DecisionHashesChecks:olean` nevertheless
returns3 (rebuild required), before any full-gate or module compilation. Its
current source key8990275316855339899 has no local input-map entry. The source
is unchanged from6f. This is a local lookup miss, not a claim that transport
failed or that the artifact does not exist elsewhere. A private diagnostic
using installed Lake trace APIs agrees with an existing saved reference key;
independent finder/skeptic reviews confirm the narrow result. The full gate
remains outstanding; no success validator or full-gate pass is claimed.

H26 lookup finds master still at6f, with no new producer stub for these
obligations. The already imported `Selection/Premises.lean` signature is on
master at3b6380b8f8243f3618b1a42456bba4e19aeefac3, and PremisesV2 at
a2928672d59b179e55fddfee12c6228a29c8ad6b. The existing decoder consumer proofs
use entry, closure, agreement and zero/successor fields explicitly. Concrete
compiler/Bridge producers remain open; no copied producer definition,
replacement axiom, Source/ExtCall edit or G49 proof is introduced.
