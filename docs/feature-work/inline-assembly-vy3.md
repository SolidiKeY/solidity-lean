# Inline assembly VY3: Yul compilation combinators

The opening inventory records the initial target-only checkpoint. Later sections
record its source/compiler extensions and the obligations that remain open.

`Yul/Compilation/**`, from the vy3-compilation lane. Target-side combinators
over the existing backend stack model (`Backend/Scalar/Heights`,
`Backend/Control`, `Backend/Passes/Stack`); no Yul AST or VY1 semantics is
consumed, so this is not yet the P20 state relation.

- Expression and statement lowering (`PureLowering`, `ArgumentLowering`,
  `ResultAssignment`, `ResultFrame`, `LocalScopeLowering`): `LoweredExpr n
  value` is indexed by an arbitrary Lean function; the relation is the stack
  layout `newer ++ locals ++ tail`.
- Opcode lowering (`OpcodeLowering`, `ClzLowering`, `ClzBounds`,
  `ByteLowering`): selection and CLZ/BYTE expansions with bounds.
- Control (`ControlLowering`, `MachineControl`, `Relocation`): branch and loop
  `Block` emission and relocation; `lowerBranch_slices` gives the runs of the
  parts, not of the whole block, and `lowerWhile` has no execution theorem.
- `*Controls`: kernel controls.

Open: a Yul AST/semantics relation (P20), run theorems for arithmetic and
control code, whole-block execution.

## Expression, statement and machine slices (sched 2026-11-03)

Core `Yul/Compilation/` modules (each `*Machine`/`*Branch`/`*Placement` with a
`*Controls` module) over the original VY1 AST and evaluator; none adds an AST,
word semantics, state or calling convention.

- Expression compilers: `WordExpressions`, `QuotientExpressions` (unsigned
  DIV/MOD with zero divisors), `SignedExpressions`, `BitExpressions`,
  `ModularExpressions`, `PureExpressions`, `ProducerExpressions`,
  `RemainingWordBridges`, `OpenExpressions` (raw external cells through the VY1
  `WordAdapter`).
- Statements and control: `ProducerStatements`, `PureStatements`,
  `OpenStatements`, `ScopedStatements`, `ScopedRawStatements`, `NormalControl`,
  `NormalStackTransport`.
- Compiler-model execution: `ArithmeticMachine` (ADD/MUL), `ShiftSubMachine`,
  `BitMachineExecution`, `QuotientMachine`, `UnaryMachine`, `ComparisonMachine`;
  concrete branches `UnaryBranch`, `ComparisonBranch`.
- Physical memory: `PhysicalStore` (constant-operand stores on the VY2 byte
  view), `PhysicalHash` (Keccak over the canonical `withKeccak` field).

Bridge `SolidityBridge/Yul/`: `ChargedQuotients`, `ChargedQuotientPrefix`,
`QuotientPlacement`, `QuotientSuffix`, `SignedPlacement`, `BinaryPlacement`,
`SignextendPlacement` — compiler-origin sites with the charged P10 producers
at arbitrary encoded offsets.

Open: native/G24 closure, general branches, finite-code transport,
source-update pairing.

## Exponent compiler-model execution

`Compilation.ExponentMachine` proves the actual complete DUP2/DUP2/EXP model run
for every base/exponent word pair, arbitrary machine fields and symbolic caller
tails. The base is on top. Existing Scalar Nat-power/modulus and Evm.Machine
word semantics agree directly; no desired-run premise, dirty-bit cleanup or
exponent restriction is assumed. Actual original intrinsic expression and
`PureExpressions.compile 2` certificate have exact code-origin and unchanged
WordMachine selection theorems. Original operands and all other state survive.

Controls distinguish2^8 from8^2,0^0=1, zero base/exponent, dirty/MAX words to the
first power and2^256 wrapping to zero. Finite examples deliberately bound actual
arithmetic work; the theorem still quantifies every word. It makes no feasible
checking-time or native gas claim for enormous natural powers. Fuel/DUP/operand
refusals, symbolic operand faults,1022/1023stackBound thresholds and oversized
uncapped-model success retain the resource boundaries.

The only resulting upstream content changes were the existing IDE trust
inventory and its assurance documentation. Prior source/evidence/checkpoints are
preserved. The updated tracked-tree trust audit passes under that published
inventory; historical raw failures are not rewritten or evidence that the sites
were removed. New modules have no scoped trust findings.

Focused build/per-file diagnostics, scoped signatures/axioms and layer checks
pass, with independent actual-file finder/skeptic reviews finding no defects.
Core registrations are generated. General source/G24/view/writeback/MemOK,
functions/control/divergence, frontend, native/Bridge/Osaka/world/trace and
final joint closure remain unfinished. No source AST/state, opcode meaning,
selector, admission, observations, budget or external solc/EVM fixture is
changed by this implementation.

## Signed comparison compiler-model execution

`Compilation.SignedComparisonMachine.reading` connects the existing machine's
`sgn` to the actual BitVec signed reading by reusing
`SignedExpressions.signed_word`. Explicit Nat-to-Int power-cast normalization
avoids the recursion-limit failure of direct conversion. No recursion, heartbeat
or other proof budget is raised, and no second signed-word meaning is defined.

`slt_run` and `sgt_run` derive actual complete DUP2/DUP2/SLT and SGT runs for every
raw word pair, arbitrary machine fields and symbolic callers. The full sign bit
and all dirty bits are preserved. Actual original intrinsic expressions and
`PureExpressions.compile 2` certificates have exact emitted-code origins and
unchanged SignedMachine selections. There is no desired-run or input-range
premise beyond intrinsic word bounds.

Controls distinguish negative one from zero, minimum/maximum signed values,
equal minima, dirty negative versus low257, positive dirty bits and reversed
operands. Fuel/access/underflow/symbolic-operand refusals, unchanged SAR refusal,
1022/1023stackBound thresholds and uncapped oversized-model success retain the
resource boundaries. These are signed comparisons, not unsigned reinterpretation.

One docs/README.md append conflict was resolved by retaining both published G18
links and the lane table. Existing Yul compilation sources did not change in the
rebase. Newly read V12 NativeParents.clause and
RecursiveResult.success/shallow_refused give concrete countdown/hand-written
runtime clients, not a general Yul function compiler or blanket runtime
producer. They do not discharge the original function/control/divergence
obligations.

Focused builds/per-file diagnostics, scoped signatures/trust/layers and
independent actual-file finder/skeptic source/documentation reviews pass. Core
registrations are generated. Raw failed direct-conversion diagnostics are kept.
General Source/G24/view/writeback/ MemOK, functions/control/divergence,
frontend, native/Bridge/Osaka/world/trace and final joint closure remain
unfinished. No AST/state, signed semantics, selector, admission, observations,
budget or external solc/EVM fixture is changed.

## Signed quotient consumption of published word producers

`Compilation.SignedQuotientMachine` consumes actual
`Yul.EvmSigned.step_sdiv/step_smod` and the existing compiler
`SignedExpressions.sdivBridge/smodBridge.agrees` proofs. It derives complete
DUP2/DUP2/SDIV and SMOD model runs for all word operands, arbitrary machine
fields and symbolic caller tails. Fin/coreWord normalization preserves the exact
raw result and retained operands. There is no desired-run or additional signed
range premise, and no duplicated quotient/range semantics. Actual original
intrinsic expressions and compiler certificates have exact code origins and
unchanged SignedMachine selections.

Controls cover zero divisors, MIN/-1 wrapping without Panic, truncation toward
zero, both divisor signs, dividend-signed remainders and dirty negative words.
Underflow/symbolic operands, source fuel, shifted DUP, SAR refusal, stackBound
thresholds and uncapped oversized-model success keep resource limits explicit.
These are compiler-model results, not charged native or full Source/G24 closure.

The branch now builds on that real tree and carries only the two later
EXP/signed-comparison checkpoints plus new work. Previously omitted
test/scripts/docs remain in the saved commit and immutable original artifacts,
not silently republished as new integration. Published parsing compositions now
live in Frontend/Yul; this Core consumer imports no parsing shim.

Focused builds (including the two carried checkpoints), per-file diagnostics,
scoped signatures/trust/layers and independent actual-file finder/skeptic
reviews pass. Failed initial Fin-image rewrite diagnostics are retained. General
source/G24/view/writeback/MemOK, functions, control/divergence, frontend,
native/Bridge/Osaka/world/trace and final joint closure remain unfinished. No
admission, observation, word meaning, AST/state, budget or external solc/EVM
fixture changes follow from this checkpoint.

## Charged bitwise compiler-origin correspondence

Optional `SolidityBridge.Yul.ChargedBitwise` consumes the actual published P10
AND/OR/XOR bodies. Each correspondence theorem combines the original intrinsic
expression's source horizon2, actual compiler emission, exact ordered
head/compiler-program/tail byte image and the real charged primitive step/X
continuation. Byte-PC bounds, gas≥3 and caller length≤1020 are explicit. The
prepared arithmetic input is the existing a,b,a,b,caller packet; after the real
three-gas step the exact compiled value sits above the original locals/caller.
No decoder result, desired execution or abstract primitive theorem is assumed.
No existing five-gas interface or proof/fuel/resource budget is changed.

These theorems start at the emitted arithmetic site. They do not prove that the
preceding DUP prefix is reached or executed. Valid-jump scanning, suffix
correctness, general source/G24 and full Osaka/world/resource/trace closure
remain separate.

Controls populate memory/returndata/return buffers, active words and caller data;
exercise both static flags, dirty high bits and all three results; distinguish
four prelude bytes from two instructions; and test gas/fuel/underflow/overflow.
The shrinking-opcode gate can accept an oversized prepared input that the DUP
prefix cannot reach. A finite DUP/ADD suffix regression is included without a
universal suffix claim. These Lean/reference controls are not new solc or client-
EVM pipeline evidence.

Focused Bridge imports/builds, per-file diagnostics, scoped
signatures/axioms/trust and independent actual-file finder/skeptic reviews pass.
Core is unchanged.

### Charged raw ISZERO slice

ChargedIszero derives both fetched DUP1/ISZERO steps and the complete native X
continuation for UnaryMachine.iszeroCompiled.value, arbitrary raw operand and
caller tail. Premises: caller.length ≤ 1022, initial gas ≥ 6, encoded prelude
length + 2 < UInt256.size. The actual P10 DUP and raw ISZERO producers discharge
execution; zero_input derives the intermediate code/PC/stack identity. No
intermediate success or desired result is assumed. Full state equality retains
the original dirty operand and caller tail.

Controls cover zero, one, dirty 2^200+257 and high-only 2^200, static flags,
populated buffers, a four-byte/two-instruction prelude, exact capacity/overflow,
gas, fuel, underflow and a finite DUP/ADD suffix. Focused kernel build and
independent finder/skeptic reviews pass; the initial invalid PUSH fixture exit
is retained separately. These are Lean/reference checks, not new external
solc/client-EVM evidence. General Source/G24/view/frontend, scanner,
function/loop and whole Osaka/world/resource/trace composition remain
unfinished.

### Charged raw NOT slice

ChargedNot derives actual fetched DUP1/NOT steps and their native X continuation
for UnaryMachine.notCompiled.value, all raw words and arbitrary caller tails.
Explicit premises: encoded prelude length + 2 < UInt256.size, caller length
≤ 1022, initial gas ≥ 6. The raw-word P10 uint_not_agreement applies without
Boolean or cleaned-local restrictions. The intermediate code/PC/stack identity
and remaining gas are derived, not input success premises. Exact final State
retains the original operand, caller and unchanged fields.

Controls use zero, one, dirty 2^200+257 and high-only 2^200, both static flags,
populated buffers, four-byte prelude, capacity/overflow, gas/fuel/underflow and
a finite DUP/ADD suffix. Standard automation fails on the execution goal; actual
producer composition succeeds. Scratch indentation/name-scope failures are
retained. Independent read-only finder/skeptic reviews found no confirmed
issues.

This is a native compiler slice, not a general Source/G24/view/frontend,
function/loop/divergence, scanner, whole Osaka/world/resource/trace theorem. No
new external solc/client-EVM evidence or full-lane gate pass is claimed.

### Charged logical shift compiler slices

ChargedShifts derives original intrinsic SHL/SHR expression evaluation and
native DUP2/DUP2/shift X continuations to the SAME ShiftSubMachine compiled
value. Premises are encoded prelude length + 3 < UInt256.size, caller.length ≤
1020 and initial gas ≥ 11. This sufficient gas bound comes from the unchanged
QuotientPlacement.reads theorem; the actual shift charges THREE gas, not five.
Intermediate stack/code/PC identity, gas reserve, prefix and last-step execution
are derived. Count is topmost, then value; the original raw operands, arbitrary
caller and unchanged native State fields are retained.

Controls include dirty value/count, zero, 255/256/257, modular left wrap, both
static flags and populated buffers, a four-byte/two-instruction prelude, exact
capacity/overflow, gas/fuel/underflow and finite DUP/ADD suffix. A finite gas9
success does not turn the general sufficient gas11 theorem into a minimum-gas
result. No new external solc or client-EVM evidence is claimed.

Standard tactic attempts fail; concrete producer composition succeeds. The
initial scratch namespace failure is retained. Focused checks and independent
read-only finder/skeptic reviews pass. General
Source/G24/views/frontend/function/loop/divergence, scanner and whole
Osaka/world/resource/trace adequacy remain unfinished.

### Charged arithmetic shift compiler slice

ChargedArithmeticShift instantiates the existing intrinsic Expr and actual
PureExpressions compiler with SAR; no new AST, signed semantics or core-machine
selector is introduced. sar_continuation proves source evalExpr2 and complete
native DUP2/DUP2/SAR X execution to the SAME compiler value. It derives prefix
execution, intermediate code/PC/stack identity and remaining gas using concrete
QuotientPlacement/P10 producers, with no desired run assumption. Premises:
encoded prelude bytes + 3 < UInt256.size, caller.length ≤ 1020, initial gas ≥
11. The old sufficient prefix gas contract is unchanged; SAR itself costs three.
Raw count/value words, original operands, caller and unchanged State fields are
preserved.

Controls cover negative odd floor rounding, minimum signed value, 255/256/257
and dirty enormous counts, positive/negative saturation, zero, unchanged dirty
words, static flags/populated buffers, four-byte prelude,
stack/gas/fuel/underflow refusals and finite suffix. A finite gas9 success is
not a universal minimum-gas claim. Focused kernel/MCP/scoped trust checks and
independent finder/skeptic reviews pass. No external solc/client-EVM evidence is
added. Full Source/G24/view/frontend, functions/loops/divergence, scanner and
whole Osaka/world/resource/trace closure remain unfinished.

### Charged arity-three modular compiler slices

ChargedModular instantiates the existing intrinsic arity-three Expr and actual
PureExpressions compiler for ADDMOD/MULMOD. read_prefix derives all three
charged DUP3 steps, exact intermediate states, full prefix X continuation and
remaining at least eight gas. The subsequent concrete P10 modular producers give
original source evalExpr2 and complete four-instruction native X continuations
to the SAME compiler values. No intermediate success/result or blanket compiler
law is assumed. Explicit premises: prelude encoded bytes + 4 < UInt256.size,
arbitrary caller.length ≤ 1018, initial gas ≥ 17. Original raw a/b/modulus and
caller/unchanged fields survive.

Controls distinguish unbounded intermediate addition/multiplication from
wrapping before modulus, modulus zero/order, dirty values/modulus, static flags
and populated buffers. They check each prefix state, four-byte prelude, local
DUP accessibility, exact capacity/overflow, gas/fuel/underflow and finite
suffix. Initial declaration-keyword failure and consequent scratch failure are
retained; corrected focused checks and independent read-only finder/skeptic
reviews pass. No new external solc/client-EVM evidence or full original lane
gate is claimed. General Source/G24/views/frontend/functions/loops/divergence,
scanner and whole Osaka/world/resource/trace composition remain unfinished.

### Charged dynamic-cost exponent compiler slice

ChargedExponent connects the existing original ExponentMachine compiler
certificate to source evalExpr2 and complete DUP2/DUP2/EXP native X execution.
Its gas premise is six plus the actual pinned exponent-byte cost: ten for zero,
otherwise ten plus fifty per unsigned exponent byte. P10.power_cost proves this
is C' on the same reached input; guarded Fin subtraction derives the two-DUP
reserve and the real P10.power_agreement discharges EXP. No desired intermediate
run/gate, uniform exponent bound or cleaned-word premise is assumed. Base is
topmost, exponent next; original operands, arbitrary caller and unchanged native
State fields are retained. Other premises: caller.length ≤ 1020 and encoded
prelude bytes + 3 < UInt256.size. Cost remains native resource bookkeeping, not
an admitted source observation or whole Osaka/resource adequacy claim.

Huge raw exponents are checked for byte cost only; no gigantic host power is
evaluated. The initial concrete decide witness could not reduce Nat.log; the
existing log_of_lt lemma fixes it without budget or verdict changes. Raw
failures are retained. Independent read-only finder/skeptic reviews and focused
checks pass. No new external solc/client-EVM evidence or full original lane gate
is claimed.

### Published selection-interface arithmetic clients

ArithmeticSelection supplies actual inhabitants of the existing published
Backend.Selection.InstructionCertificate for ADD and MUL. Code fields are the
actual single opcodes. For every numeric Scalar input/output and compiler
Evm.Machine with the interface's irStack representation, success is equivalent
in BOTH directions to Scalar execution, and machine fault is equivalent to
Scalar refusal. The existing ArithmeticMachine step theorems are reused; an
explicit equality/injectivity proof connects the existing representations and
recovers the exact output in the reverse direction. No desired run, extra
operand bound, replacement interface or new semantics/state is assumed.

Controls link the real source compiler slices to these code fields and exercise
dirty words, modular wrap, missing operands, ADD/MUL composition, populated
store/memory/balances/ghost balances/self/caller/value/time/acceptance fields.
They distinguish uncapped model success from the actual stackBound condition.
The certificate domain is numeric irStack, not arbitrary symbolic operands;
there is no claimed native fetched-byte/gas or general Source/G24 agreement.

Initial scratch failures (unavailable helper name, map simplifier order, and
missing next-constructor unfolding) are retained. Corrected focused checks and
independent read-only finder/skeptic reviews pass, with no confirmed findings.
No external solc/client-EVM evidence or full-lane gate pass is added.

### Actual selection-certificate sequence composition

SelectionSequence emits concatenated actual certificate code for a list of the
EXISTING compiler Evm.Instr. Its indexed Certificates input uses the published
Backend.Selection.InstructionCertificate for each member, not a second AST or
an assumed whole-program theorem. execute derives exact model/Scalar behavior:
Scalar failure yields Evm.Out.fault; Scalar success yields the exact full machine
with only the represented stack replaced. Head success supplies its real skip0
step and the induction composes the reached numeric stack. Both early and later
failure are derived from refusal fields. The only representation premise is
the original numeric irStack relation; arbitrary symbolic operands, new control
forms, native execution and general Source/G24 are not inferred.

A computable chooser inhabits the inputs with the actual ADD/MUL producers.
Controls include dirty nontrivial success, modular wrap, caller/metadata
preservation, later fault after successful ADD, first fault, and oversized model
success with failed physical stackBound.

Initial attempts to eliminate a membership Or proof into certificate data
failed; matching on the existing instruction constructors solves that
representation issue constructively, without an axiom or changed interface. Raw
failed exits are retained. Focused checks and independent read-only
finder/skeptic reviews pass. No external solc/client-EVM evidence or full-lane
gate pass is added. Full
source/G24/views/frontend/functions/loops/divergence/scanner/Osaka/world/resource/
trace/import composition remains unfinished.

### Finite DUP selection and actual compiler read prefixes

StackSelection supplies real published InstructionCertificate bodies for every
Backend DUP index n : Fin 16, with IR instruction dup(n.val+1). Both success and
fault equivalences derive actual input[n.val]? presence/absence and exact output,
using numeric irStack injectivity in the reverse direction. No lookup, desired
run/result or capacity hypothesis is assumed. A computable dependent selector
accepts target DUP1–DUP16 plus the existing concrete ADD/MUL producers; it refuses
DUP0/DUP17 and other unsupported instructions. This is a certificate adapter,
not Solidity/Yul admission or a changed owner selector.

Actual inhabited certificate functions now cover the original ADD/MUL compiler
programs DUP2/DUP2/operation. SelectionSequence.execute applies to those SAME
programs for numeric input stacks, carrying success and refusal. Controls check
exact source-compiler code equality, first/last valid DUP, missing operands,
dirty/MAX words, caller and full machine metadata, modular wrap and whole source
read prefixes. DUP17 can run in the uncapped model but cannot use this real
Fin16 backend encoding. Oversized model success remains distinct from the real
stackBound condition; numeric irStack does not claim arbitrary symbolic operands.
No allocation offset is equated with a live DUP position.

Focused checks and independent read-only finder/skeptic reviews pass, with no
confirmed findings.

### Local writes through actual SWAP/POP selection

Both success/refusal directions derive actual operand existence: exchange_set
follows from the list bound, and the real out-of-range law supplies failure.
Exact mapped list updates and full machine fields are preserved; no desired
exchange/run result is assumed.

statement_model combines a real ProducerStatements.Compiled certificate, its
EXACT emitted-code identity, and real per-instruction certificates to derive
original Yul evalStmt and model execution on the same numeric locals/caller.
Concrete assignment_model and sequence_model discharge the emission premises
for the original intrinsic statements x := y and x := y; y := x + y using the
actual PureStatements compiler. These are source/model word-level results, not
general Solidity source embedding, G24, physical views or native execution.
Contexts F/X are empty and caller words use the interface's numeric irStack.

The source horizons are the same actual compiler/evaluator horizons (two and
four), with insufficient horizon refusal retained.

The initial source namespace qualification and scratch record-layout failures
are retained. AST names are Solidity.Yul.Stmt/Control; the evaluator namespace
is Solidity.Yul.Closed. Checked module/signature files are authoritative; prior
sealed artifacts remain unchanged. Focused checks and independent read-only
finder/skeptic reviews pass. No external solc/client-EVM evidence or full-lane
gate pass is added.

### Literal PUSH and initialized source scopes

LiteralSelection supplies real published InstructionCertificate bodies for every
numeric PUSH word, using the existing pushWord/step_pushWord encoder law and
exact numeric-stack injectivity. PUSH32 success/refusal is derived, not assumed.
A local dependent selector accepts numeric model literals and refuses symbolic
slot terms without changing earlier selectors or source admission. The model
erases PUSH width; actual emitted code is PUSH32, not a native byte/PC/gas proof.

Concrete let_model and zero_model use the original intrinsic Yul AST and actual
ScopedStatements compiler at the same source horizon five. The initialized
scope writes its literal through an outer local, then reads that updated local
in addition; the two-local zero scope writes fresh locals, updates an outer
local and retires the whole fresh prefix. Actual per-instruction certificates
and emitted-code identities are discharged in the concrete source/model
conjunctions. Caller and full unchanged model fields are retained. This is
word-level F/X-empty, depth-zero lowering, not physical memory allocation,
general Solidity/P16 embedding, G24 or native execution.

Controls cover dirty/MAX literals and wrap, zero initialization, updated-local
reads, fresh-prefix retirement, full metadata/caller retention, missing
operands, source-horizon/depth refusals, actual 33-byte PUSH32 and 42/76-byte
program sizes, and physical stackBound versus uncapped model success. Focused
checks and independent read-only finder/skeptic reviews pass with no confirmed
findings. No external solc/client-EVM evidence or full-lane gate pass is added.

### Normal source control to the published structured relation

StructuredSource proves execution in the EXISTING Backend.Selection.StructuredExec
relation for every actually emitted NormalControl.Derivation block. The proof
reuses actual lowered Scalar certificates: scalar leaves derive their runs,
sequences pass the real updated locals, and branches derive the condition word
plus untouched stack and consume that word in the real iteTrue/iteFalse rules.
No condition/arm/whole-block run is an input premise. The real emitted-code
identity, intrinsic derivation and numeric locals/newer/caller are explicit.
The complete temporary prefix and arbitrary numeric caller tail are preserved.
No new AST, state, relation or evaluator is introduced.

Concrete source compiler witnesses cover arithmetic if, an updated condition
after assignment, nested branches and a nonempty temporary prefix. Zero, dirty
and high-only nonzero conditions, modular wrap, depth/horizon refusal and caller
framing are checked. Existing Derivation.source supplies the matching original
source evaluation;

StructuredExec is a stack-success relation, not a generic Evm.Machine/LabelExec/
Bridge/native run theorem. Finite model regressions are labeled separately;
oversized model success supplies no physical capacity. Shape, ExpansionRoom,
ControlCertificate realization, loops/divergence, general Source/G24/views/
frontend/Osaka/world/resource/trace/final import composition remain open.
Focused checks and independent read-only finder/skeptic reviews pass with no
confirmed findings.

### Arithmetic source branches through actual model execution

BranchModel.source_model proves original intrinsic Yul if evaluation AND complete
Evm.Machine branch execution using real condition/arm compiler certificates,
actual instruction-certificate bodies and exact emitted-code identities. The
condition Scalar run is derived from lowered.correct, transported to the exact
model stack, and the arm run is derived by the existing source/model consumer.
Only then is MachineControl.branchCode_run applied. No desired condition, arm
or whole-branch run is a premise. Full-word zero/nonzero truth is preserved;
false returns the unchanged machine, true preserves all nonstack fields and
updates exactly the source locals, with arbitrary numeric caller retention.

The concrete example_model uses actual expression/statement compilers and the
original normal-control visitor for if x { y := y + 1 }. Both child-code
identities are closed by rfl; the actual emitted Backend.Block is also checked.
This extends beyond the earlier stack-only model adapter. Its domain remains
closed word-level source, numeric irStack and depth0. Relative instruction skips
are NOT native byte offsets; native decoding/gas, expanded branch capacity,
physical views and general Solidity/P16/G24 composition remain separate.

Controls cover zero/high-only/dirty conditions, modular wrap, full machine
metadata/caller, empty/short true-path faults and short false-path success that
does NOT inhabit the source Vector Word2. Source-horizon/DUP-depth refusal and
uncapped model success versus arm stackBound are explicit. The initial scratch
match-normalization and undecidable IR equality guard failures are retained;
the same equality is checked as a kernel rfl proof, with semantic expectations
and budgets unchanged. Focused checks and independent read-only finder/skeptic
reviews pass. TERRA48 leaves routine projections; TERRA1–47/full original lane
obligations remain pending. No new external solc/client-EVM evidence or full-lane
gate pass is added. Optional Bridge registration is coordinator-generated.

### Checked recursive model control selection

`SolidityBridge.Yul.ControlRealization` checks scalar selection against actual
instruction certificates and exact re-emitted `Backend.Program` equality.
This refuses compact PUSH encodings whose erased model representation would
otherwise re-emit PUSH32, and instructions without proved certificates.
`Slice.lowering` supplies the actual published iff `Selection.LoweringCertificate`
for scalar leaves, including reverse reconstruction from full model outcomes.

`selectBlock` recursively builds forward successful model realization for existing
`Backend.Block` code, sequence and conditionals. Conditionals require only the
taken arm's execution. Loops refuse. This forward package is explicitly distinct
from the published iff lowering certificate for whole structured blocks.
`source_model` combines original `NormalControl` source evaluation and emitted
`StructuredExec` with the actual constructed realization. Concrete sequence,
nested branch and newer-prefix examples close all selection/emission identities.
Full numeric caller tails, dirty words and nonstack machine fields are preserved.

Controls cover updated conditions, nested inactive arms, modular wrap, high-only
conditions, an inactive ADD which would underflow if taken, empty/short stacks,
unsupported selectors, PUSH-width mismatch, DUP/SWAP limits and uncapped model
success versus stackBound. No new frontend admission or external solc/EVM result
is claimed. Native byte/PC/Osaka/charged/trace correspondence, expanded capacity,
loops/functions/divergence, full source/G24/view simulation and joint artifacts
remain open. Independent finder/skeptic reviews are recorded with focused checks
in the sealed checkpoint handoff. TERRA49 records routine projections; prior
routine obligations remain pending. Optional Bridge registration is deferred to
the coordinator's generator, as required by REG1/H14.

### Selection V2 and enforced signed axiom pins

Selection clients now import the published `Selection.InterfaceV2`. They use
unchanged instruction and lowering contracts; no lane client consumes V1
`FrameCertificate.prefixes`, `CompilerPremise` or `RuntimeConsumer`. No physical
capacity certificate is inferred from the old conditional prefix field.
`SignedQuotientMachine.sdiv_run` and `smod_run` now enforce their standard axiom
sets with `#guard_msgs`. The excluded routine ledger is preserved in checkpoint
evidence rather than resubmitted as a repository file. Earlier integrated
Bridge registrations remain done; only new unpublished modules need generated
registration at their integration.

### Whole selected-block iff and refusal transport

`SolidityBridge.Yul.ControlCompleteness` closes the earlier reverse-lowering
obligation for the actual `ControlRealization.selectBlock` numeric domain.
`selected_classified` proves every represented input really faults or returns
an actual `StructuredExec` result with the identical nonstack frame and zero
pending skip. It derives condition faults, empty condition results and exactly
the taken arm; no untaken-arm success or blanket totality premise is assumed.
`selected_lowering` therefore inhabits the published whole-block iff
`Selection.LoweringCertificate`. Its selection identity is the only additional
compiler premise; concrete sequence/nested/prefixed instances close it by rfl.
`fault_iff` equates actual model fault with absence of a structured successful
output, without reinterpreting source horizons or native EVM failures.

Controls include a source-derived prefixed success witness through the whole
iff certificate, taken versus untaken ADD underflow, left/right sequence faults,
faulting and empty-result conditions, dirty/high-only words, wrap, caller and
metadata preservation, encoding/opcode refusals and oversized uncapped success.
Scoped axiom reports are enforced by generated `#guard_msgs` pins. This adds no
selector forms or admission: loops, unsupported certificates and unequal PUSH
encodings still refuse. Native bytes/PC/charged/trace, expanded capacity, full
Source/G24/views, functions/divergence and final joint artifacts remain open.
Routine projection requests remain archived in evidence; no excluded ledger
or tests are resubmitted. New optional Bridge registrations remain generated
at integration. Independent read-only reviews and focused checks are recorded
in the checkpoint handoff.

### Concrete V2 frame certificates

`SolidityBridge.Yul.FrameCertificatesV2` constructs the published V2 frame
contract for existing old-local reads, supplied-value writes and finite nested
updates. Actual frame execution and all admitted caller-tail capacity follow
from the existing slot/nested-write laws; no desired run or stackBound premise
is supplied. Input room admits the empty caller. Reads need peak1; supplied-value
SWAP/POP writes peak0 because the value is already input; update sequences use
peak0 when empty and peak1 when nonempty. Shifted accessibility remains separate
from room, and target-package checks do not change source admission.

Controls preserve dirty words/newer locals/callers, check repeated writes and
last/beyond accessible slots, underflow, full-height empty identity, real first
PUSH prefix capacity and oversized gasless execution versus capacity refusal.
The V2 overfull-output impossibility is separately witnessed. Generated axiom
pins enforce the scoped reports. This closes V2 frame/capacity obligations for
these target slices, not native expanded control, charged execution, functions,
source/G24/views or full-lane composition. Routine projections stay archived
in evidence; registrations remain coordinator-generated.

### SUB/DIV/MOD instruction certificates

`SolidityBridge.Yul.QuotientSelection` supplies actual published instruction
success/refusal certificates for SUB/DIV/MOD. The generic binary helper states
its real one-step and underflow premises; all concrete facts are discharged
using existing Scalar selections, compiler word bridges and VY1's arithmetic
step proofs. No arithmetic semantics or source evaluator is duplicated.

A separate certificate table preserves the original selector/refusal controls.
The actual original-source compiler's mixed SUB→DIV→MOD assignment sequence
closes its emitted-code identity and all instruction-certificate inputs, proving
source evaluation and full model execution for arbitrary represented words.
Controls also inhabit the published iff lowering contract for that exact
emitted program. Operand order, wrap, dirty bits, zero-divisor zero results,
caller/nonstack preservation, underflow, depth/fuel and capacity distinctions
are checked, with generated scoped axiom pins. The older recursive checked
selector is not automatically extended. Native byte/charged/Bridge/G24, wider
operators, functions/loops/views and full frontend/joint closure remain open.
No source admission or H22 ExtCall construction changes occur. Routine named
projections remain evidence-only; optional registrations are generated later.

### Concrete arithmetic table in structured selection

The existing selector and constructive classifier now factor over a typed leaf
compiler returning the same dependent `Slice p`, with real instruction
certificates and exact emitted-program identity. The legacy entry points and
theorem contracts retain their original table and verdicts. Generic whole iff
and refusal proofs derive classification from actual leaf results rather than
accepting a simulation premise; no new AST, evaluator or lowering algorithm is
copied into a separate compiler.

`SolidityBridge.Yul.QuotientControl` plugs the concrete SUB/DIV/MOD table into
that recursion. Actual source `if div(x,y) { mixed assignments }` is compiled,
selected and proved against the source evaluator and model, with whole iff
certificates at depth0 and under two newer words. Selection/emission identities
close by rfl. Controls cover zero/truncating DIV false paths, true/MAX paths,
updated locals, caller/newer/full-machine preservation, underflow, old refusals,
unsupported operators, loops, width/fuel/depth and uncapped capacity boundaries.
Scoped reports are enforced by generated pins. This closes the earlier table
integration gap for these slices; native/G24/views/functions/divergence and full
frontend/joint closure remain open. H22 ExtCall construction remains untouched;
routine projections remain evidence-only and registrations are generated later.

### Bitwise and full-word shift selection

`SolidityBridge.Yul.BitwiseSelection` concretely discharges AND/OR/XOR/SHL/SHR
instruction certificates using existing compiler bridges and VY1 word-step
proofs. No word arithmetic or evaluator is duplicated. The separate extension
table preserves prior refusal tables and plugs into the typed structured
selector. Actual original-source compilation of an AND-guarded update sequence
closes source/model and whole-iff artifacts at depths0/2 for all represented
three-word inputs, with exact emitted-code/selection identities.

Controls exercise high-bit-only branch truth, shift operand order, counts0/255/
256/dirty-high-word, wrap and zero results, true/false guards, repeated updates,
protected caller/newer words and nonstack machine fields, underflow and static
width/fuel/depth/loop refusals. The mask local is explicitly assigned and follows
the actual compiled update; equal fixture values do not claim an independent
mask-framing theorem. Generated pins enforce scoped standard axiom reports.
No native/charged/G24/views/function/divergence, wider operator or full frontend
closure is inferred. H22 remains respected; routine named projections stay in
evidence and new optional registrations are coordinator-generated.

### Concrete signed structured selection

`SolidityBridge.Yul.SignedSelection` discharges SDIV/SMOD/SLT/SGT instruction
certificates using the existing signed compiler bridges and VY1 word-step
proofs. The typed slice checker now accepts a candidate generator, but still
checks real instruction certificates and exact re-emission; it assumes no
correctness property of that generator. The original numeric entry point and
its refusal verdicts remain unchanged.

An original source SLT-guarded sequence updates its first local by SDIV, its
second by SMOD of the updated quotient, and its third by SGT of the updated
locals. Actual compilation/emission/selection identities close by rfl. General
source/model and whole-iff artifacts are inhabited at depths0/2 for all
represented three-word locals and arbitrary caller/newer frames. No desired
source/target run or code-origin premise remains in those concrete instances.
Controls cover signed order, zero divisors, MIN/-1 overflow, negative remainder,
ordered writes, dirty words, full machine fields, underflow, incorrect candidate
proposals, old refusals and width/fuel/depth/loop boundaries. Oversized gasless
success remains distinct from physical capacity. Nineteen generated guards pin
scoped axiom reports to standard Lean axioms.

The generated Bridge root now registers the sixteen accumulated selection
modules. Its full bounded build passes; the earlier missing-object import
failure remains raw evidence. Native/G24/views/functions/loops/divergence,
Solidity raw-local readback, frontend admission and final joint composition
remain open. No external solc/client-EVM result follows from these kernel
checks. Existing scope decisions and the ExtCall construction freeze are
preserved. Routine named projections remain evidence-only.

### Unsigned comparison selection

`SolidityBridge.Yul.ComparisonSelection` concretely supplies LT/GT/EQ
certificates from existing `WordExpressions` bridges and VY1 `EvmBitwise`
steps. A separate table preserves prior selector refusals. Equality observes
all raw bits; unsigned order is distinct from the signed table. An original
source EQ-guarded sequence computes LT into its first local, GT of the second
against the updated first into its second, then EQ of both updated locals into
its flag. Actual source/model and whole-iff artifacts inhabit depths0/2 for
all represented inputs with arbitrary protected newer/caller frames; exact
compilation/emission/selection identities are discharged.

Controls distinguish dirty-high-word equality from low-bit equality, unsigned
MAX/zero order, zero/equal/unequal branch outcomes, ordered local updates,
nonstack fields, underflow and old/unsupported/fuel/depth/loop/width refusals.
Sixteen guards pin observed standard axioms. Gasless oversized success does not
supply physical capacity. Generated optional-root registration and focused
checks cover this extension; full Source/G24/views/native/frontend/joint
adequacy and the wider operator set remain open. No external pipeline result,
ExtCall construction or admission change is inferred.

### Unary word selection

`SolidityBridge.Yul.UnarySelection` derives unary Scalar/model outcomes and
published success/refusal certificates from exact empty-stack and one-word
executor laws. ISZERO and NOT discharge those premises with existing compiler
word bridges and VY1 word steps. No desired execution result is assumed. A
separate table preserves earlier selector refusals. Original source guarded by
`iszero(not a)` performs ordered NOT/ISZERO/NOT writes, with concrete source/model
and whole-iff artifacts at depths0/2 for arbitrary represented locals, newer
prefix and caller tail; full nonstack machine fields are retained.

Controls cover zero/MAX, high-bit-only values, dirty words, nested unary
expressions, ordered writes, underflow, incorrect candidates and static
refusals. General unary capacity laws show `stackBound` equals `safeHeight` at
the unchanged entry height. This height-only predicate accepts height0 even
though the actual unary executor refuses missing operands. An initially wrong
new assertion conflated those facts; its failed exit is preserved and the
corrected control checks both independently. Oversized Scalar success is
separate from the 1024-word bound. Twenty guards enforce observed standard
axiom reports. Full Source/G24/views/raw-readback, native/world/resource,
function/loop/divergence/frontend and final joint adequacy remain open.

### Exponentiation selection

`SolidityBridge.Yul.ExpSelection` discharges the EXP instruction certificate
with the existing `RemainingWordBridges.expBridge` and VY1 word-step theorem.
The separate table preserves earlier EXP refusal. Original source guarded by
EXP performs two ordered EXP writes followed by ISZERO of the updated result;
actual compilation/emission/selection identities close, with source/model and
whole-iff artifacts at depths0/2 for all represented inputs and arbitrary
newer/caller frames. No source or target execution premise is assumed.

Controls distinguish base/exponent order, `0^0`, zero, MAX-square wrapping,
`2^255`/`2^256`, dirty words, updated-local dataflow, protected frames and full
nonstack fields. The general capacity law checks entry height and height minus
one; height1 can pass while the actual binary executor refuses underflow.
Oversized Scalar success does not imply capacity. Thirteen guards pin observed
standard axiom reports. Universal mathematical word proofs and feasible finite
evaluations do not establish efficient huge-exponent execution or native gas.
Full Source/G24/views/raw-readback, native/world/resource, function/loop/
divergence/frontend and final joint adequacy remain open.

### Software BYTE and compact literals

`SolidityBridge.Yul.ByteSelection` proves exact PUSH1 execution and certificates
for values with a real one-byte bound, reusing existing literal correctness.
Its leaf compiler first retains the earlier PUSH32 selection, then tries a
compact table with the same exact re-emission check. Mixed PUSH32/PUSH1 uses
of the same value in one leaf remain refused by the current certificate-table
interface; no code normalization or general width coverage is claimed.

The existing software BYTE expansion now has concrete primitive selection and
original-source BYTE/ISZERO conditional instances, with ordered updated-index
and updated-value reads, source/model and whole-iff artifacts at depths0/2.
Controls cover big-endian indices0/31, full-word out-of-range indices32 and
high-bit-only values, dirty data, old literal behavior, width refusals,
protected frames and full machine fields. General PUSH1 capacity requires one
spare height, separately from uncapped Scalar/model success. Thirteen guards
pin observed standard axioms. This adds neither a native BYTE instruction nor
frontend admission; native bytes/PC/resources, full Source/G24/views/readback,
functions/loops/divergence and joint adequacy remain open.

### Occurrence-indexed exact selection

`SolidityBridge.Yul.OccurrenceSelection` indexes proof certificates by finite
positions in the existing instruction list. Its `Step` and `Slice` are proof
packages over existing instructions/programs, not another AST or evaluator.
The selector checks each occurrence against its original instruction and
constructs exact whole-program origin. A general execution theorem derives
success and fault outcomes from those real certificates; published scalar-leaf
lowering iff and source/compiler transport follow without assumed executions.
Older membership-indexed interfaces remain unchanged.

Concrete PUSH32/PUSH1 uses of the same value now retain distinct encodings in
one leaf. An original BYTE assignment with literal31 and compact expansion
constants closes actual compilation/selection, source/model and scalar-leaf
whole-iff instances at depths0/2. Earlier selectors still refuse that code;
the new positional factory accepts it. Controls check exact occurrence code,
dirty values, protected frames/full machine fields, underflow, mismatched
certificates, width/native-op refusals and real prefix capacity. Twenty guards
pin standard axiom reports. Structured-selector integration/completeness,
native byte/PC/resource correspondence, full Source/G24/views/readback,
functions/loops/divergence and frontend/joint closure remain open.

### Positional structured control

`SolidityBridge.Yul.OccurrenceControl` connects positional leaves to the existing
block realization and classification contracts. Its recursive code/sequence/
conditional selector constructs both proofs with each result; it does not ask
a caller to supply a classification or simulation theorem. Conditional proofs
derive actual condition failure, empty result, full-word zero/nonzero truth and
taken-arm outcomes. Existing sequence/branch/lowering lemmas are reused, giving
published whole-block iff and exact failure transport. Loops remain refused;
older selectors and interfaces remain unchanged.

An original mixed-width BYTE31 guard with BYTE0 assignment followed by ISZERO of
the updated local closes source/model and whole-iff instances at depths0/2,
with arbitrary represented locals, newer/caller frames and full machine fields.
Controls cover true/false source paths, high-bit truth, untaken failing arms,
empty condition failure and stack consumption, condition/taken-arm/early/later
faults, dirty data and static refusals. Twenty guards pin standard axioms.
This closes the positional structured integration gap for these supported
constructors, not selector completeness, loops/divergence/functions,
native byte/PC/ExpansionRoom/capacity/resources, full Source/G24/views/readback
or frontend/joint adequacy.

### Finite target-loop realization

`SolidityBridge.Yul.LoopRealization` derives actual `loopTurn` outcomes
from a positional condition slice and the existing body realization. Induction
on actual `StructuredExec` constructs a finite `loopIterN` witness, then
`loopRun_of_iterN` gives a whole-loop forward realization. No desired model run
or source horizon is assumed. The body contract remains the existing explicit
forward realization; automatic loop selection and reverse classification stay
open. A two-iteration countdown witnesses the contract with an arbitrary
full-word caller suffix and unchanged non-stack machine fields.

Controls distinguish continuing prefixes from the final zero-condition turn,
exercise dirty data and underflow, and keep 1024-word capacity separate from
gasless Scalar/model execution. An always-true loop has only continuing finite
prefixes; its mathematical `loopRun` denotation is `.fault` by the existing
no-finite-outcome definition. This is not executable termination, native fault,
gas exhaustion, source divergence or horizon correspondence. Seven guarded
axiom reports pin standard axioms. Source Yul loops, G24/views/readback,
function/early-control compilation, native byte/PC/resource/world/trace and
frontend/final joint adequacy remain unfinished.

Independent read-only finder and skeptic reviews found no confirmed defect
in these proofs and controls; neither reviewer ran Lean or a server. Focused
module checks and per-file diagnostics pass; the original failed recursion
and scratch/control checks are retained in the checkpoint evidence. No
external compiler/client EVM validation is added by this model proof.

### Target-loop classification and selection

`SolidityBridge.Yul.LoopClassification` derives one-turn outcomes from actual
condition/body runs, then classifies every finite model prefix while deriving
backwards structured-execution transport. Finite model exits reconstruct
`StructuredExec`; the no-finite-outcome case uses the existing mathematical
loop denotation. The helper's body classification premise is explicit.
`SolidityBridge.Yul.LoopSelection` recursively constructs it from real selected
bodies, including nested loops, in the existing `Selected` package. Thus
existing whole-iff lowering and exact failure transport apply to these
selected target blocks without a caller-supplied loop simulation theorem.

Controls instantiate actual countdown/nested/branch certificates, preserve
dirty caller data and full non-stack fields, and exercise empty conditions,
body failure, high-bit truth, DUP16 underflow, unsupported opcodes and separate
1024 capacity. Existing selectors and source admission are unchanged.
Macro-iterations use denotational child runs: nested divergence may already
yield mathematical fault in one turn. Neither native instruction prefixes nor
source horizons/divergence, source-loop lowering, G24/views, native byte/PC/
resource/world/trace or final frontend adequacy is established here.

Independent read-only finder and skeptic reviews found no proof/control defect.
The skeptic's ambiguous wording about the no-finite-outcome case was fixed
and confirmed. Focused kernel checks and all three per-file diagnostics pass;
four guarded reports pin standard axioms. Broad checkpoint and final lane
validation remain separate obligations.

### Closed JSON compiler slice

`SolidityBridge.Yul.JsonCompilation.checkCompile` composes the actual
`YulJson.Words.check`, scoped statement compiler, stack-slot emission and
occurrence selector. Its result retains the producer's dependent checked-JSON
certificate. `Compiled.source` proves normal closed-word execution at that
same horizon; `Compiled.model` proves emitted scalar execution and preserves
the full existing mathematical machine for every represented numeric caller
suffix. Stack capacity remains separate.

The synthetic three-statement JSON fixture declares 7, adds 9 and multiplies
by 3. A kernel theorem ties its factored decoder certificate to the original
checker/compiler call. Intermediate target results 16 and 48 precede local
retirement. Controls cover dirty caller words, all machine fields, capacity,
insufficient horizon/depth, unsafe/duplicate flags, unsupported EVM version,
compiler-dependent builtins, duplicate locals and checked-but-uncompiled `if`.
Finite string-decoder facts avoid increasing proof budgets.

Independent read-only finder and skeptic reviews found no confirmed defect;
neither ran Lean or a server. This is synthetic JSON/kernel-model evidence,
not pinned external solc/EVM evidence, Source attachment/MemOK, open dirty-local
readback, Body dispatch/admission, source-loop/function compilation or complete
Source/G24/views/native adequacy. Canonical rethrow and admission are unchanged.

Focused kernel checks, both per-file MCP diagnostics, scoped trust and three
standard axiom pins pass. The checkpoint's touched build, trust, layer, root,
doc-path and global axiom-pin gates pass; its library gate is resource-stopped
in unchanged `Frontend/Checked/UnitExamples.lean`. The broader optional Bridge
check was interrupted by runtime restart and remains pending. These outcomes
do not establish final lane validation.

### Original scopes with structured bodies

`SolidityBridge.Yul.ScopedControl` composes existing initializer compilation and
normal-control derivations for original Yul `let` and zero-initialized scopes.
Four general source/`StructuredExec` laws derive initialization, body execution
and exact fresh-prefix retirement; arbitrary caller suffixes remain identical.
The zero scope supports arbitrary arity, including zero. Emission selects at
temporary depth zero and retains actual code-selection equations. No source
AST, state, function convention or blanket simulation premise is introduced.

Controls instantiate nested branches under a fresh local, live old-local
updates with dirty full words, two fresh zero locals and zero arity. They check
both branch directions, nonselected locals, full machine fields, underflow,
last accessible live position 15 versus intrinsically valid position 16,
and separate prefix capacity versus oversized mathematical model success.
Finite selector witnesses do not replace the four general laws.

Independent read-only finder/skeptic reviews found no confirmed defect. Focused
kernel checks pass; failed scratch formatting/control-index attempts and the
default-heartbeat limit for a generic selector fixture are retained without
budget changes. These are scope/body combinators, not a complete recursive
scope visitor, source-loop/function compilation, Solidity Source attachment,
physical/G24 or native correspondence. Broad import/final gates remain open;
the unchanged library resource blocker is not retried for this component.

Both new per-file MCP diagnostics report zero errors. Focused/touched kernel,
scoped trust, layer, generated-root, doc-path and global axiom-pin checks pass.
The existing library headroom stop and interrupted optional Bridge closure
remain recorded limitations; they are not reclassified as passes.

### Recursive normal scope/control visitor

`SolidityBridge.Yul.RecursiveScopes.compile` now recursively compiles original
Yul sequences, conditionals, single-word initialized scopes and arbitrary-arity
zero scopes, using the existing normal compiler for leaves. Its evidence is
indexed by the original statement, control, context and source horizon. Two
general proofs derive actual same-horizon closed-word evaluation and exact
`StructuredExec` execution for every emitted block and caller suffix. Scope
entry/retirement is derived, not assumed; temporary depth is zero.

Controls combine nested scopes under a branch with a later scoped multiply,
producing 20 and 140 while preserving other locals, dirty words and machine
fields. They cover false/high-word conditions, actual source evaluation,
insufficient horizons, underflow, live index 15 versus inaccessible 16, separate
prefix capacity, oversized model success and explicit loop/early-flow refusals.
This extends the compiler, not Solidity admission or full Source/G24/native
adequacy; functions, loops, early flow and physical/readback composition remain
open.

Independent finder review caught a G0 indexed-match violation in three helper
definitions. It was fixed with generalized explicit recursors and structural
recursion; the same 111-job proof/control checks pass (observed 7.64 versus
7.68 seconds). Finder confirmed the fix; skeptic found no mathematical defect.
Neither reviewer ran Lean or a server. Proof budgets and verdicts are unchanged.

Focused/per-file kernel checks, both per-file MCP diagnostics, touched imports,
trust/layer/registration/docs and global axiom pins pass. Two guarded axiom
reports use standard axioms only. Broad library/optional-root/final gates remain
open; prior resource and runtime-interruption failures are retained.

### Checked JSON to recursive structured compilation

`SolidityBridge.Yul.StructuredJson.checkCompile` now composes the real checked
word JSON producer, recursive compiler and existing structured model selector.
Its certificates retain the exact checked tree, horizon, emitted block and
selected code. General laws prove same-horizon closed-word evaluation and
whole mathematical machine identity for every represented numeric caller
suffix after local retirement. Capacity remains separate.

The actual checker/compiler result is witnessed for a true conditional around
the existing let-7/add-9/multiply-3 JSON fixture. Its outer decoder derives the
real child decoder certificate at the corresponding structural bound, with
unchanged metadata/safety/preparation checks. Controls observe the actual
conditional guard and model/caller fields, refusals and oversized model
success. The prior scalar-only API keeps its old refusal; the structured API
accepts its checked conditional. No existing verdict or admission is changed.

Independent read-only finder and skeptic reviews found no confirmed defect.
This is synthetic JSON/kernel-model evidence, not external solc/EVM evidence,
Body dispatch/admission, Source attachment/MemOK, open raw-local readback,
complete Source/G24/physical views or native/world/resource/trace adequacy.

Focused/per-file kernel checks, two per-file MCP diagnostics, touched imports,
trust/layers/generated roots/docs/module-map and global axiom-pin checks pass.
Three guarded reports use standard axioms. Full library/Bridge/final gates
remain open with prior raw resource/interruption failures retained.

### Original switch component

`SolidityBridge.Yul.SwitchCompilation` compiles an original selector, intrinsic
case list and fallback with actual existing normal scope/control bodies.
Context/horizon-indexed case evidence follows the real per-arm fuel decrease.
Five general laws derive concrete PUSH/DUP2/EQ behavior, case-list source and
structured execution, and whole-switch source/structured composition. The
selector is evaluated once, compared as a full word and removed before the
chosen body or fallback; caller suffixes remain identical.

Controls distinguish first, dirty, late and default matches, scoped updates,
empty case dispatch, source evaluation and complete observed model fields.
The first body changes the selector variable to a later case label without
fallthrough. Live position15 succeeds while16 refuses emission. Existing JSON
duplicate-label refusal remains intact. A new control initially assumed that
`stackBound` certified DUP operands; the corrected paired controls show height
capacity at zero while actual execution underflows. Raw failure is retained;
the predicate, old verdicts and budgets are unchanged.

Independent read-only finder and skeptic reviews found no confirmed defect.
This is a root-switch component over existing recursive normal bodies, not a
complete mutually recursive switch visitor or frontend admission. Nested-switch
bodies, functions/loops/early flow, complete Source/G24/physical/readback and
native/resource/world/trace adequacy remain open. Prefix bounds are not whole
program physical-validity proofs; model controls are not external EVM tests.

Focused/per-file kernel checks, both per-file MCP diagnostics, touched imports,
scoped/global trust, layer/root/docs/module-map and five guarded standard axiom
pins pass. Full library/Bridge/final gates remain open with prior raw resource
and runtime-interruption failures preserved; unchanged failed full operations
were not repeated for this optional component.


### Ordered switch composition

`SolidityBridge.Yul.SwitchControl` compiles the original sequence and
conditional constructors around actual `SwitchCompilation` certificates and
`RecursiveScopes` leaves. Its evidence is indexed by the unchanged original
statement, context and source horizon. Explicit generalized recursors retain
G0. Both `Derivation.source` and `Derivation.structured` are constructive:
source evaluation uses the exact child horizon, and target emission implies
whole-block execution on every local vector and identical arbitrary caller
tail. Sequential induction uses the first body's updated locals for the
second body; it never assumes a desired execution. Two guarded axiom reports
contain only the standard axioms.

Controls distinguish sequential dispatch from stale-state execution: the
first switch changes selector1 to3 and accumulator11 to21, then a conditional
second switch produces147. Zero skips that dispatch; a dirty nonzero guard
takes it. Full dirty selector bits, caller words and machine fields remain
observable. Nested sequence/conditional uses, source execution, insufficient
fuel, inaccessible slots, actual underflow and oversized mathematical success
are checked. Switches inside case bodies or lexical scopes still refuse;
this visitor does not claim their admission or recursive compilation.

Independent read-only finder and skeptic reviews found no confirmed findings.
Focused/per-file kernel checks, two MCP diagnostics, trust/layer/root/docs and
axiom inventory checks pass. The core-only touched tool reports no targets
for this Bridge-only change; the explicit focused build supplies its import
check. Earlier broad library/Bridge failures and full-lane obligations remain
open. No new external solc/EVM evidence or Source/G24/native adequacy is claimed.


### Lexical scopes around switch composition

`SolidityBridge.Yul.ScopedSwitch` composes actual `SwitchControl` leaves with
the original sequence, conditional, one-value declaration and zero-prefix
constructors. Evidence remains indexed by the original statement, context
and horizon; helpers use explicit generalized recursors. No new source AST,
state or function convention is introduced. The initializer runs in the old
context, the body receives the exact fresh prefix, and scope exit retires
only that prefix. `Derivation.source` and `Derivation.structured` constructively
prove original evaluation and whole-block target execution for every local
vector and arbitrary caller tail. No desired run is a premise. Two guarded
standard-axiom reports are recorded.

Inhabited controls combine nested let/zero scopes and switches, multiword
zero initialization, dirty fresh words, writes to outer locals, a copied
old-context initializer, conditional scope entry and an empty prefix. Selected
model observations retain all caller words and machine fields while removing
both fresh prefixes. Additional update controls are backed by the general
source/structured proofs; they are not separate native execution evidence.
Original `SwitchControl` refusals remain unchanged. Case-body nested switches
still refuse; shifted live slot15 emits and16 does not. Actual underflow,
source fuel refusals, prefix-only capacity and oversized mathematical success
remain distinct controls.

Independent read-only finder and skeptic reviews found no confirmed findings.
Focused and per-file kernel checks, both MCP diagnostics, checked signatures,
trust/layer/root/docs/module-map and axiom inventory pass. The toolkit touched
gate selects no targets for these Bridge-only modules; their explicit focused
build supplies the local import check. Earlier broad build failures remain
open without unchanged retries. General switch case bodies, functions/loops/
early control, multi-result declarations, Source/G24/views/raw readback,
frontend admission and native/final joint adequacy are still unfinished.


### Recursive cases and defaults

`SolidityBridge.Yul.NestedSwitch` supplies a concrete mutually recursive
visitor on the original statement and case families. Its `Compiled` and
`CompiledCases` records contain the exact original source evaluation and
structured-target proofs. The visitor constructs every returned certificate
from concrete operation leaves and proved sequence, conditional, scope and
case producers; no source/target law is an assumed producer obligation.
Explicit original-family recursors and structural source-horizon recursion
retain G0. Operation leaves keep their existing supported/refusal domain;
this is normal closed word-control compilation, not general Yul admission.

Case suffixes and arm bodies consume their actual decreasing horizons while
the default retains the original switch child horizon. The selector is
computed once, compared as a full word, and retired before exactly one
chosen arm/default. Scope entry/exit preserves outer mutations and arbitrary
caller tails. Nine guarded standard-axiom reports include the actual mutual
compiler definitions and all new proof-producing combinators, rather than
only record projections.

Reviewed controls inhabit nested case/if/let/zero/switch combinations and a
nested default. A dirty accumulator selects a later inner switch after the
scope update; changing the outer selector to3 does not execute its later
outer case. Actual source evaluation and selected-model observations retain
caller words and machine metadata. False guards, earlier API refusals,
new nested-case success, exact case-fuel refusals, shifted positions15/16,
underflow and height-capacity versus oversized-model success are separate
controls. Existing expected verdicts and admission remain unchanged.

Independent read-only finder and skeptic reviews found no confirmed findings.
Focused/per-file kernel checks, both MCP diagnostics, exact signatures,
trust/layer/root/docs/module-map and axiom pins pass. Two redundant closing
tactics and an unnecessary unreduced-match change were corrected without
changing statements or budgets; raw diagnostics and automation failures are
retained. The core-only touched selector finds no Bridge targets, so the
explicit focused build supplies local import validation. No new external
compiler/EVM evidence is claimed. Functions/loops/early flow, multi-result
bindings, Source/G24/views/raw readback, frontend admission, native/resource/
world/trace correspondence and full joint gates remain unfinished.


### Checked JSON consumer migration (partial)

`SolidityBridge.Yul.StructuredJson` now consumes the actual
`NestedSwitch.Compiled` certificate and mutual compiler. Its existing
`Compiled.source` and `Compiled.model` conclusions and proofs are unchanged:
actual checked closed-word execution terminates normally, and selected-model
execution preserves the arbitrary represented caller and complete machine.
The concrete compiler/checkCompile definitions now have guarded standard-axiom
reports as well. The old conditional/arithmetic kernel packet regressions
still check with the migrated certificate type.

`StructuredSwitchJsonControls` exercises real synthetic JSON checking,
preparation, nested compilation, emission and model selection. Nested dirty
case matching changes x1 to3 without outer-case fallthrough; a following if
multiplies it to21. Late/default paths produce999/42/17. An analysis-only
extractor inspects the actual emitted block before its final local POP,
so these finite observations check arithmetic and dirty matching rather than
only the empty final scope. It is not a general compiler transformation or
source-preserving extraction theorem. Full fixture runs preserve caller words
and observed machine fields; input, safety, duplicate/default-order, opcode,
horizon and oversized-model controls remain separate.

New raw-JSON success is checked by evaluations, not a named kernel parse
certificate. Direct standard-tactic attempts at that exact success proposition
did not reduce; no budget was raised. The exact packet/equality statement is
handed off as new H14 task NJ1 in [TERRA-TODO](../../TERRA-TODO.md), with no Lean
stub or axiom. This milestone therefore remains partial. The general kernel
consumer proofs do not by themselves certify this particular JSON fixture.

Independent read-only finder and skeptic reviews found no confirmed findings.
Affected focused/per-file checks, MCP diagnostics, trust/layer/root/docs,
module-map and axiom inventory pass. Initial reserved-name/default-forwarding
syntax diagnostics and failed kernel attempts remain saved. Missing-memory-safe
control uses the otherwise-successful payload. No old verdict, fixture budget,
Body dispatch, feature status or canonical rethrow changed. These are synthetic
controls, not external solc/EVM evidence. Source attachment/MemOK/readback,
frontend admission, full Source/G24/native correspondence and final joint gates
remain open alongside NJ1 and the original unfinished queue.


### NJ1 kernel components (raw attachment still partial)

`StructuredSwitchJsonKernelControls` now constructs the explicit existing
`Syn` tree, an inhabited `WordSyntax.Prepared` program, and its concrete nested
lowering/emission/selection in the kernel. These inhabitants do not depend on
any raw parser hypothesis. Source and structured-target certificates are
available for that actual prepared program; its model prefix control produces21.
No new AST, state, parser implementation or calling convention is introduced.

`checkedFromParse`, `compiledFromParse` and `packetFromParse` construct all
remaining packet fields, reusing the actual earlier span equation.
`compilesFromParse` proves exact reconstruction of `checkCompile`, with the
single explicit premise `blockAux 20 ast = .ok tree`. That equality has NOT
been proved. Conditional packet/source/model conclusions do not inhabit the
premise or close NJ1. The updated H14 routine handoff now asks for that exact
remaining equality, then instantiation of the existing builders. No bare
`raw_nested_packet` or unconditional raw compilation theorem is exported.

Six enforced axiom reports contain only standard axioms. Independent read-only
finder and skeptic reviews found no confirmed findings and checked the partial
boundary. Focused/per-file kernel checks, MCP diagnostics, exact signatures and
static gates pass under unchanged budgets. Direct and recursive simplification
attempts retain their failed exits, including default recursion-bound failures;
no limit was raised. Polymorphic-list import, closed shape-decision type and
selected-index scoping diagnostics were fixed without changing postconditions.

New prefix/oversized controls use the independently inhabited tree compiler,
not an assumed decoder proof; they remain finite model observations. New raw
JSON guards from the previous milestone remain evaluations. Body admission,
Source/G24/views/readback, native/resource/world/trace adequacy, final joint
gates and the original unfinished queue remain open along with the NJ1 equality.


### NJ1 exact fixture attachment closed

`StructuredSwitchJsonKernelAttachment` proves `raw_nested_parsed`, the original
`blockAux 20 ast = .ok tree` obligation, without a parser premise. The original
`raw_nested_packet` and exact `raw_nested_compiles` equality are instantiated
from that proof. `raw_nested_source` proves actual checked-word execution at
horizon16, and `raw_nested_model` quantifies arbitrary mathematical machines
and caller tails with the existing represented-stack premise. NJ1 is closed
for this one unchanged synthetic fixture; it is not generic JSON correctness.

The proof reuses the existing decoder, literal-range and child equations.
Case producers retain decoded-word freshness, singleton final default and
nonempty-switch checks. Three existing path equations are exposed unchanged;
only y/eq require new finite identifier proofs. Small constructor equations
avoid failed large definitional reductions, with no recursion-budget increase.
Bounds20/16, dirty literal and expected21/999/42/17 observations are unchanged.
`raw_nested_low_fuel` additionally proves exact compiler refusal at horizon2;
this is not general source revert/divergence transport.

Independent read-only finder and skeptic reviews found no confirmed findings.
Six actual endpoint axiom reports are enforced with standard axioms only.
Focused/per-file kernel checks, MCP diagnostics, signatures, trust/layers/
roots/docs/module-map and axiom inventory pass. Raw failed automation,
elaboration and recursion-limit exits are retained. The prefix observations
remain finite target analysis controls; the raw packet/parser equality is now
a named kernel witness. No new external solc/EVM evidence is claimed.

Body admission, independent JSON specification/completeness, source attachment/
MemOK, Source/G24/views/readback, native/resource/world/trace correspondence
and final joint gates remain unfinished. Closing NJ1 does not complete VY3.


### Finite emitted while execution

`SolidityBridge.Yul.LoweredWhile` closes the target-only execution gap of the
existing `lowerWhile` emitter. `parts` recovers its actual condition/body
programs; `slices` and `structured` derive the complete finite `StructuredExec`
run from the existing lowering certificates. For every `j < count` the exact
guard at `Nat.repeat update j locals` must be nonzero, and the guard at `count`
must be zero. These are explicit finite-exit premises, not assumed slice runs.
The theorem preserves every newer-prefix/caller word and all nonselected locals
that the supplied update preserves. `model` transports that actual result
through a real selected realization with its represented-stack premise.

Controls compile the original intrinsic local condition and subtraction
assignment, inhabit zero/two-turn proofs with arbitrary caller tails and a
two-word newer prefix, and retain dirty words in both scopes. The original leaf
source certificates are checked; no whole Source FOR-loop theorem follows.
Shifted last-slot accessibility, RHS temporary-word refusal, underflow and
scalar success at height1024 with failed capacity remain distinct controls.
Seven enforced axiom reports use only standard axioms. Independent read-only
finder and skeptic reviews found no confirmed findings; bare audit reports were
pinned before committing. No AST, evaluator, calling convention, limit,
admission rule, manifest or expected verdict changed.

This is Original Backfill A/B target preparation. Whole original FOR/source
horizons, termination/divergence, source/G24/views, native/charged/capacity/world
correspondence, frontend admission and final joint gates remain open. NJ1's
previous exact fixed-fixture attachment remains complete.


### Normal original FOR compilation slice

`SolidityBridge.Yul.NormalFor` prepares the original four intrinsic FOR
components using the actual pure expression/statement compilers. `Prepared`
holds their indexed compiler outputs; it is not another AST or source state.
`emit` lowers the prelude once followed by the existing condition/body/post
loop, with body before post. `LoweredWhile.repeat_shift` is exposed unchanged
for reuse; the prior execution contracts are unchanged.

`source_loop` proves original closed-word `evalLoop` execution at horizon
`base + count + 1`; `source` includes the actual prelude and original `for_`
at `base + count + 2`. The four proved component horizons must be at most
`base`. Existing producer horizon stability supplies every actual child run.
Each pre-body guard at iterate `j < count` must be nonzero and the final guard
at `count` zero, over `post.update (body.update locals)` after the prelude.
These sufficient finite-exit premises do not infer termination or a least fuel.
`structured` and `model` give the same final word locals with arbitrary newer
prefix/caller tail; model retains actual selection and represented-stack
premises. Capacity, native gas and logical Solidity Source/G24 are separate.

The inhabited witness compiles original local/assignment/subtraction/addition
AST components. Its prelude sets counter2, the body decrements it, and post
adds the updated counter to a dirty accumulator: two turns give dirty+1,
whereas reversing body/post would give dirty+3. Kernel theorems cover the
actual original FOR at sufficient horizon7, complete structured execution and
selected mathematical-machine execution for arbitrary caller tails. Source
horizon2 exhaustion, compiler horizon2 refusal, break/continue refusal,
shifted temporary accessibility, target underflow and oversized numeric success
with failed prelude capacity remain distinct controls. No external solc/EVM
claim or old fixture budget/verdict changes follow.

Independent read-only finder/skeptic reviews found no confirmed findings.
Nine enforced axiom reports use standard axioms only (repeat_shift uses none).
Full Y08.01 logical Source/G24/views/functions/early-flow/divergence, general FOR
dispatch, Y08.02 native opcode/world/resource composition, frontend attachment,
remaining backfill and final joint gates remain unfinished. NJ1 stays complete
for its earlier fixed synthetic fixture.


### Direct MSTORE/view composition

`SolidityBridge.Yul.DirectMemory` emits value-PUSH, address-PUSH, MSTORE using
existing target instructions. Its actual byte-addressed `runSlice` execution
agrees with VY2 `mstore` for every initial byte map and caller. The target's
existing encoder and producer bytes are proved equal; no word/layout/state
semantics is replaced. Selected code retains the materializer's exact
`address + 32 ≤ 2^256` domain. Under that premise the three-instruction store
refines the earlier 96-instruction byte materializer. Instruction counts are
static controls, not gas claims.

`view_read_after_store` concerns the producer view's `mload`; it does not execute
target MLOAD (which this unchanged target slice refuses). `image_preserved`
frames an actual intrinsic `MemoryImage p d` when its whole span is disjoint
from the written32bytes. This preserves that supplied image, not global MemOK,
heap ownership or logical writeback. Canonical hashing composes the direct
store with the existing `withKeccak` adapter, without any collision premise or
claim about other Fixed instances.

`capacity_iff` derives necessary and sufficient `caller.length + 2 ≤ 1024` for
all four actual `runSlice` instruction prefixes. It does not substitute the
numeric `Scalar.stackBound` predicate, whose executor refuses MSTORE. Kernel
controls inhabit exact1022room and1023refusal, unaligned dirty-word refinement,
view reads and typed-image framing. Other controls distinguish big endian,
zero/max words, operand reversal, missing operands, header aliasing, word-end
selection, unsupported target MLOAD/SSTORE, hashing and oversized local success.

The published `SolidityBridge.AccessBridge.HostWriteControls` counterexample
still blocks general pinned native writer/image closure at host-sized gaps.
The local Nat-map theorem is not that native writer theorem: selection still
admits2^64, and an explicit control preserves its local semantics without a
host-size exclusion. No native/charged correctness, admission or premise is
weakened to hide the counterexample. No owner implementation is edited.

Independent read-only finder/skeptic reviews found no confirmed findings.
Sixteen standard-only axiom reports are enforced. The freshly published master
was adopted while preserving the old checkpoint; generated roots remain the
only registration path. Full Y08.01/02, frontend, remaining backfill and joint
validation remain open. No new external solc/native-EVM evidence is claimed.


### Branch-bearing FOR components

`SolidityBridge.Yul.StructuredFor.prepare` uses the existing `NormalControl`
compiler for prelude, body and postlude and the existing pure expression
compiler for the condition. Its `Prepared` packet is indexed by those original
intrinsic AST components. Emission preserves branch/sequence blocks instead
of inventing scalar code for them. The target-loop proof derives body/post
runs from the actual `StructuredSource.structured` theorem and composes the
whole finite loop, prelude and selected mathematical-machine result.

`ForSource.source_loop` factors the earlier original-evaluator induction. Its
two normal-source laws are explicit real premises, discharged concretely by
`NormalFor`'s `Compiled.source` and `StructuredFor`'s `Derivation.source`.
The prior `NormalFor.source_loop` statement and all other old code/proofs stay
unchanged apart from that proof and import; old controls and horizons7/3/2
are unchanged. The refactor was warned about, with bounded before/after
per-file timings retained. No representation or proof budget changed.

The new source proof still uses exact horizons `base + count + 1` for the loop
and `base + count + 2` for the original FOR. Actual component horizons must
be bounded by base; every pre-body guard must be nonzero and the final guard
zero after the prelude and repeated post-after-body update. These finite-exit
premises do not establish general termination or source divergence. Model
transport retains actual selected realization and numeric represented stack.

The kernel witness has branches in all three statement components, a flag
with only bit200 set, three locals and a dirty accumulator. Full-word truth
must take the pre/body branches; the post tests the updated counter, yielding
dirty+1 after two turns at sufficient source horizon8. Separate source6 and
whole-target proofs cover a false prelude branch and zero iterations. Arbitrary
numeric callers and newer prefixes are preserved. Other controls retain
source/compiler exhaustion,13/14access boundaries, early-flow refusal,
underflow, oversized model success and finite source exhaustion of an unending
case; the unending target is never evaluated.

Independent read-only finder/skeptic reviews found no confirmed findings.
Twelve new standard-only axiom reports are enforced. This closes the finite
branch-component slice, not general root FOR dispatch, logical Solidity
Source/G24/views/readback/functions, early-flow/divergence, native/expansion
capacity/world correspondence, frontend admission or full joint validation.
The published native host-writer counterexample and earlier partial gates
remain open. No new external solc/native-EVM evidence is claimed.


### All-horizon FOR noncompletion and finite model turns

`SolidityBridge.Yul.ForPrefixes.source_loop_never` and `source_never` prove
original closed-source noncompletion at every horizon when the actual compiled
guard stays nonzero under every post-after-body iteration. Existing completed-
run uniqueness identifies each actual condition/body/post/prelude result with
its real compiler source certificate, including horizons below component fuel.
No minimum source horizon or assumed desired whole-loop result is introduced.
The normal component and forever-guard premises remain explicit.

`macro_prefix` derives each actual model turn from the real condition Slice,
body Realization and emitted compiler blocks. It proves exact `loopIterN`
continuation after every finite turn count, preserving newer words, arbitrary
numeric callers and all nonstack machine fields. These are denotational child
macro-turns, not fetched/native instruction prefixes. The existing model
represents no finite loop outcome by `.fault`; `model_loop_no_finite_outcome`
uses that definition. It does not assert exceptional native halt, source panic
or revert, or change any observations to equate them.

The concrete original branch-bearing FOR now has a genuine unending witness:
flag0 keeps its body from decrementing counter99, while post increments the
accumulator. An inductively derived counter/flag invariant supplies forever
guards, source noncompletion for all fuel, exact target continuation for all
counts and the whole actual selected-program denotation including its prelude.
Only a three-turn model prefix is evaluated. The previous high-flag terminating
witness constructively refutes the forever premise; it still terminates by its
unchanged prior theorem. No unending target is evaluated or inferred merely
from a finite timeout.

Independent read-only finder/skeptic reviews found no confirmed findings.
Eleven new standard-only axiom reports are enforced. No AST/state, observation,
fixture budget/verdict or existing source/compiler contract changed. This
closes these pure normal-component source/model facts, not full logical
Solidity Source/G24/view/function/early-flow/divergence refinement, native
prefix/charged/capacity/world correspondence, frontend admission or final
joint validation. The native host-writer counterexample remains open. No new
external solc/native-EVM tests are claimed.


### Source-completion-driven FOR transport

`SolidityBridge.Yul.ForCompletion.loop_complete` inverts an actual successful
original closed-word `evalLoop` at any horizon. It derives a count strictly
below that horizon, all pre-body nonzero guards, the first zero guard, and the
exact iterated normal output. Real condition/body/post compiler source facts
and completed-run uniqueness discharge component identities and exclude early
flow; no desired exchange/run or source count is assumed. `source_complete`
includes the actual prelude once and derives `count + 1 < fuel` for the whole
original FOR. There is no minimum component-horizon premise.

`transport` uses this recovered certificate with actual emitted blocks and
selection to obtain `StructuredExec` and the selected mathematical `Evm.run`.
`transport_output` matches the actual successful source output vector exactly,
using pointwise raw-word injectivity; it preserves arbitrary newer/caller
prefixes and all nonstack machine fields. Its remaining premises are actual
normal compiler certificates, source completion, successful emission, selected
realization and numeric whole-stack representation. No target run/count/guard
sequence is supplied by the caller.

Controls derive results from the previous branch-bearing source run at horizon8
and zero-guard run at horizon6, without providing iteration counts. The three
source-result locals are matched exactly; the two newer words, arbitrary numeric
caller tail and unchanged high-only flag are preserved. Short horizons (at most1) and the actual infinite source witness
refuse the success premise; these are source horizon controls, not EVM underflow
or native failure. Only terminating code is executed by the runtime regression.
Eight standard-axiom reports are enforced. Independent read-only finder and
skeptic reviews found no proof defects in the final producer/controls; the
skeptic requested the preservation wording above to distinguish updated locals
from preserved frame/flag words, which is corrected here.

This is closed-word source to selected mathematical-model transport for the
actual normal FOR component compiler, not general logical Solidity Source/G24,
root frontend dispatch, early-flow/function/native instruction-prefix/resource
or view adequacy. Full Y08.01/Y08.02, frontend/joint artifacts, remaining original
backfill and full lane validation remain open. No admission, manifest, canonical
rethrow, observation, proof budget or producer-owner implementation changed.


### Finite FOR target-to-source reflection

`SolidityBridge.Yul.StructuredUnique.output_unique` proves determinism of the
unchanged finite `StructuredExec` relation, including actual branch and loop
constructors. `ForReflection.loop_complete` then inverts actual emitted FOR-loop
execution. The real scalar condition law identifies its full-word guard and
unchanged locals; target uniqueness against actual compiler body/post execution
fixes each next local vector. The finite target derivation supplies the count,
all pre-body nonzero guards, the first zero guard and exact final stack. These
facts are conclusions, not additional run/count premises.

`source_of_structured` reflects the actual prelude once and constructs original
closed-word FOR evaluation at `base + count + 2`. The bounds `af, cf, pf, bf ≤ base`
are explicit real component horizon bounds. `source_of_model` consumes any actual
successful selected mathematical-model run, uses its existing classifier, and
derives source completion, the exact returned stack/nonstack machine frame and
pending-skip count zero. Neither a source run nor desired intermediate/target
result is assumed. Actual compiler emissions and selected code, normal component
certificates, numeric initial stack representation and the stated horizon bounds
remain necessary. This complements the forward `ForCompletion` proof without
asserting a native/source observational equivalence.

Inhabited branch-bearing and zero-guard controls reuse real selected program
successes with three locals, two newer words, arbitrary caller tail and dirty/high
words. Source-result locals change exactly as the source; newer/caller/unchanged
flag words and nonstack machine fields are preserved. A nonzero pending count is
refused; the prior true infinite witness cannot provide a successful model run
(no unending execution is evaluated). Another witness has 1025 input stack words:
its mathematical-model success coexists with the actual condition code's failed
`Scalar.stackBound` check. This is not whole-block/native capacity adequacy.
Nine actual standard-axiom reports are enforced. Independent read-only finder
and skeptic reviews of the final producers, controls and metadata found no
confirmed findings; neither reviewer used Lean/server/tests.

Full logical Solidity Source/G24/views/functions/early-flow/root dispatch and dirty
readback, native/charged/decoder/physical-origin/world/resource closure, frontend
attachment, original backfill remainder and full lane/joint validation remain
open. Source/target definitions, admission, exclusions, observation and proof
budgets are unchanged; no prerequisite-owner files were edited.


### H26 P20 success interface V1

`Solidity.Yul.Compilation.P20.InterfaceV1` freezes the closed-normal success
sub-interface first. `ClosedProducer` is an alias of the existing original-AST
`ProducerStatements.Compiled`; its implementation and obligations are unchanged.
A real two-local dirty-word assignment witnesses this reused part only.

`PendingG24` refers to actual `Evm.Compiler.Compilation`, `Evm.Frag`,
`Solidity.Prog`, Yul statement/profile and target block. Its exact-code
`LoweringCertificate`, owner domain/encodings, forward/backward source-success
laws and genuine joint source/Yul success witness are explicit obligations.
`PendingRepresentedSuccess` retains actual branch-specific `Compilation.Input`
and `Compilation.Rep`, payment freedom, exact machine/caller-stack preservation
and original output fragment. Its `required_input` jointly witnesses the SAME
source state/machine/layout/outcome/horizon satisfying domain, actual Input,
payment freedom and both genuine source/Yul successes. This fixes the skeptic's
pre-freeze vacuity finding; one witness does not establish full-domain coverage.

There is no instance of either pending structure, no claimed source embedding
or G24 adequacy from these declarations, and no replacement state/relation.
Finder and skeptic re-reviewed the nonvacuity fix with no remaining contract
findings. Three actual standard-axiom reports are guarded. Registrations and the
signature ledger are generated by scripts. This is a small H26 signatures-first
handoff; original concrete proofs and their premises remain unchanged.

V1 does not freeze full P20 adequacy: actual Source/frontend origin/admission,
H11 raw-frame/pipeline readback, physical views/writeback, function/early-flow,
failure/divergence/prefix, native resource/observation and final joint laws remain
original implementation obligations. H16/H19/H25 Source and H22 ExtCall are
untouched. The separately recorded H1 cache-admission deficit remains blocked;
no protected cache/output/evidence was removed and no shipment is claimed.


### Emitted FOR physical shape and room

`SolidityBridge.Yul.ForShape.actual_layout` ties the named readable instruction
vectors to the actual previous `StructuredFor` target by kernel equality,
including PUSH32 widths and zero-based DUP/SWAP indices. Independently computed
height traces show prelude-arm peak `h+1` and body/post-arm peaks `h+2`, with
final height `h`. Actual `InstrShape`/`CodeShape` proofs derive operand existence
from `h ≥ 5` (three locals, two newer words), separately from every scalar
prefix's `stackBound` capacity. No successful run/exchange/shape is assumed.

`shape_iff` proves precisely that the EXISTING `LabelExec.BlockShape` for this
emitted block, with input/output height `h ≥ 5`, holds iff `h+2 ≤ 1024`.
Necessity comes from the prelude branch's actual test-capacity field via a
generalized existing-shape recursor; it is not a lower-bound theorem for every
possible EVM execution. `expansion_room` separately constructs the existing
join-jump `ExpansionRoom` obligation. Neither result supplies the remaining
`ControlCertificate.realize` field or a whole native execution certificate.

Controls prove the actual five-word frame plus arbitrary caller is shaped when
caller length is at most1017, including the last accepted height1022. Height1023
is refused despite the scalar loop condition fitting by itself. Body/post
arithmetic also peaks at two extra words; no claim blames only the jump. A real
finite selected-model run at that refused height remains successful, explicitly
separating mathematical success from physical shape/native adequacy. Actual
flag/counter underflow and high-only/dirty-word controls retain their original
semantics and expected outputs. Sixteen standard-axiom reports are enforced.
Independent read-only finder and skeptic reviews of the final producers,
controls, pins, imports and documentation found no confirmed findings; neither
reviewer used Lean/server/tests.

These are target preparation for Y08.01/Y08.02/original Backfill A; full byte/PC,
charged/native/scanner/resource/G24/views/frontend/function/early-flow/readback,
original backfill remainder and final joint/lane gates remain open. The H26 V1
signatures and existing concrete producer premises are unchanged. No source,
state, target predicate, calling convention, budget, admission or owner file is
modified; allocation offsets are not equated with live stack positions.


### FOR with lexical scope and switch components

`SolidityBridge.Yul.ScopedFor` consumes the actual `NestedSwitch.Compiled`
prelude/body/post and `PureExpressions` condition outputs. `prepare`, `emit`,
`select` and `compile` construct real original-AST-indexed certificates, target
blocks and selected code; no simulation callback or replacement syntax/state is
introduced. This adapter uses depth0 locals with an arbitrary numeric caller
suffix, not an additional newer-prefix convention.

`source` discharges both shared `ForSource` laws using actual component `.source`
proofs, includes the prelude once and proves original FOR execution at
`base + count + 2` with common component fuel at most base. `loop_structured`
and `structured` independently derive body-before-post and whole-block execution
from the real component emissions. `Packet.model` derives the complete selected
mathematical machine result, preserving the caller and every nonstack field.
Finite pre-body nonzero/final-zero guards remain explicit; no general termination,
source completion inversion, native/capacity or Source/G24 theorem is asserted.

The inhabited control uses a scoped fresh temporary to save/decrement the old
counter and a postlude switch: zero adds10, default adds1. Prelude resets the
counter to2, so for EVERY initial raw counter the original source at horizon10
(component6 + count2 +2) and target/model finish at `[0, dirty+11]`. Reversing
post/body order would yield `dirty+2`, which is refused. Caller suffixes are
arbitrary. Break and compiler horizon0 are actual preparation refusals, not
reclassified source failures. Full dirty-word/nonstack observations are retained.

The first control proof hit the unchanged200000 heartbeat limit by repeatedly
reducing combined compile/selection data. Factoring actual preparation/emission/
selection and exact reset/step/finish proofs removed that reduction; `compile_entry`
proves the factored packet equals the real combined compiler result using existing
Option bind laws. No theorem statement, initial-word quantifier, expected result,
source horizon or proof budget was weakened/raised. Raw failures are retained.
Twenty actual standard-axiom reports are enforced. Independent read-only finder
and skeptic reviews of final producers, controls, pins, imports and metadata
found no confirmed findings; neither reviewer used Lean/server/tests.

This adds concrete compilation beyond the previous branch-only FOR adapter.
Actual root frontend dispatch/JSON attachment, functions/early-flow, physical
views/capacity, H11 readback, full Source/G24/native/charged/world/observation
closure, remaining original backfill and joint/lane validation remain open.
H26 frozen interfaces, H16/H19/H25 Source and H22 ExtCall are unchanged.


### Source-success transport for scoped FOR

`ForCompletionSource.loop_complete` factors the existing original-source
completion induction with its two real universal normal-source premises.
`ForCompletion.loop_complete` keeps its exact old proposition and concretely
passes actual `NormalControl` source facts. All declarations after that proof,
old controls, premises and axiom guards remain byte-identical. This proof-only
refactor was announced before editing and checked before/after; no source/target
AST, state, evaluator, calling convention or runtime definition changed.

`ScopedForCompletion` passes actual `NestedSwitch` component source facts through
the same induction and includes the actual prelude. From ANY successful original
source horizon it derives count, finite guards, exact normal output and
`count + 1 < horizon`. There is no minimum source horizon assumption or supplied
count/guard oracle. The actual `ScopedFor` packet then supplies real emission and
selected code; concrete whole structured/model transport and raw-word output
injectivity preserve exact source-result locals, arbitrary numeric caller and
all nonstack machine fields. The shared helper by itself is not adequacy.

Controls quantify over every source horizon and complete output, with the actual
unchanged source10/dirty+11/all-initial-counter witness inhabiting the premise.
Short horizons are refused and the wrong-order dirty+2 result cannot be obtained
at another horizon, using actual completed-run uniqueness. Compiler fuel6,
source witness10, original budgets, observations and expected verdicts are
unchanged. Ten new standard-axiom reports are guarded. Independent read-only finder and
skeptic reviews of the final helper, concrete consumers, controls, pins, imports
and metadata found no confirmed findings; neither used Lean/server/tests.

This remains depth0 normal closed-word scope/switch FOR to the mathematical
model. Generic root frontend attachment, Source/G24/views/functions/early-flow,
readback, native/charged/capacity/world/observation closure, remaining backfill and
full lane/joint gates remain open. H26 interfaces and all owner holds are intact.


### Target-success reflection for scoped FOR

`ScopedForReflection` inverts the actual compiled scope/switch FOR target. The condition compiler's exact word/stack law and the real `NestedSwitch` body/post execution laws identify each iteration; target determinism supplies the exact next locals. From actual finite target evidence it derives the stopping count, every earlier nonzero guard and the final zero. From an actual packet and `compilerFuel ≤ base` it proves original source completion at `base + count + 2`. Selected-model success yields that source execution, identical arbitrary caller tail, exact raw locals/nonstack machine frame and pending zero. No source run, iteration count or desired exchange/run is assumed.

The controls use the existing original scoped-temporary/switch FOR with dirty `2^200+257`, all raw initial counters and arbitrary caller tails. They reject nonzero pending and the wrong body/post-order accumulator, and exhibit mathematical-model success at initial stack length1025 while explicitly recording that capacity is exceeded. Source/compiler fuels, original observations and expected results are unchanged. These are kernel/model results; no new solc/native EVM experiment was performed.

Validation: focused import build and two changed-file diagnostics; seven enforced standard-axiom reports; scoped trust, layers, generated roots, doc paths, module-map and inventory checks. Separate read-only finder and skeptic found no confirmed findings. Initial binder/parser/control-representation failures and a reduction-depth failure are retained; list-length lemmas fix the last without a budget change. Prior failed broad gates remain failed evidence, not passes.

This closes a target-only reflection slice, not Y08.01/Y08.02. General logical Source/G24/H11/view/function/early-flow/admission-origin producers, native fetched-byte/charged/scanner/world/ordered-observation/host-writer closure, frontend dispatch and complete final validation remain open. H26 P20 interfaces and all earlier contracts stay unchanged.


### Closed scoped FOR result and noncompletion equivalence

`ScopedForAdequacy.output_iff` relates an actual original source completion at some horizon with the exact full selected-model result for any final raw local vector. It retains the actual `ScopedFor.Prepared`/`Packet`, numeric initial stack representation and `compilerFuel ≤ base`. The reverse proof uses real reflection, injectivity of the numeric word encoding, caller-tail cancellation and finite-vector equality; the final locals are derived, not assumed.

`no_source_iff_fault` equates absence of completion at every source horizon with the selected model's denotation of no finite outcome. This is valid for the concrete closed normal component slice: actual component correctness and selection classification discharge the two directions. It does not equate a single exhausted horizon with divergence, or model fault with native exceptional halt, source revert or Panic.

The new witness uses the actual original literal-one condition and real compiled lexical-temporary body/switch postlude. Its actual `prepare` equality is kernel checked. Original source completion at any horizon would require one=zero; therefore the selected model has no finite outcome for every initial counter and arbitrary represented caller/full machine. The unending model is never evaluated by runtime testing. The earlier terminating source10 fixture remains the inhabited opposite control, retaining dirty `2^200+257` and the exact observation.

Validation: focused import build, changed-file MCP/per-file diagnostics, eight enforced standard-axiom reports and scoped static gates. Independent finder/skeptic reviews found no confirmed findings. The failed automation attempt is retained; no proof/fuel/node budget or existing verdict changed. This is kernel/model correspondence only. Full Y08.01 logical Source/G24/H11/view/function/early-flow and authentic frontend composition, Y08.02 native opcode/charged/scanner/world/ordered observations/host-writer adequacy, remaining original backfill and full lane validation stay open. Frozen H26 interfaces are unchanged.


### Finite scoped FOR macro-turn prefixes

`ScopedForPrefixes.macro_prefix` derives the exact selected numeric-machine state after any finite count of nonzero-condition turns, using the actual `ScopedFor.Prepared` condition/body/post emissions and real selection certificates. Every turn executes body before post, preserving the arbitrary caller suffix and all nonstack machine fields. The finite guard premise is explicit; no desired run/exchange result is assumed. The local vector is at loop entry, not automatically at the original source input. The companion no-finite-outcome law uses the existing model denotation and is not a native exception or source Panic/revert theorem.

The controls realize the actual prelude separately: arbitrary initial counter becomes two while the dirty accumulator, caller and nonstack fields are preserved. All-count prefixes then begin at that reset local vector. The literal-true original scoped/switch witness admits every finite prefix, including zero. Two turns yield counterzero/dirty+11; the third continues, wraps the counter to the maximum word and yields dirty+12. The bounded three-turn observation retains every original machine observation field and caller88. The whole unending evaluator is never runtime-executed; its original success refusal remains available.

Validation: focused actual import build, changed-file MCP/per-file diagnostics, eight standard-axiom guard pins and scoped static checks; independent read-only finder/skeptic reviews found no confirmed findings. Raw failed automation and initial parser diagnostics are retained; no budgets, existing verdicts or theorem contracts changed. These are kernel/model macro-turn prefixes, not native fetched-instruction prefixes or source-fuel-prefix adequacy. Full logical Source/G24/H11/view/function/early-flow/front-origin compilation, native opcode/charged/scanner/world/ordered-observation/host-writer correspondence, original backfill remainder and final full-lane validation remain open. Frozen H26 interfaces stay unchanged.


### Constructive target shape and caller capacity

`ShapeCapacity.code_total` derives a real scalar execution result and its exact length from the existing intrinsically indexed `LabelExec.CodeShape`, using the published `arity_domain` for each real instruction. It does not assume a run or desired exchange result. `code_frame` constructs one actual output for any intrinsically sized local vector before quantifying over every caller tail, then reuses the existing scalar frame law. Local values may change; only the caller tail is framed. Syntactic operand-height lifting remains separate from value preservation and capacity. No source AST/state, target evaluator or calling convention is introduced or changed.

The exact trace-shift theorem covers entry, all intermediate boundaries and exit. `capacity_shift` characterizes the actual existing 1024-word check at every shifted boundary. `framed_capacity` retains that check as a separate premise and derives the final bound alongside the real result/caller frame; execution success does not supply the capacity premise.

Controls use actual DUP16, PUSH1, ADD, SWAP16, POP over sixteen locals. Static shape constructs execution for every raw sixteen-word input; a separate exact witness updates the last dirty `2^200+257` word to dirty+1 with every other local and arbitrary caller unchanged. The five-instruction trace peaks two words above entry. Caller length1006 is admitted; length1007 still executes in Scalar with entry/final height1023 but reaches an intermediate1025 and is refused by stackBound. DUP16/SWAP16 missing-operand controls remain refusals. These are numeric target/kernel facts, not physical/native EVM validity or a Solidity source simulation.

Validation: focused imports and changed-file MCP/per-file/affected checks, fifteen enforced standard-axiom reports and scoped static gates; separate read-only finder/skeptic reviews found no confirmed findings. Failed automation and the initial implicit-vector-lemma diagnostic are retained without budget changes. Original H26 interfaces, target operations, source/observation/admission semantics and expected verdicts stay unchanged. Full Y08.01/Y08.02/frontend/final artifacts, remaining backfill and final whole-lane validation remain open, including concrete G24/represented producers and native/world/ordered-observation/host-writer closure.

The affected-root check (`gate.sh touched`, including generated `Solidity`) exited1 after the resource guard stopped the unchanged `Frontend/Checked/UnitExamples.lean` check when actual parent-cgroup headroom fell below2GiB. The 12GiB/no-swap limit was unchanged; this is a failed broad import gate with no completed proof-check verdict for that file. The focused new-module checks passed. No owner repair or budget increase was attempted; full import/final validation remains open.


### Actual pure-expression operand certificates

`ExpressionShapes` proves `CodeShape` for successful emissions of the existing literal/local lowering and composes the existing binary lowering. Local accessibility is recovered from its real successful-emission branch and finite local index. The binary theorem retains the actual primitive arity row `(2,1)` and both child emitted-code shape laws; it respects right-before-left evaluation, with the left operand one word deeper. These are explicit metadata premises, not assumed execution results or coverage of arbitrary lowerings/operators. No source syntax, lowered code, builtin semantics or admission is changed.

The concrete witness is original intrinsic Yul `sub(local0,local1)`, with an exact equality for the real producer visitor at fuel2. Its actual emission uses zero-based `.DUP 1` twice (physical DUP2), then SUB. Source evaluation and target execution hold for every raw word pair and arbitrary caller. At depth14, both real reads are physical DUP16 and preserve all fourteen newer words, both old locals and caller; depth15 is actually refused. Allocated offsets are not equated with live stack positions. Dirty `2^200+257` and reversed-operand controls distinguish subtraction order without cleaning.

The exact target trace peaks two words above input. Capacity can hold at height1 while execution still lacks a second operand. Conversely entry1023/final1024 scalar success can coexist with a refused intermediate1025. Static operand sufficiency, actual value/frame correctness and all-prefix capacity stay separate; none is promoted to native EVM or logical Solidity Source/G24 adequacy.

Validation: focused actual import build, changed-file MCP/per-file diagnostics, thirteen enforced standard-axiom reports and scoped static gates; independent read-only finder/skeptic reviews found no confirmed findings. Raw automation and initial elaboration failures are retained; no proof/fuel/node budget changed. The unchanged failed affected-root check from the preceding checkpoint remains failed evidence and is not repeated or relabeled. Full import/final validation, concrete G24/represented producers, general Source/H11/views/functions/early-flow/frontend attachment, native/world/ordered-observation/host-writer correspondence and the remaining original queue stay open. H26 interfaces remain unchanged.


### Recursive arithmetic visitor operand producer

`ArithmeticVisitorShapes.visit_shape` derives the existing `CodeShape` directly from actual `ProducerExpressions.compile` success and actual target emission, for arbitrary fuel, original expression, context/return indices and emitted depth. No child metadata, primitive row or desired run is a public premise. Fuel induction recovers both real successful child visits and discharges the earlier composition helper with concrete ADD/SUB/MUL arity rows. Unsupported forms are eliminated using the actual visitor's `none` results. The private helper states its real metadata premises, which the public theorem closes; it is not substituted for the final concrete producer proof.

This covers the successful domain of the existing arithmetic visitor (literal/local/add/sub/mul), not all forms supported by the wider pure visitor or frontend admission. Emission may still refuse inaccessible local depths. Capacity, actual value/frame semantics and native/logical Source/G24 adequacy are separate. No compiler, source AST/state, target instruction or calling convention is changed.

The nested original witness is `sub(mul(local0,3),add(local1,7))`. Actual visitor success/source completion at its structural horizon3 and exact emitted code are kernel checked; the horizon2 visitor is a refusal control, not a changed budget. Source and target laws hold for every raw word pair and arbitrary caller. At depth13 both local reads are physical DUP16 and preserve thirteen newer words plus locals/caller; depth14 is refused. Dirty `2^200+257` produces `3*2^200+759` for the chosen second input5, with a reversed-operand negative control. The real trace peaks three words above entry: scalar entry1022/final1023 success can coexist with an intermediate1025 capacity refusal. A height1 capacity check also does not cure missing operands.

Validation: focused actual import build, changed-file MCP/per-file diagnostics, eleven enforced standard-axiom reports and scoped static gates; separate read-only finder/skeptic reviews found no confirmed findings. Failed standard automation is retained; no proof/fuel/node budget or existing verdict changed. The unchanged resource-stopped affected-root gate stays failed evidence and is not repeated or relabeled. Full import/final gates, wider visitor metadata, concrete G24/represented producers, general Source/H11/views/functions/early-flow/frontend origin, native/world/ordered-observation/host-writer correspondence and the remaining original lane queue remain open. Frozen H26 interfaces are unchanged.


### Recursive statement visitor operand producer

`StatementVisitorShapes.visit_shape` derives balanced `CodeShape` from actual `ProducerStatements.compile` success and target emission, for arbitrary control/context indices, fuel and depth. No child metadata, target-slot range, primitive row or desired run is a public premise. Sequence children are handled by fuel induction; real arithmetic RHS visits supply expression shapes; the successful assignment-emission branch and finite target index establish SWAP/POP operand existence. The intermediate height after RHS evaluation is explicitly one above the local-frame height. No actual compiler or source/state representation is changed.

The result covers only the current successful skip/singleton-assignment/sequence visitor domain. Balanced height does not mean unchanged local values, arbitrary wider statement/control support, frontend admission, Source/G24 or native execution. All-prefix capacity remains a separate real check.

The original witness writes local0 from the prior nested arithmetic expression, then writes local1 from `local1-local0`, reading the first write's updated value. Actual visitor/source horizon5 and exact emitted code are checked; horizon4 is a refusal control for this new structural nesting, not a changed budget. For all raw inputs a,b the result is `[x,b-x]`, where x=(a*3)-(b+7), preserving the arbitrary caller. The shifted-depth13 case preserves thirteen newer words and uses physical DUP16; depth14 is refused. A wrong parallel-old-read result is explicitly rejected. Entry/final height1022 scalar success still has an intermediate1025 capacity refusal; a height1 capacity check also does not supply missing operands.

Validation: focused actual import build, changed-file MCP/per-file diagnostics, twelve enforced standard-axiom reports and scoped static gates; independent read-only finder/skeptic reviews found no confirmed findings. Failed automation and the initial unresolved-intermediate-height diagnostic are retained; explicit height annotation fixes elaboration without changing contracts or budgets. The earlier resource-stopped affected-root gate stays failed and is not rerun or relabeled. Full import/final checks, wider statement/control/physical visitors, concrete G24/represented producers, Source/H11/functions/early-flow/frontend origin, native/world/ordered-observation/host-writer correspondence and the remaining original lane queue stay open. Frozen H26 interfaces remain unchanged.


### Recursive word visitor operand producer

`WordVisitorShapes.visit_shape` derives `CodeShape` from actual `WordExpressions.compile` success and actual target emission. Fuel induction discharges all recursive child metadata and concrete binary/unary arity rows; neither is a public premise. The successful domain is the existing literal/local/ADD/SUB/MUL/DIV/MOD/LT/GT/EQ/ISZERO/NOT visitor. Wider bit/signed/modular/software-expansion visitors, general frontend admission and logical Source/G24/native adequacy are not covered. No original AST, visitor, word semantics or calling convention is changed.

The original mixed witness is `not(eq(div(local0,local1),mod(local0,local1)))`. Actual visitor/source horizon4 and exact eight-instruction code are checked; horizon3 is a refusal control for this structural nesting, not an increased budget. MOD is evaluated first, then DIV, matching the actual right-before-left lowering. Source and target equations hold for every raw input pair and arbitrary caller. For every dividend with divisorzero, DIV and MOD each returnzero, EQ returnsone and full-word NOT yields2^256-2; no Boolean cleaning or panic is substituted. Inputs3,2 distinguish operand direction, and the dirty/5 case yields the other full-complement value2^256-1.

At depth13 the deepest reads use physical DUP16, preserving thirteen newer words, both old locals and caller; depth14 is refused. The real trace peaks three words above entry. Height1 can pass capacity while still lacking operands; entry1022/final1023 scalar success can coexist with an intermediate1025 capacity refusal. Shape, value/frame semantics and all-prefix resource checks remain independent.

Validation: focused actual import build, changed-file MCP/per-file diagnostics, thirteen enforced standard-axiom reports and scoped static gates; independent read-only finder/skeptic reviews found no confirmed findings. Failed standard automation is retained; no proof/fuel/node budget, expected verdict or producer implementation changed. The earlier resource-stopped affected-root gate remains failed and is not rerun or relabeled. Full import/final gates, wider visitors, concrete G24/represented producers, general Source/H11/views/functions/early-flow/frontend origin, native/world/ordered-observation/host-writer correspondence and the remaining original queue stay open. Frozen H26 interfaces are unchanged.

### Software CLZ shape and capacity

`ClzShapes` certifies the existing software expansion without changing emitted instructions or word semantics. Every19-instruction step has a two-word operand requirement, netzero height and peakfour; scan induction covers each count up to256. The full4867-instruction expansion requires one copied argument, balances the stack and has exact every-boundary capacity `0 ≤ h ∧ h + 5 ≤ 1024`. `expansionCode` constructs the existing intrinsic target packet from separate operand and capacity proofs. `lowering_shape` retains an explicit actual argument-shape premise; this is preparation, not a general source/G24 simulation theorem.

Controls reuse the established exact full-word run theorem for arbitrary input and caller contents. They cover bit200 dirty input yielding55, zero yielding256, first/last scan steps, a concrete two-step scan, input1019 passing capacity and input1020 reaching1025 despite scalar success. Capacity at heightzero is distinguished from the initializer-only first step's missing operand. The CLZ refusal control concerns the Scalar executor, not native Osaka behavior.

Profiling isolated a slow concrete instruction-count proof; proving the same count symbolically before specializing preserves the statement and removes the large conversion. Failed zero-word computation and the initial proof attempts are retained; the general BitVec zero-CLZ theorem supplies that result without increasing limits. Focused import/per-file checks and enforced scoped axiom reports validate only these target certificates. Full lane/import validation, general source/G24/view lowering, functions/control/divergence, native/Bridge/world correspondence, frontend authenticity and final composition remain open. Earlier resource-stopped broad gates and historical script failures are not relabeled passes.

### Full pure-visitor operand producer

`PureVisitorShapes.visit_shape` derives operand metadata from actual `PureExpressions.compile` success and target emission for all26 supported pure constructors. Fuel induction closes recursive child metadata and real primitive arity rows, including modulus/right/left ternary order and the software BYTE/CLZ bodies. `ArityShapes` reuses the existing arity-indexed argument and inline lowerers; these copied operands are not a function-frame convention. The public visitor theorem has no child-shape, primitive-row or chosen-run premise.

`source_target` combines the actual same-horizon closed-Yul evaluator equation, derived operand shape and existing target-run theorem, preserving raw locals, newer prefix and arbitrary caller. It does not replace logical Solidity Source or the G24 state relation. `packet` additionally requires the real all-prefix capacity check at the complete caller height; a nontrivial packet at entry1021/final1022 is inhabited at the last valid ADDMOD boundary.

The original combination `addmod(byte(local0, local1), clz(local0), local2)` has source/target and shape witnesses for arbitrary inputs and twelve newer locals. Depth13 and structural horizon2 are refusals; the pure visitor also refuses non-pure MLOAD. A separate four-opcode ADDMOD witness distinguishes unbounded addition from wrapped addition, and capacity from missing operands or an intermediate1025 height. Review found that the first dirty-index fixture did not distinguish truncation; an added all-ones-data control now yields actual55 versus the truncation counterfactual53, including the actual compiled run for arbitrary callers. The original fixture outcome is unchanged.

Focused import builds, per-file diagnostics, scoped guarded axiom reports and independent read-only reviews validate this producer. General Source/H11/G24/view compilation, functions/control/divergence, frontend provenance/admission, native/Bridge/world correspondence, remaining original backfill and full final validation stay open. No semantics, expected verdict, proof budget or original producer obligation changed; historical failed broad/script gates remain failed evidence.

### Full-pure assignment transport

`PureAssignmentShapes.assignment_shape` derives balanced operand metadata from actual `PureExpressions.assignment` success and emission. The existing statement module exposes its unchanged assignment proof as `lowerAssign_shape`, with the RHS requirement explicit; the new producer discharges it through the full pure visitor. `sequence_shape` composes two actual same-horizon assignment visits with the existing normal sequence builder. It does not extend the general statement visitor. `source_target` retains the original closed-Yul evaluator and exact update/run equations, while `packet` separately requires capacity at the complete caller height.

The concrete sequence writes `or(local0, addmod(byte(local0, local1), clz(local0), local2))` into slot2, then reads the updated slot2 into slot1. Source and target equations hold for arbitrary raw inputs, twelve newer locals and caller contents. At zero modulus, the actual whole sequence maps `[dirty, dirty, 0]` to `[dirty, dirty, dirty]`, distinguishing a completed write from a stale-slot read. The new structural horizons follow this expression/statement nesting; no existing budget or expected outcome changed.

A separate dirty-literal assignment reaches physical SWAP16 under thirteen newer words and refuses the next depth. Its balanced packet at entry1023 reaches1024 transiently; scalar success at entry1024 can still fail capacity by reaching1025. Missing-operand, shorter-horizon and inaccessible-slot controls remain distinct. Focused new and affected statement regression builds, per-file diagnostics, guarded axiom reports and independent read-only reviews validate these components. General logical Source/H11/G24/view compilation, function/control/divergence, frontend authenticity, native/Bridge/world correspondence and full lane validation remain open; historical broad/script failures are preserved.

### Scoped visitor operand producer

`ScopedVisitorShapes.visit_shape` derives balanced operand shapes from actual `ScopedStatements.compile` success and emission for its existing skip, sequence, full-pure assignment, singleton-let and zero-binding domain. Structural PUSH/POP proofs supply real prefix entry and retirement; fuel induction discharges initializer/body/child metadata. The statement module exports its unchanged sequence proof as `lowerSeq_shape` for reuse. Scope lowering still selects only depthzero, and this restriction is not Solidity admission. `source_target` retains the same-horizon original closed-Yul update and scalar run; `packet` separately requires capacity at the complete caller height.

A nested singleton-let/two-zero-local witness saves an old value, computes through initialized scratch locals, mutates two outer locals and removes all three fresh words while preserving arbitrary caller contents. Its dirty/zero case preserves every high bit. Direct normalization initially hit the unchanged heartbeat limit; proved equations for the actual compiled children now compose to the same exact outer update and source/run postconditions. No desired update is assumed and no budget was raised.

Seventeen fresh zero locals with a skip body emit successfully, with capacity boundaries1007/1008 and an inhabited balanced packet at entry1007. A separate intrinsically valid slot16 write has a genuine source result but no target emission, distinguishing frame size from instruction accessibility. Depthone, shorter-horizon, underflow and unsupported-if controls retain actual refusal behavior. Focused new/affected regression builds, per-file diagnostics, guarded axiom reports and independent read-only reviews validate these components. General logical Source/H11/G24/view/function/control/divergence, frontend provenance, native/Bridge/world composition and full lane validation remain unfinished; historical broad/script failures are preserved.

### General numeric compiler-machine execution

`NumericExecution.step` and `run` prove success transport for the unchanged `NumericMachine` selector: ADD/SUB/MUL/DIV/MOD/AND/OR/XOR/SHL/SHR plus its existing stack operations. Operands and intermediate scalar stacks are derived from actual scalar success; concrete dispatch/model laws are proved, with existing stack and ADD/MUL results reused. Arbitrary symbolic caller words and every nonstack compiler-machine field remain unchanged. This is one-way success transport, not a generic reflection of scalar failure.

`loweredExpr_machine` and `loweredStmt_machine` discharge the scalar-run premise with real compiler correctness. The original pure-expression and scoped-statement endpoints additionally retain actual visit/emission/selection facts and same-horizon closed-Yul equations. The selector and its refusal domain are not widened. PUSH width is erased by the model adapter; the zero outcome index means no pending jump, not a gas result. Native bytes/PC, gas,1024-capacity and logical Solidity Source/G24/world correspondence remain separate.

A genuine original expression uses all ten operators and selects an exact21-instruction model program. Universal raw-input and shifted-seven-local results preserve arbitrary symbolic callers; the concrete5,2→6 and zero-divisor/high-bit cases check operand direction and raw-word behavior. The nested scoped producer also executes in the compiler machine with its proved exact update. A large-prefix model success coexists with failed actual capacity. Closed-frame underflow controls, depth/fuel refusals and unchanged EXP/SSTORE/native-CLZ selection refusals remain explicit. Scoped builds, per-file diagnostics, guarded axiom reports and independent read-only reviews validate this component; full original compilation/Bridge/frontend/final obligations and historical failed gates remain open.
