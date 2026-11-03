# Inline assembly VY3: Yul compilation combinators

`Yul/Compilation/**`, from the vy3-compilation lane. Target-side combinators
over the existing backend stack model (`Backend/Scalar/Heights`,
`Backend/Control`, `Backend/Passes/Stack`); no Yul AST or VY1 semantics is
consumed, so this is not yet the P20 state relation.

- Stack slots and scopes (`Allocation`, `Slices`, `SlotSemantics`,
  `ScopeSemantics`, `NestedWrites`): slot allocation, arity slices, DUP/SWAP
  writes, push/pop of prefixes; general over locals, newer values and tails.
- Expression and statement lowering (`PureLowering`, `ArgumentLowering`,
  `ResultAssignment`, `ResultFrame`, `LocalScopeLowering`): `LoweredExpr n
  value` is indexed by an arbitrary Lean function; the relation is the stack
  layout `newer ++ locals ++ tail`.
- Opcode lowering (`OpcodeLowering`, `ClzLowering`, `ClzBounds`,
  `ByteLowering`): selection and CLZ/BYTE expansions with bounds.
- Control (`ControlLowering`, `MachineControl`, `Relocation`): branch and loop
  `Block` emission and relocation; `lowerBranch_slices` gives the runs of the
  parts, not of the whole block, and `lowerWhile` has no execution theorem.
- `MachineAdapter`: transport to `Evm.Machine` for stack-only code
  (`stackCode` covers PUSH/DUP/SWAP/POP only). `NumericMachine`,
  `WordMachine`, `SignedMachine`, `WordControl` are selectors without run
  theorems. `MemoryHarness`, `PhysicalCombination`: a byte-materialization
  harness and an unproved storage/transient suffix.
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

Before this checkpoint, the clean branch was preserved at recovery ref
`recovery/vy3-before-trust-inventory-15ada9ff` and rebased onto published master
16d713bb. The only resulting upstream content changes were the existing IDE trust
inventory and its assurance documentation. Prior source/evidence/checkpoints are
preserved. The updated tracked-tree trust audit passes under that published
inventory; historical raw failures are not rewritten or evidence that the sites
were removed. New modules have no scoped trust findings.

Focused build/per-file diagnostics, scoped signatures/axioms and layer checks
pass, with independent actual-file finder/skeptic reviews finding no defects.
Core registrations are generated. TERRA31 and earlier TERRA1–30 remain pending.
General source/G24/view/writeback/MemOK, functions/control/divergence, frontend,
native/Bridge/Osaka/world/trace and final joint closure remain unfinished. No
source AST/state, opcode meaning, selector, admission, observations, budget or
external solc/EVM fixture is changed by this implementation.


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

The saved head5ee991c9 was preserved at recovery/vy3-before-sched-5ee991c9 before
rebasing onto published70f3f358. One docs/README.md append conflict was resolved
by retaining both published G18 links and the lane table. Existing Yul compilation
sources did not change in the rebase. Newly read V12 NativeParents.clause and
RecursiveResult.success/shallow_refused give concrete countdown/hand-written
runtime clients, not a general Yul function compiler or blanket runtime producer.
They do not discharge the original function/control/divergence obligations.

Focused builds/per-file diagnostics, scoped signatures/trust/layers and
independent actual-file finder/skeptic source/documentation reviews pass. Core
registrations are generated. Raw failed direct-conversion diagnostics are kept.
TERRA32 and earlier TERRA1–31 remain pending. General Source/G24/view/writeback/
MemOK, functions/control/divergence, frontend, native/Bridge/Osaka/world/trace and
final joint closure remain unfinished. No AST/state, signed semantics, selector,
admission, observations, budget or external solc/EVM fixture is changed.


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

Published integration 4b304a7c already carries the earlier 41 Core and 13 Bridge
modules. The branch now builds on that real tree and carries only the two later
EXP/signed-comparison checkpoints plus new work. The saved full lane head remains
in recovery/vy3-before-yul-integration-034fac0e and older sealed bundles. Condensed
published docs and generated registrations were retained; the local TERRA ledger
is preserved. Previously omitted test/scripts/docs remain in the saved commit
and immutable original artifacts, not silently republished as new integration.
The 13 Bridge modules are registered by the coordinator; private ChargedEntry
modules remain separately deferred optional registrations (REG1 resolved by
deferral). Published parsing compositions now
live in Frontend/Yul; this Core consumer imports no parsing shim.

Focused builds (including the two carried checkpoints), per-file diagnostics,
scoped signatures/trust/layers and independent actual-file finder/skeptic reviews
pass. Failed initial Fin-image rewrite diagnostics are retained. TERRA33 and
TERRA1–32 remain pending. General source/G24/view/writeback/MemOK, functions,
control/divergence, frontend, native/Bridge/Osaka/world/trace and final joint
closure remain unfinished. No admission, observation, word meaning, AST/state,
budget or external solc/EVM fixture changes follow from this checkpoint.


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
preceding DUP prefix is reached or executed. TERRA34/35 record the exact gas9
prefix reserve and continuation glue, without applying the stronger old gas11
contract. Valid-jump scanning, suffix correctness, general source/G24 and full
Osaka/world/resource/trace closure remain separate.

Controls populate memory/returndata/return buffers, active words and caller data;
exercise both static flags, dirty high bits and all three results; distinguish
four prelude bytes from two instructions; and test gas/fuel/underflow/overflow.
The shrinking-opcode gate can accept an oversized prepared input that the DUP
prefix cannot reach. A finite DUP/ADD suffix regression is included without a
universal suffix claim. These Lean/reference controls are not new solc or client-
EVM pipeline evidence.

The branch rebased its three post-integration checkpoints onto published 312ed47a,
with recovery/vy3-before-review-fixes-d5120f6f preserving the prior head. Focused
Bridge imports/builds, per-file diagnostics, scoped signatures/axioms/trust and
independent actual-file finder/skeptic reviews pass. Optional Bridge-root
registration is deferred to the coordinator's generated integration; Core is
unchanged. TERRA1–35 and full original lane obligations remain unfinished.


### Charged raw ISZERO slice

ChargedIszero derives both fetched DUP1/ISZERO steps and the complete native X
continuation for UnaryMachine.iszeroCompiled.value, arbitrary raw operand and
caller tail. Premises: caller.length ≤ 1022, initial gas ≥ 6, encoded prelude
length + 2 < UInt256.size. The actual P10 DUP and raw ISZERO producers discharge
execution; zero_input derives the intermediate code/PC/stack identity. No
intermediate success or desired result is assumed. Full state equality retains
the original dirty operand and caller tail. TERRA36 leaves only counted-step
joining as routine glue; TERRA1–35 remain pending.

Controls cover zero, one, dirty 2^200+257 and high-only 2^200, static flags,
populated buffers, a four-byte/two-instruction prelude, exact capacity/overflow,
gas, fuel, underflow and a finite DUP/ADD suffix. Focused kernel build and
independent finder/skeptic reviews pass; the initial invalid PUSH fixture exit
is retained separately. These are Lean/reference checks, not new external
solc/client-EVM evidence. Optional Bridge root registration is deferred to the
coordinator generator. General Source/G24/view/frontend, scanner, function/loop
and whole Osaka/world/resource/trace composition remain unfinished.


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
a finite DUP/ADD suffix. TERRA37 records counted joining only; TERRA1–36 remain
pending. Standard automation fails on the execution goal; actual producer
composition succeeds. Scratch indentation/name-scope failures are retained.
Independent read-only finder/skeptic reviews found no confirmed issues.

This is a native compiler slice, not a general Source/G24/view/frontend,
function/loop/divergence, scanner, whole Osaka/world/resource/trace theorem.
No new external solc/client-EVM evidence or full-lane gate pass is claimed.
New optional Bridge registrations are deferred to the coordinator generator.


### Charged logical shift compiler slices

ChargedShifts derives original intrinsic SHL/SHR expression evaluation and native
DUP2/DUP2/shift X continuations to the SAME ShiftSubMachine compiled value.
Premises are encoded prelude length + 3 < UInt256.size, caller.length ≤ 1020
and initial gas ≥ 11. This sufficient gas bound comes from the unchanged
QuotientPlacement.reads theorem; the actual shift charges THREE gas, not five.
Intermediate stack/code/PC identity, gas reserve, prefix and last-step execution
are derived. Count is topmost, then value; the original raw operands, arbitrary
caller and unchanged native State fields are retained. TERRA38 records counted
driver joining, with TERRA1–37 still pending; the full X chain is already proved.

Controls include dirty value/count, zero, 255/256/257, modular left wrap, both
static flags and populated buffers, a four-byte/two-instruction prelude, exact
capacity/overflow, gas/fuel/underflow and finite DUP/ADD suffix. A finite gas9
success does not turn the general sufficient gas11 theorem into a minimum-gas
result. No new external solc or client-EVM evidence is claimed.

Standard tactic attempts fail; concrete producer composition succeeds. The
initial scratch namespace failure is retained. Focused checks and independent
read-only finder/skeptic reviews pass. Optional Bridge root registration remains
coordinator-generated. General Source/G24/views/frontend/function/loop/divergence,
scanner and whole Osaka/world/resource/trace adequacy remain unfinished.


### Charged arithmetic shift compiler slice

ChargedArithmeticShift instantiates the existing intrinsic Expr and actual
PureExpressions compiler with SAR; no new AST, signed semantics or core-machine
selector is introduced. sar_continuation proves source evalExpr2 and complete
native DUP2/DUP2/SAR X execution to the SAME compiler value. It derives prefix
execution, intermediate code/PC/stack identity and remaining gas using concrete
QuotientPlacement/P10 producers, with no desired run assumption. Premises:
encoded prelude bytes + 3 < UInt256.size, caller.length ≤ 1020, initial gas ≥ 11.
The old sufficient prefix gas contract is unchanged; SAR itself costs three.
Raw count/value words, original operands, caller and unchanged State fields
are preserved. TERRA39 leaves counted joining routine; TERRA1–38 remain pending.

Controls cover negative odd floor rounding, minimum signed value, 255/256/257
and dirty enormous counts, positive/negative saturation, zero, unchanged dirty
words, static flags/populated buffers, four-byte prelude, stack/gas/fuel/underflow
refusals and finite suffix. A finite gas9 success is not a universal minimum-gas
claim. Focused kernel/MCP/scoped trust checks and independent finder/skeptic
reviews pass. No external solc/client-EVM evidence is added. Optional Bridge
registration remains coordinator-generated. Full Source/G24/view/frontend,
functions/loops/divergence, scanner and whole Osaka/world/resource/trace closure
remain unfinished.


### Charged arity-three modular compiler slices

ChargedModular instantiates the existing intrinsic arity-three Expr and actual
PureExpressions compiler for ADDMOD/MULMOD. read_prefix derives all three charged
DUP3 steps, exact intermediate states, full prefix X continuation and remaining
at least eight gas. The subsequent concrete P10 modular producers give original source
evalExpr2 and complete four-instruction native X continuations to the SAME
compiler values. No intermediate success/result or blanket compiler law is
assumed. Explicit premises: prelude encoded bytes + 4 < UInt256.size, arbitrary
caller.length ≤ 1018, initial gas ≥ 17. Capacity includes six live stack words
at the prefix peak. Original raw a/b/modulus and caller/unchanged fields survive.

Controls distinguish unbounded intermediate addition/multiplication from
wrapping before modulus, modulus zero/order, dirty values/modulus, static flags
and populated buffers. They check each prefix state, four-byte prelude, local
DUP accessibility, exact capacity/overflow, gas/fuel/underflow and finite suffix.
TERRA40 leaves counted-four-step joining routine; TERRA1–39 remain pending.
Initial declaration-keyword failure and consequent scratch failure are retained;
corrected focused checks and independent read-only finder/skeptic reviews pass.
No new external solc/client-EVM evidence or full original lane gate is claimed.
General Source/G24/views/frontend/functions/loops/divergence, scanner and whole
Osaka/world/resource/trace composition remain unfinished. New optional Bridge
root registrations remain coordinator-generated.


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

Controls cover zero power/zero exponent, unequal swapped operands, dirty/MAX
bases, modular overflow, byte-cost boundaries, exact gas failures, stack/fuel/
underflow, both static flags/populated buffers and a finite suffix. Huge raw
exponents are checked for byte cost only; no gigantic host power is evaluated.
TERRA41 leaves counted joining routine, with TERRA1–40 pending. The initial
concrete decide witness could not reduce Nat.log; the existing log_of_lt lemma
fixes it without budget or verdict changes. Raw failures are retained.
Independent read-only finder/skeptic reviews and focused checks pass. No new
external solc/client-EVM evidence or full original lane gate is claimed. Full
Source/G24/views/frontend/functions/loops/divergence/scanner/world/trace closure
remains unfinished; optional Bridge registration is coordinator-generated.


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
TERRA42 hands off routine source-slice FrameCertificate packaging to the
coordinator's Terra queue, retaining its explicit whole-stack prefix bounds.
TERRA1–41 and full original lane obligations remain pending.

Initial scratch failures (unavailable helper name, map simplifier order, and
missing next-constructor unfolding) are retained. Corrected focused checks and
independent read-only finder/skeptic reviews pass, with no confirmed findings.
No external solc/client-EVM evidence or full-lane gate pass is added. Optional
Bridge-root registration remains coordinator-generated.


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
success with failed physical stackBound. TERRA43 records routine iff projections
and an optional capacity wrapper with its real premise; TERRA1–42 remain pending.

Initial attempts to eliminate a membership Or proof into certificate data failed;
matching on the existing instruction constructors solves that representation
issue constructively, without an axiom or changed interface. Raw failed exits
are retained. Focused checks and independent read-only finder/skeptic reviews
pass. No external solc/client-EVM evidence or full-lane gate pass is added. Full
source/G24/views/frontend/functions/loops/divergence/scanner/Osaka/world/resource/
trace/import composition remains unfinished. Optional Bridge registration is
coordinator-generated.


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

TERRA44 records routine finite-selection/code projections. TERRA1–43, general
Source/G24/views/frontend/functions/loops/divergence, native/scanner/Osaka/world/
resource/trace/final import composition remain pending. Focused checks and
independent read-only finder/skeptic reviews pass, with no confirmed findings.
No new external solc/client-EVM evidence or full-lane gate pass is added; new
optional Bridge registrations remain coordinator-generated.


### Local writes through actual SWAP/POP selection

WriteSelection supplies real published InstructionCertificate bodies for all
SWAP indices n : Fin 16 and POP. Both success/refusal directions derive actual
operand existence: exchange_set follows from the list bound, and the real
out-of-range law supplies failure. Exact mapped list updates and full machine
fields are preserved; no desired exchange/run result is assumed. A new local
certificate selector adds SWAP1–16 and POP without changing earlier selectors
or admission; SWAP0/17 remain unencoded by the actual Fin16 backend family.

statement_model combines a real ProducerStatements.Compiled certificate, its
EXACT emitted-code identity, and real per-instruction certificates to derive
original Yul evalStmt and model execution on the same numeric locals/caller.
Concrete assignment_model and sequence_model discharge the emission premises
for the original intrinsic statements x := y and x := y; y := x + y using the
actual PureStatements compiler. These are source/model word-level results, not
general Solidity source embedding, G24, physical views or native execution.
Contexts F/X are empty and caller words use the interface's numeric irStack.

Controls check updated-local reads, dirty/MAX wrap, first/last SWAP, POP and
underflow, exact source/compiler code, full machine metadata/caller retention
and physical stackBound versus uncapped model success. The source horizons are
the same actual compiler/evaluator horizons (two and four), with insufficient
horizon refusal retained. TERRA45 records routine code projections only;
TERRA1–44 and full original lane obligations remain pending.

The initial source namespace qualification and scratch record-layout failures
are retained. AST names are Solidity.Yul.Stmt/Control; the evaluator namespace
is Solidity.Yul.Closed. Checked module/signature files are authoritative; prior
sealed artifacts remain unchanged. Focused checks and independent read-only
finder/skeptic reviews pass. No external solc/client-EVM evidence or full-lane
gate pass is added. Optional Bridge registration remains coordinator-generated.


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
reads, fresh-prefix retirement, full metadata/caller retention, missing operands,
source-horizon/depth refusals, actual 33-byte PUSH32 and 42/76-byte program sizes,
and physical stackBound versus uncapped model success. TERRA46 records routine
code projections; TERRA1–45 and full original lane obligations remain pending.
Focused checks and independent read-only finder/skeptic reviews pass with no
confirmed findings. No external solc/client-EVM evidence or full-lane gate pass
is added. Optional Bridge registration remains coordinator-generated.


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
source evaluation; TERRA47 leaves only their routine pairing wrapper. TERRA1–46
and full original lane obligations remain pending.

StructuredExec is a stack-success relation, not a generic Evm.Machine/LabelExec/
Bridge/native run theorem. Finite model regressions are labeled separately;
oversized model success supplies no physical capacity. Shape, ExpansionRoom,
ControlCertificate realization, loops/divergence, general Source/G24/views/
frontend/Osaka/world/resource/trace/final import composition remain open. Focused
checks and independent read-only finder/skeptic reviews pass with no confirmed
findings. No new external solc/client-EVM evidence or full-lane gate pass is
added; optional Bridge registration remains coordinator-generated.
