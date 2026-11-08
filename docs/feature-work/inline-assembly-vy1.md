# Inline assembly VY1: Yul syntax, checking and word semantics

The `Solidity/Yul/**` library (root `Yul.lean`) and its JSON ingress
`Frontend/SolcJson/Yul*.lean`.

## Proved

- Words and builtins (`Words`, `WordLaws`, `Builtins`, `CatalogLaws`): word
  operations on `Fin (2 ^ 256)` with zero-divisor and large-shift conventions;
  builtin arities and tiers (`TierPolicy`, `BuiltinUse`, `WordPolicy`).
- Syntax and static checks (`Syntax`, `StatementTags`, `Static`,
  `ExpressionCheck`, `LocalScope`, `FunctionScope`, `Declaration*`,
  `PlacementCheck`, `AssignmentCheck`, `ReservedNames`): an intrinsic AST and
  primitive checkers; `ExpressionCheck.inferExpr_iff` holds for every
  environment and expression.
- Typing and extraction (`BlockTyping`, `ScopedBlockTyping`, `BlockExtract*`,
  `ClosedSyntax`, `Typing*`).
- Closed fuelled execution (`ClosedFunctions`, `ClosedPure`, `ClosedRun`,
  `ClosedHorizon`, `HorizonAdapter`) and a direct tier-A runner
  (`Open*`; `OpenComposition.run_agrees` for all code, policy and state).
- A Lean-only word logic (`WordUpdates`, `WordLogic`, `WordRules`,
  `WordNotation`, `WordAgreement`, `WordCoverage`, `Word{Terms,Branches,Switch,
  Loops,Arguments,Expressions}`) and a raw-cell runner (`WordCells`,
  `WordLocals`, `WordInputs`, `WordAdapter*`). The logic is shallow: `atom`
  takes a Lean predicate, so `rule_sound` in this existence form is weak; the
  concrete rule premise comes from `rule_exists`. Its 20 rules are marked as Lean-only extensions in the
  [rule map](../lean-key-rule-map.md).
- Source local bridge and statement adapters (`Source*`, `Local*`, `Clean*`,
  `Raw*`): a concrete bool-control slice; `RawSourceAdapter.Adapter.correct`
  is an obligation the caller supplies, and `SourceBoundary` proves only
  impossibility results. This is not a general P16 Source embedding.
- `Checks/**`: kernel controls, including integer-oracle vectors
  (`Checks/Arithmetic`, `Checks/Shifts`; finite tests, not universal opcode
  agreement). `WordPrint` holds the printers; the restored printing tests import it, while core does not.

## Open

General Source embedding (P16), agreement for remaining target operations,
a deep word logic, and separating checked-parser adapters from core.
Concrete context-changing raw producers, return/frame transport and final
physical/compiler/world composition also remain open.

## Follow-up implementation

The approved [assembly decisions](../solidity-scope.md#inline-assembly-decisions-2026-10-31)
remain the semantic contract; none of these changes promotes admission status.

- RawSourceForPost proves same-context Boolean-post Source iteration and
  initialized-loop agreement from concrete producers and raw coherence.
  Absent.source_true and source_initialized preserve every identical horizon
  for arbitrary typed optional posts and context-changing syntax. The raw
  adapter reuses an existing literal-true producer; general evaluator equality
  does not establish arbitrary raw producer support.
- WordAdapter.rule_premise_sound and OpenRun.rule_premise_sound require the
  concrete Logic.Rule for the exact displayed premise. The shallow Lean-function
  atom/substitution deviation remains; the older existential rule_sound result
  alone is not evidence for a specific premise.
- Builtin.checkTier replaces the former admit-named checker without changing
  any refusal. Its 16 false-positive recovery inventory rows are removed.
- Checks use exact message guards for the 16 evaluation blocks and carry no
  Elab.async overrides. Existing predicates, values and success messages remain.
- The tests, JSON fixtures, pinned compiler harnesses and the integer-vector
  generator script are not on master; the generated `Yul/Checks/**` vectors
  are. They remain finite kernel controls, not universal EVM agreement. Six
  routine laws remain open.

The full source boundary and pure calculus assignment remains unfinished.

## Signed target-word agreement

Yul.Word reuses Roadmap.Word without changing its Fin word representation.
Yul/EvmSigned.lean proves universal Pure.eval agreement for SDIV, SMOD, SLT
and SGT with the existing target machine. Each Instr.step theorem preserves
the complete machine except its specified stack update, with an arbitrary
remaining stack. Division/modulo by zero return zero; signed-minimum division
overflow wraps. The integer conversion helper states its necessary lower
bound, discharged from operand-range lemmas in the public operation laws.

Yul/Checks/EvmSigned.lean includes a nested intrinsic expression, two concrete
machine steps preserving a slot sentinel and dirty word, signed/zero boundary
cases, malformed operand controls and a counterexample below the helper bound.
The source expression distinguishes exhaustion from completion at adjacent
horizons. These are kernel proofs and controls against the repository machine;
they establish no compiler lowering or external EVM agreement. Other word
operations and the general Source/dirty boundary remain separate obligations.

## Parser import boundary

The source parser adapters now live under Solidity/Frontend/Yul. The intrinsic
ClosedSyntax, WordSyntax, OccurrenceSyntax and ScopedSyntax preparation modules
retain their certificates and checker laws, including the structural precedence
premise. Parsed certificates and parsing composition keep their declaration names
but require an explicit frontend import. Dedicated old parser entry points remain
compatibility imports. Existing lexer and structural-predicate definitions are
reused; no lexer or parser is duplicated.

The layer gate checks transitive core reachability to the full checked parser and
frontend Yul adapters independently of elaborator reachability. Parser controls
move with the adapters, while pure preparation controls remain in the core.
This separation establishes no new admission or general Source adequacy claim.
Read-only finder review caught a missing explicit parser import in TypingSites;
that consumer and its dependent parser tests were corrected. Skeptic review found
no semantic changes on inspection.

## Unsigned target-word agreement

Yul/EvmArithmetic.lean proves universal actual Instr.step agreement for ADD,
SUB, MUL, DIV and MOD, preserving every other machine field and an arbitrary
stack tail. SUB discharges its natural-subtraction bound from the intrinsic
operand; DIV and MOD cover zero and discharge their result bounds. No additional
premises restrict words or machines.

mulDiv_agrees composes actual MUL and DIV steps for arbitrary operands, including
a zero divisor. Multiplication wraps before division. This is not a full-precision
mulDiv contract. Checks/EvmArithmetic includes an inhabited nested intrinsic AST,
adjacent fuel horizons, wraparound, zero divisors, a raw 257 word, malformed
stacks, asymmetric operands and a machine with nondefault memory and sentinel
tail. A concrete unbounded-product control distinguishes the two meanings.

Automation was tried before final proofs. Independent proof and control finder
and skeptic reviews reported no findings. These are kernel proofs about the
repository target machine, not compiler lowering or external EVM validation.
General Source embedding, other word-operation agreements and final gates
remain open; no Source definitions or peer modules change.

## Comparisons, bits, shifts and powers

Yul/EvmBitwise.lean proves universal target-step agreement for AND, OR, XOR,
NOT, LT, GT, EQ, ISZERO, SHL, SHR and EXP. Each law quantifies arbitrary word
operands, machine and stack tail, with no additional premises, and preserves all
other machine fields. Bitwise bounds and right-shift quotient bounds follow from
intrinsic word ranges. Shift amounts of 256 or larger return zero; smaller shifts
use the exact multiplication/division identities. EXP uses powWord_correct for
arbitrary word exponents without an artificial exponent or execution cutoff.

Checks/EvmBitwise contains 22 exact boundary vectors and an inhabited nested
SHL/SHR/AND expression with adjacent fuel horizons. Its concrete four-step machine
trace includes PUSH and preserves a nondefault machine and sentinel tail.
Negative controls reject malformed operands/stacks and distinguish reversed SHL
operands and logical SHR from signed SAR. Kernel evaluation closes the latter
without raising the recursion limit that an ordinary decide attempt reached.

Independent proof and controls finder/skeptic reviews reported no findings.
The proofs establish operation-level agreement with the repository machine.
They do not establish compiler lowering, external EVM adequacy or general Source
embedding. The existing target has no corresponding Instr constructors for CLZ,
BYTE, SAR, SIGNEXTEND, ADDMOD or MULMOD; those pure operations retain their
existing Yul meanings and controls, without a target agreement claim here.
Final joint import/composition and full gates remain open.

## Void return beside raw locals

Yul/RawSourceVoidReturn.lean supplies concrete runners and universal Source
execS/execItems soundness for a void return, a return followed by an arbitrary
typed tail, and an enclosing block. The resolved statement's return list is
explicitly empty. Each theorem conjoins exact full raw-frame identity with the
existing Source execution equation, at every fuel and arbitrary globals, frame,
control context, placeholder and input raw state. No coherence premise is used.

The Source outcome is an explicit projection through the stored clean locals;
the authoritative raw overlay remains separate and unchanged. Void return reads
no local value. This supplies no dirty-read equivalence or cleanup policy.
The arbitrary tail may have a different output context but is not executed.
It therefore proves short-circuit composition, not declaration execution or a
general context-changing adapter. Return thresholds are one statement horizon,
two item horizons and three enclosing-block horizons.

Checks/RawSourceVoidReturn inhabits an actual Source block with a skipped local
declaration. An incoherent mixed local frame retains raw bool 2 and narrow word
257 across timeout and successful return. A concrete Source theorem instance
uses that exact tail. The nonvoid negative refutes only the empty-return-list
equality index; it is not frontend refusal evidence.

Independent proof and controls finder/skeptic reviews reported no findings.
No Source.Val/Eval/Machine definition changed. Valued returns, general control
transport and Source embedding remain open. This is not Yul leave/RETURN builtin
semantics, compiler adequacy or an expanded frontend admission claim.

## Return through control wrappers

Yul/RawSourceReturnControl.lean proves concrete Source execution equations for
do/while with an immediate void-return body, return from an unchecked region,
and literal-guard while with that body. Positive laws conjoin exact whole
raw-frame retention with the explicit stored-clean Source projection at every
fuel, without coherence or caller-provided execution laws. True literal while
returns and false literal while completes normally, both from horizon two.
Do/while returns from horizon two; the nested unchecked return requires three.

The do/while condition and both unchecked tails are arbitrary typed terms but
are skipped. Context-changing tails do not imply context-changing execution.
The existing Source evaluator rejects a return used as a for initializer with
its exact stuck result; the negative theorem preserves this resolved-model
behavior and makes no frontend admission claim.

Checks/RawSourceReturnControl inhabits actual do/while and unchecked terms over
an incoherent raw frame. Its condition assigns false to a clean flag: independent
Source evaluation proves a real 1-to-0 change if evaluated. Return skips that
effect and preserves raw bool 2, narrow word 257, all other locals and world.
Controls distinguish timeout, return and explicit false-while normal flow.
Independent proof and controls finder/skeptic reviews reported no findings.

This adds no ordinary dirty-read policy, valued returns, arbitrary returning
loop adapter, Yul RETURN semantics, compiler theorem or frontend admission.
Existing Source definitions remain unchanged; general P16 and final gates
remain open.

## Executed Boolean declaration

Yul/RawLocalDeclaration.lean adds a snapshot indexed by the actual Source
environment and type context. It stores clean Source locals beside the existing
context-computed LocalValues product and unchanged world. Snapshot.ofFrame uses
RawFrame.materialize; its word-view agreement is the existing
RawFrame.materialize_view law. Names are not added to the new context index.
Outcome observers use casesOn over a parameter-only result family.

The concrete run executes Source declVar(bool). At horizons zero and one, timeout
retains the entire input snapshot. Success from horizon two has context
bool::types, prepends clean false to both representations, preserves the entire
older raw-values product and leaves the world unchanged. The universal correct
theorem conjoins this exact invariant with actual Source.execS equality through
the explicit clean projection. It assumes neither coherence nor a child law.

Checks/RawLocalDeclaration inhabits an executed context-growing declaration.
The new head is false; shifted old Source indices still read raw bool 2 and
narrow word 257. Exact outcome, old-prefix/world and clean?-projection controls
retain the mixed raw state. Independent proof/G0 and controls finder/skeptic
reviews reported no semantic findings. Diagnostics caught a reserved control
theorem name; it was renamed without changing its statement or proof.

Existing Source/RawFrame representations are unchanged. This is one Boolean
declaration producer, not arbitrary declarations, partial-context sequencing,
scope restoration, frontend-name reconstruction or a dirty-read policy.
General P16 and final joint/full gates remain open.

## Closing an executed Boolean scope

Yul/RawLocalScope.lean invokes the concrete declaration producer and drops only
its temporary Boolean head. Exact Source restore_cons handles the dependent
suffix cast for any typed head value. The all-fuel correct theorem proves whole
enclosing-snapshot identity and actual Source execution of the declaration
block: horizons zero through three time out; success starts at four.

frame_correct additionally relates the computed snapshot to Snapshot.ofFrame
of the returned original frame, alongside actual Source execution equality.
The concrete adapter implements the existing RawSourceAdapter.Adapter interface.
That interface retains its coherence premise; the underlying frame theorem
needs none for this read-free program. No child execution law is assumed.

Checks/RawLocalScope verifies exact low-horizon timeout tags, successful actual
adapter execution, raw 2/257 retention and a two-scope combination through the
existing cons/block factories. The combination times out at six and succeeds
at seven with the entire dirty frame unchanged. Its formal combined Source law
uses a concretely clean/coherent frame; dirty runtime controls do not imply a
general dirty-composition theorem.

Independent proof/G0 and controls finder/skeptic reviews found no correctness
issue. The finder requested stronger low-horizon tag controls; exact timeout
and full-input-state equations at zero, one and two were added and reviewed.
This closes one temporary Boolean declaration without intervening reads, not
arbitrary context-changing sequencing, general restoration into named contexts,
dirty reads, valued-return integration, frontend admission or compiler adequacy.
General P16 and final full gates remain open.

## Constant-default declarations

Yul/RawDefaultDeclaration.lean extends context-growing declarations without
changing the Boolean producer or Source types. Default carries a typed Source
value and the exact Val.default lookup equation. The generic correct theorem
uses that real premise in Source.zeroVal/execS and conjoins exact new-head,
old-raw-prefix, world and failure-state preservation. Result is parameter-only;
observers use casesOn and locals reuse the existing computed product.

int_default and intDefault discharge the lookup for every Source IntTy.
The concrete int_correct theorem therefore has no caller default premise.
Checks/RawDefaultDeclaration inhabits a uint8 declaration and instantiates the
Source law for uint8 and uint256, including precise timeout/success contexts,
zero-valued heads and shifted old raw 2/257 values.

The lookup control for memory bytes returns no constant-default certificate.
This is not refusal of Source allocation or a reopened/closed feature row.
Only constant-default declarations are implemented here. No coherence or child
execution law is assumed; Source equality uses the explicit stored-clean
projection beside retained authoritative raw values. Independent proof/G0 and
controls finder/skeptic reviews reported no findings.

Reference allocation, arbitrary initialization, scope/sequence integration for
these declarations, dirty reads, frontend-name construction, compiler adequacy
and final full gates remain separate obligations.

## Closing constant-default scopes

Yul/RawDefaultScope.lean composes the actual certified declaration runner with
one-head scope closure. Generic correct retains the exact default certificate;
int_correct discharges it for every IntTy. Theorems prove whole enclosing
snapshot restoration and actual Source block execution at every fuel. Frame
correspondence also equates the returned frame view with the computed snapshot.
The existing adapter and integer factory use these concrete bodies and proofs.

Checks/RawDefaultScope inhabits uint8 and uint256 scope adapters. Exact equations
identify timeout with unchanged input at zero through three and normal closure
at four. A heterogeneous two-scope combination through existing cons/block
factories times out at six and succeeds at seven with the full dirty frame and
raw 2/257 retained. Its formal mixed Source law uses a concretely clean/coherent
frame; it is not a generic dirty-composition theorem. The single-scope Source
frame law itself needs no coherence beyond the actual default certificate.

Independent proof/G0 and controls finder/skeptic reviews reported no findings.
These are concrete constant-default scope proofs, not merely parameterized
preparation laws. They do not implement arbitrary initialization, reference
allocation, intervening dirty reads, named-context reconstruction, valued returns,
frontend admission or compiler adequacy. Final joint/full-lane gates remain open.

## Boolean literal initialization

Yul/RawLiteralInitialization executes either Boolean literal through the existing
context-indexed snapshot and declaration result. Its correct theorem relates
the concrete Source declInit/evalE/convRV/getV path to the runner at every fuel,
conjoining exact new-head, older raw-prefix, world and failure-state preservation.
Fuel zero and one time out with the complete input; later horizons prepend the
chosen Boolean. No default certificate, coherence or child execution law is
assumed. Source equality uses the explicit stored-clean projection; authoritative
older raw words are retained rather than implicitly cleaned.

Checks/RawLiteralInitialization inhabits the true initializer, instantiates the
Source law for either value, checks exact horizons and canonical true/false
heads, and retains shifted dirty words 2 and 257. The nondefault control proves
that true differs from the existing Boolean default in every environment.
Independent proof/G0, controls and documentation finder/skeptic reviews reported no findings.

This covers literal initialization only. Arbitrary expressions, ordinary dirty
reads, scope/sequence closure for these initializers, frontend admission,
compiler adequacy, general P16 and full-lane gates remain open. Source.Val,
Source.Eval and existing typed-layer proofs are unchanged.

## Closing literal initializer scopes

Yul/RawLiteralScope runs the committed Boolean initializer and closes its
temporary head using existing snapshot operations. correct proves entire
enclosing snapshot identity and actual Source block execution at every fuel;
frame_correct additionally relates the computed snapshot to the returned frame.
The adapter implements the existing typed Source adapter with these concrete
bodies. There is no assumed child law, default certificate or cleaning policy.
Its adapter interface retains coherence; the underlying read-free frame theorem
does not require it.

Checks/RawLiteralScope inhabits the true initializer scope and also instantiates
the false adapter. Exact outcomes distinguish unchanged-input timeout at zero
through three from normal restoration at four. A literal-true/integer-default
two-scope combination uses existing cons/block factories, times out at six and
succeeds at seven with the whole dirty frame retained, including raw 2/257.
The formal mixed Source law uses a concretely clean/coherent frame; these dirty
runtime controls do not assert a general dirty-composition theorem.

Independent proof/G0, controls and documentation finder/skeptic reviews reported no findings.
This adds concrete literal scope composition, not arbitrary initializer
expressions, intervening dirty reads or general context-changing sequencing.
General P16, frontend admission, compiler adequacy and final joint/full-lane
gates remain open. Source types and Source.Eval are unchanged.

## In-range integer literal initialization

Yul/RawIntegerInitialization extends concrete declaration execution to every
Source IntTy and integer inside its exact declared bounds. fits identifies
the rational literal range condition; conversion discharges actual constVal;
admissible constructs the real implicit-typing evidence. correct then conjoins
new-head, older raw-prefix, world and failure-state preservation with actual
Source declInit/evalE/convRV/getV execution at every horizon. No conversion
agreement, default or child execution law is assumed. The integer is retained
without wrapping; the new local is initialized at its declared type. Older
authoritative raw locals are not cleaned. Source equality uses their explicit
stored-clean projection, not an ordinary dirty-read policy.

Checks/RawIntegerInitialization inhabits uint8 255 and signed8 -128 declarations,
instantiates the all-fuel law for uint8 and uint256 maximum, and preserves old
raw words 2/257 through two context extensions. Fractional and out-of-range
controls check actual implicit typing and constVal refusals. They do not assert
general frontend admission. The concrete unsigned-then-signed Source item
sequence is proved successful at every horizon from four; horizon three times
out without changing the world. This combination law uses stored-clean Source
locals alongside separate raw snapshot controls.

Initial scratch failures, including default decide recursion depth, are kept;
kernel decide and explicit constructor proofs discharge controls without raised
budgets. The producer proof uses the concrete conversion witness. Independent
proof/G0, controls and documentation finder/skeptic reviews reported no substantive findings.
The documentation skeptic suggested distinguishing typing from frontend admission;
the parent handoff now uses conversion/typing laws.
General initializer expressions, integer scope closure, intervening dirty reads,
general P16, full admission/calculus/compiler composition and final full gates
remain open. No existing Source definition or typed-layer proof changes.

## Closing in-range integer initializer scopes

Yul/RawIntegerScope executes the committed integer initializer and closes its
temporary head using existing snapshot operations. correct retains the exact
IntTy range premise and proves full enclosing snapshot restoration plus actual
Source block execution at every horizon. frame_correct additionally identifies
the computed snapshot with the returned original frame. The concrete existing
Adapter uses these bodies and proofs, retaining its coherence contract; the
underlying read-free frame theorem needs no coherence. No child execution law,
default certificate or conversion agreement is assumed.

Checks/RawIntegerScope inhabits an unsigned-255 scope and instantiates signed
minimum and uint256 maximum adapters. Exact equations distinguish unchanged
input timeout at zero through three from normal restoration at four. Both
unsigned/signed and integer/Boolean mixed-scope programs time out at six and
succeed at seven with the full dirty frame retained, including raw 2/257.
Their formal Source laws use a concrete clean/coherent frame; dirty runtime
controls do not imply generic dirty-composition adequacy. At fuel two an empty
block succeeds while the integer scope times out, distinguishing executed
initialization from an elided declaration.

Independent proof/G0, controls and documentation finder/skeptic reviews reported no findings.
This supplies concrete bounded-integer scope composition. Arbitrary initializer
expressions, intervening dirty reads, general context-changing sequencing,
general P16, frontend admission, full calculus/compiler composition and final
joint/full gates remain open. Existing Source definitions and proofs are unchanged.

## Context-growing Boolean expression initialization

Yul/LocalBoolInitialization connects the existing concrete LocalBoolControl
certificate/evaluator to actual Source declInit. Result is parameter-only:
normal execution carries LocalState at bool :: types; a halt carries the
original-context partial LocalState. The runner prepends the actual returned
LocalValue, retaining raw constructors and every effect already performed.
It neither cleans a copied word nor restores the initial locals on failure.

source_agrees proves actual Source declaration equality for every certified
Boolean-control expression and horizon from LocalState.ofClean input. It
discharges expression agreement through the existing concrete producer, including
conversion/getV/EM.sub. Normal projection requires genuine clean constructors;
raw normal outputs return none. Halt projection matches Source world observation
while the executable result also retains partial locals. No child execution law,
conversion oracle or implicit dirty-read policy is assumed.

Checks/LocalBoolInitialization inhabits a nonliteral declaration with assignment,
conjunction and nested negation. At fuel four the left assignment occurs before
the right times out; fuel five adds the new false local while retaining that
assignment. Short-circuiting a false left side instead succeeds at four. A raw
local-copy initializer preserves word 2 and its sibling 257 and refuses clean
projection. Actual Source timeout/success equations are proved for arbitrary
globals and frame on the explicit clean baseline.

Independent proof/G0, controls and documentation finder/skeptic reviews reported no findings.
This is concrete composition for the existing Boolean-control certificate,
not every Source expression, dirty compiler correspondence or frontend admission.
General P16, other initializer types, context-changing sequencing and final
calculus/compiler/joint/full gates remain open. Existing Source types and proofs
are unchanged.

## Scope closure with Boolean initializer effects

Yul/LocalBoolScope consumes the committed LocalBoolInitialization runner and
drops its temporary head only after successful initialization. Existing-local
updates and the complete world remain; a halt retains the original-context
partial state returned by the initializer. Scope closure therefore does not
restore the input locals. Normal projection requires genuine clean constructors.

source_agrees proves actual Source block execution for every existing
Boolean-control certificate and every horizon from explicit ofClean input.
The proof composes the concrete initializer theorem, real Source item execution
and existing suffix restoration. No child-law or conversion agreement is assumed.

Checks/LocalBoolScope inhabits the nonliteral assignment/AND/NOT scope. Fuel five
times out before the write; six times out after retaining the outer assignment;
seven succeeds, removes only the new head and retains that assignment. False-left
short circuit succeeds at six. Raw-copy closure keeps words 2/257 and refuses
clean projection. Independent Source controls prove timeout six and successful
outer-local update seven for arbitrary globals/frame on the clean baseline.
These controls distinguish partial LOCAL state from Source halt/world projection.

Independent proof/G0, controls and documentation finder/skeptic reviews reported no findings.
This closes scopes for the existing Boolean-control expression producer.
Generic context-changing sequencing, other expression classes, dirty pipeline
correspondence, general P16, frontend admission and final calculus/compiler/joint
gates remain open. Existing Source definitions and proofs are unchanged.

## A Boolean binding consumed in its extended context

Yul/LocalBoolBinding composes an actual certified Boolean initializer with a
following Boolean expression statement. The latter certificate is indexed by
bool :: types, so it can read or update the introduced local. Parameter-only
Result distinguishes normal extended locals, an initializer halt at the original
context, and a body halt at the extended context. Both failure stages retain
their complete partial state; an introduced slot is not discarded on body error.

tail_source_agrees composes the concrete expression-statement producer with its
final nil horizon. source_agrees then composes the concrete initializer theorem,
that tail theorem and actual Source Out.up transport. The result is all-fuel
Source execution equality for the two-item program from explicit ofClean input,
without a caller-provided child law. Normal projection requires genuine clean
constructors; raw execution does not clean copied words.

Checks/LocalBoolBinding inhabits a context-growing program whose body reads the
new local and assigns an older local before further work. Stage controls retain
the introduced slot and outer assignment on body timeout, distinguish initializer
failure before context growth, and verify a later successful result. Another
body updates the new local itself. Raw copying retains words 2/257 and refuses
clean projection. Independent Source controls prove timeout six/success seven
for arbitrary globals/frame on the clean baseline.

Independent proof/G0, controls and documentation finder/skeptic reviews reported no findings.
This supplies concrete two-item context-changing composition, not arbitrary
statement lists, other initializer types, dirty compiler correspondence or
frontend admission. General P16 and final calculus/compiler/joint/full gates
remain open. Existing Source definitions and proofs are unchanged.

## Arbitrary Boolean declaration/expression lists

Yul/LocalBoolItems adds an intrinsic certificate over existing Source.RItems.
Its nil, expression and Boolean declaration constructors preserve exact input
and output contexts. Runtime structurally eliminates that certificate using
index-generalized casesOn and the actual expression/declaration producers.
A halted Result retains an existential reached context together with LocalState
at precisely that context; no untyped state or erased intermediate binding is
introduced. Normal output remains indexed by the final context.

source_agrees proves actual Source.execItems equality for every certified list
and horizon from explicit ofClean input. Concrete child theorems and tail
induction discharge all execution laws. project_up and lift_up_run establish
the real Source outcome transport; normal projection still requires genuine
clean constructors, with no implicit raw-word cleaning.

Checks/LocalBoolItems inhabits a five-item program with three declarations,
new-binding reads and cross-binding writes. Failure controls retain the exact
reached original, one-, two- and three-binding contexts, including a write before
timeout. Success updates the intended bindings while retaining sibling 257.
A multi-declaration raw-copy program keeps word 2 and refuses clean projection.
Independent Source controls prove timeout seven and success eight for arbitrary
globals/frame on the clean baseline.

Independent proof/G0, controls and documentation finder/skeptic reviews reported no findings.
This covers arbitrary lists of the certified Boolean declaration/expression
forms. Other Source statements and types, dirty pipeline correspondence, general
P16 and final calculus/compiler/joint/full gates remain open. Existing Source
definitions and proofs are unchanged.

## Closing arbitrary certified Boolean item scopes

Yul/LocalBoolItemScope derives the exact output-context suffix from the actual
item-list certificate. Its raw drop operates on existing context-computed local
products; restore uses the proved suffix to retain the enclosing context. Normal
closure drops declarations only by position, preserving outer values and world.
A halted result retains its full existential reached context and partial state.

Source restoration and clean transport are proved against the existing
Locals.restore implementation. restore_project requires successful decoding of
the complete pre-restoration state. This premise is necessary: discarding a
dirty temporary may expose a clean enclosing state. The final source_agrees
theorem obtains the needed premise from concrete item execution and proves
Source block equality at every fuel from ofClean input, without a child oracle.

Checks/LocalBoolItemScope closes the three-declaration program, retaining its
outer write on success and all three temporary slots on timeout. Raw-copy scope
closure preserves enclosing words 2/257 and refuses clean projection. A separate
synthetic typed result contains dirty temporary words over a clean old state:
projection fails before closure, but dropping those slots restores exactly the
original clean state. This is an algebraic restoration control, not a claim that
clean execution produces that synthetic result. Independent Source controls
prove timeout eight/success nine for arbitrary globals/frame on the clean baseline.

Independent proof/G0, controls and documentation finder/skeptic reviews reported no findings.
This composes scopes of the certified Boolean declaration/expression lists.
Other Source statement/type classes, dirty pipeline correspondence, general P16
and final calculus/compiler/joint/full gates remain open. Existing Source
definitions and proofs are unchanged.

### Boolean conditional scope adapter

LocalBoolIf.run executes a certified Boolean condition and actual certified item block with Source's predecessor fuel. False conditions retain condition effects and skip the block; true conditions restore only a successful block's local scope. A halted block retains its reached context and world. source_agrees universally relates execution to Source.execS ifThen from a completely clean local frame, using concrete LocalBoolControl and LocalBoolItemScope proofs. RawSequence.restore_self accounts for Source's additional close.

Checks.LocalBoolIf inhabits the Source conditional and tests timeout/success
horizons, branch skipping, condition assignment, partial condition failure, and
dirty nonzero truth with an observable branch timeout. Dirty frames still fail
clean projection. Finder caught and corrected an initially nondiscriminating
empty-branch dirty control. No Source/** changes, solc/EVM evidence or admission
expansion occur here. Full VY1/general P16, dirty Source adequacy and final
joint/checkpoint gates remain open.

Validation: serial affected build and two per-file gates pass; MCP reports zero
errors in both modules; layer/registration/orphan/doc-path/diff checks pass (40
existing ambiguous doc references all resolve). Scoped reports contain only
propext, Classical.choice and Quot.sound. Independent semantic, controls and
foundation finder/skeptic reviews completed; the controls finding above was
fixed and re-reviewed. Full gates were not rerun in this incremental turn. The
persistent goal read API is unavailable; no goal was created or changed.

### Two-branch Boolean scope adapter

LocalBoolIfElse.run selects between two independently indexed certified Boolean item lists. Their output contexts may differ: each successful block drops only its own declarations; a halted block retains its actual reached context. Both the condition and selected block use the actual Source predecessor horizon. source_agrees quantifies all supported conditions/branches, globals, frames, horizons, parameters, phases, typed clean input locals and world, and concretely agrees with Source.execS ifElse. It invokes the existing expression and scoped-item proofs and accounts for Source's additional close; no caller agreement assumption is introduced.

Checks.LocalBoolIfElse inhabits the actual Source ifElse with a
three-declaration true branch and two-declaration false branch. Controls
distinguish their timeout/success horizons and partial contexts, condition
assignment and condition timeout effects, and raw word 2 selecting the true
branch rather than false. Raw 257 remains dirty, so final clean projection
fails. Dirty execution is retained; dirty Source/compiler adequacy is not
claimed. Source/** and frontend admission remain unchanged. Full lane, general
P16, dirty per-pipeline boundaries and final joint/full gates remain open.

All six independent read-only reviews found no issues. Both per-file MCP
diagnostics report zero errors; serial affected build (130 jobs), two per-file
gates, layer/registration/orphan/doc-path/diff checks pass. Layer check: 540
core modules, zero reach elaborator or checked parser adapters; 3331 reachable,
zero orphans. Forty existing ambiguous doc references all resolve. Scoped
theorem/control reports use only propext, Classical.choice and Quot.sound. Final
lane gates are pending, not claimed. get_goal remains unavailable; persistent
goal unchanged.
### Scoped loops

LocalBoolWhile and LocalBoolDoWhile execute certified Boolean conditions and
context-growing item scopes with Source's predecessor horizons. Successful
bodies restore their declarations; halts retain their reached context and
partial effects. Their source_agrees theorems prove all-fuel correspondence
with Source.execS from completely clean input, using concrete condition/scope
proofs and decoder inversion. Do/while executes the body before its condition.

Controls cover declaration/outer-write combinations, partial body and condition
effects, recursive iteration, false-guard ordering and dirty projection refusal.
LocalBoolDivergence proves no finite normal completion for literal-true guards
and certified bodies, for arbitrary raw frames and actual clean Source execution.
It does not classify all halts or cover unsupported break/return bodies.

The shared restoration fact is RawSequence.restore_self; the duplicate
LocalBoolIf.restore_self was removed. Conditional and loop consumers reuse the
existing theorem without changing their Source agreement statements.

These extensions do not expand frontend admission or establish dirty
Source/compiler adequacy. General P16, remaining statement/type cases and final
joint/full lane validation remain open. No new external solc/EVM evidence is
claimed.

The loop checkpoints passed scoped kernel checks and independent finder/skeptic
reviews. Repeated-loop controls use a proved iteration step after direct
reduction reached the unchanged heartbeat limit. Raw failed attempts remain
preserved with the external handoff evidence. This integration correction
rechecks restoration consumers; it does not replace final lane validation.

Restoration reuse passed affected and per-file kernel checks and independent
finder/skeptic review. Agreement statements and control expectations are unchanged.

### Constant-true do/while

LocalBoolDoDivergence.no_normal excludes normal completion at every finite
horizon for arbitrary raw frames and any certified Boolean item body.
source_no_normal derives the corresponding actual Source result from clean
input through concrete do/while agreement. Body halts are permitted; neither
body success nor a caller simulation law is assumed. Theorems do not classify
all halts, cover unsupported exits or establish dirty compiler correspondence.
Nonempty scoped-body witnesses clear an outer flag; false/mutable-guard controls
terminate, distinguishing the literal-true premise. Full P16 and lane gates
remain open.

Scoped kernel checks and independent finder/skeptic reviews pass; final lane
validation remains pending.

### For initializer and body scopes

LocalBoolFor composes a certified Boolean initializer, a condition in its
extended context, and a context-growing certified item body, with no post.
Successful exit drops the initializer head after body scopes close; failures
retain their reached context and partial effects. source_agrees proves all-fuel
clean-input Source.execS correspondence using concrete initializer/while laws,
the existing forIter equivalence, decoder inversion and restore_cons.
Controls cover initializer/body timeout contexts, false initial flags,
enclosing writes surviving successful cleanup, partial initializer writes and
dirty projection refusal. A recursive conversion simplification exceeded the
unchanged depth limit; the existing clean-frame identity discharges that step.
This does not cover post expressions, other initializer types or dirty compiler
adequacy. Full P16 and final lane validation remain open.

Scoped kernel checks and independent finder/skeptic reviews pass; final lane
validation remains pending.

### Scoped for post expressions

LocalBoolPostIter and LocalBoolForPost add present Boolean posts to the
certified iteration and context-growing initializer composition. Guard, body
and post use Source's predecessor horizon; post values are discarded while
their effects survive. Both source_agrees theorems prove concrete all-fuel
Source equality from completely clean input, using actual producer equations
and decoder inversion. Successful exit closes only declared scopes; failures
retain their reached context.
Controls distinguish a false-valued post from a false guard, exercise post
writes before timeout, skipped posts, initializer failures and enclosing writes
through final cleanup. This remains the Boolean initializer/guard/post and
certified item-body slice, without dirty compiler adequacy or full P16 coverage.
Final joint/full lane validation remains open.

Scoped kernel checks and independent finder/skeptic reviews pass; final lane
validation remains pending.

### Omitted for guards

LocalBoolForNoGuard proves evaluator equalities replacing an omitted Source
guard with literal true at every fuel, including zero/one. These transport
theorems quantify arbitrary actual Source initializers, bodies and optional
posts without support assumptions. Concrete adapters reuse existing runtimes
with and without Boolean posts; their Source adequacy retains certified
Boolean initialization/item scopes and completely clean input.
Controls distinguish omitted guards from explicit local guards after false
initialization or flag clearing, retain partial initializer/post effects and
exercise both post modes. An independent low-fuel Source control demonstrates
body timeout versus normal guarded exit. Broad evaluator transport does not
claim arbitrary-syntax runtime admission or dirty compiler correspondence.
Full P16 and final lane validation remain open.

Scoped kernel checks and independent finder/skeptic reviews pass; final lane
validation remains pending.

### Unchecked and ordinary item scopes

LocalBoolUnchecked composes a certified unchecked Boolean item scope with
ordinary following items. Concrete all-fuel Source item/block proofs execute
the inner scope with checked=false, restore its declarations, and resume the
tail in the original frame. Successful enclosing blocks close tail declarations;
failures retain their reached context and partial effects. Clean representation
is derived through producer equations and decoder inversion.
Controls distinguish inner and restored-tail timeout contexts, final enclosing
writes, tail cleanup and dirty projection refusal. Independent actual Source
checks prove timeout and a successful true-to-false enclosing write. This
Boolean slice makes no new arithmetic, pipeline or dirty compiler claim.
Full P16 and final lane validation remain open.

Scoped kernel checks and independent finder/skeptic reviews pass; final lane
validation remains pending.

### Constant-default local bindings

LocalDefaultBinding composes an actual constant-default declaration with a
certified Boolean item body in the extended typed context. Its certificate
retains the real Source.Val.default lookup; it makes no allocation promise.
The all-fuel clean-input Source item theorem uses concrete declaration/body
proofs and intrinsic outcome transport. Raw execution prepends only the new
default and preserves existing values until the body acts.
Integer and Boolean witnesses cover shifted enclosing writes, partial contexts,
default zero and preserved dirty sibling bits. Independent Source controls
check timeout and completion. A missing constant default for memory bytes is
not a general refusal of allocating reference declarations. Compiler
representation, dirty ordinary reads and full P16/lane validation remain open.

Scoped kernel checks and independent finder/skeptic reviews pass; final lane
validation remains pending.

### Constant-default enclosing scopes

LocalDefaultBinding now closes the declaration and body scope using the proved
context suffix. Restoration drops only the added raw locals and preserves the
world and surviving words. Halts retain their reached context. The concrete
all-fuel block theorem composes Source execution from clean input; its internal
restoration projection requires a successful decoder before dropping locals.
Integer and Boolean witnesses check restoration, enclosing writes, timeout
contexts and dirty sibling preservation. Independent Source controls distinguish
fuel-six timeout from fuel-seven completion. General P16, dirty compiler
adequacy and final lane gates remain open.

Scoped kernel checks and independent finder/skeptic reviews pass; final lane
validation remains pending.

### Heterogeneous constant-default sequences

LocalDefaultItems certifies arbitrary finite sequences of actual constant-default
declarations before a supported Boolean item body. Contexts, declared types and
the original Source item syntax index every certificate. Execution preserves raw
surviving locals and reached-context failures; no cleanup or allocation choice is
introduced. The all-fuel clean-input theorem composes concrete Source declaration
and body proofs rather than requiring a supplied simulation law.
A uint8/uint256 sequence checks shifted enclosing writes, multiple partial
contexts, preserved dirty sibling bits and refusal of clean projection. Independent
Source controls distinguish timeout from successful execution. Broader P16 and final lane gates remain open.

Scoped kernel checks and independent finder/skeptic reviews pass; final lane
validation remains pending.

### Closing heterogeneous default sequences

LocalDefaultItems now proves that each certified output context extends the input
by a prefix. Its scope runtime restores only successful outcomes, dropping that
prefix without decoding surviving raw values; halts retain their reached context.
The all-fuel block theorem composes actual Source item execution and restoration
from clean input, with successful decoding required before the restoration
projection law. Controls distinguish partial declaration/body contexts from
successful closure, preserve the enclosing write and dirty sibling bits, and
independently evaluate actual Source block timeout/completion. Broader P16,
general admission, dirty compiler adequacy and final lane validation remain open.

Scoped kernel checks and independent finder/skeptic reviews pass; final lane
validation remains pending.

### Unchecked default scopes and ordinary continuations

LocalDefaultUnchecked composes certified heterogeneous default sequences inside
an unchecked scope and its ordinary continuation. Successful inner execution
restores the enclosing context before running the tail; failures retain their
reached locals and partial effects. The all-fuel clean-input item and block
theorems use actual Source execution with the inner frame checked flag false
and the original continuation frame, concrete decoder inversion and restoration.
A two-default inner scope and a delayed default/Boolean tail check both partial
contexts, final cleanup, enclosing writes and preserved dirty sibling bits.
Independent Source controls expose the intermediate true-to-false write and the
final false-to-true continuation. Controls are separate lemmas to stay within
the unchanged proof budget. This adds no arithmetic, pipeline or general dirty
compiler claim. Broader P16, admission and final lane validation remain open.

Scoped kernel checks and independent finder/skeptic reviews pass; final lane
validation remains pending.

### World preservation on raw local inputs

LocalItemWorld proves world preservation for every supported Boolean item list,
constant-default sequence, successful or halted scope closure, and unchecked
scope/continuation execution. These laws quantify arbitrary raw local states and
all fuel values without a cleanliness premise. They use the existing expression
purity and concrete item runners, introducing no physical/world-effect model.
Any observation depending only on the existing Source world is consequently
preserved. This does not freeze local values or views depending on them.
An inhabited default/unchecked witness instantiates the law for every world and
horizon. Success and timeout controls retain local writes and dirty decoder
refusal. Proofs use bounded one-step rewrites rather than recursive unfolding;
failed scratch attempts remain in external evidence. General P16, admission,
dirty compiler adequacy and final lane gates remain open.

Scoped kernel checks and independent finder/skeptic reviews pass; final lane
validation remains pending.

### Conditional default scopes

LocalDefaultIfElse selects between two certified constant-default item scopes
with independently indexed output contexts. Condition effects precede branch
execution; only the selected scope runs. Success restores its enclosing context,
while a halt retains its reached context and partial effects. The all-fuel clean
Source theorem composes actual condition and block execution, including Source's
extra close through the existing restore-self law. A separate theorem preserves
the world for arbitrary raw inputs and all horizons.
The inhabited witness uses different branch prefixes. Controls distinguish both
outcomes and timeout contexts, nonzero dirty condition selection, and a condition
assignment retained before branch timeout. Independent actual Source evaluations
check both outcomes and timeout. Source and world interfaces are concretely
instantiated for literal, local and assigning conditions. General P16, admission,
dirty compiler adequacy and final lane gates remain open.

Scoped kernel checks and independent finder/skeptic reviews pass; final lane
validation remains pending.

### Loops with heterogeneous default scopes

LocalDefaultWhile iterates a certified default-item scope after an actual Boolean
condition. Each successful iteration drops its temporary prefix before the next
guard; a halt retains its reached locals and partial effects. The all-fuel clean
Source theorem composes concrete condition/block execution and recursive Source
iteration. A separate raw-input theorem preserves the existing world at every
horizon. Constant-true supported loops have no finite normal result, both in raw
execution and actual clean-input Source execution; this does not classify halts.
An inhabited uint8/uint256/Boolean body updates the enclosing guard and exits.
Controls distinguish guard, first-declaration and body-grown timeouts, restored
completion, untouched state on a false guard and an assigning guard's effect.
Dirty siblings remain present. Independent Source checks confirm completion and
timeout. General P16, admission, dirty compiler adequacy and final lane gates
remain open.

Scoped kernel checks and independent finder/skeptic reviews pass; final lane
validation remains pending.

### Body-first default-scope loops

LocalDefaultDoWhile executes the actual certified default scope before its guard,
restoring the successful scope before guard evaluation and recursion. Its all-fuel
clean Source agreement uses concrete block/condition execution and actual Source
restoration. Raw world preservation includes partial halts. Constant-true raw and
clean-Source loops have no finite normal result, without classifying their halts.
The witness reuses the existing heterogeneous body. Controls check partial
contexts, restored exit, body execution despite a false guard, and a post-body
assignment retained during a later body timeout. Independent actual Source
checks distinguish do/while from while with the same false guard and body.
Dirty siblings remain observable. General P16, admission, dirty compiler
adequacy and final lane gates remain open.

Scoped kernel checks and independent finder/skeptic reviews pass; final lane
validation remains pending.

### Scoped for-iterations with post expressions

LocalDefaultPostIter composes a supported Boolean guard, heterogeneous default
scope and supported Boolean post expression through actual Source.forIter.
The body closes before the post; the post runs at the predecessor horizon and
its returned value is discarded. The all-fuel clean Source theorem concretely
supplies guard/body/post agreement, restoration and recursion. Raw world
preservation includes partial halts. Constant-true guards have no finite normal
outcome for any supported post, including one returning false; no halt
classification or dirty Source adequacy is asserted.
The witness reuses the existing body. Controls check both post values, continued
iteration after a false post under a true guard, post writes and writes retained
before a post timeout. Independent Source evaluations confirm the same outcomes.
Dirty siblings remain present. General P16, admission, dirty compiler adequacy
and final lane gates remain open.

Scoped kernel checks and independent finder/skeptic reviews pass; final lane
validation remains pending.

### Omitted guards and H22/H21 integration

LocalDefaultNoGuard reuses the committed universal Source omitted-guard equality
and the actual default-scoped literal-true runners, with present-post and no-post
forms. Concrete clean Source agreements, raw world preservation and finite-normal
exclusions retain actual supported-body/post premises. No optional-guard semantics
is duplicated. Controls contrast omitted and present guards, retain partial post
writes and demonstrate continuing iteration after the body clears a local.
The branch is rebased onto H22. Existing lane source bodies match the saved
pre-rebase checkpoint; incoming ExtCall fields are preserved. H21 roots are
regenerated and module-map rows live in the Yul area file. General P16, admission,
dirty compiler adequacy and final lane validation remain open.

The checkpoint library build passed (3,270 jobs), along with trust, layers,
roots and documentation checks. The axiom-pin gate failed on an unrecorded
Mathlib cache test pin outside the lane; its raw failure is retained, not
reported as a pass. Eight adapter laws and six controls have only standard
Lean axioms. Independent finder/skeptic reviews reported no findings.

The lane adopts the published integration dependency. Post-rebase touched
checks passed (169 jobs), and both omitted-guard files have zero diagnostics.
The upstream cache-scan correction yields 6,343 axiom pins with zero drift.
Review found and corrected two conflict-resolution defects in the shared
checker and module map; both full upstream files are preserved with only
existing lane rows appended. Independent re-review found no remaining issues.
No Source or scoped-syntax definitions were changed by the lane.

### Boolean failure classification

LocalBoolFailure proves that errors from the existing four-form expression
certificate and its short-circuit/control extension are exactly horizon
timeouts, for every fuel and raw local state. No clean-state premise is used.
Controls retain writes before timeout and dirty words across skipped branches;
they distinguish timeout from revert and refuse an unsupported base certificate.
This classifies returned errors only: it does not prove termination, loop
divergence, general Source embedding or compiler adequacy. Evaluators and Source
types are unchanged. Broader P16 and final lane validation remain open.

Scoped diagnostics, touched builds and independent finder/skeptic reviews pass;
all seven reported theorem axiom sets contain only standard Lean axioms.

### Context-growing item failures

LocalItemFailure extends timeout classification to actual expression statements,
Boolean initialization and certified Boolean/default item lists, at all fuel
and arbitrary raw inputs. List theorems quantify the halted result's actual
reached context and locals; initializer failure retains the input context with
its partial writes. Controls expose grown timeout contexts, normal completion
and precisely scoped negative halt/certificate cases. Source, evaluators and
state types are unchanged. This classifies halted outcomes only; general
embedding, loop adequacy and final lane validation remain open.

Scoped diagnostics/builds and six independent finder/skeptic reviews pass.
All eleven reported axiom sets contain only standard Lean axioms.

### Concrete finite-horizon loop timeouts

LocalLoopFailure classifies actual scope/while halts on raw inputs, retains an
actual reached context/state for omitted-guard no-post timeouts at every fuel,
and proves the exact Source.forIter timeout/world result from clean Source
locals. All body certificates remain explicit; no supplied execution law is
assumed. Raw results remain separate from the old Source projection. A direct
Source break loop completes normally and cannot inhabit this body certificate,
showing why the premise is necessary. These finite-horizon laws do not assert
coinductive divergence, general embedding or compiler adequacy. Source and
runners are unchanged; broader P16 and final lane gates remain open.

Scoped diagnostics/builds and six independent finder/skeptic reviews pass.
All eleven reported axiom sets contain only standard Lean axioms.

### Post and body-first horizons

LocalPostHorizon classifies actual post-iteration and do/while halts at all
fuel on raw inputs. An omitted guard with a certified Boolean post has an
actual retained timeout result at every finite horizon; exact Source.forIter
timeout/world output follows from clean Source locals. Guard, post and body
certificates remain explicit. Controls retain post writes, ignore false post
values, skip post evaluation under a false guard, and distinguish do/while's
body-first execution. Equality refusal concerns only this control certificate.
Source, state and evaluators are unchanged. No general divergence, embedding
or compiler adequacy is claimed; broader P16 and final lane gates remain open.

Scoped diagnostics/builds and six independent finder/skeptic reviews pass.
All eleven reported axiom sets contain only standard Lean axioms.

### Constant-loop reductions

LocalLoopReductions proves full raw-result equality between false do/while at
fuel+2 and one scoped body at fuel+1, and between false/true literal posts at
every fuel. The post equality is limited to those literals: an assigning post
can change the result. Constant-true do/while has an actual retained timeout
state at every finite horizon; exact Source timeout/world output follows from
clean Source locals with the real body certificate. A breaking Source body
completes normally, so the certificate cannot be dropped. These are concrete
runner laws, not general divergence, dirty readback or compiler adequacy.
Source, state and evaluators are unchanged; broader P16/final gates remain open.

Scoped diagnostics/builds and six independent finder/skeptic reviews pass.
All eleven reported axiom sets contain only standard Lean axioms.


### Syntax and bounded Source interface freeze

`Solidity.Yul.Interfaces.P16` imports existing context/arity-indexed syntax,
`RawFrame.State`, and `RawSourceAdapter.Adapter` / `ItemAdapter` without
duplicate declarations. These APIs were published at
`6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`.
Adapter fields `run` and `correct` retain the same-context syntax indices,
coherent-input premise and exact represented Source result/world.
Consumers must supply both fields for each supported statement.
Existing `Checks.RawLiteralScope.adapterTrue`, `mixedSource`, and `timeouts`
provide inhabited, combination and horizon controls.
This freeze supplies no universal adapter, general dirty readback or full
Source embedding. Those original obligations remain open.

Independent read-only finder and skeptic reviews found no scope or contract
findings. Per-file interface/signature checks and generated registration pass;
this is an interface checkpoint, not full-lane validation.


### Exact-word Boolean representation congruence

`LocalBoolRepresentation.expression` relates the existing four-form
`LocalBoolExpr.Supported` evaluator for every fuel and pair of related typed
local states. Boolean locals may differ in constructor only when their complete
words agree; all other values and the full Source world remain equal.
Read/write laws preserve the relation, result observation preserves error tags
and full words, and negation/branch truth respect exact word equality.
The assignment-negation-read witness, raw-zero/one witnesses, dirty-two refusal,
equal-truth counterexample, projection distinction and halt distinction guard
the boundary. Constructor-sensitive `clean?` is deliberately not preserved:
this relation is not Source admission or readback equivalence.
No runtime or Source definitions change. Six-form control congruence, general
P16 and the remaining full-lane obligations remain open.

Independent read-only finder/skeptic reviews found no issues. Both per-file
diagnostics report zero errors; all 15 scoped axiom reports use only Lean
standard axioms. Full-lane gates and external compiler/EVM validation are not
claimed for this proof-only increment.


### Exact-word control congruence

`LocalBoolControlRepresentation.control` extends the existing exact-word
relation to all six `LocalBoolControl.Supported` constructors for every fuel
and related typed local state. Short-circuit and conditional branches agree
because the guard words agree; errors retain their exact tag, local updates
retain the indexed relation, and the complete world remains equal.
Seven controls exercise skipped writes, retained raw word 2, conditional
mutation, a write retained before timeout, zero fuel, non-clean raw projection
and distinct raw observations despite equal truthiness. The conditional
assignment/read certificate is inhabited.
This does not establish constructor-sensitive `clean?` equivalence, Source
admission/readback, general statement embedding or full-lane completion.
No Source or runtime definitions change.

Independent read-only finder/skeptic reviews found no issues. Both per-file
diagnostics report zero errors; eight scoped axiom reports contain only Lean
standard axioms. Final lane gates and external compiler/EVM tests remain open.


### Context-growing Boolean item congruence

`LocalBoolItemRepresentation.finish`, `initialization` and `items` prove
exact-word congruence for the existing Boolean initialization and item-list
executions. The result relations keep normal output contexts and each halted
execution's exact reached context, halt reason, related full locals and equal
world. The item theorem quantifies over every existing supported body, input
and output context, fuel and related input pair.
An inhabited declaration-then-negating-assignment witness has seven controls:
completion, timeouts before/after declaration, zero fuel, refused dirty normal
projection, existing error projection, and refusal to relate halts at different
reached contexts. Proofs use bounded unfolding, not higher recursion budgets.
These proof-only relations do not change evaluators or imply clean? projection
equivalence, admission/readback or general P16 embedding.

Independent read-only finder/skeptic reviews found no issues. Both new files
have zero diagnostic errors and passing per-file checks. Ten scoped axiom
reports contain only Lean standard axioms; final lane gates remain open.


### Scope and conditional exact-word congruence

`LocalBoolScopeRepresentation` proves six universal laws: indexed suffix
`drop`, dependent `cast`, existing `restore`, `close`, all-fuel `scope`
and all-fuel `conditional`. Normal scope completion restores the certified
suffix; halted results retain their actual reached context and exact reason.
Conditional execution preserves guard effects before selecting the same branch
from equal complete words. Related full locals and equal worlds are retained.
Eight controls exercise normal prefix removal, halted extended contexts,
skipped/taken branches, guard writes retained on a skipped branch, dirty normal
projection refusal and zero fuel, using an inhabited conditional/declaration
combination. These proof-only laws change no runtime or Source definitions.
They do not establish clean? equivalence, admission/readback, general P16 or
full-lane completion.

Independent read-only finder/skeptic reviews found no issues. Both per-file
diagnostics report zero errors; fourteen scoped axiom reports contain only
Lean standard axioms. Full-lane and external compiler/EVM checks remain open.


### While and do/while exact-word congruence

`LocalBoolWhileRepresentation.whileLoop` and `doWhileLoop` prove all-fuel
congruence for the existing runners over related full local frames and equal
worlds. Their original `LocalBoolControl.Supported` condition and
`LocalBoolItems.Supported` scoped body certificates remain required.
Guard-first versus body-first effects, predecessor recursion horizons and
halted reached contexts/reasons are preserved. The body certificate remains
restricted to its existing Boolean expressions/declarations; no new
break/continue or general statement support is claimed.
Eight controls distinguish false-guard while termination from body-first
do/while timeout, recursive body timeouts, completed do/while scope restoration,
guard writes, zero fuel and dirty projection refusal. An intrinsic scoped loop
witness is inhabited. No Source/runtime definitions, readback policy or
admission changes; general P16 and full-lane gates remain open.

Independent read-only finder/skeptic reviews found no issues. Both modules
have zero diagnostic errors and passing per-file checks; ten scoped axiom
reports contain only Lean standard axioms. Final lane gates remain open.


### Boolean-initialized for congruence

`LocalBoolForRepresentation.close` and `forLoop` preserve the existing
exact-word/local/world relation through the concrete no-post Boolean for
runner. The all-fuel theorem retains the original initializer/guard/body
certificates and their actual typed contexts. Normal completion removes only
the initializer local; halted results retain their exact reached context and
reason. Eight controls exercise normal closure, initializer/guard writes,
timeouts before/after initialization and inside/after repeated bodies, and
dirty projection refusal, with an inhabited intrinsic for/declaration witness.
No runtime, Source or readback policy changes occur. Post expressions, broader
body certificates, admission and general P16 remain outside this theorem.

Independent read-only finder/skeptic reviews found no issues. Both modules
have zero diagnostic errors; ten scoped axiom reports use only Lean standard
axioms. Final lane gates and external compiler/EVM validation remain open.


### Post-iteration exact-word congruence

`LocalBoolPostRepresentation.postIter` proves all-fuel congruence for the
existing guarded Boolean post-iteration runner with its original guard, post
and scoped-item certificates. Guard, body and post partial effects retain their
actual order and predecessor horizons. Halted body contexts are preserved;
post failures retain post-updated locals. Successful post values are discarded,
while related updated full states feed recursion.
Eight controls exercise post writes stopping the next guard, ignored false/true
post values, skipped posts, body failure before post, post failure after a write,
zero fuel and dirty projection refusal. The side-effecting failing post
certificate is inhabited.
These proof-only results change no evaluator, Source type, readback policy or
admission. Broader body/post certificates and general P16 remain open.

Independent read-only finder/skeptic reviews found no issues. Both per-file
diagnostics report zero errors; nine scoped axiom reports contain only Lean
standard axioms. Final lane and external compiler/EVM validation remain open.


### Initializer and post-loop congruence

`LocalBoolForPostRepresentation.forLoop` concretely composes the existing
initializer, guarded post-iteration and normal-only scope-closing laws for
every fuel and related typed input frame. The original initializer, guard,
post and scoped-body certificates and their actual contexts remain required.
Normal completion removes only the initializer local; failures retain their
exact reached context, halt reason, related full locals and equal world.
Nine controls distinguish scoped-counter updates from surviving outer writes,
ignored false/true post values, skipped posts, initializer writes, body versus
post failure frames and dirty projection refusal. An intrinsic for statement
with a side-effecting failing post is inhabited.
No evaluator, Source type, readback or admission changes occur; broader
certificates, general P16 and full-lane validation remain open.

Independent read-only finder/skeptic reviews found no issues. Both modules
have zero diagnostic errors; ten scoped axiom reports use only Lean standard
axioms. Final lane and external compiler/EVM validation remain open.


### Heterogeneous default and unchecked congruence

`LocalDefaultRepresentation` proves six universal laws: `items`,
`restore`, `close`, `block`, `unchecked`, and `uncheckedBlock`.
Real default-lookup certificates add identical typed values beside related
surviving locals; no allocation premise is substituted. Existing fuel guards,
dependent certified suffixes and checked/unchecked continuation contexts remain
unchanged. Only normal results close their scopes; exact halt reasons, reached
contexts, related full locals and equal worlds are preserved.
Nine controls use heterogeneous uint8/uint256 prefixes and distinct clean/raw
Boolean constructors with equal complete words. Both input and output frames
are related, but their normal Source projections differ. Prefix-growth
timeouts, scope closure and unchecked continuation/block behavior are concrete.
The default-list certificate is inhabited.
These proof-only laws change no runtime/Source representation and establish
neither cleanup nor admission/readback equivalence. Broader certificates,
allocation support, general P16 and full-lane validation remain open.

Independent read-only finder/skeptic reviews found no issues. Both modules
have zero diagnostic errors; fifteen scoped axiom reports use only Lean
standard axioms. Final lane and external compiler/EVM validation remain open.


### Independently indexed default control congruence

`LocalDefaultControlRepresentation.ifElse`, `whileLoop` and `doWhileLoop`
prove exact-word congruence for the existing heterogeneous default-scope
runners at every fuel. The conditional retains independent yes/no output
contexts; no equality of their declaration prefixes is required. Actual guard
effects, selected scope, predecessor recursion horizons and guard-first versus
body-first order remain unchanged. Halted results retain exact reached
contexts/reasons, related full locals and equal worlds.
Eleven controls exercise uint8 versus uint256 branch prefixes, scope closure,
guard writes, loop order/recursion and dirty projection refusal. A negative
control holds surviving words, error and world fixed while refusing to relate
different reached prefix types. The intrinsic conditional witness is inhabited.
No Source/runtime/readback/admission changes occur. Original default/Boolean
certificates remain required; broader certificates and general P16 remain open.

Independent read-only finder/skeptic reviews found no issues. Both modules
have zero diagnostic errors; fourteen scoped axiom reports use only Lean
standard axioms. Final lane and external compiler/EVM validation remain open.


### Default post and omitted-guard congruence

`LocalDefaultPostRepresentation.postIter`, `noGuard` and
`noGuardNoPost` prove all-fuel exact-word congruence for the existing
default-scope post runner and concrete literal-true wrappers. Original
guard/post/default-body certificates remain required. Guard/body/post order,
predecessor horizons, full local/world relations and exact body/post failure
frames remain unchanged; successful post values are discarded.
Ten controls distinguish a post write stopping the next present guard from
continued omitted-guard execution, ignored false/true post values, skipped
posts, body versus post failures, zero fuel and dirty projection refusal.
Existing typed default-body and side-effecting post witnesses are reused.
The pre-existing `LocalLoopReductions.literalPost` supplies the universal
false/true literal-post equivalence separately.
No Source/runtime/readback/admission changes or broader certificate support
are claimed. General P16 and full-lane validation remain open.

Independent read-only finder/skeptic reviews have no remaining findings; the
existing literal-post citation was confirmed against its committed signature.
Both modules have zero diagnostic errors; thirteen scoped axiom reports use
only Lean standard axioms. Final lane validation remains open.


### Checked uint8 and comparison congruence

`LocalU8Representation.value_eq`, `expression`, `comparison`, and
`conditional` prove congruence for the existing checked-u8 read/assign/add,
comparison and Boolean-selection runners. Numeric results and errors are
exactly equal within the same pipeline; the local-frame relation allows only
complete-word-equal Boolean constructor differences and keeps all other values
identical. Legacy right-first and via-IR left-first operand evaluation retain
their actual pair-fuel offset, partial states and full world relation.
Eleven mixed-frame controls cover related inputs, legacy 3 versus via-IR 4,
pipeline-specific writes retained on timeout, checked arithmetic panic,
conditional selection, distinct clean projections, unsupported subtraction
certificates and retained raw Boolean flags. An intrinsic arithmetic certificate
is inhabited. Fixed observations and proof budgets are unchanged; explicit
step/residue reductions discharge the numeric controls.
No unchecked or cross-pipeline equality is claimed. Existing Source agreement
still requires its original checked-frame premise; Source/runtime/readback/
admission are unchanged, and general P16/full-lane validation remain open.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero diagnostic errors; fifteen scoped axiom reports use
only Lean standard axioms. Failed reduction attempts are retained in checkpoint
evidence; explicit step/residue proofs keep the original statements and budgets.

### Checked uint8 terminal horizons

`LocalU8Horizon.successor` proves exact result/state equality after one extra
fuel level when the existing run does not return timeout; `extension` proves
the same for arbitrary added fuel. Both quantify over the existing read,
assignment and checked-add certificates, every raw local frame and each
pipeline separately. The proofs use the existing pair cost and right-first
legacy versus left-first via-IR execution, including child halts and writes.
Eight controls reuse inhabited side-effecting certificates: both pipeline
results remain stable, checked panic remains stable, assignments and raw flags
are retained, multiplication remains unsupported, and zero/assignment-timeout
runs concretely change at higher fuel. The non-timeout premise is essential.
This is a local horizon law, not a general divergence, unchecked arithmetic,
Source readback, assembly-admission or compiler-adequacy result. Existing Source
checked-frame premises and observations are unchanged. General P16 and the
full Y01/Y02/Y03/Y09.01 queue and final gates remain open.

Independent read-only finder and skeptic reviews report no findings.
Per-file MCP diagnostics report zero errors for both modules; scoped Lean,
generated-root and layer checks pass. Ten scoped axiom reports use only
Lean standard axioms. Raw failed automation/reduction attempts are retained
separately from passing checks; no proof budgets were raised.

### Checked uint8 comparison horizons

`LocalU8CompareHorizon.successor` and `extension` prove exact full-run equality
for the existing comparison runner after one or arbitrary additional fuel
levels, provided the original result is not timeout. Both operand laws come
from concrete `LocalU8Horizon.successor`; no child simulation premise is assumed.
The statements retain all existing operation values, raw input frames and
same-pipeline evaluation, with pair cost two and actual intermediate writes.
Invalid comparison operators keep the existing stuck result and are not
promoted to admission. Nine controls reuse inhabited side-effecting operands:
legacy false versus via-IR true, full-run terminal stability, invalid-operation
stuck stability, legacy untouched versus via-IR written timeout frames, and a
timeout counterexample. The non-timeout premise remains essential.
This adds no evaluator or Source/ExtCall edits, unchecked arithmetic, readback,
admission, general divergence or compiler-adequacy claim. Existing Source
checked-frame premises remain intact. General P16/full VY1 and final gates
remain open.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; scoped Lean, layer and
generated-root checks pass. Eleven scoped axiom reports use only Lean standard
axioms. Failed automation/import/configuration/proof attempts remain raw evidence;
the final proofs keep the original statements and budgets.

### Boolean terminal horizons

`LocalBoolHorizon.baseSuccessor` proves exact full-run equality at one extra
fuel level for all four existing Boolean base certificates, after a non-timeout
result. `successor` covers all six existing control constructors, including
short-circuit and conditional execution, and `extension` handles arbitrary
additional fuel. The concrete base theorem supplies the base case; every
evaluated child premise follows actual parent execution. Skipped children need
no termination premise. Complete raw values, local writes and worlds remain
in the equality; no cleanup is introduced.
Nine controls cover stable short-circuit results, preserved dirty words and
failed clean projection, conditional writes, an inhabited selected-true
conditional with an unselected timeout branch, retained partial writes,
observable timeout changes and comparison-certificate refusal. Timeout
prefixes remain excluded. These are local horizon laws, not general divergence,
readback, arbitrary Source embedding, admission or compiler adequacy.
No Source/ExtCall/evaluator edits or changed observations, expectations or
budgets. General P16/full Y01/Y02/Y03/Y09.01 and final gates remain open.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; scoped Lean, generated-root
and layer checks pass. Twelve scoped axiom reports use only Lean standard
axioms. Failed automation/branch reductions and the initial incomplete refusal
proof are retained as raw evidence; no statements or budgets were changed.

### Mixed comparison and Boolean conditional horizons

`LocalCompareHorizon.successor` and `extension` prove exact full-run equality
for the existing comparison/Boolean conditional after one or arbitrary added
fuel levels, when the original result is not timeout. They compose concrete
`LocalU8CompareHorizon.successor` and `LocalBoolHorizon.successor` bodies:
comparison stability fixes the actual result and intermediate raw frame before
the same truth choice; only the selected branch needs its derived terminality
fact. No assumed child simulation or new execution interface is introduced.
Ten controls reuse inhabited side-effecting certificates. They preserve exact
legacy clean-false versus via-IR raw-one results and updated numeric frames,
arithmetic panic before branch execution, pipeline-specific partial writes,
timeout-to-success change, and failed dirty-value clean projection.
This is concrete local horizon composition, not general P16, arbitrary Source
embedding/readback, divergence, admission or Source-to-EVM adequacy. Existing
Source checked-frame premises, observations and certificates remain unchanged.
No Source/ExtCall/evaluator edits or proof-budget changes. Full VY1 and final
gates remain open.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; scoped Lean, root and layer
checks pass. Twelve scoped axiom reports use only Lean standard axioms.
Raw failed automation and the misspelled panic-reference attempt are preserved;
the actual PanicCode correction changes no expected behavior or proof budget.

### Context-growing completed item horizons

`LocalItemHorizon.successor` proves that actual normal completion of any
existing Boolean item certificate yields the identical final indexed raw frame
at one extra fuel level; `extension` covers arbitrary added fuel. The statements
quantify over the actual input/output contexts, syntax and certificates.
Concrete `LocalBoolHorizon.successor` stabilizes each executed initializer or
expression, then structural tail induction uses its actual next frame (including
a prepended declaration value). No child simulation law is assumed.
Nine controls include a new inhabited two-declaration certificate reaching a
three-local context, its arbitrary-fuel final-state equality, pre/post growth
timeouts, retained partial frames, timeout-to-completion change, persistent
failed clean projection and unsupported comparison-statement refusal.
These are completed-run laws only: timeout-prefix equality, general divergence,
arbitrary declarations/control, parser admission, dirty readback and full Source
or compiler adequacy remain separate. Existing runners, Source/ExtCall layers,
checked-frame premises and observations are unchanged. General P16/full VY1
and final gates remain open. Recursive simplification initially reached the
existing recursion limit; one-constructor reductions solved it without raising
any checking/proof budget.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; scoped Lean, generated-root
and layer checks pass. Eleven scoped axiom reports use only Lean standard
axioms. Failed automation and recursive-simplification diagnostics are retained
separately from passing checks; no checking/proof limits were increased.

### Heterogeneous default item and block horizons

`LocalDefaultHorizon.successor` and `extension` preserve the exact final
indexed raw frame after actual normal completion of any existing default-item
certificate. They use concrete `LocalItemHorizon.successor` for Boolean bodies
and structural induction for real typed default prepends at the runner's
original three-level execution threshold and residual horizon. No new defaults,
allocation/layout contracts or assumed child law are introduced.
`blockSuccessor` and `blockExtension` preserve the completed caller-context
frame. Actual block normal completion implies an actual normal child run;
stability fixes that child before the existing certified restoration is reused.
Ten controls reuse inhabited uint8/uint256 default declarations beside a dirty
Boolean: exact completed prefixes, arbitrary added fuel, exact block restoration,
three reached-context timeout prefixes, timeout-to-completion change, persistent
clean-projection refusal and unsupported comparison-statement refusal.
Normal completion remains an explicit premise; timeout stability, arbitrary
declarations/control, dirty readback, admission and general Source/compiler
adequacy are not established. Source/ExtCall/evaluators, observations and budgets
are unchanged. General P16/full VY1 and final gates remain open.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; scoped Lean, generated-root
and layer checks pass. Fourteen scoped axiom reports use only Lean standard
axioms. Raw failed automation attempts remain distinct from passing checks;
no checking/proof limits were increased.

### Unchecked scope and ordinary continuation horizons

`LocalUncheckedHorizon.successor` and `extension` preserve exact completed
raw frames for the existing unchecked default-item scope followed by ordinary
default items. Actual normal completion supplies a normal inner run; concrete
`LocalDefaultHorizon.successor` fixes that frame before its existing certified
restoration, then fixes the ordinary continuation at the same residual horizon.
`blockSuccessor` and `blockExtension` apply the unchanged outer restoration
to the fixed completed continuation. True/false control indices remain explicit.
Eleven controls reuse inhabited uint8/uint256 prefixes and add an inhabited
side-effecting Boolean continuation. They cover exact completed/restored frames,
arbitrary added fuel, inner-prefix timeout contexts, a continuation timeout
after restoration retaining its Boolean write, later completion of that
continuation, timeout-to-completion change and persistent dirty projection refusal.
These laws concern the existing wrapper's certified defaults and Boolean items;
they add no unchecked numeric arithmetic, arbitrary control, readback or admission.
Normal completion is required. No Source/ExtCall/evaluator/layout or observation
changes; proof budgets are unchanged. General P16/full VY1 and final gates remain
open.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; scoped Lean, generated-root
and layer checks pass. Fifteen scoped axiom reports use only Lean standard
axioms. Failed standard automation attempts are retained separately from
passing gates; no checking/proof limits were increased.

### Independently typed conditional scope horizons

`LocalIfHorizon.successor` and `extension` preserve the exact final caller
raw frame after actual normal completion of the existing default-item
conditional. Branch output contexts remain independently quantified.
Concrete `LocalBoolHorizon.successor` fixes the actual successful guard value
and intermediate state before the same truth choice; concrete
`LocalDefaultHorizon.blockSuccessor` stabilizes only the selected restored
branch. Its completion premise follows actual parent execution, with no
assumed child simulation or unselected-branch termination requirement.
Ten controls exercise uint8 versus uint256 branch prefixes, arbitrary added
fuel, guard writes retained after restoration, distinct prefix timeout contexts,
timeout-to-completion change and persistent dirty projection refusal. An
inhabited empty-branch certificate combines with a nontrivial opposite branch:
selected execution completes while the unselected block times out at that horizon.
These are completed-run laws for existing certificates, not arbitrary control,
timeout stability, readback, admission or general Source/compiler adequacy.
No Source/ExtCall/evaluator/layout, observation or proof-budget changes.
General P16/full VY1 and final gates remain open.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; scoped Lean, generated-root
and layer checks pass. Twelve scoped axiom reports use only Lean standard
axioms. Failed standard automation attempts remain raw evidence, distinct from
passing gates; no checking/proof limits were increased.

### Published P16 dependency adoption

Adopted the published scheduled dependency checkpoint while preserving later
local proofs. The P16 import boundary is byte-identical to the published and
previous local versions. The sole module-map conflict retained both row sets
and deduplicated the generic P16 row; generated roots retain both parents'
imports. Source, Core call syntax and local runtime definitions are unchanged.
Focused P16, local-horizon and published P20 interface checks pass, with no layer
violations. Independent read-only finder/skeptic merge reviews report no findings.
P20 pending producer fields remain explicit obligations; importing them proves
no concrete Source/compiler adequacy. General P16/full VY1 and final lane gates
remain open.

### Declaration-field classifiers

Reuse `declarationFieldUses` for direct metadata classifiers over intrinsic
`Syn` nodes. Its exact membership and original-unit witness lemmas retain the
actual declaration roster and syntax site; `declarationElementaryUses_iff`
instantiates this API. A classifier can return an empty or incomplete list, so
these traversal laws do not establish classifier validity, whole-catalog
coverage, lexical scope, or admission. Keep the original source unit available:
its headers cannot be recovered from the declaration environment alone.
`LocationFeatures.lean` instantiates the collector for every explicit `DataLoc`
field in `Syn`: parameter and variable-declaration metadata. Its independent
relation proves exact direct-field accounting, and a generic unused-function
control retains all three locations while omission yields no location feature.
These are syntax features; legality and default/inferred locations remain
separate from this subset and from operational admission.

`declarationFieldRefusals` retains every rejected field and its actual
intrinsic declaration/site; `declarationFieldRefusal?` selects the first.
The exactness and source-witness lemmas are relative to the supplied classifier
and Boolean predicate. The predicate sees field values, not a derived typing
context. An empty or incomplete classifier can be silent, and an accept-all
predicate can silence nonempty syntax. Do not equate silence with admission:
complete extraction, classifier validity and the versioned profile/policy
linkage must be established separately. Sites do not provide unique character
offsets or prove lexical scope.

`StructuralFeatures.lean` combines selected constructor markers and the
existing elementary/location classifiers over the original source unit.
It reuses the generated `Syn.ctor` and canonical visitor rather than copying
indexed constructor projectors. Use `sourceStructuralSubset` only as a partial
inventory: even marked constructors can need further payload/typing features.
Calls, allocation, tuples, assembly and user/function types are deliberately
not interpreted from constructor tags alone. In particular, this prevents
mistaking conversions for function calls or treating canonical rethrow as an
arbitrary assembly refusal. The import control shows why `Env` alone is
insufficient; retain the original unit or equivalent header information.
Membership bridges do not promise equality of old/new ordering or counts.

`ExclusionFeatures.lean` supplements the subset using the existing `Syn.excl`.
All six exclusion IDs match the catalog exactly; canonical-rethrow syntax keeps
its existing exception. Retain and check the intrinsic rejection channel
independently of catalog feature extraction. `syntaxExclusionUses` supplies
actual typed sites, and reported flags also occur in `Syn.rejections`; no
converse list/order equality is claimed. `syntaxFieldUses` shares whole-unit
metadata traversal with the structural collector. The inherited Source syntax
examples cover general assembly, mixed buffers, removed constructs and malformed
modifiers; none is presented as operational admission evidence.

### P16 generated-file maintenance

Run `python3 -B scripts/h62/item1/p16-generator/check.py` to verify the generated
marker, complete P16 bytes, ordered import/documentation census and pinned Git
baseline. Edit registered fragments rather than the generated interface. The
baseline commit must exist locally. This integrity check does not certify live
producer completeness, semantic coverage or Lean elaboration. Extension ordering
and producer membership require separate reconciliation. Checkpoint and full
gates run this checker as `p16-generated`; the pinned baseline object must be
present locally, including in CI checkouts. A missing object fails closed.

### P20 represented-success consumer (V2)

Use `Backend/Selection/P20ConsumerInterface.lean`'s
`P20RepresentedConsumerV2` and `Backend/Selection/P20Consumer.lean`'s
`p20RepresentedConsumerV2` when an actual V2 `PendingG24` link is supplied.
`p20_joint_success_v2` retains its joint domain/Input witness, payment freedom,
source/Yul success, target execution, unchanged caller stack and full G24 `Rep`.
The memory-store control reuses the reviewed producer in
`tests/h62/item2/audit-v09-passes/P20InterfaceV2Controls.lean`.

The V1 assembly consumer and both interface versions remain available unchanged.
V2 does not provide V1's unrestricted stack-only lowering certificate; the
existing V1 overlap conversion still requires that certificate independently.
This migration does not establish general P20 adequacy, admission/origin,
failures, divergence, physical/dirty views or native/resource/observation closure.

### Recursive while completed horizons

`LocalWhileHorizon.successor` and `extension` preserve the exact final caller
raw frame after actual normal completion of the existing default-scoped while.
Fuel induction uses concrete `LocalBoolHorizon.successor` and
`LocalDefaultHorizon.blockSuccessor` to fix each actual predecessor guard/body
result and restored intermediate state before the recursive induction step.
No child simulation or termination law is assumed.
Ten controls include a new inhabited scoped body: declare a uint8, write the
surviving Boolean guard false, evaluate another Boolean expression, restore
the caller frame and exit. They cover completed extra-fuel equality, timeouts
before/after the write in the extended context, changed timeout outcomes,
skipped body and zero fuel, persistent dirty projection refusal on the stopped
path, and the existing literal-true noncompletion theorem instantiated with
the mutating body. The latter does not assert general divergence.
Normal completion remains required. Timeout-prefix stability, arbitrary
control/readback, admission and general Source/compiler adequacy remain open.
No Source/ExtCall/evaluator/layout, observation or proof-budget changes.
General P16/full VY1 and final gates remain open.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; scoped Lean, generated-root
and layer checks pass. Twelve scoped axiom reports use only Lean standard
axioms. Raw failed automation, redundant-rewrite and reserved fixture-name
attempts are retained separately; statements, observations and budgets were
not weakened or increased.

### Body-first do/while completed horizons

`LocalDoWhileHorizon.successor` and `extension` preserve the identical final
caller raw frame after actual normal completion of the existing default-scoped
do/while. Fuel induction first stabilizes the actual restored body through
`LocalDefaultHorizon.blockSuccessor`, then the actual guard through
`LocalBoolHorizon.successor`, before recursing from the exact postguard state.
No supplied child simulation or termination law replaces those concrete bodies.
Eleven controls reuse the prior mutating body and add an inhabited toggling
uint8-scoped body requiring two iterations to complete. They cover exact
extra-fuel final frames, body execution under a false guard, first/second
iteration timeout frames, timeout-to-completion change, zero fuel, the existing
restricted literal-true noncompletion law and projection after an explicit
existing Boolean write. No implicit cleanup/readback rule is introduced.
These are completed-run laws for existing certificates. Timeout stability,
general divergence/control, readback, admission and full Source/compiler
adequacy remain open. Source/ExtCall/evaluators/layouts, observations and
proof budgets are unchanged. General P16/full VY1 and final gates remain open.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; scoped Lean, generated-root
and layer checks pass. Thirteen scoped axiom reports use only Lean standard
axioms. Raw failed standard automation attempts remain distinct from passing
gates; no checking/proof limits were increased.

### Guarded for/post completed horizons

`LocalForPostHorizon.successor` and `extension` preserve the identical final
caller raw frame after actual normal completion of the existing guarded
default-scoped for/post runner. Fuel induction fixes actual guard and restored
body results through concrete Boolean/block horizon producers, then fixes the
post's full state before the actual recursive step. The successful post value
remains ignored exactly as in the existing runner; its effects are retained.
Eleven controls add an inhabited post that writes the caller Boolean false
before a delayed expression times out. They distinguish body failure in its
extended prefix from post failure in the restored, written caller frame, then
show later exact completion and arbitrary added-fuel stability. Additional
controls cover false guards skipping both body/post, false versus true post
values over a mutating body, dirty projection refusal and zero fuel.
No simulation or child termination law is supplied. Normal completion remains
required; timeout stability, arbitrary for control, readback, admission and
general Source/compiler adequacy remain open. Source/ExtCall/evaluators/layouts,
observations and proof budgets are unchanged. General P16/full VY1 and final
gates remain open.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; scoped Lean, generated-root
and layer checks pass. Thirteen scoped axiom reports use only Lean standard
axioms. Raw failed standard automation remains separate from passing gates;
no checking/proof limits were increased.

### Full for initializer completed horizons

`LocalForInitHorizon.scope_agrees` and `iteration_agrees` prove exact equality
between existing Boolean scopes/iterations and their default-item body
embeddings at every fuel, including halts and reached contexts. No agreement
law is assumed. `initializerSuccessor` preserves the real added Boolean frame;
`iterationSuccessor` transports the concrete guarded-post horizon through the
proved equality. `successor` and `extension` compose actual initializer and
iteration completion with unchanged final initializer removal, preserving the
literal same caller raw frame for present Boolean guard/post certificates.
Eleven controls reuse inhabited initialized-loop/body/post witnesses: scoped
counter writes, retained initializer effects, skipped post, exact added frames,
all-fuel scope/iteration agreement, different body/post timeout frames, dirty
projection refusal and timeout-to-completion change.
Normal completion is an explicit premise. Arbitrary for admission/control,
timeout stability, general Source/readback/compiler adequacy and full P16
remain open. No duplicate evaluator, assumed simulation, Source/ExtCall/layout,
observation or proof-budget change is introduced. Full VY1/final gates remain
open.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; scoped Lean, generated-root
and layer checks pass. Seventeen scoped axiom reports use only Lean standard
axioms. Failed direct-reflexivity/standard-automation and redundant-rewrite
attempts are retained as raw evidence; no statements or proof limits changed.

### Initialized no-post for completed horizons

`LocalForNoPostHorizon.iteration_agrees` proves exact all-fuel Boolean/default
while-runner equality using the existing scope agreement, including halts and
reached contexts. `iterationSuccessor` transports the concrete while horizon
through that proved equality. `successor` and `extension` compose actual
initializer and no-post iteration completion with unchanged final initializer
removal, preserving the identical caller raw frame.
Twelve controls add an inhabited body with a body-local declaration and
separate counter/caller writes. They distinguish initializer and three-local
body timeout frames, a retained counter write before the caller write, exact
completed caller effects and extra-fuel equality. Other controls cover stopped
and initializer-writing paths, all-fuel scope/while agreement, dirty projection
refusal, changed timeout outcomes and zero fuel.
No duplicate runner or assumed child simulation is introduced. Actual normal
completion and existing Boolean certificates remain required; arbitrary for
admission/control, timeout stability, readback and full Source/compiler
adequacy remain open. Source/ExtCall/evaluators/layouts, observations and proof
budgets are unchanged. General P16/full VY1 and final gates remain open.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; scoped Lean, generated-root
and layer checks pass. Sixteen scoped axiom reports use only Lean standard
axioms. Failed standard automation remains raw evidence separate from passing
gates; no checking/proof limits were increased.

### Initialized omitted-guard noncompletion

`LocalForNoGuardFailure.no_normal` and `no_post_normal` exclude finite
normal completion of the existing full Boolean initializer/omitted-guard
adapters, with or without a post expression. They compose the actual initializer,
unchanged scope close, existing constant-true noncompletion and concrete
all-fuel iteration agreement; no bridge or child termination law is assumed.
`source_no_normal` and `source_no_post_normal` carry this through existing
clean-input Source agreements, quantifying over both initial and final worlds.
Nine controls reuse an inhabited context-growing body that writes counter and
caller separately. They cover arbitrary-fuel raw noncompletion, exact retained
counter writes, a present guard that completes, a false initializer that still
enters an omitted-guard loop, dirty projection refusal, a post failure retaining
effects, and both concrete Source noncompletion cases.
The certificates contain no break or return. This excludes finite normal
completion only, without classifying halts, proving general divergence or
expanding admission. Dirty readback, arbitrary control, general Source/compiler
adequacy, full P16/VY1 and final lane gates remain open.
No Source/ExtCall/evaluator/layout, expected outcome or proof-budget changes.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; focused Lean, generated-root
and layer checks pass. Thirteen scoped axiom reports use only Lean standard
axioms. Raw failed standard automation is separate from passing gates.
A wrapper-only version-query failure is retained; direct toolchain binaries
report Lean 4.24.0 and Lake 5.0.0-src+797c613. No checking/proof limits changed.

### Full Boolean for timeout classification

`LocalForTimeout.halt_kind` and `no_post_halt_kind` classify actual
halted full-for executions as timeout, for present Boolean guards with or
without post expressions. They compose existing initializer failure and
loop-failure proofs through concrete all-fuel Boolean/default iteration
agreement, retaining the exact reached context and state.
`omitted` and `omitted_no_post` combine this classification with concrete
omitted-guard noncompletion to produce a reached raw timeout state at every
fuel. `source_omitted` and `source_omitted_no_post` use the existing
clean-input full-for agreement to return the actual execution's final world
with the Source timeout. They assume no final-world identity or dirty readback.
Ten controls reuse an inhabited context-growing counter/caller-writing body:
both arbitrary-fuel timeout witnesses, original caller timeout, retained counter
and post effects, present/false guards that complete normally, refusal of
non-timeout halts, and both concrete clean Source timeout witnesses.
These are existing restricted Boolean certificates with no break/return or
world effects. No arbitrary-loop divergence, expanded admission or general
Source/compiler adequacy is claimed. Source/ExtCall/evaluators/layouts, expected
outcomes, observations and proof budgets are unchanged. Full VY1/general P16
and final lane gates remain open.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; focused Lean, generated-root
and layer checks pass. Sixteen scoped axiom reports use only Lean standard
axioms. Failed standard automation and the initial reflexivity-branch correction
remain raw evidence separate from passing checks. No checking/proof limits
were increased.

### Concrete Source horizon selection

`LocalForFirstDone.post` and `no_post` connect the actual initialized
omitted-guard Boolean Source executions to Source's existing `firstDone`.
Every search bound returns `none`, using concrete every-fuel timeout outcomes
and `Source.firstDone_none_iff`; callers supply no divergence, stability or
simulation law. The intrinsic initializer/post/body certificate indices and
clean Source-local boundary remain explicit.
Nine controls use an inhabited body with scoped declarations and separate
counter/caller writes. Omitted guards find no completion at any bound; a present
guard first completes at fuel 9, finds nothing through 8, and retains that
selection at every larger bound. Separate Source controls find a break at 3,
leave continue unfinished through 8, find an invalid-initializer control result
as a completed failure at 2, and stop on a false guard at 3.
Break/continue and the invalid initializer are outside the Boolean certificates;
they demonstrate why this result does not cover arbitrary control. The test
search wrapper calls the existing interpreter and selector, with no new
evaluator, state representation or expected-verdict change.
Dirty Source readback, general assembly admission, arbitrary-loop adequacy,
general Source/compiler composition and full VY1/P16 remain open. No Source,
ExtCall, evaluator, layout, observation or proof-budget changes are introduced.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; focused Lean, generated-root
and layer checks pass. Eleven scoped axiom reports use only Lean standard
axioms. The initial missing Source.Semantics import and invalid-import tactic
attempts remain raw failures, distinct from the corrected valid-import attempts
and passing concrete proofs. No checking/proof limits were increased.

### Completed raw-frame statement horizons

`RawStatementHorizon.discardSuccessor` lifts concrete Boolean control
execution stability through the existing expression-statement discard.
`rawSuccessor`/`rawExtension` and
`coherentSuccessor`/`coherentExtension` then prove exact whole-result and
whole-frame equality for the existing `RawSource.execS` and
`RawCoherent.execS` at larger horizons. The original non-timeout premise is
explicit. No coherent-input, clean projection, child simulation or abstract
adapter stability law is assumed; unchanged capture functions preserve the
same clean backup, raw cells and world.
Ten controls use an inhabited conditional-write certificate over the existing
mixed Boolean/narrow-word/function-field frame. The condition first writes
Boolean true; a selected triple-not assignment later writes false. Fuel 4
retains the first write on timeout; fuel 7 completes with the second write,
and each complete result/frame is identical at every larger bound. The
untouched narrow word remains 257, dirty input/output coherence fails, and
both normal dirty projections refuse. Clean input has a separate successful
coherent observation. Distinct timeout/completion tags show why the premise
cannot be dropped.
These concrete same-context expression-statement laws add no Source/readback
or compiler adequacy, general admission, arbitrary statement/control support,
or physical state semantics. Source/ExtCall/evaluators/layouts, observations,
expected outcomes and proof budgets are unchanged. Full VY1/general P16 and
final lane gates remain open.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; focused Lean, generated-root
and layer checks pass. Fifteen scoped axiom reports use only Lean standard
axioms. Raw failed standard automation, initial fixture-parenthesis correction
and scratch constructor-tactic correction remain separate from passing checks;
no control statement, expected outcome or proof/checking limit changed.

### Completed raw sequence and block horizons

`RawSequenceHorizon.successor` and `blockSuccessor` preserve the entire
actual sequence/block result and raw frame after non-timeout execution.
`extension` and `blockExtension` extend that equality to every larger
horizon. Certificate induction derives the head's non-timeout premise from
actual sequence propagation, fixes its captured frame using the concrete
statement producer, and applies the tail induction at that same next frame.
No coherent-input, clean projection, supplied child simulation or abstract
adapter-stability law is assumed.
Ten controls use two distinct conditional-write statements over the existing
mixed raw frame. Fuel 5 retains the first statement's partial true write; fuel 8
retains the second statement's partial false write. The sequence completes at
9 with true, and its block at 10 returns the same full frame; both remain exactly
equal at every larger horizon. The narrow sibling stays 257, whereas its clean
backup is 1, giving an explicit cell witness against coherence. This witness
also proves dirty projection refusal without whole-frame brute-force checking.
Separate clean-start observation and all-fuel concrete Source block agreement
controls retain the existing coherence boundary.
The original brute-force control proof reached the existing heartbeat limit.
The cell-witness proof, beta reduction and corrected scratch indentation pass
without changing any control statement, outcome or checking/proof limit.
These same-context Boolean expression sequences add no declarations, arbitrary
control, Source dirty readback, general admission or compiler adequacy.
Source/ExtCall/evaluators/layouts and observations remain unchanged.
Full VY1/general P16 and final lane gates remain open.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; focused Lean, generated-root
and layer checks pass. Fourteen scoped axiom reports use only Lean standard
axioms. Raw failed standard automation, the brute-force heartbeat failure and
intermediate witness rewrite/indentation failures remain separate from passing
checks. No control statement, expected outcome or proof/checking limit changed.

### Completed raw condition and loop-body horizons

`RawLoopBodyHorizon.conditionSuccessor` and `conditionExtension` preserve
the full actual condition result and captured raw frame after non-timeout.
`successor` and `extension` prove the same for existing certified loop
bodies: actual sequence blocks, skip, break, continue and conditional bodies.
They use the concrete expression/sequence horizon producers. Conditional
induction fixes the actual condition result and frame first, then applies
the child induction only on the selected true branch. No coherence, projection,
supplied simulation or abstract adapter-stability law is assumed.
Eleven controls reuse the mixed dirty frame and the distinct conditional-write
sequence. Raw Boolean word 2 selects true and retains 2; selected break/continue
complete at fuel 2 with the untouched narrow word 257. A false-writing condition
skips the deep body and completes at 3. The selected sequence times out at 10
with a partial false write and completes at 11 with true; entire completed
condition/body frames remain identical at every larger horizon. Zero/condition
timeout controls retain their exact behavior. A separate all-fuel concrete
Source agreement control requires the existing clean-start coherence boundary.
These same-context certified bodies add no arbitrary statements, loop
iteration/return coverage, dirty Source readback, admission or compiler
adequacy. Source/ExtCall/evaluators/layouts, observations, expected outcomes
and proof budgets are unchanged. Full VY1/general P16 and final gates remain
open.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; focused Lean, generated-root
and layer checks pass. Fifteen scoped axiom reports use only Lean standard
axioms. Raw failed standard automation remains distinct from passing concrete
proofs and gates; no statements, outcomes or proof/checking limits changed.

### Completed raw control-sequence horizons

`RawControlSequenceHorizon.successor` and `blockSuccessor` preserve the
exact completed flow/result and whole raw frame for the existing control
sequence/block runners. `extension` and `blockExtension` extend that
equality to every larger horizon. Actual body stability fixes the head first;
only normal flow invokes the tail induction at that same captured frame.
Break, continue and errors retain their original short-circuit behavior;
leave remains impossible from the intrinsic control index. No coherence,
projection or supplied child/adapter law is assumed.
Eleven controls use break/continue heads followed by a deep sequence and a
separate false-writing normal head. Break and continue propagate at fuel 3,
retaining raw Boolean 2 and narrow word 257. The normal path reaches the tail:
fuel 11 retains its partial false write, and 12 completes with true; block 13
returns the identical result/frame. Completed break/continue/normal/block
frames remain exactly equal at every larger horizon. Early timeout controls
and separate all-fuel clean-start Source block agreement preserve the existing
boundary.
These same-context certified control sequences add no arbitrary statements,
loop iteration/return semantics, dirty Source readback, admission or compiler
adequacy. Source/ExtCall/evaluators/layouts, observations, expected outcomes
and proof budgets are unchanged. Full VY1/general P16 and final gates remain
open.

Independent read-only finder and skeptic reviews report no findings.
Both modules have zero per-file diagnostic errors; focused Lean, generated-root
and layer checks pass. Fifteen scoped axiom reports use only Lean standard
axioms. Raw failed standard automation remains separate from passing concrete
proofs and gates; no statements, outcomes or proof/checking limits changed.

### Completed raw controlled-while horizons

`RawControlledWhileHorizon.successor` and `extension` preserve the exact
whole loop result and raw frame after non-timeout execution. Actual condition
and body producers fix their captured frames before fuel induction: normal
and continue recurse at the same post-body state, break exits, and false/error
paths keep their original result. All child terminality is derived from the
actual parent run; no coherence, projection or supplied simulation law is assumed.
`RawReadOnlyViews.condition`, `continueBody` and `loop` additionally prove
actual word-view preservation for indexed read/read-continue execution at every
fuel. These laws allow capture metadata to change and assert neither whole-frame
identity nor divergence.
Eleven controls cover break exit at 3 retaining raw 2/257; a false-writing
continue body that actually continues then exits at 5; normal-body mutation
and exit at 10; and exact larger-horizon equality of completed frames.
A false guard skips the deep body at 2. The unchanged true continue loop is
tested only through finite timeout 5; normal-body timeout 9 retains its partial
true write before completion writes false. Concrete all-fuel clean Source
agreement uses an explicitly indexed Source loop matching the certificate.
Brute-force narrow-word checking reached the existing heartbeat limit.
The concrete read-view laws prove the same expected word observation without
raising limits. Initial branch, ambiguous Source-index, missing helper-object
and failed brute-force attempts remain raw evidence; no expected verdict changed.
These existing certified loops add no arbitrary statement/return support, dirty
Source readback, admission or compiler adequacy. Source/ExtCall/evaluators/layouts,
observations and proof budgets remain unchanged. Full VY1/general P16 and final
lane gates remain open.

Independent read-only finder and skeptic reviews report no findings across all
three modules. Per-file diagnostics report zero errors; focused Lean, the helper
module build, generated-root and layer checks pass. Sixteen scoped axiom reports
use only Lean standard axioms. Raw failed attempts remain separate from passes.
No theorem premise, expected outcome or proof/checking limit was weakened.

### Completed raw sequence-bodied while horizons

`RawSequenceWhileHorizon.successor` and `extension` preserve the exact
whole loop result and raw frame after non-timeout execution. Concrete condition
and control-block producers fix captures before the actual normal/continue
post-body state recurses. Break exits; false/error paths and the intrinsic
leave exclusion remain unchanged. No coherence, projection or supplied child
simulation/termination law is assumed.
Nine controls reuse inhabited control sequences followed by deep tails:
break exits at 5 with raw 2/257; a false-writing continue bypasses its tail
and exits at 7; normal mutation exits at 12 with false and untouched 257.
All three completed frames remain identical at every larger horizon.
A false guard skips the body at 2; the continue path at 6 still times out.
Concrete all-fuel Source agreement remains separately clean-start bounded.
These existing same-context certificates add no arbitrary statements/returns,
dirty Source readback, admission or compiler adequacy. Source/ExtCall/evaluators/
layouts, observations, expected outcomes and proof budgets are unchanged.
Full VY1/general P16 and final lane gates remain open.

Independent read-only finder and skeptic reviews report no findings.
Per-file diagnostics report zero errors; focused Lean, affected core build,
generated-root and layer checks pass. Eleven scoped axiom reports use only
Lean standard axioms. Raw failed standard automation remains separate from
passing concrete proofs; no statements, outcomes or checking limits changed.

### Concrete P16 loop-adapter horizons

`RawAdapterLoopHorizon.body_agrees` proves exact all-fuel driver equality
between the actual `RawSourceAdapter.body` factory instance and
`RawControlledWhile.run`, including errors and whole raw frames.
`successor` and `extension` transport concrete completed-frame stability
to the genuine typed `RawSourceAdapterLoop.loop` instance, preserving its
existing normal-flow mapping. The real intrinsic body certificate and
non-timeout premise remain explicit; no coherence, projection or caller-supplied
driver equality is assumed. This does not infer raw stability for arbitrary
adapters from their clean-Source `correct` field.
Nine controls inhabit actual P16 adapter types and exercise break/continue/
normal exits, raw 2/257 retention, larger-horizon whole-frame equality,
all-fuel driver agreement, early timeout and a false guard skipping the body.
The adapter's actual all-fuel Source correctness remains separately clean-start.
The initial alias rewrite failure is retained; exposing the identical concrete
adapter before rewriting fixes it without changing any statement/outcome/limit.
No Source/ExtCall/evaluator/layout/observation changes, general admission,
dirty Source readback or compiler adequacy are introduced.
Full VY1/general P16 and final lane gates remain open.

Independent read-only finder and skeptic reviews report no findings.
Per-file diagnostics report zero errors; focused Lean, affected core build,
generated-root and layer checks pass. Twelve scoped axiom reports use only
Lean standard axioms. Failed standard automation and the corrected concrete
alias rewrite remain raw evidence; statements, outcomes and limits unchanged.

### Concrete P16 sequence-loop adapter horizons

`RawAdapterSequenceLoopHorizon.block_agrees` proves exact all-fuel execution
equality for the actual block/sequence factory and control-block runner.
`body_agrees` composes that fact into exact concrete adapter/sequence-while
driver equality, including errors and raw frames. `successor` and
`extension` transport actual completed-frame stability to the genuine typed
P16 loop(block(sequence)) adapter. The real intrinsic item certificate and
original non-timeout premise remain explicit; no supplied driver equality,
coherence or projection law is assumed. No arbitrary-adapter raw stability is
inferred from the clean Source correctness field.
Nine controls inhabit actual P16 instances: break5 retains raw2/u8257;
mutating continue7 and normal12 exit with false and untouched257. Entire
completed frames stabilize at every larger horizon. Block/driver agreement
is checked at every fuel/raw state; early timeout6 remains distinct, and
actual Source correctness remains separately clean-start bounded.
No Source/ExtCall/evaluator/layout/observation or budget changes, general
admission, dirty Source readback or compiler adequacy are introduced.
Full VY1/general P16 and final lane gates remain open.

Independent read-only finder and skeptic reviews report no findings.
Per-file diagnostics report zero errors; focused Lean, affected core build,
generated-root and layer checks pass. Thirteen scoped axiom reports use only
Lean standard axioms. Standard automation failures remain raw evidence;
statements, outcomes and proof limits are unchanged.

### Concrete body-first adapter horizons

`RawDoWhileHorizon.successor` and `extension` prove exact completed-result
stability for the real do/while driver with the concrete body adapter factory.
`adapterSuccessor` and `adapterExtension` transport this to the genuine
intrinsic P16 do/while adapter, preserving the entire raw frame.
Body terminality comes from the actual parent result. Normal/continue evaluate
the condition on the actual postbody frame and recurse on the actual
postcondition frame; break bypasses the condition. The original intrinsic
body certificate and non-timeout premise remain explicit. No coherence,
projection, assumed child law or arbitrary-adapter raw stability is introduced.

Nine controls use actual typed adapters. Break3 preserves raw2/u8257 and
skips a guard that independently times out at fuel2. Continue5 writes false;
normal10 executes its mutating body even with a false guard. Both preserve
the sibling raw257. All three completed entire frames stabilize at every
larger horizon; normal9 remains timeout. Source correctness is checked
separately from a clean initial frame for every horizon.
No Source/ExtCall/evaluator/layout/observation/admission/dirty-readback/compiler
changes or adequacy claims are made. Full VY1/general P16 and final lane
gates remain open.

Independent read-only finder and skeptic core/final reviews report no
findings. Per-file diagnostics, focused checks, affected core build and
layer/root checks pass. Thirteen scoped axiom reports use only Lean standard
axioms. Standard tactic failures and the redundant solved-goal tactic failure
remain raw evidence; removing that redundant tactic changes no statement,
expected behavior or proof limit.
