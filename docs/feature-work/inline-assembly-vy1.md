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
