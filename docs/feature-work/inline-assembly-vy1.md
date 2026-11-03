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
