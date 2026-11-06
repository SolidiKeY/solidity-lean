#!/usr/bin/env node
// The core does not reach the elaborator: no core module imports, even
// transitively, a module of the source elaborator (`Syntax/{Elab,Quote,Splice}`)
// or of the printers and tactic front ends (`Calculus/{Print*,Surface*,
// TacticSyntax,Quote,NamedTerm}`). An edit to those then rebuilds the meta
// layer, the tactics and the examples, not the calculus and its soundness.
// The core is listed in `docs/parallelism.md`, "The core"; it is `CORE` below.
//
// Usage: node scripts/check-layers.mjs
// Exit 0 = no core module reaches the elaborator, 1 = at least one does
// (each printed with one import path down to it).
import { loadGraph, findPath, reach } from "./import-fanout.mjs";
import { loadAllowlist, closureViolations, closureGraph } from "./core-import-closure.mjs";

const CORE = [
  /^Solidity\.Yul\.(RawDoWhileHorizon|Checks\.RawDoWhileHorizon)$/, // Concrete body-first adapter completed-frame horizons.
  /^Solidity\.Yul\.(RawAdapterSequenceLoopHorizon|Checks\.RawAdapterSequenceLoopHorizon)$/, // Concrete P16 sequence-loop driver agreement and full-frame horizons.
  /^Solidity\.Yul\.(RawAdapterLoopHorizon|Checks\.RawAdapterLoopHorizon)$/, // Concrete body-factory P16 loop agreement and full-frame horizons.
  /^Solidity\.Yul\.(RawSequenceWhileHorizon|Checks\.RawSequenceWhileHorizon)$/, // Concrete sequence-bodied while full-frame horizons.
  /^Solidity\.Yul\.(RawControlledWhileHorizon|RawReadOnlyViews|Checks\.RawControlledWhileHorizon)$/, // Concrete controlled-while full-frame horizons and read-view laws.
  /^Solidity\.Yul\.(RawControlSequenceHorizon|Checks\.RawControlSequenceHorizon)$/, // Concrete raw control-sequence/block whole-frame horizons.
  /^Solidity\.Yul\.(RawLoopBodyHorizon|Checks\.RawLoopBodyHorizon)$/, // Concrete raw condition/control-body whole-frame horizons.
  /^Solidity\.Yul\.(RawSequenceHorizon|Checks\.RawSequenceHorizon)$/, // Concrete whole raw-frame sequence/block horizons.
  /^Solidity\.Yul\.(RawStatementHorizon|Checks\.RawStatementHorizon)$/, // Concrete whole raw-frame expression-statement horizons.
  /^Solidity\.Yul\.(LocalForFirstDone|Checks\.LocalForFirstDone)$/, // Concrete actual Source horizon-selector consequences.
  /^Solidity\.Yul\.(LocalForTimeout|Checks\.LocalForTimeout)$/, // Concrete full-for timeout classification and Source consequences.
  /^Solidity\.Yul\.(LocalForNoGuardFailure|Checks\.LocalForNoGuardFailure)$/, // Initialized omitted-guard finite noncompletion.
  /^Solidity\.Yul\.(LocalLoopReductions|Checks\.LocalLoopReductions)$/, // Exact constant-loop reductions and horizon results.
  /^Solidity\.Yul\.(LocalPostHorizon|Checks\.LocalPostHorizon)$/, // Concrete post/do-while finite-horizon laws.
  /^Solidity\.Yul\.(LocalLoopFailure|Checks\.LocalLoopFailure)$/, // Concrete scope/loop timeout and Source horizon laws.
  /^Solidity\.Yul\.(LocalItemFailure|Checks\.LocalItemFailure)$/, // Indexed statement and context-growing item failure classification.
  /^Solidity\.Yul\.(LocalU8Representation|Checks\.LocalU8Representation)$/, // Checked-u8 per-pipeline exact-result congruence.
  /^Solidity\.Yul\.(LocalU8Horizon|Checks\.LocalU8Horizon)$/, // Checked-u8 terminal fuel stability.
  /^Solidity\.Yul\.(LocalU8CompareHorizon|Checks\.LocalU8CompareHorizon)$/, // Checked-u8 comparison terminal fuel stability.
  /^Solidity\.Yul\.(LocalBoolHorizon|Checks\.LocalBoolHorizon)$/, // Boolean full-run terminal fuel stability.
  /^Solidity\.Yul\.(LocalCompareHorizon|Checks\.LocalCompareHorizon)$/, // Concrete comparison/Boolean conditional horizon composition.
  /^Solidity\.Yul\.(LocalItemHorizon|Checks\.LocalItemHorizon)$/, // Context-growing completed item fuel stability.
  /^Solidity\.Yul\.(LocalDefaultHorizon|Checks\.LocalDefaultHorizon)$/, // Heterogeneous default item/block completed fuel stability.
  /^Solidity\.Yul\.(LocalUncheckedHorizon|Checks\.LocalUncheckedHorizon)$/, // Existing unchecked scope/continuation completed fuel stability.
  /^Solidity\.Yul\.(LocalIfHorizon|Checks\.LocalIfHorizon)$/, // Independently typed conditional scope completed fuel stability.
  /^Solidity\.Yul\.(LocalWhileHorizon|Checks\.LocalWhileHorizon)$/, // Recursive default-scoped while completed fuel stability.
  /^Solidity\.Yul\.(LocalDoWhileHorizon|Checks\.LocalDoWhileHorizon)$/, // Body-first recursive do/while completed fuel stability.
  /^Solidity\.Yul\.(LocalForPostHorizon|Checks\.LocalForPostHorizon)$/, // Guard/body/post recursive completed fuel stability.
  /^Solidity\.Yul\.(LocalForInitHorizon|Checks\.LocalForInitHorizon)$/, // Concrete initializer/full-for completed horizon composition.
  /^Solidity\.Yul\.(LocalForNoPostHorizon|Checks\.LocalForNoPostHorizon)$/, // Concrete initialized no-post for completed horizon composition.
  /^Solidity\.Yul\.(LocalDefaultPostRepresentation|Checks\.LocalDefaultPostRepresentation)$/, // Default-scope post and omitted-guard congruence.
  /^Solidity\.Yul\.(LocalDefaultControlRepresentation|Checks\.LocalDefaultControlRepresentation)$/, // Independently indexed default branches and loops.
  /^Solidity\.Yul\.(LocalDefaultRepresentation|Checks\.LocalDefaultRepresentation)$/, // Heterogeneous default and unchecked exact-word congruence.
  /^Solidity\.Yul\.(LocalBoolForPostRepresentation|Checks\.LocalBoolForPostRepresentation)$/, // Concrete initializer/post-loop word congruence.
  /^Solidity\.Yul\.(LocalBoolPostRepresentation|Checks\.LocalBoolPostRepresentation)$/, // Exact-word post-iteration congruence.
  /^Solidity\.Yul\.(LocalBoolForRepresentation|Checks\.LocalBoolForRepresentation)$/, // Boolean initializer for-loop exact-word congruence.
  /^Solidity\.Yul\.(LocalBoolWhileRepresentation|Checks\.LocalBoolWhileRepresentation)$/, // Exact-word loop congruence.
  /^Solidity\.Yul\.(LocalBoolScopeRepresentation|Checks\.LocalBoolScopeRepresentation)$/, // Exact-word scope and conditional congruence.
  /^Solidity\.Yul\.(LocalBoolItemRepresentation|Checks\.LocalBoolItemRepresentation)$/, // Indexed context-growing exact-word relations.
  /^Solidity\.Yul\.(LocalBoolControlRepresentation|Checks\.LocalBoolControlRepresentation)$/, // Exact-word control congruence.
  /^Solidity\.Yul\.(LocalBoolRepresentation|Checks\.LocalBoolRepresentation)$/, // Exact-word local Boolean proof relation.
  /^Solidity\.Yul\.(LocalBoolFailure|Checks\.LocalBoolFailure)$/, // Exact failure classification for certified local Boolean evaluators.
  /^Solidity\.Yul\.(LocalDefaultNoGuard|Checks\.LocalDefaultNoGuard)$/, // Omitted-guard consumers of actual scoped runners.
  /^Solidity\.Yul\.(LocalDefaultPostIter|Checks\.LocalDefaultPostIter)$/, // Actual scoped for-iterations with discarded post values.
  /^Solidity\.Yul\.(LocalDefaultDoWhile|Checks\.LocalDefaultDoWhile)$/, // Actual body-first iteration of typed default scopes.
  /^Solidity\.Yul\.(LocalDefaultWhile|Checks\.LocalDefaultWhile)$/, // Concrete iteration of typed default scopes.
  /^Solidity\.Yul\.(LocalDefaultIfElse|Checks\.LocalDefaultIfElse)$/, // Conditional selection of typed default scopes.
  /^Solidity\.Yul\.(LocalItemWorld|Checks\.LocalItemWorld)$/, // World preservation for actual pure local runners.
  /^Solidity\.Yul\.(LocalDefaultUnchecked|Checks\.LocalDefaultUnchecked)$/, // Actual unchecked default-scope composition.
  /^Solidity\.Yul\.(LocalDefaultItems|Checks\.LocalDefaultItems)$/, // Typed constant-default declaration sequences.
  /^Solidity\.Yul\.(LocalDefaultBinding|Checks\.LocalDefaultBinding)$/, // Actual constant-default declaration/body composition.
  /^Solidity\.Yul\.(LocalBoolUnchecked|Checks\.LocalBoolUnchecked)$/, // Concrete unchecked and ordinary scope composition.
  /^Solidity\.Yul\.(LocalBoolForNoGuard|Checks\.LocalBoolForNoGuard)$/, // Exact omitted-guard transport and concrete adapters.
  /^Solidity\.Yul\.(LocalBoolPostIter|LocalBoolForPost|Checks\.LocalBoolForPost)$/, // Scoped Boolean for posts.
  /^Solidity\.Yul\.(LocalBoolDivergence|Checks\.LocalBoolDivergence)$/, // No finite normal completion of constant-true scoped loops.
  /^Solidity\.Yul\.(LocalBoolDoDivergence|Checks\.LocalBoolDoDivergence)$/, // No finite normal completion of literal-true do/while.
  /^Solidity\.Yul\.(LocalBoolFor|Checks\.LocalBoolFor)$/, // Context-growing Boolean for initializer and scoped body.
  /^Solidity\.Yul\.(LocalBoolDoWhile|Checks\.LocalBoolDoWhile)$/, // Body-first iteration of certified Boolean scopes.
  /^Solidity\.Yul\.(LocalBoolWhile|Checks\.LocalBoolWhile)$/, // Iteration of context-growing Boolean scopes.
  /^Solidity\.Yul\.Views\.NominalInventory(?:Laws|Controls)?$/, // Intrinsic nominal view inventory.
  /^Solidity\.Yul\.World\.SelfDestructBuiltin(?:Controls)?$/, // Typed builtin binding and controls.
  /^Solidity\.Yul\.(LocalBoolWhile|LocalBoolDivergence|Checks\.LocalBoolWhile|Checks\.LocalBoolDivergence)$/, // Typed loop checkpoints.
  /^Solidity\.Yul\.(LocalBoolIfElse|Checks\.LocalBoolIfElse)$/, // Conditional selection of independently indexed scopes.
  /^Solidity\.Yul\.(LocalBoolIf|Checks\.LocalBoolIf)$/, // Conditional execution of a certified Boolean item scope.
  /^Solidity\.Yul\.(LocalBoolItemScope|Checks\.LocalBoolItemScope)$/, // Typed Boolean item-list scope closure.
  /^Solidity\.Yul\.(LocalBoolItems|Checks\.LocalBoolItems)$/, // Intrinsic Boolean item-list composition.
  /^Solidity\.Yul\.(LocalBoolBinding|Checks\.LocalBoolBinding)$/, // Concrete context-growing declaration/body composition.
  /^Solidity\.Yul\.(LocalBoolScope|Checks\.LocalBoolScope)$/, // Concrete effectful Boolean initializer scope closure.
  /^Solidity\.Yul\.(LocalBoolInitialization|Checks\.LocalBoolInitialization)$/, // Concrete Boolean expression initialization.
  /^Solidity\.Yul\.(RawIntegerScope|Checks\.RawIntegerScope)$/, // Concrete integer initializer scope closure.
  /^Solidity\.Yul\.(RawIntegerInitialization|Checks\.RawIntegerInitialization)$/, // Concrete integer initialization.
  /^Solidity\.Yul\.(RawLiteralScope|Checks\.RawLiteralScope)$/, // Concrete literal initializer scope closure.
  /^Solidity\.Yul\.(RawLiteralInitialization|Checks\.RawLiteralInitialization)$/, // Concrete literal initialization.
  /^Solidity\.Yul\.(RawDefaultScope|Checks\.RawDefaultScope)$/, // Concrete constant-default scope composition.
  /^Solidity\.Yul\.(RawDefaultDeclaration|Checks\.RawDefaultDeclaration)$/, // Certified constant-default Source declarations.
  /^Solidity\.Yul\.(RawLocalScope|Checks\.RawLocalScope)$/, // Executed Boolean scope closure and Source adapter.
  /^Solidity\.Yul\.(RawLocalDeclaration|Checks\.RawLocalDeclaration)$/, // Context-growing Boolean local declaration.
  /^Solidity\.Yul\.(RawSourceReturnControl|Checks\.RawSourceReturnControl)$/, // Read-free Source return/control transport.
  /^Solidity\.Yul\.(RawSourceVoidReturn|Checks\.RawSourceVoidReturn)$/, // Source void-return transport.
  /^Solidity\.Yul\.(EvmBitwise|Checks\.EvmBitwise)$/, // Bitwise/comparison/shift/power correspondence.
  /^Solidity\.Yul\.(EvmArithmetic|Checks\.EvmArithmetic)$/, // Unsigned word/target correspondence.
  /^Solidity\.Yul\.(EvmSigned|Checks\.EvmSigned)$/, // Signed word/machine agreement.
  /^Solidity\.Yul\.RawSourceForPost$/, // Generated VY1 module registration.
  /^Solidity\.Yul\.Compilation\./, // Yul compilation (target-side combinators).
  /^Solidity\.Yul\.World\.(Raw|Observations|Frames|Lifecycle|Adapters|ByteMemory|AdapterRules|LifecycleAdapter|CreationFrames|CreationRules|CreationAddressing|ReturnSize)$/, // Yul world consumer core.
  /^Solidity\.Yul\.RawSourceAdapterFor$/, // Generated VY1 new-module registration.
  /^Solidity\.Yul\.RawSourceForIter$/, // Generated VY1 new-module registration.
  /^Solidity\.Yul\.RawSourceAdapterUnchecked$/, // Generated VY1 new-module registration.
  /^Solidity\.Yul\.RawSourceAdapterDoWhile$/, // Generated VY1 new-module registration.
  /^Solidity\.Yul\.RawSourceAdapterIfElse$/, // Generated VY1 new-module registration.
  /^Solidity\.Yul\.(RawCondition|RawIfElse|RawIfThen|RawWhile|RawLoopBody|RawControlledWhile|RawControlSequence|RawSequenceWhile|RawSourceAdapter|RawSourceAdapterLoop)$/, // VY1 concrete conditional Source transport.
  /^Solidity\.Yul\.(RawCoherent|RawSequence)$/, // VY1 actual coherent Source block transport.
  /^Solidity\.Yul\.RawSource$/, // VY1 additive actual Source statement adapter.
  /^Solidity\.Yul\.(RawFrame|RawBoundary)$/, // VY1 H11 raw frame and explicit return boundary.
  /^Solidity\.Yul\.BuiltinUse$/, // VY1 independent bare-builtin-use judgement.
  /^Solidity\.Yul\.StatementTags$/, // VY1 intrinsic constructor metadata.
  /^Solidity\.Yul\.TypingStatements$/, // VY1 actual direct statement certificate observer.
  /^Solidity\.Yul\.TypingTargetPaths$/, // VY1 original target certificate/path laws.
  /^Solidity\.Yul\.TypingLeafPaths$/, // VY1 exact relative leaf-path transport.
  /^Solidity\.Yul\.(TypingLeaves|TypingLeafScope)$/, // VY1 intrinsic typed leaves and scoped preservation.
  /^Solidity\.Yul\.TypingSites$/, // VY1 actual typing-context site observer.
  /^Solidity\.Yul\.(LocalExprStatement|Checks\.LocalExprStatement)$/, // VY1 actual Source expression statements.
  /^Solidity\.Yul\.(LocalCompareControl|Checks\.LocalCompareControl)$/, // VY1 comparison-selected LOCAL control.
  /^Solidity\.Yul\.(LocalU8Compare|Checks\.LocalU8Compare)$/, // VY1 actual Source u8 comparisons.
  /^Solidity\.Yul\.(OpenFunctions|OpenRun|OpenAgreement|OpenExpressionAgreement|OpenStatementAgreement|OpenCasesAgreement|OpenLoopAgreement|OpenComposition|OpenCalculus|OpenScoped|OpenLocal|Checks\.(OpenRun|OpenControls))$/, // VY1 full independent AST execution.
  /^Solidity\.Yul\.(LocalCoordinates|CoordinateUpdates|CoordinateControl|DirectBindings|Checks\.DirectBindings)$/, // VY1 concrete direct binder composition.
  /^Solidity\.Yul\.(DirectControl|Checks\.DirectControl)$/, // VY1 actual direct sequencing/control composition.
  /^Solidity\.Yul\.(DirectUpdates|Checks\.DirectUpdates)$/, // VY1 direct raw assignment transport.
  /^Solidity\.Yul\.(DirectWords|Checks\.DirectWords)$/, // VY1 direct original-AST expression agreement.
  /^Solidity\.Yul\.(LocalU8Expr|LocalU8Source|LocalU8Agreement|Checks\.LocalU8Expr)$/, // VY1 checked Source u8 consumer.
  /^Solidity\.Yul\.(LocalBoolControl|LocalBoolControlSource|LocalBoolControlAgreement|LocalBoolControlEvidence|Checks\.LocalBoolControl)$/, // VY1 actual Source short-circuit consumer.
  /^Solidity\.Yul\.(LocalBoolExpr|LocalBoolAgreement|Checks\.LocalBoolExpr)$/, // VY1 actual Source bool/local consumer.
  /^Solidity\.Yul\.(LocalOperations|Checks\.LocalOperations)$/, // VY1 explicit LOCAL operation boundaries.
  /^Solidity\.Yul\.(LocalBlockLogic|Checks\.(LocalBlockLogic|LocalBlockDivergence))$/, // VY1 concrete LOCAL modal bridge.
  /^Solidity\.Yul\.(LocalWordWrite|LocalWriteback|LocalBlock|Checks\.LocalBlock)$/, // VY1 actual pure-local block/writeback.
  /^Solidity\.Yul\.(CleanFunctions|LocalWordView|Checks\.LocalWordView)$/, // VY1 actual Source pure-local word view.
  /^Solidity\.Yul\.(CleanLocals|Checks\.CleanLocals)$/, // VY1 actual clean Source scalar initialization.
  /^Solidity\.Yul\.(LocalState|Checks\.LocalState)$/, // VY1 actual Source state/clean bridge.
  /^Solidity\.Yul\.(LocalValues|Checks\.LocalValues)$/, // VY1 intrinsic raw LOCAL extension.
  /^Solidity\.Yul\.(SourceBoundary|Checks\.SourceBoundary)$/, // VY1 exact clean Source representation boundary.
  /^Solidity\.Yul\.(WordInputs|WordAdapter|WordAdapterLogic|ScopedWordSyntax|Checks\.(WordAdapterFixtures|WordAdapterCode|WordAdapter|RawWordLogic|RawDivergence))$/, // VY1 actual pure raw-cell execution/rules.
  /^Solidity\.Yul\.(WordLocals|Checks\.WordLocals)$/, // VY1 concrete logical raw-word/local bijection.
  /^Solidity\.Yul\.(WordCells|Checks\.WordCells)$/, // VY1 logical raw mutable word fields.
  /^Solidity\.Yul\.(ScopedSyntax|Checks\.ScopedSyntax)$/, // VY1 combined scoped static/tier preparation.
  /^Solidity\.Yul\.(BlockScope|ScopedBlockTyping|Checks\.ScopedBlocks)$/, // VY1 single shared scoped checker/extraction.
  /^Solidity\.Yul\.(OccurrenceCheck|OccurrenceSyntax|Checks\.Occurrences)$/, // VY1 original local-variable occurrence isolation.
  /^Solidity\.Yul\.(ScopedAssignments|Checks\.ScopedAssignments)$/, // VY1 actual assignment namespace composition.
  /^Solidity\.Yul\.BlockEnvironment$/, // VY1 unchanged shared block-name environment.
  /^Solidity\.Yul\.(ScopedExpressions|Checks\.ScopedExpressions)$/, // VY1 supplemental expression namespace certificates.
  /^Solidity\.Yul\.(ExternalKeys|ScopedNames|Checks\.ScopedNames)$/, // VY1 constructed scoped external-name inputs.
  /^Solidity\.Yul\.(BlockExtract|BlockExtractLogic|WordPolicy|WordSyntax|Checks\.BlockExtract|Checks\.WordSyntax|Checks\.ExtractDivergence)$/, // VY1 actual closed source extraction/composition.
  /^Solidity\.Yul\.(BlockTyping|ClosedSyntax|Checks\.BlockTyping)$/, // VY1 constructed closed-root typing.
  /^Solidity\.Yul\.(DeclarationScope|Checks\.DeclarationScopes)$/, // VY1 whole-block declaration visibility.
  /^Solidity\.Yul\.(WordArguments|WordExpressions|Checks\.WordExpressions)$/, // VY1 actual expression/call composition.
  /^Solidity\.Yul\.(WordLoops|WordCoverage|Checks\.WordLoops)$/, // VY1 loop composition/closed statement coverage.
  /^Solidity\.Yul\.(WordSwitch|Checks\.WordSwitch)$/, // VY1 actual switch composition.
  /^Solidity\.Yul\.(WordBranches|Checks\.WordBranches)$/, // VY1 actual branch/binder composition.
  /^Solidity\.Yul\.(WordTerms|Checks\.WordTerms)$/, // VY1 actual RHS modal composition.
  /^Solidity\.Yul\.(LocalProjection|Checks\.LocalProjection)$/, // VY1 total raw scalar projection.
  /^Solidity\.Yul\.(SourceContext|Checks\.SourceContext)$/, // VY1 concrete Source local contexts.
  /^Solidity\.Yul\.(ScalarLocals|Checks\.ScalarLocals)$/, // VY1 intrinsic scalar projections.
  /^Solidity\.Yul\.(WordLogic|WordRules|WordNotation|WordAgreement|Checks\.WordLogic)$/, // VY1 closed word logic.
  /^Solidity\.Yul\.(WordUpdates|Checks\.WordUpdates)$/, // VY1 exact local word updates.
  /^Solidity\.Yul\.(SourceTypes|Checks\.SourceTypes)$/, // VY1 declaration-backed local shapes.
  /^Solidity\.Yul\.(SourceBindings|Checks\.SourceBindings)$/, // VY1 actual S01 local identities.
  /^Solidity\.Yul\.(ExternalScope|Checks\.ExternalScopes)$/, // VY1 nested external contexts.
  /^Solidity\.Yul\.(PlacementCheck|Checks\.Placement)$/, // VY1 source control placement.
  /^Solidity\.Yul\.ReservedNames$/, // VY1 pinned inline identifier reservations.
  /^Solidity\.Yul\.(DeclarationCheck|Checks\.Declarations)$/, // VY1 declaration legality.
  /^Solidity\.Yul\.(TierPolicy|Checks\.Tiers)$/, // VY1 intrinsic tier policy.
  /^Solidity\.Yul\.(AssignmentCheck|Checks\.Assignments)$/, // VY1 assignment checking.
  /^Solidity\.Yul\.(ClosedHorizon|HorizonAdapter|Checks\.Horizons)$/, // VY1 horizon proofs/adapters.
  /^Solidity\.Yul\.(ClosedRun|Checks\.ClosedRun)$/, // VY1 closed word execution.
  /^Solidity\.Yul\.(ClosedPure|ClosedProfile|Checks\.ClosedPure)$/, // VY1 word effect profiles.
  /^Solidity\.Yul\.(ClosedFunctions|Checks\.ClosedFunctions)$/, // VY1 finite lexical environments.
  /^Solidity\.Yul\.(BlockHeaders|Checks\.Headers)$/, // VY1 direct syntax-to-header collection.
  /^Solidity\.Yul\.(ExternalCheck|GlobalExternal|Checks\.External|Checks\.GlobalExternal)$/, // VY1 checked external resolution.
  /^Solidity\.Yul(?:$|\.(?:Builtins|Words|WordLaws|Syntax|Static|CatalogLaws|ExpressionCheck|LocalScope|FunctionScope)$|\.Checks\.(?:(?:Arithmetic|Shifts)(?:\.Part[0-9][0-9])?|Bytes|Powers|Static|Contracts|Expressions|Scope)$)/, // Intrinsic assembly core; frontend adapters stay separate.
  /^Solidity\.Yul\.Composition\./, // VY5 intrinsic producer-bound consumer proofs.
  /^Solidity\.(KeySort|Eqns|AST|TypeGraph|Scope|SpecSyntax|Hashes|Keccak|ERC7201|Secp256k1|RevertBytes|Syntax|Semantics|Signature|Update)$/,
  /^Solidity\.Syntax\.(Raw|Grammar|Contract|Scoped|Checked|Inlined|PushSource|Join)$/,
  /^Solidity\.(Semantics|Typing|Theory)\./,
  /^Solidity\.Calculus\.(Fml|Rules|RuleSyntax|RuleKit|KeyTaclets|Step|Arms|Blocks|Taclet|Proves|Logic|Preconditions|FiniteMembership|FilteredMembership|Hyp|Correct|FirstOrder|Transient|Lifetime|ContractWorld|PaymentWitness|PaymentConditions)$/,
  /^Solidity\.Calculus\.(Sound.*|StmtSound|ProvesSound|PremiseSound|UpdRuleScoped|UpdateRules|TermLib\.Rules)$/,
  /^Solidity\.Calculus\.StaticInvocation$/, // Intrinsic static callback transport.
  // Owned intrinsic capture/join producers: their imports stay below elaborators.
  /^Solidity\.Calculus\.(AnonLocalCapture|CallResultCapture|CallResultRestore|JoinSequence|JoinSequenceSize)$/,
  /^Solidity\.Calculus\.RuleSyntax\./,
  /^Solidity\.Roadmap\./, // The roadmap's contracts are statements below the elaborator.
  /^Solidity\.Hash\.CollisionBound$/,
  /^Solidity\.Backend\.(Opcode|Jumpdest|Assembler|Control)$/,
  /^Solidity\.Hash\.Adaptive$/,
  /^Solidity\.Storage\.HashedLayout$/,
  /^Solidity\.Storage\.HashedKeccak$/,
  /^Solidity\.Storage\.HashedSeparation$/,
  /^Solidity\.Calculus\.(TermEval|TermEq|TermWk|LoopInvariantWk|Lower|LowerRun|Shift|WkOver|Lands|StateFacts|ReadWrite|DataIn|SeqRewrite|SyntaxSize|Graft|CallSummary|KIntTwoAnchors)$/,
];
const ELABORATOR = [
  /^Solidity\.Yul\.WordPrint$/, // VY1 DSL printers stay outside the core.
  /^Solidity\.Tools\.SolCases$/, // External-source printer stays outside the core.
  /^Solidity\.Syntax\.(Elab|Quote|Splice)(\.|$)/,
  /^Solidity\.Calculus\.(Print[^.]*|Surface[^.]*|TacticSyntax|Quote|NamedTerm)(\.|$)/,
];

const PARSER_ADAPTER = [
  /^Solidity\.Frontend\.Yul(?:\.|$)/,
  /^Solidity\.Frontend\.Checked\.(Check|Parser)(?:\.|$)/,
  /^Solidity\.Yul\.(CheckedParse|DeclarationParse)$/,
  /^Solidity\.Yul\.Checks\.(Parsing|DeclarationParsing|ClosedSyntax)$/,
];
const { graph } = loadGraph();
const isCore = (m) => CORE.some((r) => r.test(m)) && !ELABORATOR.some((r) => r.test(m));
const isElab = (m) => ELABORATOR.some((r) => r.test(m));
const core = [...graph.keys()].filter(isCore).sort();
// The Yul parser shims moved out of CORE still must not reach the elaborator.
const yulShims = [...graph.keys()].filter((m) => /^Solidity\.Yul\./.test(m) && PARSER_ADAPTER.some((r) => r.test(m)) && !isCore(m)).sort();
let bad = 0;
for (const m of [...core, ...yulShims]) {
  const hit = [...reach(graph, m)].filter(isElab).sort()[0];
  if (!hit) continue;
  bad++;
  console.log(`LAYER  ${findPath(graph, m, hit).map((x) => x.replace(/^Solidity\./, "")).join(" → ")}`);
}
console.log(`${core.length} core modules, ${bad} reach the elaborator`);
let parserBad = 0;
for (const m of core) {
  const hit = [...reach(graph, m)].filter((n) => PARSER_ADAPTER.some((r) => r.test(n))).sort()[0];
  if (!hit) continue;
  parserBad++;
  console.log(`PARSER_LAYER  ${findPath(graph, m, hit).join(" → ")}`);
}
console.log(`${core.length} core modules, ${parserBad} reach the checked parser adapters`);
let closureBad = 0;
try {
  const allowed = loadAllowlist();
  const violations = closureViolations(closureGraph(graph), isCore, allowed);
  for (const path of violations) console.log(`CORE_CLOSURE  ${path.join(" → ")}`);
  closureBad = violations.length;
  console.log(`${core.length} core modules, ${closureBad} new core → non-core edges (${allowed.size} pinned allowances)`);
} catch (error) {
  console.error(`CORE_CLOSURE_BASELINE ${error.message}`);
  closureBad = 1;
}
process.exit(bad || parserBad || closureBad ? 1 : 0);
