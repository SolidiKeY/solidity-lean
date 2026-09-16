import Solidity.MultiStep
import Solidity.CandidateStep
import Solidity.Update.Merge
import Solidity.Update.SequentSyntax
import Solidity.Examples.SimpAttr

namespace Solidity.Examples

open Rules StandardExample SoliditySyntax SequentSyntax

/-! ### Alias helpers

The `sstmt!`/`splace!` macros map `"sp"` → `accountTy` and `"pp"` → `personTy`
via `localStorageTyFor`, but rules produce aliases typed to the *actual* path
type.  These abbreviations build correctly-typed alias terms; the `name@Type`
syntax they use is declared in `AST.lean`. -/

abbrev spExpr (ty : Ty) : WrappedExpr :=
  Rules.aliasExpr Kind.storage ty Rules.storagePathAliasName

abbrev spPlace (ty : Ty) : PlaceExpr :=
  Rules.aliasPlace Kind.storage ty Rules.storagePathAliasName

abbrev mvExpr (ty : Ty) : WrappedExpr :=
  Rules.aliasExpr Kind.memory ty Rules.memoryPathAliasName

abbrev mvPlace (ty : Ty) : PlaceExpr :=
  Rules.aliasPlace Kind.memory ty Rules.memoryPathAliasName

abbrev pvExprK (kind : Kind) (ty : Ty) : WrappedExpr :=
  Rules.aliasExpr kind ty Rules.valueAliasName

abbrev pvPlaceK (kind : Kind) (ty : Ty) : PlaceExpr :=
  Rules.aliasPlace kind ty Rules.valueAliasName

abbrev idxExpr (ty : Ty) : WrappedExpr :=
  Rules.aliasExpr Kind.stack ty Rules.indexAliasName

/-- The frozen value operand `rv` that `Rules.freezeRhs` binds ahead of every
target capture (`Counterexamples/EvaluationOrder.lean`,
`Counterexamples/ErrorOrder.lean`).

**Prefer the notation.** `rv` has explicit `rootExpr`/`rootPlace` arms, so a
derivation writes `solbox!{ uint rv = e; ...; p = rv }` and never needs these.
They are here for the same reason as `idxExpr` and `spExpr`: stating a residual
whose type is not fixed to `uint`. -/
abbrev rvExpr (ty : Ty) : WrappedExpr :=
  Rules.aliasExpr Kind.stack ty Rules.rhsValueAliasName

abbrev rvPlace (ty : Ty) : PlaceExpr :=
  Rules.aliasPlace Kind.stack ty Rules.rhsValueAliasName

abbrev rvUint : WrappedExpr := rvExpr Ty.uint

/-! ### Numeric constant helpers

The `sol_expr` syntax category only accepts identifiers, not numeric literals.
These abbreviations let us refer to constant values by name. -/

abbrev val (n : String) : WrappedExpr := SoliditySyntax.rootExpr n

/-! ### Proof automation for step-case navigation -/

-- Make rule infrastructure, effect constructors, boolean predicates, and AST
-- constructors all reducible so `decide` can synthesise `Decidable` instances
-- through the full evaluation chain: stepCase → ruleEffect →
-- assignEffect/... → condition match → boolean predicates.
set_option allowUnsafeReducibility true in
attribute [reducible]
  -- Rule infrastructure
  Rules.stepCase Rules.ruleEffect
  -- Effect constructors
  assignEffect deleteEffect storageDeclEffect memoryDeclEffect pushEffect popEffect
  stackDeclEffect compoundAssignEffect exprEffect assertEffect requireEffect
  iteEffect transferEffect revertEffect callEffect
  pushAssignEffect pushFieldAssignEffect storagePlaceAliasEffect
  Rules.captureFirstComplexArg SoliditySyntax.expandCall
  SoliditySyntax.funDef SoliditySyntax.paramDecls SoliditySyntax.retDecl
  -- Mode checking
  withMode CaseMode.applies SolidityModality.appliesCaseMode
  -- Predicate wrappers (Rules namespace)
  Rules.isLocal Rules.isGlobal Rules.isStorage Rules.isStack
  Rules.isSimple Rules.isComplex Rules.isMemory Rules.isPrimitive Rules.isIdentity
  Rules.isArray Rules.isMapping
  -- Boolean functions on expressions (Typed.WrappedExpr)
  Typed.WrappedExpr.simple Typed.WrappedExpr.complex Typed.WrappedExpr.complexCount
  Typed.WrappedExpr.kind Typed.WrappedExpr.ty
  Typed.WrappedExpr.isComplex Typed.WrappedExpr.isSimpleAtom
  Typed.WrappedExpr.isStack Typed.WrappedExpr.isStorage Typed.WrappedExpr.isMemory
  Typed.WrappedExpr.isLocal Typed.WrappedExpr.isGlobal
  Typed.WrappedExpr.isPrimitive Typed.WrappedExpr.isIdentity
  -- Delegating wrappers (WrappedExpr namespace)
  WrappedExpr.isComplex WrappedExpr.kind
  -- Type and field predicates
  Ty.isPrimitive Field.isPrimitive Field.isIdentity
  Field.sort Ty.fieldSort RefTy.fieldSort
  -- AST smart constructors
  SoliditySyntax.varExpr SoliditySyntax.varPlace
  SoliditySyntax.rootPlace SoliditySyntax.rootExpr
  SoliditySyntax.fieldExpr SoliditySyntax.fieldPlace
  SoliditySyntax.fieldTy SoliditySyntax.fieldForName
  -- `name@@Type` state variables: added for the calculus-example derivations,
  -- which name the calculus's auxiliary globals this way rather than widening
  -- `rootExpr` (see the note at `AST.lean`'s `globalExpr`).
  SoliditySyntax.globalExpr SoliditySyntax.globalPlace
  SoliditySyntax.pushPlace SoliditySyntax.pushPlaceExpr
  -- The running structs, so `Ty.isPrimitive accountTy` (and hence
  -- `Rules.valueCaptureKind` on a struct-typed capture) reduces.
  StandardExample.personTy StandardExample.accountTy StandardExample.tokenTy
  StandardExample.personRef StandardExample.accountRef StandardExample.tokenRef
  StandardExample.stackUint StandardExample.stackBool
  StandardExample.stackUintPlace StandardExample.stackIntPlace StandardExample.stackBoolPlace
  StandardExample.memoryPerson StandardExample.memoryPersonPlace
  StandardExample.storagePersonPlace
  PlaceExpr.var PlaceExpr.field PlaceExpr.index PlaceExpr.pushPlace
  -- Alias and capture infrastructure (for skip/condition evaluation)
  Rules.aliasField Rules.aliasExpr Rules.aliasPlace
  Rules.storagePathAliasName Rules.memoryPathAliasName
  Rules.valueAliasName Rules.indexAliasName
  Rules.valueAlias Rules.indexAlias Rules.storageAlias Rules.memoryAlias
  Rules.capture Rules.captureValue Rules.valueCaptureKind
  Rules.captureStoragePath
  Rules.captureMemoryPath Rules.captureIndex
  Rules.isStackVar Rules.captureStackValue Rules.stackValueAlias
  Rules.captureRhsValue Rules.rhsValueAlias
  Rules.valueRhsCaptureRhs
  Rules.fieldFromAlias Rules.indexFromAlias Rules.asPlace?
  -- Block builders (for effect type matching)
  Rules.fieldWriteResolveBlock Rules.indexWriteResolveBlock
  Rules.fieldReadResolveBlock Rules.indexReadResolveBlock
  Rules.captureAssignBlock Rules.captureIndexTargetBlock
  Rules.storageDeleteComplexTargetBlock Rules.memoryDeleteComplexTargetBlock
  -- Delete target predicates
  Rules.isSimpleStorageDeleteTarget Rules.isSimpleMemoryDeleteTarget
  Rules.isComplexStorageDeleteTarget Rules.isComplexMemoryDeleteTarget
  -- Index operations
  SoliditySyntax.indexExpr SoliditySyntax.indexPlace SoliditySyntax.indexElemTy
  Ty.indexElemTy Ty.isReference PlaceExpr.index
  -- Operator and alias smart constructors (value-capture rules)
  SoliditySyntax.binopExpr SoliditySyntax.unopExpr SoliditySyntax.incDecExpr
  SoliditySyntax.ternaryExpr
  SoliditySyntax.intLitExpr SoliditySyntax.aliasExpr SoliditySyntax.aliasPlace
  SoliditySyntax.aliasKind SoliditySyntax.declTy SoliditySyntax.typedVarTy

/-- Decide the `ifElseUnfold` negation guard by case analysis on
the condition shape, so the step-case search can skip that rule when
stepping with `ifElseTrue`/`ifElseFalse`/`ifElseNegated`. -/
instance (c : WrappedExpr) :
    Decidable (∀ inner, c = WrappedExpr.unop UnOp.not inner →
      Rules.isComplex inner) :=
  match c with
  | .mkUnop UnOp.not inner =>
      if h : Rules.isComplex inner then
        .isTrue fun _ hi => by injection hi with _ harg; exact harg ▸ h
      else
        .isFalse fun hall => h (hall inner rfl)
  | .mkUnop UnOp.neg _ =>
      .isTrue fun _ hi => by injection hi with hop _; exact nomatch hop
  | .var .. => .isTrue fun _ hi => nomatch hi
  | .field .. => .isTrue fun _ hi => nomatch hi
  | .index .. => .isTrue fun _ hi => nomatch hi
  | .pushPlace _ => .isTrue fun _ hi => nomatch hi
  | .bool _ => .isTrue fun _ hi => nomatch hi
  | .intLit _ _ => .isTrue fun _ hi => nomatch hi
  | .mkCall .. => .isTrue fun _ hi => nomatch hi
  | .mkBinop .. => .isTrue fun _ hi => nomatch hi
  | .mkIncDec .. => .isTrue fun _ hi => nomatch hi
  | .mkTernary .. => .isTrue fun _ hi => nomatch hi

-- Shared simp set for reducing rule effects and AST constructors, registered
-- once under the `rule_simp_set` attribute (see `SimpAttr.lean`) so that each
-- `rule_simp` invocation reuses the prebuilt discrimination tree instead of
-- re-elaborating the ~100-lemma list.
attribute [rule_simp_set]
  Rules.stepCase Rules.ruleEffect
  StepEffect.block StepEffect.mainBlock
  Rules.unfoldGoal Rules.terminalGoal Rules.splitGoals Rules.obligation
  Rules.revertGoals Rules.withOrigin Rules.writeBack Rules.compoundGoals
  Rules.compoundIndexGoals Rules.incDecGoals Rules.assertGoals Rules.varName
  assignEffect deleteEffect storageDeclEffect memoryDeclEffect
  pushEffect popEffect pushAssignEffect pushFieldAssignEffect
  storagePlaceAliasEffect
  stackDeclEffect compoundAssignEffect exprEffect assertEffect
  requireEffect iteEffect transferEffect revertEffect callEffect
  Rules.captureFirstComplexArg SoliditySyntax.expandCall
  SoliditySyntax.funDef SoliditySyntax.paramDecls SoliditySyntax.retDecl
  withMode CaseMode.applies
  SolidityModality.appliesCaseMode
  SoliditySyntax.varExpr SoliditySyntax.varPlace
  SoliditySyntax.rootPlace SoliditySyntax.rootExpr
  SoliditySyntax.fieldExpr SoliditySyntax.fieldPlace
  SoliditySyntax.fieldTy SoliditySyntax.fieldForName
  SoliditySyntax.globalExpr SoliditySyntax.globalPlace
  SoliditySyntax.pushPlace SoliditySyntax.pushPlaceExpr
  StandardExample.personTy StandardExample.accountTy StandardExample.tokenTy
  StandardExample.personRef StandardExample.accountRef StandardExample.tokenRef
  StandardExample.stackUint StandardExample.stackBool
  StandardExample.stackUintPlace StandardExample.stackIntPlace
  StandardExample.stackBoolPlace
  StandardExample.memoryPerson StandardExample.memoryPersonPlace
  StandardExample.storagePersonPlace
  PlaceExpr.var PlaceExpr.field PlaceExpr.index PlaceExpr.pushPlace
  Typed.WrappedExpr.kind Typed.WrappedExpr.ty
  Rules.aliasField Rules.aliasExpr Rules.aliasPlace
  Rules.storagePathAliasName Rules.memoryPathAliasName
  Rules.valueAliasName Rules.indexAliasName
  Rules.valueAlias Rules.indexAlias Rules.storageAlias Rules.memoryAlias
  Rules.capture Rules.captureValue Rules.valueCaptureKind
  Rules.captureStoragePath
  Rules.captureMemoryPath Rules.captureIndex
  Rules.isStackVar Rules.captureStackValue Rules.stackValueAlias
  Rules.captureRhsValue Rules.rhsValueAlias
  Rules.valueRhsCaptureRhs
  Rules.fieldFromAlias Rules.indexFromAlias Rules.asPlace?
  Rules.fieldWriteResolveBlock Rules.indexWriteResolveBlock
  Rules.fieldReadResolveBlock Rules.indexReadResolveBlock
  Rules.captureAssignBlock Rules.captureIndexTargetBlock
  Rules.storageDeleteComplexTargetBlock Rules.memoryDeleteComplexTargetBlock
  Rules.isSimpleStorageDeleteTarget Rules.isSimpleMemoryDeleteTarget
  Rules.isComplexStorageDeleteTarget Rules.isComplexMemoryDeleteTarget
  Rules.isArray Rules.isMapping
  SoliditySyntax.indexExpr SoliditySyntax.indexPlace SoliditySyntax.indexElemTy
  Ty.indexElemTy Ty.isReference PlaceExpr.index
  SoliditySyntax.binopExpr SoliditySyntax.unopExpr SoliditySyntax.incDecExpr
  SoliditySyntax.ternaryExpr
  SoliditySyntax.intLitExpr SoliditySyntax.aliasExpr SoliditySyntax.aliasPlace
  SoliditySyntax.aliasKind SoliditySyntax.declTy SoliditySyntax.typedVarTy

-- The sequent layer's own reduction: a successor frontier is
-- `goalSequents ... (goals lhs h) ++ after`, and it has to come back as a
-- literal list of `Sequent`s before the next step's `firstOpen?` can whnf
-- through it. Indexed by head symbol, so this costs the block layer nothing.
attribute [rule_simp_set]
  Update.goalSequents Update.addGuard Update.pushUpd
  Frontier.firstOpen? Sequent.isOpen
  -- The guard of an operator family is `if op.needsGuard then … else ⊤`, and
  -- only the sequent layer ever looks at it: `StepEffect.mainBlock` drops
  -- guards, so the block layer never had to reduce this.
  BinOp.needsGuard

macro "rule_simp" : tactic => `(tactic| simp only [rule_simp_set])

/-- The former literal spelling of `rule_simp`, kept for reference and for any
site that needs the list without the attribute. -/
macro "rule_simp_literal" : tactic => `(tactic|
  simp only [Rules.stepCase, Rules.ruleEffect,
    StepEffect.block, StepEffect.mainBlock,
    Rules.unfoldGoal, Rules.terminalGoal, Rules.splitGoals, Rules.obligation,
    Rules.revertGoals, Rules.withOrigin, Rules.writeBack, Rules.compoundGoals,
    Rules.compoundIndexGoals, Rules.incDecGoals, Rules.assertGoals, Rules.varName,
    assignEffect, deleteEffect, storageDeclEffect, memoryDeclEffect,
    pushEffect, popEffect,
    stackDeclEffect, compoundAssignEffect, exprEffect, assertEffect,
    requireEffect, iteEffect, transferEffect, revertEffect, callEffect,
    Rules.captureFirstComplexArg, SoliditySyntax.expandCall,
    SoliditySyntax.funDef, SoliditySyntax.paramDecls, SoliditySyntax.retDecl,
    withMode, CaseMode.applies,
    SolidityModality.appliesCaseMode,
    SoliditySyntax.varExpr, SoliditySyntax.varPlace,
    SoliditySyntax.rootPlace, SoliditySyntax.rootExpr,
    SoliditySyntax.fieldExpr, SoliditySyntax.fieldPlace,
    SoliditySyntax.fieldTy, SoliditySyntax.fieldForName,
    StandardExample.stackUint, StandardExample.stackBool,
    StandardExample.stackUintPlace, StandardExample.stackIntPlace,
    StandardExample.stackBoolPlace,
    StandardExample.memoryPerson, StandardExample.memoryPersonPlace,
    StandardExample.storagePersonPlace,
    PlaceExpr.var, PlaceExpr.field,
    Typed.WrappedExpr.kind, Typed.WrappedExpr.ty,
    -- Alias and capture infrastructure
    Rules.aliasField, Rules.aliasExpr, Rules.aliasPlace,
    Rules.storagePathAliasName, Rules.memoryPathAliasName,
    Rules.valueAliasName, Rules.indexAliasName,
    Rules.valueAlias, Rules.indexAlias, Rules.storageAlias, Rules.memoryAlias,
    Rules.capture, Rules.captureValue, Rules.valueCaptureKind,
    Rules.captureStoragePath,
    Rules.captureMemoryPath, Rules.captureIndex,
    Rules.isStackVar, Rules.captureStackValue, Rules.stackValueAlias,
    Rules.valueRhsCaptureRhs,
    Rules.fieldFromAlias, Rules.indexFromAlias, Rules.asPlace?,
    -- Block builders
    Rules.fieldWriteResolveBlock, Rules.indexWriteResolveBlock,
    Rules.fieldReadResolveBlock, Rules.indexReadResolveBlock,
    Rules.captureAssignBlock, Rules.captureIndexTargetBlock,
    Rules.storageDeleteComplexTargetBlock, Rules.memoryDeleteComplexTargetBlock,
    -- Delete target predicates
    Rules.isSimpleStorageDeleteTarget, Rules.isSimpleMemoryDeleteTarget,
    Rules.isComplexStorageDeleteTarget, Rules.isComplexMemoryDeleteTarget,
    Rules.isArray, Rules.isMapping,
    -- Index operations
    SoliditySyntax.indexExpr, SoliditySyntax.indexPlace, SoliditySyntax.indexElemTy,
    Ty.indexElemTy, Ty.isReference, PlaceExpr.index,
    -- Operator and alias smart constructors (value-capture rules)
    SoliditySyntax.binopExpr, SoliditySyntax.unopExpr, SoliditySyntax.incDecExpr,
    SoliditySyntax.ternaryExpr,
    SoliditySyntax.intLitExpr, SoliditySyntax.aliasExpr, SoliditySyntax.aliasPlace,
    SoliditySyntax.aliasKind, SoliditySyntax.declTy, SoliditySyntax.typedVarTy])

/-- Recursively find the first applicable step case in the rule list.
    Phase 1: `dsimp` unfolds `stepCases` through chained definitions into `_ :: _`.
             Uses `dsimp` because Lean 4 compiles large list literals with
             `have y := ...` sharing; `dsimp` performs zeta-reduction to flatten them.
    Phase 2: recursively tries `.here` or `.there` with `rule_simp; decide`. -/
syntax "find_first_step" : tactic
syntax "find_first_step_aux" : tactic

macro_rules
  | `(tactic| find_first_step) => `(tactic|
    (dsimp only [Rules.stepCases, Rules.rules, Rules.ruleCases,
       Rules.ruleNames, List.map]
     find_first_step_aux))

macro_rules
  | `(tactic| find_first_step_aux) => `(tactic|
    first
    | exact FirstStepCase.here (by rule_simp)
        (by rule_simp <;> (try simp) <;> decide)
    | exact FirstStepCase.there
        (by rule_simp <;> (try simp) <;> decide)
        (by find_first_step_aux))

/-- Like `find_first_step`, but for goals whose step case (and block) are
already pinned: wrong rules fail on index unification before any tactic
runs, so the target rule's condition proof may use `all_goals decide`
(tolerating conditions that `rule_simp` closes outright, e.g. `ifElseTrue`
on a literal condition). -/
syntax "find_pinned_step" : tactic
syntax "find_pinned_step_aux" : tactic

macro_rules
  | `(tactic| find_pinned_step) => `(tactic|
    first
    -- Exclusivity route (CandidateStep.lean): once the pinned rule applies, no
    -- other rule can, so no per-rule skip proofs are needed. Membership and
    -- the mode check are `decide`-fast; only the rule's own condition needs
    -- the simp+decide treatment.
    | exact UniquenessAux.firstStepCase_box (by decide) (by decide)
        (by rule_simp <;> (try simp) <;> decide)
    | exact UniquenessAux.firstStepCase_diamond (by decide) (by decide)
        (by rule_simp <;> (try simp) <;> decide)
    -- Legacy positional walk, kept as a fallback (e.g. `.both` blocks).
    | (dsimp only [Rules.stepCases, Rules.rules, Rules.ruleCases,
         Rules.ruleNames, List.map]
       find_pinned_step_aux))

macro_rules
  | `(tactic| find_pinned_step_aux) => `(tactic|
    first
    | exact FirstStepCase.here (by rule_simp)
        (by rule_simp <;> (try simp) <;> decide)
    | exact FirstStepCase.there
        (by rule_simp <;> (try simp) <;> decide)
        (by find_pinned_step_aux))

/-- Solve a single `BlockReflMultiStep` calc step.
    Handles rule-backed steps (via `find_first_step`) and reflexivity. -/
syntax "block_step" : tactic

macro_rules
  | `(tactic| block_step) => `(tactic|
    first
    | exact BlockReflMultiStep.refl
    | (set_option maxRecDepth 4096 in
       exact BlockReflMultiStep.step
        (.head (.ofStepCase (by find_first_step))) .refl))

open Lean Elab Tactic Meta in
/-- Solve a single `BlockStep` calc step by applying the *named* rule.
    The rule name pins the step case, `find_pinned_step` verifies
    that no earlier rule in `Rules.stepCases` applies, and the written
    successor state is checked definitionally against the rule's block.
    Needed when the successor block cannot be inferred by unification
    (the unifier cannot invert `?block ++ rest =?= literal`). -/
elab "named_step " rule:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
   withOptions (fun o => maxRecDepth.set o 32768) do
    let goalType ← goal.getType
    unless goalType.isAppOf ``BlockStep do
      throwError "named_step: expected a BlockStep goal, got {goalType}"
    let gargs := goalType.getAppArgs
    let src ← whnf gargs[0]!
    unless src.isAppOfArity ``SolidityBlock.mk 2 do
      throwError "named_step: cannot destructure source block {src}"
    let sm := src.getAppArgs[0]!
    let stmts ← whnf src.getAppArgs[1]!
    unless stmts.isAppOfArity ``List.cons 3 do
      throwError "named_step: source block has no head statement"
    let head := stmts.getAppArgs[1]!
    let stepTerm ← Term.elabTerm (← ``(Rules.stepCase $rule))
      (some (mkConst ``StepCase))
    let condMVar ← mkFreshExprMVar (mkSort levelZero)
    let blockMVar ← mkFreshExprMVar (mkConst ``Block)
    let fscType := mkAppN (mkConst ``FirstStepCase)
      #[sm, head, mkConst ``Rules.stepCases, stepTerm, condMVar, blockMVar]
    let fscMVar ← mkFreshExprMVar fscType
    let restGoals := (← getGoals).tail
    setGoals [fscMVar.mvarId!]
    evalTactic (← `(tactic| find_pinned_step))
    let proof ← instantiateMVars fscMVar
    let rest := stmts.getAppArgs[2]!
    let bs ← mkAppOptM ``BlockStep.head
      #[none, none, none, none, some rest,
        some (← mkAppM ``RuleStep.ofStepCase #[proof])]
    unless ← isDefEq (← inferType bs) goalType do
      throwError "named_step: the rule's successor block does not match the stated one"
    goal.assign bs
    setGoals restGoals

/-- Short spelling for a checked, named rule step. -/
macro "single_step " ruleName:ident : tactic =>
  `(tactic| named_step .$ruleName)

/-! ### The calculus-style step tactics

`rule_step` closes a `b ⇝[.rule] b'` goal and `steps [...]` a `b ⇝* b'` goal
whose intermediate blocks are elided -- the two shapes the calculus's
`⇝` and `⇝*` lines take.  Both go through
`find_pinned_step`, whose exclusivity route (`CandidateStep.lean`) is what keeps
them affordable; the rule name is what pins the step case. -/

/-- Discharge a `⇝[.rule]` step.  Unlike `named_step`, no elaborator is needed:
the rule comes from the goal's index, and `NamedBlockStep.head`'s residual
equation turns the successor check into `rfl` once `find_pinned_step` has
determined the rule's block. -/
macro "rule_step" : tactic => `(tactic|
  set_option maxRecDepth 32768 in
    (refine NamedBlockStep.head (by find_pinned_step) ?_) <;> rfl)

open Lean in
/-- Discharge a `⇝*` step by applying the listed rules in order, leaving the
intermediate blocks implicit -- the elision the calculus writes as one
`⇝*` line.  Each rule is pinned, so this costs the same as
the equivalent run of `rule_step`s; the final `exact BlockReflMultiStep.refl`
is the definitional check against the block that *was* written, so a stale
derivation still fails. -/
macro "steps " "[" rs:term,* "]" : tactic => do
  let mut tacs : Array (TSyntax `tactic) := #[]
  for r in rs.getElems do
    tacs := tacs.push (← `(tactic|
      refine BlockReflMultiStep.step
        (.head (.ofStepCase
          (show FirstStepCase _ _ Rules.stepCases (Rules.stepCase $r) _ _ from
            by find_pinned_step))) ?_))
    -- Renormalize the inferred residual (`(ruleEffect r).block stmt h ++
    -- rest`) back to a literal statement list, so the next step's `decide`
    -- goals stay decidable.
    tacs := tacs.push (← `(tactic| try dsimp only [rule_simp_set]))
  tacs := tacs.push (← `(tactic| exact BlockReflMultiStep.refl))
  let seq ← `(tacticSeq| $[$tacs]*)
  `(tactic| set_option maxRecDepth 32768 in $seq)

/-- The old blind loop: at each step search `Rules.stepCases` for the rule that
applies, paying `find_first_step`'s skip proof over the whole ~190-entry list.
Roughly two orders of magnitude more expensive than a pinned step.

Superseded by `steps!`, which asks `UniquenessAux.candidate` instead of
searching. Kept because it needs no oracle: it is the fallback if `candidate`
and the rule set ever disagree. -/
macro "steps_search!" : tactic => `(tactic|
  repeat (first
    | exact BlockReflMultiStep.refl
    | (set_option maxRecDepth 4096 in
        refine BlockReflMultiStep.step
          (.head (.ofStepCase (by find_first_step))) ?_
        try dsimp only [rule_simp_set])))

/-! ### `steps!` — the rule sequence, computed instead of written

`UniquenessAux.candidate : Modality -> Stmt -> Option RuleName`
(`Uniqueness.lean`) is a total computable dispatch mirroring every rule
condition, and it reduces in the kernel -- `decide` already closes closed
applications of it (`Counterexamples/CoverageResidue.lean`). So one `whnf` per
step names the rule, and the step is then discharged by the *same* pinned
route `steps [...]` uses. The emitted tactic text is identical, so this is not
a new trust assumption and not a new cost model: only the typing of the name
moves from the source file to elaboration.

`candidate` is an **oracle, not an authority**. `find_pinned_step` still proves
the rule applies, so the one case where `candidate` overreaches
(`Coverage.lean`'s `pushRhsStorageB`: `x = mv.push()` on a memory array) fails
loudly rather than proving anything false. Nothing here adds an axiom -- in
particular no `native_decide`, which `Wp/ExamplesWP.lean` is careful to
avoid.

There is no termination measure to appeal to (`Termination.lean` states that
obligation and leaves it open -- `functionBodyExpand` *grows* the block), so
the loop is fuel-bounded by construction, and it also stops if a step leaves
the block unchanged. -/

open Lean Elab Tactic Meta in
/-- Render a `RuleName` value as the source text a reader would paste:
`.storagePlaceAlias`, `.localAssignIncDec .preInc`. -/
private partial def ruleNameText (e : Lean.Expr) : MetaM String := do
  match (← instantiateMVars e) with
  | .const c _ => return "." ++ c.componentsRev.head!.toString
  | .app f a =>
      let ft ← ruleNameText f
      let at_ ← ruleNameText a
      return ft ++ " " ++ (if a.isApp then "(" ++ at_ ++ ")" else at_)
  | other => return toString (← ppExpr other)

open Lean Elab Tactic Meta in
private def rulesText (rs : Array Lean.Expr) : MetaM String := do
  let parts ← rs.mapM ruleNameText
  return "steps [" ++ String.intercalate ", " parts.toList ++ "]"

open Lean Elab Tactic Meta in
/-- **The oracle**, shared by the block loop (`steps!`) and the sequent loop
(`seq_steps!`): given the modality of a block and its head statement, the rule
`UniquenessAux.candidate` names for it, reduced to a closed constructor
application.

Extracted so that the two loops cannot drift in *which* rule they pick or in
what they say when there is none; the `before`/`after` arguments appear only in
the error messages. -/
private def candidateRule (sm head before after : Lean.Expr)
    (acc : Array Lean.Expr) : TacticM Lean.Expr := do
  -- `candidate` is indexed by `Modality` (box/diamond), the block by
  -- `SolidityModality` (box/diamond/both). Under `.both` a box/diamond twin
  -- pair applies simultaneously and `FirstStepCase` takes the box twin
  -- (`CandidateStep.twinEffects`), so `.box` is the right oracle there too.
  let m ←
    if sm.isConstOf ``SolidityModality.box then pure (mkConst ``Modality.box)
    else if sm.isConstOf ``SolidityModality.diamond then
      pure (mkConst ``Modality.diamond)
    else if sm.isConstOf ``SolidityModality.both then
      pure (mkConst ``Modality.box)
    else throwError "steps!: the block's modality is not a literal{indentExpr sm}"
  -- Ask the oracle. Default transparency suffices (`candidate` is a plain
  -- non-recursive `def`); the wider fallbacks cost nothing on success.
  let app := mkAppN (mkConst ``UniquenessAux.candidate) #[m, head]
  let mut res ← whnf app
  unless res.isAppOfArity ``Option.some 2 || res.isAppOfArity ``Option.none 1 do
    res ← withTransparency .all (whnf app)
  if res.isAppOfArity ``Option.none 1 then
    throwError "steps!: stuck after {acc.size} step(s).\n\
      head statement:{indentExpr head}\n\
      remaining block:{indentExpr before}\n\
      stated target:{indentExpr after}\n\
      `UniquenessAux.candidate` names no rule for this statement: either the \
      program is outside the calculus (see `Coverage.lean`'s residue \
      census) or a previous residual failed to normalise.\n{← rulesText acc}"
  unless res.isAppOfArity ``Option.some 2 do
    throwError "steps!: could not reduce `UniquenessAux.candidate` on\
      {indentExpr head}\nit got stuck at{indentExpr res}"
  -- `whnf` stops at head-normal form, so the *payload* of the `some` can
  -- still be unreduced: the modality-twin families come back as
  -- `UniquenessAux.pick m .fooBox .fooDiamond`, which `Rules.stepCase` then
  -- cannot reduce through and `find_pinned_step`'s `decide` chokes on.
  -- Normalize it to a constructor application -- these terms are a
  -- constructor plus at most an operator, so `reduce` is cheap here.
  let r ← Meta.reduce (← instantiateMVars res.getAppArgs[1]!)
  if r.hasExprMVar then
    throwError "steps!: the rule for{indentExpr head}\nis not a closed term: \
      {r}. The block is probably not a literal."
  return r

open Lean Elab Tactic Meta in
/-- One round of `steps!`: returns `none` when the goal is closed by
reflexivity, `some r` when rule `r` was applied and a goal remains. -/
private def autoStepsRound (acc : Array Lean.Expr) : TacticM (Option Lean.Expr) := do
  let g ← getMainGoal
  g.withContext do
    let ty ← whnf (← g.getType)
    unless ty.isAppOfArity ``BlockReflMultiStep 2 do
      throwError "steps!: expected a `⇝*` goal, got{indentExpr ty}"
    let before := ty.appFn!.appArg!
    let after := ty.appArg!
    -- Reflexivity first, so the loop stops at the *stated* target rather than
    -- running the program to the end.
    if ← isDefEq before after then
      g.assign (← mkAppOptM ``BlockReflMultiStep.refl #[some before])
      replaceMainGoal []
      return none
    -- Destructure the block, exactly as `named_step` does.
    let src ← whnf before
    unless src.isAppOfArity ``SolidityBlock.mk 2 do
      throwError "steps!: cannot destructure the source block{indentExpr src}"
    let sm ← whnf src.getAppArgs[0]!
    let stmts ← whnf src.getAppArgs[1]!
    if stmts.isAppOfArity ``List.nil 1 then
      throwError "steps!: the program finished after {acc.size} step(s), but \
        the stated target is{indentExpr after}\n{← rulesText acc}"
    unless stmts.isAppOfArity ``List.cons 3 do
      throwError "steps!: source block has no head statement{indentExpr stmts}"
    let head := stmts.getAppArgs[1]!
    let r ← candidateRule sm head before after acc
    -- One pinned step, emitted as the *same* tactic text `steps [...]` uses.
    let rStx ← Term.exprToSyntax r
    try
      evalTactic (← `(tactic|
        refine BlockReflMultiStep.step (.head (.ofStepCase
          (show FirstStepCase _ _ Rules.stepCases (Rules.stepCase $rStx) _ _ from
            by find_pinned_step))) ?_))
    catch e =>
      let hint :=
        if before.find? (·.isConstOf ``Rules.ruleEffect) |>.isSome then
          "\nThe block still mentions `ruleEffect`, so the previous \
           `dsimp only [rule_simp_set]` was a no-op and this statement is not \
           in literal form -- that, not the rule, is the likely cause."
        else ""
      throwError "steps!: step {acc.size + 1}: `{← ruleNameText r}` is the rule \
        `UniquenessAux.candidate` names for{indentExpr head}\nbut it does not \
        apply. Either this is the known `candidate` overreach (`Coverage.lean`'s \
        `pushRhsStorageB`) or the condition needs more than \
        `rule_simp <;> decide`; pin the step with `⇝[.rule]` / \
        `steps [...]`.{hint}\n{← rulesText acc}\nunderlying error: \
        {e.toMessageData}"
    -- Renormalize the residual so the next round's `decide` -- and the next
    -- `whnf` of `candidate` -- see a literal statement list.
    evalTactic (← `(tactic| try dsimp only [rule_simp_set]))
    return some r

open Lean Elab Tactic Meta in
/-- Close a `⇝*` goal by reflexivity when the stated target is already the
block we are at.  The twin of `autoSeqStepsClose`, which has a merge line to
try as well. -/
private def autoStepsClose : TacticM Bool := do
  let g ← getMainGoal
  g.withContext do
    let ty ← whnf (← g.getType)
    unless ty.isAppOfArity ``BlockReflMultiStep 2 do
      throwError "steps!: expected a `⇝*` goal, got{indentExpr ty}"
    let before := ty.appFn!.appArg!
    if ← isDefEq before ty.appArg! then
      g.assign (← mkAppOptM ``BlockReflMultiStep.refl #[some before])
      replaceMainGoal []
      return true
    return false

open Lean Elab Tactic Meta in
private partial def autoStepsLoop (fuel : Nat) (acc : Array Lean.Expr) :
    TacticM (Array Lean.Expr) := do
  -- The stated target may be the block we are already at, so reflexivity is
  -- checked *before* the fuel: `fuel` counts steps taken, not rounds entered,
  -- and `steps! 1` proves a genuine one-step line.
  if ← autoStepsClose then return acc
  match fuel with
  | 0 =>
      throwError "steps!: gave up after {acc.size} steps without reaching the \
        stated target.\n{← rulesText acc}\nRaise the bound with \
        `steps! {2 * acc.size}` if the derivation really is that long."
  | fuel + 1 => do
      let before? := (← getGoals).head?
      match ← autoStepsRound acc with
      | none => return acc
      | some r =>
          trace[solidity.steps] "step {acc.size + 1}: {← ruleNameText r}"
          -- Cycle guard: a rule that leaves the block unchanged would other-
          -- wise burn the whole fuel budget for nothing.
          if let (some g₀, some g₁) := (before?, (← getGoals).head?) then
            if ← isDefEq (← g₀.getType) (← g₁.getType) then
              throwError "steps!: rule `{← ruleNameText r}` left the block \
                unchanged.\n{← rulesText (acc.push r)}"
          autoStepsLoop fuel (acc.push r)

open Lean Elab Tactic Meta in
/-- Run a `⇝*` goal to its stated target, computing the rule at each step.
Optional explicit fuel: `steps! 400`. -/
elab "steps!" fuelStx:(num)? : tactic =>
  withOptions (fun o => maxRecDepth.set o 32768) do
    let fuel := (fuelStx.map (·.getNat)).getD 128
    let used ← autoStepsLoop fuel #[]
    trace[solidity.steps] "{← rulesText used}"

open Lean Elab Tactic Meta in
/-- `steps!`, and report the sequence it found as a pasteable `steps [...]`.
The names come from the proof that was actually built, so this cannot drift
from what was checked. -/
elab tk:"steps?" fuelStx:(num)? : tactic =>
  withOptions (fun o => maxRecDepth.set o 32768) do
    let fuel := (fuelStx.map (·.getNat)).getD 128
    let used ← autoStepsLoop fuel #[]
    Lean.Meta.Tactic.TryThis.addSuggestion tk (← rulesText used)

/-! ### The judgment-layer tactics

`Examples/Derivations/DynamicLogic.lean`'s `⇝ᵈ` chains are the block tactics
with the postcondition riding along, so each `dl_*` tactic is its block twin
wrapped in `JudgmentStep.prog` / `NamedJudgmentStep.prog` /
`JudgmentMultiStep.ofBlock`.  They live here rather than there because
`sol_derivation` dispatches to them. -/

/-- `single_step`, lifted to dynamic-logic judgments. -/
macro "dl_step " rule:ident : tactic =>
  `(tactic| exact JudgmentStep.prog (by single_step $rule))

/-- `named_step`, lifted to dynamic-logic judgments. -/
macro "dl_named_step " rule:term : tactic =>
  `(tactic| exact JudgmentStep.prog (by named_step $rule))

/-- `rule_step`, lifted: closes a `⇝ᵈ[.rule]` goal. -/
macro "dl_rule_step" : tactic =>
  `(tactic| exact NamedJudgmentStep.prog (by rule_step))

/-- `block_step`, lifted: closes a `⇝ᵈ*` goal by one step with the rule
inferred. -/
macro "dl_block_step" : tactic =>
  `(tactic| exact JudgmentMultiStep.ofBlock (by block_step))

/-- `steps [...]`, lifted: closes a `⇝ᵈ*` goal by running the listed rules
on the program and carrying the postcondition along. -/
macro "dl_steps " "[" rs:term,* "]" : tactic =>
  `(tactic| exact JudgmentMultiStep.ofBlock (by steps [$rs,*]))

/-- `steps!`, lifted: the rules are computed rather than listed.  This is
what lets a `⇝*` line of a *judgment* derivation elide an administrative run
without restating the postcondition on the elided lines. -/
macro "dl_steps!" : tactic =>
  `(tactic| exact JudgmentMultiStep.ofBlock (by steps!))

/-! ### `sol_runs` — a whole program, once

The shortest honest statement about a program is "it runs to the empty block":
the modality named once instead of per block, the empty target implied, the
rules computed.

```
sol_runs deepFieldWrite { alice.account.balance = amount }
sol_runs arrayRead diamond { result = values[i] }
```

It states `theorem <name> : ⟨m, program⟩ ⇝* ⟨m, []⟩` and proves it with
`steps!`, so it is exactly the theorem the long form states.

**Statements are `;`-separated, inside braces.** Newline separation
(`sepByIndentSemicolon`) parses, but two `sol_expr` productions reach across a
line break -- postfix `++` (`x = y` ⏎ `++i` becomes `x = (y++)`) and the call
form `ident(…)` (`result = f` ⏎ `(p).pop()` becomes `f(p)`). The failure mode
is the dangerous one: the merged program still reduces to the empty block, so
the theorem would be *true and about a different program*. `;` ends an item
where no expression production can continue, and the braces stop the list
running into the next command. Solidity needs the `;` anyway. -/

-- These three become global tokens, so a Solidity variable spelled `box`,
-- `diamond` or `both` would need `«box»` inside `sol_stmt`. The corpus has
-- none (every occurrence of those words is prose in a comment).
declare_syntax_cat sol_modality
/-- Box modality, the default. -/
syntax "box" : sol_modality
/-- Diamond modality. -/
syntax "diamond" : sol_modality
/-- The combined modality. No fast pinned path exists for it
(`CandidateStep.lean` has no `firstStepCase_both`), so it falls back to the
positional walk. -/
syntax "both" : sol_modality

syntax (docComment)? "sol_runs " ident (sol_modality)?
  " {" sepBy(sol_stmt, "; ", "; ", allowTrailingSep) "}" : command

open Lean Elab Command in
elab_rules : command
  | `(command| $[$doc:docComment]? sol_runs $name:ident $[$m:sol_modality]?
        { $stmts;* }) => do
      let mTerm : Term ←
        match m with
        | none => `(SolidityModality.box)
        | some mm =>
            match mm with
            | `(sol_modality| diamond) => `(SolidityModality.diamond)
            | `(sol_modality| both) => `(SolidityModality.both)
            | _ => `(SolidityModality.box)
      elabCommand (← `(command|
        $[$doc:docComment]? theorem $name :
            SolidityBlock.mk $mTerm (sblock!{ $stmts;* })
              ⇝* SolidityBlock.mk $mTerm (([] : Block)) := by steps!))

/-! ### The sequent layer

`Examples/Derivations/Paper.lean` writes the calculus's own lines --
`Γ ⟹ {U} ⟨[ p ]⟩ φ` -- so each of the block tactics above has a twin here.
Two things are new, and both are about the update the block layer throws away.

`upd_merge` closes the **merge line**: the derivation's last step is usually
not a rule application at all but the update calculus collapsing `{u}{v}` into
`{u ‖ {u}v}`, and its content is an equality of two `Upd`s as state functions.
`upd_case` is what makes that provable by simp: the two spellings reach the
same interpreter reader through *different* bindings, so a proof has to case on
that reader once and let both sides reduce together -- which `split` cannot do,
because it cases the two sides independently.

`seq_steps!` reuses the block loop's oracle (`candidateRule`) on the head
statement of the first open sequent, so the two loops cannot drift in which
rule they pick. -/

open Lean Elab Tactic Meta in
/-- Case on the first interpreter reader in the goal that both spellings of an
update have to agree on.  The list is the readers a merged update can get
stuck at: each looks at the *incoming* state, which is what the merge moved. -/
elab "upd_case" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let heads : List (Lean.Name × Nat) :=
      [ (``Wp.varPath, 2), (``Wp.stackVal, 2), (``Wp.memRef, 2),
        (``Wp.simpleVal, 2), (``Semantics.State.saveStorage, 4),
        (``Semantics.State.findStorage, 3), (``Semantics.State.getObj, 2),
        -- The coercions a read ends in: a storage cell holding a struct has
        -- no `Value`, so these can fail and both spellings reach them.
        (``Semantics.SVal.asValue, 1), (``Semantics.MVal.asValue, 1) ]
    let some t := ty.find? (fun e =>
        heads.any (fun (h, n) => e.isAppOfArity h n) &&
          !e.hasLooseBVars && !e.hasExprMVar)
      | throwError "upd_case: no shared interpreter reader left in{indentExpr ty}"
    evalTactic (← `(tactic| cases hcase : $(← Term.exprToSyntax t)))

/-- Normalize an update to the interpreter readers it is made of, without
unfolding the readers themselves: `upd_merge_set` rewrites *through* a binding
and only fires while `varPath`/`stackVal`/`readMem` are still folded. -/
macro "upd_norm" : tactic => `(tactic|
  simp +decide (disch := decide) only [upd_merge_set, rule_simp_set,
    Sequent.upd, stackUpd, List.foldr, Upd.seq, Upd.id, Update.UpdTerm.toUpd, Update.UpdTerm.toPar,
    Update.elemPar, Upd.Par.toUpd, Upd.Par.apply, Upd.Par.writers,
    Upd.Elem.eval, Update.bindRhs, Update.Sym.eval, Update.readTerm,
    Update.storageRhs, Update.heapRhs, Update.storageSave, Update.memWrite,
    Wp.locPath, Upd.saveSt, Wp.placePath, Wp.readVal, Wp.defaultValue,
    RuleSoundness.usesVar, SoliditySyntax.fieldFor, Field.primitive,
    Field.identity, Field.name, List.flatMap, List.flatten, List.map,
    List.foldl, List.append, List.append_nil, List.nil_append,
    List.cons_append, List.append_assoc, bind, Except.bind, Except.map,
    pure, Except.pure])

/-- Close a `≡ᵘ` goal: the two lines carry the same update, spelled
sequentially on one side and as one parallel update on the other.  Structural
components go by `rfl`; the updates go by `upd_norm`, then one `upd_case` per
reader the two spellings reach differently. -/
macro "upd_merge" : tactic => `(tactic|
  (first
    | exact Frontier.Equiv.refl _
    | (refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩ <;>
        first
          | trivial
          | exact Frontier.Equiv.refl _
          | (funext s
             try upd_norm
             repeat (first | rfl | (upd_case <;> (try upd_norm)))
             all_goals (try rfl)))))

/-- Discharge a `⇝ᵘ[.rule]` step.  `firstOpen?` computes the split, so the
first hypothesis is `rfl`; the successor is checked definitionally once
`find_pinned_step` has determined the rule's goals. -/
macro "seq_rule_step" : tactic => `(tactic|
  set_option maxRecDepth 32768 in
    (refine NamedFrontierStep.head rfl (by find_pinned_step) ?_) <;> rfl)

open Lean in
/-- Discharge a `⇝ᵘ*` line by applying the listed rules in order.  A trailing
merge is allowed, so an elided run may end on the calculus's parallel form. -/
macro "seq_steps " "[" rs:term,* "]" : tactic => do
  let mut tacs : Array (TSyntax `tactic) := #[]
  for r in rs.getElems do
    tacs := tacs.push (← `(tactic|
      refine FrontierMultiStep.step
        ⟨_, NamedFrontierStep.head rfl
          (show FirstStepCase _ _ Rules.stepCases (Rules.stepCase $r) _ _ from
            by find_pinned_step) rfl⟩ ?_))
    tacs := tacs.push (← `(tactic| try dsimp only [rule_simp_set]))
  tacs := tacs.push (← `(tactic| first
    | exact FrontierMultiStep.refl
    | (refine FrontierMultiStep.equiv ?_ FrontierMultiStep.refl
       upd_merge)))
  let seq ← `(tacticSeq| $[$tacs]*)
  `(tactic| set_option maxRecDepth 32768 in $seq)

open Lean Elab Tactic Meta in
/-- Do two literal frontiers agree, line by line, on antecedent and goal?

Then they can differ only in *how their updates are spelled*, and the line
between them is the calculus's merge rather than a rule application: every
rule rewrites the head statement, so a step always changes a goal.  This is
what lets `⇝ᵘ*` land on the parallel form while the program is still open,
which is where the calculus writes it. -/
private partial def sameShape (a b : Lean.Expr) : MetaM Bool := do
  let a ← whnf a
  let b ← whnf b
  if a.isAppOfArity ``List.nil 1 then return b.isAppOfArity ``List.nil 1
  unless a.isAppOfArity ``List.cons 3 && b.isAppOfArity ``List.cons 3 do
    return false
  let qa ← whnf a.getAppArgs[1]!
  let qb ← whnf b.getAppArgs[1]!
  unless qa.isAppOfArity ``Sequent.mk 3 && qb.isAppOfArity ``Sequent.mk 3 do
    return false
  unless ← isDefEq qa.getAppArgs[0]! qb.getAppArgs[0]! do return false
  unless ← isDefEq qa.getAppArgs[2]! qb.getAppArgs[2]! do return false
  sameShape a.getAppArgs[2]! b.getAppArgs[2]!

open Lean Elab Tactic Meta in
/-- Try to *close* a `⇝ᵘ*` goal without taking a step: by reflexivity, or by
the merge line when the two frontiers differ only in how their update is
spelled.  `true` means the goal is gone.

Run before every step and again when the fuel is spent, which is what makes
`seq_steps! 1` mean "at most one step, then close". -/
private def autoSeqStepsClose (acc : Array Lean.Expr) : TacticM Bool := do
  let g ← getMainGoal
  g.withContext do
    let ty ← whnf (← g.getType)
    unless ty.isAppOfArity ``FrontierMultiStep 2 do
      throwError "seq_steps!: expected a `⇝ᵘ*` goal, got{indentExpr ty}"
    let before := ty.appFn!.appArg!
    let after := ty.appArg!
    if ← isDefEq before after then
      g.assign (← mkAppOptM ``FrontierMultiStep.refl #[some before])
      replaceMainGoal []
      return true
    let src ← whnf before
    let opened ← whnf (mkAppN (mkConst ``Frontier.firstOpen?) #[src])
    let noneLeft := opened.isAppOfArity ``Option.none 1
    -- The merge is the expensive tactic in this file, so it is tried only
    -- where it can be the answer: nothing left to execute, or the two lines
    -- already agree on everything but the spelling of the update.
    unless noneLeft || (← sameShape src after) do return false
    let st ← saveState
    let merged ←
      try
        evalTactic (← `(tactic|
          refine FrontierMultiStep.equiv ?_ FrontierMultiStep.refl))
        evalTactic (← `(tactic| upd_merge))
        pure (← getGoals).isEmpty
      catch _ => pure false
    if merged then return true
    st.restore
    if noneLeft then
      throwError "seq_steps!: no open sequent left after {acc.size} step(s). \
        The frontier reached is{indentExpr src}\nand the stated target is\
        {indentExpr after}\nwhich is not the same line up to the spelling of \
        its update (`upd_merge` did not close it). Write the merge as its own \
        `⇝≡` line, or supply it with `⇝≡[h]`.\n{← rulesText acc}"
    throwError "seq_steps!: after {acc.size} step(s) the frontier reached\
      {indentExpr src}\nand the stated target{indentExpr after}\nagree on \
      every antecedent and goal, so the line between them is the merge -- but \
      `upd_merge` did not close it. Write the two updates the way the calculus \
      stacks them, or supply the equality with `⇝≡[h]`.\n{← rulesText acc}"

open Lean Elab Tactic Meta in
/-- One step of `seq_steps!`.  Same oracle as the block loop's
`autoStepsRound`; what differs is where the head statement is found (inside
the first *open* sequent).  Closing is `autoSeqStepsClose`'s job, and has
already been tried when this runs. -/
private def autoSeqStepsStep (acc : Array Lean.Expr) : TacticM Lean.Expr := do
  let g ← getMainGoal
  g.withContext do
    let ty ← whnf (← g.getType)
    let before := ty.appFn!.appArg!
    let after := ty.appArg!
    let src ← whnf before
    let opened ← whnf (mkAppN (mkConst ``Frontier.firstOpen?) #[src])
    unless opened.isAppOfArity ``Option.some 2 do
      throwError "seq_steps!: cannot split the frontier{indentExpr src}\n\
        `Frontier.firstOpen?` got stuck at{indentExpr opened}"
    -- `some (before, q, after)`: the open sequent is the second component.
    let triple ← whnf opened.getAppArgs[1]!
    let pair ← whnf triple.getAppArgs[3]!
    let q ← whnf pair.getAppArgs[2]!
    unless q.isAppOfArity ``Sequent.mk 3 do
      throwError "seq_steps!: the open sequent is not a literal{indentExpr q}"
    let goal ← whnf q.getAppArgs[2]!
    unless goal.isAppOfArity ``SeqGoal.prog 2 do
      throwError "seq_steps!: the open sequent has no program{indentExpr goal}"
    let blk ← whnf goal.getAppArgs[0]!
    unless blk.isAppOfArity ``SolidityBlock.mk 2 do
      throwError "seq_steps!: cannot destructure the block{indentExpr blk}"
    let sm ← whnf blk.getAppArgs[0]!
    let stmts ← whnf blk.getAppArgs[1]!
    unless stmts.isAppOfArity ``List.cons 3 do
      throwError "seq_steps!: the open sequent's block has no head statement\
        {indentExpr stmts}"
    let head := stmts.getAppArgs[1]!
    let r ← candidateRule sm head before after acc
    let rStx ← Term.exprToSyntax r
    try
      evalTactic (← `(tactic|
        refine FrontierMultiStep.step
          ⟨_, NamedFrontierStep.head rfl
            (show FirstStepCase _ _ Rules.stepCases (Rules.stepCase $rStx) _ _ from
              by find_pinned_step) rfl⟩ ?_))
    catch e =>
      throwError "seq_steps!: step {acc.size + 1}: `{← ruleNameText r}` is the \
        rule `UniquenessAux.candidate` names for{indentExpr head}\nbut it does \
        not apply; pin the step with `⇝ᵘ[.rule]` / `seq_steps [...]`.\n\
        {← rulesText acc}\nunderlying error: {e.toMessageData}"
    evalTactic (← `(tactic| try dsimp only [rule_simp_set]))
    return r

open Lean Elab Tactic Meta in
private partial def autoSeqStepsLoop (fuel : Nat) (acc : Array Lean.Expr) :
    TacticM (Array Lean.Expr) := do
  -- Closure is checked *before* the fuel, so `fuel` counts steps taken rather
  -- than rounds entered: `seq_steps! 1` proves a genuine one-step line.
  if ← autoSeqStepsClose acc then return acc
  match fuel with
  | 0 =>
      throwError "seq_steps!: gave up after {acc.size} step(s) without reaching \
        the stated target.\n{← rulesText acc}"
  | fuel + 1 => do
      let before? := (← getGoals).head?
      let r ← autoSeqStepsStep acc
      trace[solidity.steps] "step {acc.size + 1}: {← ruleNameText r}"
      if let (some g₀, some g₁) := (before?, (← getGoals).head?) then
        if ← isDefEq (← g₀.getType) (← g₁.getType) then
          throwError "seq_steps!: rule `{← ruleNameText r}` left the \
            frontier unchanged.\n{← rulesText (acc.push r)}"
      autoSeqStepsLoop fuel (acc.push r)

open Lean Elab Tactic Meta in
/-- Run a `⇝ᵘ*` goal to its stated target, computing the rule at each step. -/
elab "seq_steps!" fuelStx:(num)? : tactic =>
  withOptions (fun o => maxRecDepth.set o 32768) do
    let fuel := (fuelStx.map (·.getNat)).getD 128
    let used ← autoSeqStepsLoop fuel #[]
    trace[solidity.steps] "{← rulesText used}"

/-- One step of a `⇝ᵘ*` line with the rule inferred.  `seq_steps! 1` is
"at most one step, then close", so a line that only merges is covered too. -/
macro "seq_block_step" : tactic => `(tactic| seq_steps! 1)

/-! ### `seq_closes` — run to closure, with the endpoint unwritten

`seq_steps!` runs toward a *stated* target.  For a whole solkey obligation
there is nothing to state: the accumulated update of a fifteen-statement body
is not something to type out, and typing it out would not be checking
anything the chain does not already check.

`seq_steps!` also cannot simply be pointed at a metavariable.  Its first move
is `isDefEq before after`, which against a metavariable succeeds at once by
assigning it — the goal would close having taken no step, and the theorem
would say nothing about the rules.  So the loop below tests
`Frontier.firstOpen?` instead: it steps while a line still has a statement,
and only then assigns the target.  `Frontier.isClosed` is the same condition
as a Boolean, and `CalculusHolds` carries it as a conjunct for exactly this
reason. -/

open Lean Elab Tactic Meta in
/-- Step while the frontier has an open line; assign the target to the
frontier reached.  Returns the rules fired, for the trace. -/
private partial def seqClosesLoop (fuel : Nat) (acc : Array Lean.Expr) :
    TacticM (Array Lean.Expr) := do
  let g ← getMainGoal
  let done ← g.withContext do
    let ty ← whnf (← g.getType)
    unless ty.isAppOfArity ``FrontierMultiStep 2 do
      throwError "seq_closes: expected a `⇝ᵘ*` goal, got{indentExpr ty}"
    let src ← whnf ty.appFn!.appArg!
    let opened ← whnf (mkAppN (mkConst ``Frontier.firstOpen?) #[src])
    unless opened.isAppOfArity ``Option.none 1 do
      unless opened.isAppOfArity ``Option.some 2 do
        throwError "seq_closes: `Frontier.firstOpen?` got stuck at\
          {indentExpr opened}\non the frontier{indentExpr src}"
      return false
    -- The target is normally a goal metavariable (`refine ⟨?f, …⟩`), and a
    -- *named* goal is synthetic opaque, which `isDefEq` refuses to assign.
    -- Assign it outright: where a run-to-closure ends is computed, not
    -- something unification should be asked to guess.
    let tgt ← instantiateMVars ty.appArg!
    if tgt.isMVar then
      tgt.mvarId!.assign src
    else
      unless ← isDefEq src tgt do
        throwError "seq_closes: after {acc.size} step(s) the frontier\
          {indentExpr src}\nhas no open line, but does not match the stated \
          target{indentExpr tgt}\n{← rulesText acc}"
    g.assign (← mkAppOptM ``FrontierMultiStep.refl #[some src])
    return true
  if done then
    replaceMainGoal []
    return acc
  match fuel with
  | 0 =>
      throwError "seq_closes: gave up after {acc.size} step(s) with an open \
        line left.\n{← rulesText acc}"
  | fuel + 1 =>
      let before? := (← getGoals).head?
      let r ← autoSeqStepsStep acc
      trace[solidity.steps] "step {acc.size + 1}: {← ruleNameText r}"
      if let (some g₀, some g₁) := (before?, (← getGoals).head?) then
        if ← isDefEq (← g₀.getType) (← g₁.getType) then
          throwError "seq_closes: rule `{← ruleNameText r}` left the frontier \
            unchanged.\n{← rulesText (acc.push r)}"
      seqClosesLoop fuel (acc.push r)

open Lean Elab Tactic Meta in
/-- Drive a `⇝ᵘ*` goal with the rule table until no line has a statement
left, and let the endpoint be whatever the rules produce.  The fuel counts
steps, and the default is generous because a solkey body of twenty
statements costs several hundred of them. -/
elab "seq_closes" fuelStx:(num)? : tactic =>
  withOptions (fun o => maxRecDepth.set o 32768) do
    let fuel := (fuelStx.map (·.getNat)).getD 1024
    let used ← seqClosesLoop fuel #[]
    trace[solidity.steps] "{← rulesText used}"

/-! ### `sol_calculus` — a whole obligation, by the rule table alone

```
sol_calculus storageRootReadWrite from State.testSuiteStore
  { age = 34; uint r = age; assert((r == 34)) }
```

It states `CalculusHolds <modality> <program> (true) <store>` and proves it
with `seq_closes` and a decided endpoint, which is the whole of the claim:
the taclets drove the program to a frontier with nothing left to execute, and
that frontier -- the accumulated update, plus one obligation line per
`assert` -- holds at the store.

The modality is `diamond` by default, as the ported corpus is: KeY's
obligation is `\<{ f(); }\>(true)`, and a diamond additionally proves the
program does not revert.

**The endpoint is `native_decide`, deliberately.**  `Frontier.Holds` runs the
accumulated update through the interpreter's readers, and the WF-recursive
interpreter does not kernel-reduce -- `decide` fails on it, which is the same
reason `Examples/Derivations/Paper.lean` checks its chains' endpoints that
way.  The *derivation* adds no axiom; the endpoint does.

**Statements are `;`-separated, inside braces**, for the reason `sol_runs`
gives: newline separation parses, and the misparse is silent. -/

open Lean Elab Tactic in
/-- The proof `sol_calculus` writes: run to closure, then decide the two
Boolean facts about the frontier reached. -/
macro "calculus_proof" : tactic => `(tactic| (
  refine ⟨?f, ?hs, ?hc, ?hh⟩
  case hs => seq_closes
  case hc => decide
  case hh => native_decide))

syntax (docComment)? "sol_calculus " ident (sol_modality)? " from " ident
  " {" sepBy(sol_stmt, "; ", "; ", allowTrailingSep) "}" : command

open Lean Elab Command in
elab_rules : command
  | `(command| $[$doc:docComment]? sol_calculus $name:ident $[$m:sol_modality]?
        from $store:ident { $stmts;* }) => do
      let mTerm : Term ←
        match m with
        | none => `(SolidityModality.diamond)
        | some mm =>
            match mm with
            | `(sol_modality| box) => `(SolidityModality.box)
            | `(sol_modality| both) => `(SolidityModality.both)
            | _ => `(SolidityModality.diamond)
      -- The postcondition is written as the term, not as `sexpr!{ true }`.
      -- An identifier inside a macro's own quotation carries that macro's
      -- hygiene scopes, and `sol_expr`'s ident production reads the name
      -- *as a Solidity variable*: `true` would come back as a seven-deep
      -- chain of stack field accesses named after the macro scope, and the
      -- obligation would be about that instead of about `true`. The spliced
      -- `$stmts` are the user's syntax and carry the user's scopes, so the
      -- program is unaffected.
      elabCommand (← `(command|
        $[$doc:docComment]? theorem $name :
            CalculusHolds $mTerm (sblock!{ $stmts;* })
              (Solidity.Typed.WrappedExpr.bool true) $store := by
          calculus_proof))

/-! ### The `sol_derivation` command

The calculus writes a derivation as a chain of `⇝` lines and nothing else --
no per-line justification, because the rule is named on the line.  This
command writes the `calc` plus `:= by rule_step` scaffolding, elaborating to
`theorem <name> : <first> ⇝* <last>` with each line discharged by the tactic
its arrow selects, and each `where` binding to an `abbrev` in the enclosing
namespace -- the calculus's "Let ℓ = ...".  Worked chains:
`Examples/Derivations/`.

The blocks are parsed at precedence 51, above the `⇝` infixes, so the chain
does not collapse into a single term. -/

declare_syntax_cat sol_arrow
/-- One step, rule inferred (`block_step`). -/
syntax " ⇝ " : sol_arrow
/-- One step by a named rule (`rule_step`). -/
syntax " ⇝[" term "] " : sol_arrow
/-- Several steps, rules listed (`steps [...]`). -/
syntax " ⇝*[" term,* "] " : sol_arrow
/-- Several steps, rules computed and not shown (`steps!`). Costs the same as
the listed form; use it when the rules are bookkeeping rather than content. -/
syntax " ⇝* " : sol_arrow
/-! The ASCII twins of the four arrows, for the same reason as `MultiStep.lean`'s
`~>` family: the glyph is what the calculus draws and what goals print, but a
derivation has to be typeable without an input method. -/
/-- ASCII twin of `⇝`. -/
syntax " ~> " : sol_arrow
/-- ASCII twin of `⇝[r]`. -/
syntax " ~>[" term "] " : sol_arrow
/-- ASCII twin of `⇝*[rs]`. -/
syntax " ~>*[" term,* "] " : sol_arrow
/-- ASCII twin of `⇝*`. -/
syntax " ~>* " : sol_arrow
/-- The paper's many-step arrow, `~*>`: the same tactic as `⇝*`/`~>*`, in the
spelling the paper's chains are written in. -/
syntax " ~*> " : sol_arrow
/-! The merge arrow.  Not a step of the rule set: the calculus's last line is
usually the update calculus collapsing `{u}{v}` into `{u ‖ {u}v}`, and writing
it with `⇝` would claim a taclet fired.  `⇝≡` is that line, discharged by
`upd_merge`; `⇝≡[h]` takes the update equality by hand, for a merge the
automation cannot close. -/
/-- A merge line: same derivation line, the update respelled. -/
syntax " ⇝≡ " : sol_arrow
/-- A merge line with the update equality supplied. -/
syntax " ⇝≡[" term "] " : sol_arrow
/-- ASCII twin of `⇝≡`. -/
syntax " ~>= " : sol_arrow

declare_syntax_cat sol_where_bind
syntax ident " := " term : sol_where_bind

/-! A line of a chain is one of three things: a term (`solbox!{…}`, `sol!{…}`,
a bare name -- every layer), a `=>` line written the way the calculus draws it
(`Update/SequentSyntax.lean`), or a bracketed frontier of such lines, which is
what a guarded rule leaves open.

The three alternatives cannot be confused.  No term begins with `=>`, and a
line that *starts* like one (`flag => …`, `¬inBounds(values[i]) => …`) parses
as a term only up to the turnstile, so the `sol_line` reading is longer and
wins; `[ g => … ]` fails as a Lean list literal at the `=>`; and `seq!{…}`
fails as a `sol_line` at the `!`.  A chain may therefore mix the spellings,
which is what makes an old derivation migrate one line at a time. -/
declare_syntax_cat sol_deriv_line
/-- Any layer's line, written as a term. -/
syntax term:51 : sol_deriv_line
/-- The sequent layer's line, written as the calculus draws it. -/
syntax sol_line : sol_deriv_line
/-- The sequents a guarded rule leaves open at once. -/
syntax "[" sepBy1(sol_line, ", ") "]" : sol_deriv_line

syntax (docComment)? "sol_derivation " ident (" let " sol_where_bind,+)?
  " : " sol_deriv_line (sol_arrow sol_deriv_line)+
  (" where " sol_where_bind,+)? : command

/-- Which layer is this derivation written at?

Sniffed from the syntax, not from the elaborated type, for the reason
`isJudgmentSyntax` gives below: a first line typically mentions a section
`variable (φ : WrappedExpr)`, which a command-level `liftTermElabM` cannot
see.  `seq!` and `sol!` are the only notations that build a `Sequent` and a
`SolidityJudgment` respectively, so their atoms are sound tests. -/
inductive DerivLayer where
  | block | judgment | sequent
  deriving DecidableEq

private partial def hasAtom (a : String) : Lean.Syntax → Bool
  | .atom _ v => v == a
  | .node _ _ args => args.any (hasAtom a)
  | _ => false

/-- Does this term denote a *judgment* rather than a bare block?

Sniffed from the syntax, not from the elaborated type: the first line of a
judgment derivation typically mentions a `variable (φ : WrappedExpr)`, which
is a section variable and so is not in scope for a command-level
`liftTermElabM` -- elaborating it there would fail on every derivation that
uses the calculus's opaque postcondition, which is exactly the case this has to
get right.  `sol!` is the only notation that builds a `SolidityJudgment`
(`solbox!`/`soldiamond!`/`solboth!` build blocks), so its atom is a sound
test for every derivation written in the surface notation.  A first line that
is a bare identifier of judgment type is not recognised; write the `sol!` out,
which is what the derivations do anyway. -/
private partial def isJudgmentSyntax : Lean.Syntax → Bool
  | .atom _ v => v == "sol!"
  | .node _ _ args => args.any isJudgmentSyntax
  | _ => false

/-- The modality a chain is written in, read off its first line.  Only the
paper's bare `(φ)` goal needs it -- every other goal writes its own -- and
reading it here is what makes the last line of a chain agree with the first by
construction, which `upd_merge` then closes by `rfl`.

A chain whose first line is a term (`seq!{…}`, `solbox!{…}`) has none to
offer, so a bare `(φ)` after it is the combined modality, the default of every
worked example. -/
private def chainMode : Lean.TSyntax `sol_deriv_line → Option Lean.Ident
  | `(sol_deriv_line| $l:sol_line) => lineMode? l
  | `(sol_deriv_line| [ $ls:sol_line,* ]) => ls.getElems[0]?.bind lineMode?
  | _ => none

open Lean Elab Command in
/-- A chain line as the term it denotes.  A `=>` line and a bracketed frontier
go through `Update/SequentSyntax.lean`'s expander with the chain's modality;
a term is already one. -/
private def derivLineTerm (mode : Lean.Ident) :
    Lean.TSyntax `sol_deriv_line → CommandElabM Term
  | `(sol_deriv_line| $t:term) => pure t
  | `(sol_deriv_line| $l:sol_line) => liftMacroM (expandLine mode l)
  | `(sol_deriv_line| [ $ls:sol_line,* ]) => do
      let ts ← ls.getElems.mapM fun l => liftMacroM (expandLine mode l)
      `(([$ts,*] : Frontier))
  | stx => throwErrorAt stx "malformed `sol_derivation` line"

/-- Is this line written in the calculus's own notation?  Then the derivation
is at the sequent layer, whatever the rest of the chain looks like. -/
private def isSeqLine : Lean.TSyntax `sol_deriv_line → Bool
  | `(sol_deriv_line| $_:sol_line) => true
  | `(sol_deriv_line| [ $_:sol_line,* ]) => true
  | _ => false

open Lean Elab Command in
elab_rules : command
  | `(command| $[$doc:docComment]? sol_derivation $name:ident
        $[let $lets:sol_where_bind,*]? : $firstLine:sol_deriv_line
        $[$arrows:sol_arrow $targetLines:sol_deriv_line]*
        $[where $binds:sol_where_bind,*]?) => do
      -- The named abbreviations first, in source order, since the chain may
      -- mention them: the calculus's "Let l = find(storage, values.length)" is
      -- the `let` prefix, its trailing `where` twin the older spelling.
      for group in [lets, binds] do
        if let some group := group then
          for bind in group.getElems do
            match bind with
            | `(sol_where_bind| $bindName:ident := $value:term) =>
                elabCommand (← `(command| abbrev $bindName := $value))
            | _ => throwErrorAt bind "malformed `sol_derivation` binding"
      -- Block layer or judgment layer?  The source is the same either way --
      -- one arrow glyph, as the calculus draws it -- and only the tactics and the
      -- transitivity lemma differ.
      let mode := chainMode firstLine |>.getD (mkIdent ``SolidityModality.both)
      let first ← derivLineTerm mode firstLine
      let targets ← targetLines.mapM (derivLineTerm mode)
      let layer : DerivLayer :=
        if isSeqLine firstLine || hasAtom "seq!" first then .sequent
        else if isJudgmentSyntax first then .judgment
        else .block
      -- One `⇝*`/`⇝ᵈ*` proof per line, then fold them with transitivity.  Each
      -- line is `show`-ascribed, so a failure points at that line's block.
      let mut prev := first
      let mut proofs : Array Term := #[]
      for (arrow, target) in arrows.zip targets do
        let proof ←
          match arrow with
          | `(sol_arrow| ⇝) | `(sol_arrow| ~>) =>
              match layer with
              | .sequent => `(show $prev ⇝ᵘ* $target from by seq_block_step)
              | .judgment => `(show $prev ⇝ᵈ* $target from by dl_block_step)
              | .block => `(show $prev ⇝* $target from by block_step)
          | `(sol_arrow| ⇝[$rule:term]) | `(sol_arrow| ~>[$rule:term]) =>
              match layer with
              | .sequent =>
                  `(NamedFrontierStep.toMultiStep
                      (show $prev ⇝ᵘ[$rule] $target from by seq_rule_step))
              | .judgment =>
                  `(NamedJudgmentStep.toMultiStep
                      (show $prev ⇝ᵈ[$rule] $target from by dl_rule_step))
              | .block =>
                  `(NamedBlockStep.toReflMultiStep
                      (show $prev ⇝[$rule] $target from by rule_step))
          | `(sol_arrow| ⇝*[$rules:term,*]) | `(sol_arrow| ~>*[$rules:term,*]) =>
              match layer with
              | .sequent => `(show $prev ⇝ᵘ* $target from by seq_steps [$rules,*])
              | .judgment => `(show $prev ⇝ᵈ* $target from by dl_steps [$rules,*])
              | .block => `(show $prev ⇝* $target from by steps [$rules,*])
          | `(sol_arrow| ⇝*) | `(sol_arrow| ~>*) | `(sol_arrow| ~*>) =>
              match layer with
              | .sequent => `(show $prev ⇝ᵘ* $target from by seq_steps!)
              | .judgment => `(show $prev ⇝ᵈ* $target from by dl_steps!)
              | .block => `(show $prev ⇝* $target from by steps!)
          | `(sol_arrow| ⇝≡) | `(sol_arrow| ~>=) =>
              if layer == .sequent then
                `(show $prev ⇝ᵘ* $target from
                    FrontierMultiStep.equiv (by upd_merge) FrontierMultiStep.refl)
              else throwErrorAt arrow
                "`⇝≡` is a merge line: it needs a `seq!` derivation, where the \
                 update is written"
          | `(sol_arrow| ⇝≡[$h:term]) =>
              if layer == .sequent then
                `(show $prev ⇝ᵘ* $target from
                    FrontierMultiStep.equiv ⟨⟨rfl, rfl, $h⟩, trivial⟩
                      FrontierMultiStep.refl)
              else throwErrorAt arrow
                "`⇝≡` is a merge line: it needs a `seq!` derivation, where the \
                 update is written"
          | _ => throwErrorAt arrow "unknown `sol_derivation` arrow"
        proofs := proofs.push proof
        prev := target
      let some proof := proofs.back? | throwErrorAt name
        "`sol_derivation` needs at least one step"
      let mut folded := proof
      for p in proofs.pop.reverse do
        folded ← match layer with
          | .sequent => `(FrontierMultiStep.trans $p $folded)
          | .judgment => `(JudgmentMultiStep.trans $p $folded)
          | .block => `(BlockReflMultiStep.trans $p $folded)
      let stmt ← match layer with
        | .sequent => `($first ⇝ᵘ* $prev)
        | .judgment => `($first ⇝ᵈ* $prev)
        | .block => `($first ⇝* $prev)
      elabCommand (←
        `(command| $[$doc:docComment]? theorem $name : $stmt := $folded))

end Solidity.Examples
