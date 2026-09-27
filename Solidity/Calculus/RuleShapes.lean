import Solidity.Calculus.Rules

/-!
# Where each taclet comes from

`Rules.lean` names each `Taclet` constructor after the solkey taclet it
transcribes, but a name is a promise, not a check: an operator family is one
constructor for five or fourteen taclets, a constructor can cover two KeY
shapes the Lean syntax does not tell apart, and a KeY taclet can have no
constructor at all.  This module writes the correspondence down and checks
it.

`Taclet` is a `Prop`, so there is no function on its derivations to hang an
origin on; the table is keyed by constructor *name* instead, and two checks
keep it honest.  Each key is a double-backtick name, which fails elaboration
if the constructor does not exist; `#check_constructor_table` then reads the
constructor list from the environment and fails unless every constructor has
exactly one row.  A constructor added to `Rules.lean` without an origin does
not build here.

The other direction is `taclets_partitioned`: every taclet of
`solidityProgramRules.key` is claimed by some row or listed in
`unclaimedTaclets` with a reason, never both.  The reasons are the places the
typed syntax is narrower than solkey's (no calls, no `new`, no memory
`delete`), the places it is coarser (a memory path is a source as it stands,
so nothing captures one), and the places the calculus has no strategy to
express (the literal-condition `if` rules, the callback semantics of
`transfer`).

What this module does *not* say is whether a constructor's premise is
*right*; that is the soundness development.
-/

namespace Solidity

/-! ## Checking a table against the environment -/

section Check
open Lean Elab Command Meta

private unsafe def evalNamesImpl (e : Expr) : MetaM (List Lean.Name) :=
  evalExpr (List Lean.Name) (mkApp (mkConst ``List [levelZero]) (mkConst ``Lean.Name)) e

@[implemented_by evalNamesImpl]
private opaque evalNames (e : Expr) : MetaM (List Lean.Name)

/-- `#check_constructor_table I, names` fails unless the list `names` (a
`List Lean.Name`, evaluated) is the constructors of the inductive `I`, each once.
The error names every constructor missing from the list, every entry that is
not a constructor, and every entry listed twice. -/
elab "#check_constructor_table " ind:ident ", " tbl:term : command => do
  let indName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo ind
  let .inductInfo info ← getConstInfo indName
    | throwErrorAt ind "{indName} is not an inductive type"
  let names ← liftTermElabM do
    let ty := mkApp (mkConst ``List [levelZero]) (mkConst ``Lean.Name)
    let e ← Term.elabTermEnsuringType tbl ty
    Term.synthesizeSyntheticMVarsNoPostponing
    evalNames (← instantiateMVars e)
  let missing := info.ctors.filter (!names.contains ·)
  let extra := names.filter (!info.ctors.contains ·)
  let dups := (names.filter fun n => names.count n > 1).eraseDups
  unless missing.isEmpty && extra.isEmpty && dups.isEmpty do
    throwError "the table does not list the constructors of {indName}:\
      \n  missing: {missing}\n  not a constructor: {extra}\n  listed twice: {dups}"

end Check

namespace RuleShapes

/-! ## The origin of each constructor

In `Rules.lean`'s order.  A `merged` row is a constructor whose `\find`
covers several taclets: an operator family, a KeY split by the source's
kind (a value against a reference, `…MemRef…`) or by the receiver's (a
mapping against an array). -/


/-- Every `Taclet` constructor, and the solkey taclets it transcribes. -/
def tacletOrigins : List (Lean.Name × KeyOrigin) := [
  -- Step 1: unfold a storage read
  (``Taclet.storageFieldRead_unfold_rightFst, .taclet .storageFieldRead_unfold_rightFst),
  (``Taclet.storageIndexRead_unfold_rightFst, .taclet .storageIndexRead_unfold_rightFst),
  (``Taclet.storageIndexRead_unfold_rightSndIndex, .taclet .storageIndexRead_unfold_rightSndIndex),
  (``Taclet.storageFieldRead_unfold_rightSndResult,
    .merged [.storageFieldRead_unfold_rightSndResult, .storageFieldWriteCaptureSrc]),
  (``Taclet.storageIndexRead_unfold_rightSndResult,
    .merged [.storageIndexRead_unfold_rightSndResult, .storageIndexWriteStorageRefRhsCapture]),
  -- Step 2: decompose a storage write
  (``Taclet.storageFieldWrite_unfold_leftFst, .taclet .storageFieldWrite_unfold_leftFst),
  (``Taclet.storageFieldWriteStorageRef_unfold_leftFst,
    .taclet .storageFieldWriteStorageRef_unfold_leftFst),
  (``Taclet.storageIndexWriteCaptureAllComplexRecv,
    .taclet .storageIndexWriteCaptureAllComplexRecv),
  (``Taclet.storageIndexWriteStorageRefCaptureAllComplexRecv,
    .taclet .storageIndexWriteStorageRefCaptureAllComplexRecv),
  (``Taclet.storageIndexWriteCaptureAllNonSimpleIndex,
    .taclet .storageIndexWriteCaptureAllNonSimpleIndex),
  (``Taclet.storageIndexWriteStorageRefCaptureAllNonSimpleIndex,
    .taclet .storageIndexWriteStorageRefCaptureAllNonSimpleIndex),
  (``Taclet.storageRootWriteValueRhsCapture, .taclet .storageRootWriteValueRhsCapture),
  (``Taclet.fieldWriteValueRhsCapture, .taclet .fieldWriteValueRhsCapture),
  (``Taclet.indexWriteValueRhsCapture, .taclet .indexWriteValueRhsCapture),
  (``Taclet.storageFieldDelete_unfold_leftFst, .taclet .storageFieldDelete_unfold_leftFst),
  (``Taclet.storageIndexDelete_unfold_leftFst, .taclet .storageIndexDelete_unfold_leftFst),
  (``Taclet.storageIndexDeleteNonSimpleIndexCapture,
    .taclet .storageIndexDeleteNonSimpleIndexCapture),
  -- Declarations
  (``Taclet.localValueDeclInitDrop, .taclet .localValueDeclInitDrop),
  (``Taclet.valueDeclSkip, .taclet .valueDeclSkip),
  (``Taclet.storageLocalDeclInitDrop, .taclet .storageLocalDeclInitDrop),
  (``Taclet.storageLocalDeclSkip, .taclet .storageLocalDeclSkip),
  (``Taclet.memoryLocalDeclInitDrop, .taclet .memoryLocalDeclInitDrop),
  (``Taclet.memoryReferenceDeclFreshAlloc, .taclet .memoryReferenceDeclFreshAlloc),
  -- Step 3: storage reads and writes as updates
  (``Taclet.localValueAssign, .taclet .localValueAssign),
  (``Taclet.storageRootReadSelect, .taclet .storageRootReadSelect),
  (``Taclet.storageFieldReadFind, .taclet .storageFieldReadFind),
  (``Taclet.storageIndexReadMappingFind, .taclet .storageIndexReadMappingFind),
  (``Taclet.storageIndexReadArrayFind, .taclet .storageIndexReadArrayFind),
  (``Taclet.storageRootWriteStore, .taclet .storageRootWriteStore),
  (``Taclet.storageRootWriteCopySource, .taclet .storageRootWriteCopySource),
  (``Taclet.storageFieldReadStoreRoot, .taclet .storageFieldReadStoreRoot),
  (``Taclet.storageIndexReadMappingStoreRoot, .taclet .storageIndexReadMappingStoreRoot),
  (``Taclet.storageIndexReadArrayStoreRoot, .taclet .storageIndexReadArrayStoreRoot),
  (``Taclet.storageFieldWriteSave, .taclet .storageFieldWriteSave),
  (``Taclet.storageFieldWriteCopySource, .taclet .storageFieldWriteCopySource),
  (``Taclet.storageIndexWriteMappingSave, .taclet .storageIndexWriteMappingSave),
  (``Taclet.storageIndexWriteArraySave, .taclet .storageIndexWriteArraySave),
  (``Taclet.storageIndexWriteMappingCopySource, .taclet .storageIndexWriteMappingCopySource),
  (``Taclet.storageIndexWriteArrayCopySource, .taclet .storageIndexWriteArrayCopySource),
  (``Taclet.storageLocalRootRebind, .taclet .storageLocalRootRebind),
  (``Taclet.storageFieldReadBindLocalRoot, .taclet .storageFieldReadBindLocalRoot),
  (``Taclet.storageIndexReadMappingBindLocalRoot, .taclet .storageIndexReadMappingBindLocalRoot),
  (``Taclet.storageIndexReadArrayBindLocalRoot, .taclet .storageIndexReadArrayBindLocalRoot),
  (``Taclet.storageIndexReadArrayBindLocalRootMappingElement,
    .taclet .storageIndexReadArrayBindLocalRootMappingElement),
  (``Taclet.storageRootDelete, .taclet .storageRootDelete),
  (``Taclet.storageFieldDelete, .taclet .storageFieldDelete),
  (``Taclet.storageIndexDelete, .taclet .storageIndexDelete),
  (``Taclet.storageIndexArrayDelete, .taclet .storageIndexArrayDelete),
  -- Operators: `+ - * ** / %`, then the comparisons, then `&& ||`
  (``Taclet.binopAssignment, .merged [.additionAssignment, .subtractionAssignment,
    .multiplicationAssignment, .powerAssignment, .divisionAssignment, .moduloAssignment,
    .lessThanAssignment, .greaterThanAssignment, .lessEqualAssignment, .greaterEqualAssignment,
    .boolEqualityAssignment, .boolInequalityAssignment,
    .logicalAndAssignment, .logicalOrAssignment]),
  (``Taclet.binopUnfoldLeft, .merged [.addition_unfold_left, .subtraction_unfold_left,
    .multiplication_unfold_left, .power_unfold_left, .division_unfold_left, .modulo_unfold_left,
    .lessThanCaptureLhs, .greaterThanCaptureLhs, .lessEqualCaptureLhs, .greaterEqualCaptureLhs,
    .boolEqualityCaptureLhs, .boolInequalityCaptureLhs,
    .logicalAndCaptureLhs, .logicalOrCaptureLhs]),
  -- no `&&`/`||` instance: those are the short-circuit rows below
  (``Taclet.binopUnfoldRight, .merged [.addition_unfold_right, .subtraction_unfold_right,
    .multiplication_unfold_right, .power_unfold_right, .division_unfold_right,
    .modulo_unfold_right,
    .lessThanCaptureRhs, .greaterThanCaptureRhs, .lessEqualCaptureRhs, .greaterEqualCaptureRhs,
    .boolEqualityCaptureRhs, .boolInequalityCaptureRhs]),
  (``Taclet.logicalAndShortCircuitRhs, .taclet .logicalAndShortCircuitRhs),
  (``Taclet.logicalOrShortCircuitRhs, .taclet .logicalOrShortCircuitRhs),
  (``Taclet.unopAssignment, .merged [.unaryMinusAssignment, .logicalNotAssignment]),
  (``Taclet.unopCapture, .merged [.unaryMinusCapture, .logicalNotCapture]),
  -- The conditional: `lhs` is a local, a storage or a memory location
  (``Taclet.ternaryToIf, .merged [.ternaryToIf, .ternaryToIfStorage]),
  (``Taclet.ternaryCaptureCond, .taclet .ternaryCaptureCond),
  -- Compound assignment (`+= -= *= /= %=`) and `++`/`--` (pre, post)
  (``Taclet.localOpAssign, .merged [.localAddAssign, .localSubAssign, .localMulAssign,
    .localDivAssign, .localModAssign]),
  (``Taclet.storageRootOpAssign, .merged [.storageRootAddAssign, .storageRootSubAssign,
    .storageRootMulAssign, .storageRootDivAssign, .storageRootModAssign]),
  (``Taclet.storageFieldOpAssign, .merged [.storageFieldAddAssign, .storageFieldSubAssign,
    .storageFieldMulAssign, .storageFieldDivAssign, .storageFieldModAssign]),
  (``Taclet.storageIndexMappingOpAssign, .merged [.storageIndexMappingAddAssign,
    .storageIndexMappingSubAssign, .storageIndexMappingMulAssign, .storageIndexMappingDivAssign,
    .storageIndexMappingModAssign]),
  (``Taclet.storageIndexArrayOpAssign, .merged [.storageIndexArrayAddAssign,
    .storageIndexArraySubAssign, .storageIndexArrayMulAssign, .storageIndexArrayDivAssign,
    .storageIndexArrayModAssign]),
  (``Taclet.memoryFieldOpAssign, .merged [.memoryFieldAddAssign, .memoryFieldSubAssign,
    .memoryFieldMulAssign, .memoryFieldDivAssign, .memoryFieldModAssign]),
  (``Taclet.memoryIndexArrayOpAssign, .merged [.memoryIndexArrayAddAssign,
    .memoryIndexArraySubAssign, .memoryIndexArrayMulAssign, .memoryIndexArrayDivAssign,
    .memoryIndexArrayModAssign]),
  (``Taclet.storageFieldOpAssignUnfoldLeftFst, .merged [.storageFieldAddAssign_unfold_leftFst,
    .storageFieldSubAssign_unfold_leftFst, .storageFieldMulAssign_unfold_leftFst,
    .storageFieldDivAssign_unfold_leftFst, .storageFieldModAssign_unfold_leftFst]),
  (``Taclet.storageIndexOpAssignUnfoldLeftFst, .merged [.storageIndexAddAssign_unfold_leftFst,
    .storageIndexSubAssign_unfold_leftFst, .storageIndexMulAssign_unfold_leftFst,
    .storageIndexDivAssign_unfold_leftFst, .storageIndexModAssign_unfold_leftFst]),
  (``Taclet.memoryFieldOpAssignUnfoldLeftFst, .merged [.memoryFieldAddAssign_unfold_leftFst,
    .memoryFieldSubAssign_unfold_leftFst, .memoryFieldMulAssign_unfold_leftFst,
    .memoryFieldDivAssign_unfold_leftFst, .memoryFieldModAssign_unfold_leftFst]),
  (``Taclet.memoryIndexOpAssignUnfoldLeftFst, .merged [.memoryIndexAddAssign_unfold_leftFst,
    .memoryIndexSubAssign_unfold_leftFst, .memoryIndexMulAssign_unfold_leftFst,
    .memoryIndexDivAssign_unfold_leftFst, .memoryIndexModAssign_unfold_leftFst]),
  (``Taclet.compoundAssignValueRhsCapture, .merged [.addAssignValueRhsCapture,
    .subAssignValueRhsCapture, .mulAssignValueRhsCapture, .divAssignValueRhsCapture,
    .modAssignValueRhsCapture]),
  (``Taclet.localIncrement, .merged [.localPreincrement, .localPredecrement,
    .localPostincrement, .localPostdecrement]),
  (``Taclet.storageRootIncrement, .merged [.storageRootPreincrement, .storageRootPredecrement,
    .storageRootPostincrement, .storageRootPostdecrement]),
  (``Taclet.storageFieldIncrement, .merged [.storageFieldPreincrement,
    .storageFieldPredecrement, .storageFieldPostincrement, .storageFieldPostdecrement]),
  (``Taclet.storageIndexIncrement, .merged [
    .storageIndexMappingPreincrement, .storageIndexMappingPredecrement,
    .storageIndexMappingPostincrement, .storageIndexMappingPostdecrement,
    .storageIndexArrayPreincrement, .storageIndexArrayPredecrement,
    .storageIndexArrayPostincrement, .storageIndexArrayPostdecrement]),
  (``Taclet.memoryFieldIncrement, .merged [.memoryFieldPreincrement, .memoryFieldPredecrement,
    .memoryFieldPostincrement, .memoryFieldPostdecrement]),
  (``Taclet.memoryIndexArrayIncrement, .merged [.memoryIndexArrayPreincrement,
    .memoryIndexArrayPredecrement, .memoryIndexArrayPostincrement,
    .memoryIndexArrayPostdecrement]),
  (``Taclet.storageFieldIncrementUnfoldLeftFst, .merged [
    .storageFieldPreincrement_unfold_leftFst, .storageFieldPredecrement_unfold_leftFst,
    .storageFieldPostincrement_unfold_leftFst, .storageFieldPostdecrement_unfold_leftFst]),
  (``Taclet.storageIndexIncrementUnfoldLeftFst, .merged [
    .storageIndexPreincrement_unfold_leftFst, .storageIndexPredecrement_unfold_leftFst,
    .storageIndexPostincrement_unfold_leftFst, .storageIndexPostdecrement_unfold_leftFst]),
  (``Taclet.memoryFieldIncrementUnfoldLeftFst, .merged [
    .memoryFieldPreincrement_unfold_leftFst, .memoryFieldPredecrement_unfold_leftFst,
    .memoryFieldPostincrement_unfold_leftFst, .memoryFieldPostdecrement_unfold_leftFst]),
  (``Taclet.memoryIndexIncrementUnfoldLeftFst, .merged [
    .memoryIndexPreincrement_unfold_leftFst, .memoryIndexPredecrement_unfold_leftFst,
    .memoryIndexPostincrement_unfold_leftFst, .memoryIndexPostdecrement_unfold_leftFst]),
  -- `vp = v++`: KeY has one taclet for the assignment and one for the declaration
  (``Taclet.localAssignIncrement, .merged [
    .localAssignPreincrement, .localAssignPredecrement,
    .localAssignPostincrement, .localAssignPostdecrement,
    .localDeclPreincrement, .localDeclPredecrement,
    .localDeclPostincrement, .localDeclPostdecrement]),
  (``Taclet.storageRootIncrementAssignment, .merged [
    .storageRootPreincrementAssignment, .storageRootPredecrementAssignment,
    .storageRootPostincrementAssignment, .storageRootPostdecrementAssignment]),
  (``Taclet.storageFieldIncrementAssignment, .merged [
    .storageFieldPreincrementAssignment, .storageFieldPredecrementAssignment,
    .storageFieldPostincrementAssignment, .storageFieldPostdecrementAssignment]),
  (``Taclet.storageIndexIncrementAssignment, .merged [
    .storageIndexMappingPreincrementAssignment, .storageIndexMappingPredecrementAssignment,
    .storageIndexMappingPostincrementAssignment, .storageIndexMappingPostdecrementAssignment,
    .storageIndexArrayPreincrementAssignment, .storageIndexArrayPredecrementAssignment,
    .storageIndexArrayPostincrementAssignment, .storageIndexArrayPostdecrementAssignment]),
  (``Taclet.memoryFieldIncrementAssignment, .merged [
    .memoryFieldPreincrementAssignment, .memoryFieldPredecrementAssignment,
    .memoryFieldPostincrementAssignment, .memoryFieldPostdecrementAssignment]),
  (``Taclet.memoryIndexArrayIncrementAssignment, .merged [
    .memoryIndexArrayPreincrementAssignment, .memoryIndexArrayPredecrementAssignment,
    .memoryIndexArrayPostincrementAssignment, .memoryIndexArrayPostdecrementAssignment]),
  -- Arrays
  (``Taclet.storagePushValueSave, .taclet .storagePushValueSave),
  (``Taclet.storagePushValueCopySource, .taclet .storagePushValueCopySource),
  (``Taclet.storagePushLengthSave, .taclet .storagePushLengthSave),
  (``Taclet.storagePushLengthSaveReferenceElement,
    .taclet .storagePushLengthSaveReferenceElement),
  (``Taclet.storagePushValue_unfold_rightSndArgument,
    .taclet .storagePushValue_unfold_rightSndArgument),
  (``Taclet.storagePushValue_unfold_leftFstReceiver,
    .taclet .storagePushValue_unfold_leftFstReceiver),
  (``Taclet.storagePush_unfold_leftFstReceiver, .taclet .storagePush_unfold_leftFstReceiver),
  (``Taclet.storagePop_unfold_leftFstReceiver, .taclet .storagePop_unfold_leftFstReceiver),
  (``Taclet.storagePopSave, .taclet .storagePopSave),
  (``Taclet.storagePopSaveMappingElement, .taclet .storagePopSaveMappingElement),
  (``Taclet.storageLocalRootPush_unfold_leftFstReceiver,
    .taclet .storageLocalRootPush_unfold_leftFstReceiver),
  (``Taclet.storageLocalRootPushBind, .taclet .storageLocalRootPushBind),
  (``Taclet.storageLocalRootPushBindMappingElement,
    .taclet .storageLocalRootPushBindMappingElement),
  -- Transfer
  (``Taclet.transfer_unfold_leftFstReceiver, .taclet .transfer_unfold_leftFstReceiver),
  (``Taclet.transfer_unfold_rightSndArgument, .taclet .transfer_unfold_rightSndArgument),
  (``Taclet.transferNoCallback, .merged [.transferNoCallbackBox, .transferNoCallbackDiamond]),
  -- Memory: `msrc` is a value or a memory reference, so a row covers `…MemRef…` except
  -- for the index captures, which KeY and the table split by the source
  (``Taclet.memoryFieldRead_unfold_rightFst, .taclet .memoryFieldRead_unfold_rightFst),
  (``Taclet.memoryIndexRead_unfold_rightFst, .taclet .memoryIndexRead_unfold_rightFst),
  (``Taclet.memoryIndexRead_unfold_rightSndIndex, .taclet .memoryIndexRead_unfold_rightSndIndex),
  (``Taclet.memoryFieldReadHeap, .taclet .memoryFieldRead),
  (``Taclet.memoryIndexReadHeap, .taclet .memoryIndexReadArrayValue),
  (``Taclet.memoryRootAlias, .taclet .memoryRootRebind),
  (``Taclet.memoryFieldReadAliasRoot, .taclet .memoryFieldRead),
  (``Taclet.memoryIndexReadAliasRoot, .taclet .memoryIndexReadArrayMemory),
  (``Taclet.memoryFieldWriteStore, .taclet .memoryFieldWrite),
  (``Taclet.memoryIndexWriteStore, .taclet .memoryIndexWriteArray),
  (``Taclet.memoryFieldWriteCopy, .taclet .memoryFieldWrite),
  (``Taclet.memoryIndexWriteCopy, .taclet .memoryIndexWriteArray),
  (``Taclet.memoryFieldWrite_unfold_leftFst,
    .merged [.memoryFieldWrite_unfold_leftFst, .memoryFieldWriteMemRef_unfold_leftFst]),
  (``Taclet.memoryIndexWriteCaptureAllComplexRecv,
    .taclet .memoryIndexWriteCaptureAllComplexRecv),
  (``Taclet.memoryIndexWriteMemRefCaptureAllComplexRecv,
    .taclet .memoryIndexWriteMemRefCaptureAllComplexRecv),
  (``Taclet.memoryIndexWriteCaptureAllNonSimpleIndex,
    .taclet .memoryIndexWriteCaptureAllNonSimpleIndex),
  (``Taclet.memoryIndexWriteMemRefCaptureAllNonSimpleIndex,
    .taclet .memoryIndexWriteMemRefCaptureAllNonSimpleIndex),
  (``Taclet.memoryFieldWriteUnfoldSource, .taclet .fieldWriteValueRhsCapture),
  (``Taclet.memoryIndexWriteUnfoldSource, .taclet .indexWriteValueRhsCapture),
  -- Storage and memory: `mpath` is any memory path, a member one included
  (``Taclet.memoryStorageCopy, .taclet .memoryStorageCopy),
  (``Taclet.memoryStorageCopyUnfold, .taclet .memoryStorageCopyUnfold),
  (``Taclet.memoryToStorageStoreRoot, .taclet .memoryToStorageStoreRoot),
  (``Taclet.memoryToStorageFieldCopyRoot,
    .merged [.memoryToStorageFieldCopyRoot, .memoryToStorageFieldCopyField]),
  (``Taclet.memoryToStorageIndexMappingCopyRoot, .taclet .memoryToStorageIndexMappingCopyRoot),
  (``Taclet.memoryToStorageIndexArrayCopyRoot, .taclet .memoryToStorageIndexArrayCopyRoot),
  (``Taclet.memoryToStorageField_unfold_leftFst, .taclet .memoryToStorageField_unfold_leftFst),
  (``Taclet.memoryToStorageIndexCaptureAllComplexRecv,
    .taclet .memoryToStorageIndexCaptureAllComplexRecv),
  (``Taclet.memoryToStorageIndexCaptureAllNonSimpleIndex,
    .taclet .memoryToStorageIndexCaptureAllNonSimpleIndex),
  -- Control flow: an `if` without `else` is one with an empty `else`
  (``Taclet.ifElseUnfold, .merged [.ifUnfold, .ifElseUnfold]),
  (``Taclet.ifElseSplit, .merged [.ifSplit, .ifElseSplit]),
  (``Taclet.requireConditionCapture, .taclet .requireConditionCapture),
  (``Taclet.requireSimple, .taclet .requireSimple),
  (``Taclet.assertConditionCapture, .taclet .assertConditionCapture),
  (``Taclet.assertSimple, .taclet .assertSimple),
  (``Taclet.revertBox, .taclet .revertBox),
  (``Taclet.revertDiamond, .taclet .revertDiamond) ]

#check_constructor_table Taclet, tacletOrigins.map Prod.fst

/-! ## Which KeY taclets the table claims -/

/-- Whether some row names the taclet. -/
def claims (t : KeyTaclet) : Bool :=
  tacletOrigins.any fun r => r.2.taclets.contains t

/-- Every taclet some row names, in `KeyTaclet.all`'s order. -/
def claimedTaclets : List KeyTaclet := KeyTaclet.all.filter claims

/-- The taclets of `solidityProgramRules.key` that **no** row claims, and why.

* `emptyModality`, `blockEmpty` — architectural.  A program is a list of
  statements with branch bodies inlined, so there is no nested block to erase
  and no `{} ; rest` to find; a derivation that reaches `⟨[ ]⟩` *is* the Lean
  analogue of `emptyModality`.
* `functionBodyExpand` — the typed syntax has no calls.
* `memoryArrayFreshAlloc`, `newArrayCapture` — nor `new T[](n)` (no `new`
  yet): a memory array is made by declaration (`memoryReferenceDeclFreshAlloc`)
  or by copy from storage.
* The eight memory-`delete` taclets — nor `delete` of a memory location;
  `Stmt.delete` takes a storage one.
* `memoryFieldRead_unfold_rightSndResult`, `memoryIndexRead_unfold_rightSndResult`,
  `memoryFieldWriteCaptureSrc`, `memoryIndexWriteMemRefRhsCapture` — KeY
  captures a memory reference into an alias before writing it; here a memory
  path is a source as it stands (`mpath`), so `memoryFieldWriteCopy` and the
  `memoryToStorage…CopyRoot` rows write it in one step, and a value read is
  captured by `fieldWriteValueRhsCapture`/`indexWriteValueRhsCapture`.
* `ifTrue`, `ifFalse`, `ifElseTrue`, `ifElseFalse`, `ifElseNegated` — the
  `concrete_solidity` shortcuts on a literal or negated condition.  A literal is
  simple, so `ifElseSplit` applies and one of its goals assumes `true = false`;
  `!se` is not simple, so `ifElseUnfold` captures it.  They are strategy, and
  the table has no strategy.
* `transferWithCallbackBox`, `transferWithCallbackDiamond` — the other
  semantics of `transfer`, in which the callee may re-enter; the table
  transcribes the no-callback pair. -/
def unclaimedTaclets : List KeyTaclet :=
  [ .emptyModality, .blockEmpty,
    .functionBodyExpand,
    .memoryArrayFreshAlloc, .newArrayCapture,
    .memoryRootDeleteFreshRebind, .memoryFieldDeletePrimitive, .memoryFieldDeleteReference,
    .memoryIndexDeletePrimitive, .memoryIndexDeleteReference,
    .memoryFieldDelete_unfold_leftFst, .memoryIndexDelete_unfold_leftFst,
    .memoryIndexDeleteNonSimpleIndexCapture,
    .memoryFieldRead_unfold_rightSndResult, .memoryIndexRead_unfold_rightSndResult,
    .memoryFieldWriteCaptureSrc, .memoryIndexWriteMemRefRhsCapture,
    .ifTrue, .ifFalse, .ifElseTrue, .ifElseFalse, .ifElseNegated,
    .transferWithCallbackBox, .transferWithCallbackDiamond ]

/-- **The coverage fact**: the corpus splits into what the table claims and
what this file excuses, with nothing in both and nothing in neither.  A taclet
that appears upstream and is never ported fails this, and so does a row that
claims a taclet the list above excuses. -/
theorem taclets_partitioned :
    KeyTaclet.all.all (fun t => claims t != unclaimedTaclets.contains t) = true := by
  decide +kernel

theorem claimedTaclets_count : claimedTaclets.length = 287 := by decide +kernel

theorem unclaimedTaclets_count : unclaimedTaclets.length = 24 := by decide +kernel

/-! ## The rows with no taclet

A `leanOnly` row would be a claim that upstream has no counterpart.  There is
none: the constructors that used to be Lean's own (front-end lowering of push
sugar, scratch aliases, the call rule, `**=`) went with the untyped syntax.
The count is kept so that one added later has to say so here. -/

theorem leanOnly_count :
    (tacletOrigins.filter fun r => r.2 == .leanOnly).length = 0 := by decide +kernel

/-! ## `\heuristics` agree within a row

`\heuristics` is KeY's strategy annotation (`KeyTaclets.lean`) and the table
has no strategy, but it is still information about the calculus: a row whose
taclets sat in two rule sets would be merging taclets KeY treats differently.
None does, and no row claims a `concrete_solidity` taclet — those are exactly
the five literal-condition `if` rules excused above. -/

/-- The rule sets a row's taclets are filed under. -/
def heuristics (o : KeyOrigin) : List Heuristic :=
  (o.taclets.map KeyTaclet.heuristic).eraseDups

theorem heuristics_agree :
    tacletOrigins.all (fun r => (heuristics r.2).length == 1 || r.2 == .leanOnly) = true := by
  decide +kernel

theorem concrete_unclaimed :
    claimedTaclets.all (fun t => t.heuristic != .concreteSolidity) = true := by
  decide +kernel

end RuleShapes
end Solidity
