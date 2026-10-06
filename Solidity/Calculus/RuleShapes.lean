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
typed syntax is narrower than solkey's, the places it is coarser (a memory path is a source as it stands,
so nothing captures one), and the places the calculus has no strategy to
express (the literal-condition `if` rules).  The callback semantics of
`transfer` is a table of its own (`callbackOrigins`), its taclet being sound
for another reading of the modalities.

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

/-- `#enum_ctors I` defines, for an inductive `I` whose constructors take no
arguments, `I.all`, every constructor in declaration order, and `I.name`, a
constructor's own name (`I.c` is `"c"`): the two tables an enumeration of
names needs, written from the constructor list so that they cannot drift
from it.  Both are ordinary definitions, which the kernel reduces. -/
elab "#enum_ctors " ind:ident : command => do
  let indName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo ind
  let .inductInfo info ← getConstInfo indName
    | throwErrorAt ind "{indName} is not an inductive type"
  let T := mkIdent indName
  let ctors := info.ctors.toArray.map mkIdent
  let alts ← info.ctors.toArray.mapM fun c =>
    `(Parser.Term.matchAltExpr| | $(mkIdent c):ident => $(quote c.getString!))
  elabCommand (← `(/-- Every constructor, in declaration order. -/
    def $(mkIdent (`_root_ ++ indName ++ `all)):ident : List $T := [$ctors,*]))
  elabCommand (← `(/-- The constructor's own name. -/
    def $(mkIdent (`_root_ ++ indName ++ `name)):ident : $T → String :=
      fun r => match r with $alts:matchAlt*))

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
  -- Lengths: KeY reads `sp.length` as the member `length`, so the member-read taclets
  (``Taclet.storageLengthRead, .taclet .storageFieldReadFind),
  (``Taclet.storageLengthRead_unfold_rightFst, .taclet .storageFieldRead_unfold_rightFst),
  (``Taclet.memoryLengthRead, .taclet .memoryFieldRead),
  (``Taclet.memoryLengthRead_unfold_rightFst, .taclet .memoryFieldRead_unfold_rightFst),
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
  (``Taclet.transferNoCallbackBox, .taclet .transferNoCallbackBox),
  (``Taclet.send_unfold_leftFstReceiver, .taclet .send_unfold_leftFstReceiver),
  (``Taclet.send_unfold_rightSndArgument, .taclet .send_unfold_rightSndArgument),
  (``Taclet.sendNoCallbackBox, .taclet .sendNoCallbackBox),
  (``Taclet.sendNoCallbackDiamond, .taclet .sendNoCallbackDiamond),
  -- Memory: `msrc` is a value or a memory reference, so a row covers `…MemRef…` except
  -- for the index captures, which KeY and the table split by the source
  (``Taclet.memoryFieldRead_unfold_rightFst, .taclet .memoryFieldRead_unfold_rightFst),
  (``Taclet.memoryIndexRead_unfold_rightFst, .taclet .memoryIndexRead_unfold_rightFst),
  (``Taclet.memoryIndexRead_unfold_rightSndIndex, .taclet .memoryIndexRead_unfold_rightSndIndex),
  (``Taclet.memoryFieldRead, .taclet .memoryFieldRead),
  (``Taclet.memoryIndexReadArrayValue, .taclet .memoryIndexReadArrayValue),
  (``Taclet.memoryRootRebind, .taclet .memoryRootRebind),
  (``Taclet.memoryFieldReadAliasRoot, .taclet .memoryFieldRead),
  (``Taclet.memoryIndexReadArrayMemory, .taclet .memoryIndexReadArrayMemory),
  (``Taclet.memoryFieldWrite, .taclet .memoryFieldWrite),
  (``Taclet.memoryIndexWriteArray, .taclet .memoryIndexWriteArray),
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
  (``Taclet.memoryRootDeleteFreshRebind, .taclet .memoryRootDeleteFreshRebind),
  (``Taclet.memoryFieldDeletePrimitive, .taclet .memoryFieldDeletePrimitive),
  (``Taclet.memoryFieldDeleteReference, .taclet .memoryFieldDeleteReference),
  (``Taclet.memoryIndexDeletePrimitive, .taclet .memoryIndexDeletePrimitive),
  (``Taclet.memoryIndexDeleteReference, .taclet .memoryIndexDeleteReference),
  (``Taclet.memoryFieldDelete_unfold_leftFst, .taclet .memoryFieldDelete_unfold_leftFst),
  (``Taclet.memoryIndexDelete_unfold_leftFst, .taclet .memoryIndexDelete_unfold_leftFst),
  (``Taclet.memoryIndexDeleteNonSimpleIndexCapture,
    .taclet .memoryIndexDeleteNonSimpleIndexCapture),
  (``Taclet.memoryArrayFreshAlloc, .taclet .memoryArrayFreshAlloc),
  (``Taclet.newArrayCapture, .taclet .newArrayCapture),
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
  (``Taclet.revertDiamond, .taclet .revertDiamond),
  -- Calls
  (``Taclet.functionBodyExpand, .taclet .functionBodyExpand),
  -- solkey `671f6762a9` splits it off `functionBodyExpand`: a call without targets
  (``Taclet.internalCallExpand, .taclet .internalCallExpand),
  (``Taclet.tryCallNoCallbackBox, .taclet .tryCallNoCallbackBox) ]

#check_constructor_table Taclet, tacletOrigins.map Prod.fst

/-- The callback taclets (`Rules.lean`'s `CallbackTaclet`, the other
`transferSemantics`), and the solkey taclets they transcribe. -/
def callbackOrigins : List (Lean.Name × KeyOrigin) := [
  (``CallbackTaclet.transferWithCallbackBox, .taclet .transferWithCallbackBox),
  (``CallbackTaclet.sendWithCallbackBox, .taclet .sendWithCallbackBox),
  (``CallbackTaclet.tryCallWithCallbackBox, .taclet .tryCallWithCallbackBox) ]

#check_constructor_table CallbackTaclet, callbackOrigins.map Prod.fst

/-! ## KeY's taclet at an operator

A `merged` row of an operator family lists KeY's taclets in the order of
its operators (`operatorOrder`): the proof tree prints a node as KeY's
taclet at the operator its statement has (`keyTacletAt`), `additionAssignment`
where the row is `binopAssignment`.  A row split by something other than the
operator (a mapping against an array) is not listed, and prints under its
own name.  `localAssignIncrement`'s row also lists KeY's declaration
taclets, after the four of the assignment; the rule fires only on the
assignment (a declaration reaches it through `localValueDeclInitDrop`), so
its operator picks one of the first four. -/

/-- The operators of a merged row, in the order of its taclets. -/
def operatorOrder : List (Lean.Name × List Lean.Name) :=
  let arith := [``BinOp.add, ``BinOp.sub, ``BinOp.mul, ``BinOp.pow, ``BinOp.div, ``BinOp.mod]
  let cmp := [``BinOp.lt, ``BinOp.gt, ``BinOp.le, ``BinOp.ge, ``BinOp.eqB, ``BinOp.neB]
  let compound := [``BinOp.add, ``BinOp.sub, ``BinOp.mul, ``BinOp.div, ``BinOp.mod]
  let incDec := [``IncDec.preInc, ``IncDec.preDec, ``IncDec.postInc, ``IncDec.postDec]
  [(``Taclet.binopAssignment, arith ++ cmp ++ [``BinOp.and, ``BinOp.or]),
   (``Taclet.binopUnfoldLeft, arith ++ cmp ++ [``BinOp.and, ``BinOp.or]),
   (``Taclet.binopUnfoldRight, arith ++ cmp),
   (``Taclet.unopAssignment, [``UnOp.neg, ``UnOp.not]),
   (``Taclet.unopCapture, [``UnOp.neg, ``UnOp.not])] ++
  ([``Taclet.localOpAssign, ``Taclet.storageRootOpAssign, ``Taclet.storageFieldOpAssign,
    ``Taclet.storageIndexMappingOpAssign, ``Taclet.storageIndexArrayOpAssign,
    ``Taclet.memoryFieldOpAssign, ``Taclet.memoryIndexArrayOpAssign,
    ``Taclet.storageFieldOpAssignUnfoldLeftFst, ``Taclet.storageIndexOpAssignUnfoldLeftFst,
    ``Taclet.memoryFieldOpAssignUnfoldLeftFst, ``Taclet.memoryIndexOpAssignUnfoldLeftFst,
    ``Taclet.compoundAssignValueRhsCapture].map (·, compound)) ++
  ([``Taclet.localIncrement, ``Taclet.storageRootIncrement, ``Taclet.storageFieldIncrement,
    ``Taclet.memoryFieldIncrement, ``Taclet.memoryIndexArrayIncrement,
    ``Taclet.storageFieldIncrementUnfoldLeftFst, ``Taclet.storageIndexIncrementUnfoldLeftFst,
    ``Taclet.memoryFieldIncrementUnfoldLeftFst, ``Taclet.memoryIndexIncrementUnfoldLeftFst,
    ``Taclet.storageRootIncrementAssignment, ``Taclet.storageFieldIncrementAssignment,
    ``Taclet.memoryFieldIncrementAssignment, ``Taclet.memoryIndexArrayIncrementAssignment,
    ``Taclet.localAssignIncrement].map
    (·, incDec))

/-- KeY's taclet for the row of the constructor `c` at the operator `op` (a
constructor of `BinOp`, `UnOp` or `IncDec`). -/
def keyTacletAt (c op : Lean.Name) : Option KeyTaclet := do
  let ops ← operatorOrder.lookup c
  let .merged ts ← tacletOrigins.lookup c | none
  (ops.zip ts).lookup op

-- Every listed row is merged, one taclet per operator (`localAssignIncrement`'s
-- then the declaration's four).
#guard operatorOrder.all fun (c, ops) =>
  match tacletOrigins.lookup c with
  | some (.merged ts) =>
    ts.length == ops.length || (c == ``Taclet.localAssignIncrement && ts.length == 2 * ops.length)
  | _ => false

#guard keyTacletAt ``Taclet.binopAssignment ``BinOp.eqB == some .boolEqualityAssignment
#guard keyTacletAt ``Taclet.storageFieldIncrement ``IncDec.postDec ==
  some .storageFieldPostdecrement
#guard keyTacletAt ``Taclet.localAssignIncrement ``IncDec.postInc ==
  some .localAssignPostincrement

/-! ## Which KeY taclets the table claims -/

/-- Whether some row names the taclet. -/
def claims (t : KeyTaclet) : Bool :=
  (tacletOrigins ++ callbackOrigins).any fun r => r.2.taclets.contains t

/-- Every taclet some row names, in `KeyTaclet.all`'s order. -/
def claimedTaclets : List KeyTaclet := KeyTaclet.all.filter claims

/-- The taclets of `solidityProgramRules.key` that **no** row claims, and why.

* `emptyModality` — a rule of `⊢`, not of a statement: `Proves.empty`
  (`Proves.emptyModality`), which the proof tree prints under this name.  The
  table lists `Taclet` constructors only, so it does not claim it.
* `blockEmpty` — architectural.  A program is a list of statements with
  branch bodies inlined, so there is no nested block to erase and no
  `{} ; rest` to find.
* `blockReturn`, `functionFrameReturn`, `functionFrameEmpty` — architectural.
  Returns are lowered at elaboration (`lowerReturns`: a `return` in a block
  splices the block into the statements after it, which is `blockReturn`'s
  effect), and a call's body is spliced flat, so there is no block, no
  function frame and no `return` in `Stmt` to rewrite.
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
* `transferNoCallbackDiamond`, `transferWithCallbackDiamond` — a payment
  under the diamond.  solkey's diamond rules owe a "non-negative amount" goal
  and book the payment; here a payment has a rule under the box only, and the
  diamond closes to `false` (`LeanTaclet.transferDiamond`): whether the world
  pays is the compiler theorem's, not the calculus's.
* `sendWithCallbackDiamond` — a send that may call back, under the diamond:
  the callback reading is the box's only (`Calculus/Callback.lean`).  A send
  with no callback has its diamond (`sendNoCallbackDiamond`): a refused send
  is an outcome of the run (`Semantics.sendAt`), not the world's.

The other semantics of `transfer` and `send`, `transferWithCallbackBox` and
`sendWithCallbackBox`, are claimed by `callbackOrigins`. -/
def unclaimedTaclets : List KeyTaclet :=
  [ .emptyModality, .blockEmpty, .blockReturn, .functionFrameReturn, .functionFrameEmpty,
    .memoryFieldRead_unfold_rightSndResult, .memoryIndexRead_unfold_rightSndResult,
    .memoryFieldWriteCaptureSrc, .memoryIndexWriteMemRefRhsCapture,
    .ifTrue, .ifFalse, .ifElseTrue, .ifElseFalse, .ifElseNegated,
    .transferNoCallbackDiamond, .transferWithCallbackDiamond, .sendWithCallbackDiamond ]

/-- **The coverage fact**: the corpus splits into what the table claims and
what this file excuses, with nothing in both and nothing in neither.  A taclet
that appears upstream and is never ported fails this, and so does a row that
claims a taclet the list above excuses. -/
theorem taclets_partitioned :
    KeyTaclet.all.all (fun t => claims t != unclaimedTaclets.contains t) = true := by
  decide +kernel

theorem claimedTaclets_count : claimedTaclets.length = 306 := by decide +kernel

theorem unclaimedTaclets_count : unclaimedTaclets.length = 17 := by decide +kernel

/-! ## The rules with no taclet

A rule upstream has no counterpart for is a `LeanTaclet`, not a `Taclet`, so
every row above claims a taclet.  There are four:
`functionCallArgCapture`, printed as `unfoldArgument`, which solkey's
`docs/net.md` lists as missing (its `ExpandFunctionBody` binds the parameters
to the arguments as they are; here a parameter is bound to a ready argument
only, so that inlining is exact); `tryCallDiamond`, a `try` under the
diamond closed to `false`, where solkey has no rule (a call may revert in the
caller, which no formula rules out); and `transferDiamond`, a payment under
the diamond closed to `false`, where solkey's diamond rules are not ported;
and `whileClose`, a loop closed to `false` until the loop rules are ported
(solkey's `whileUnwind`, `whileInvariantBox`, `whileInvariantDiamond`, past
the pinned checkout).  The list is checked against the constructors, so one added later has to say
so here. -/

/-- Every `LeanTaclet` constructor. -/
def leanTaclets : List Lean.Name :=
  [``LeanTaclet.functionCallArgCapture, ``LeanTaclet.tryCallDiamond, ``LeanTaclet.transferDiamond,
    ``LeanTaclet.whileClose]

#check_constructor_table LeanTaclet, leanTaclets

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
    tacletOrigins.all (fun r => (heuristics r.2).length == 1) = true := by
  decide +kernel

theorem concrete_unclaimed :
    claimedTaclets.all (fun t => t.heuristic != .concreteSolidity) = true := by
  decide +kernel

end RuleShapes
end Solidity
