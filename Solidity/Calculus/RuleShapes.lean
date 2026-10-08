import Solidity.Calculus.Core.Callback

/-!
# Where each taclet comes from

`Calculus/Core/Rules.lean` names each `Core.Taclet` constructor after the
solkey taclet it transcribes, but a name is a promise, not a check: an operator family is one
constructor for five or fourteen taclets, a constructor can cover two KeY
shapes the Lean syntax does not tell apart, and a KeY taclet can have no
constructor at all.  This module writes the correspondence down and checks
it.

`Taclet` is a `Prop`, so there is no function on its derivations to hang an
origin on; the table is keyed by constructor *name* instead, and two checks
keep it honest.  Each key is a double-backtick name, which fails elaboration
if the constructor does not exist; `#check_constructor_table` then reads the
constructor list from the environment and fails unless every constructor has
exactly one row.  A constructor added to `Calculus/Core/Rules.lean` without
an origin does not build here.

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

In `Calculus/Core/Rules.lean`'s order.  A `merged` row is a constructor whose `\find`
covers several taclets: an operator family, a KeY split by the source's
kind (a value against a reference, `…MemRef…`) or by the receiver's (a
mapping against an array). -/


/-- Every `Taclet` constructor, and the solkey taclets it transcribes. -/
def tacletOrigins : List (Lean.Name × KeyOrigin) := [
  -- Step 1: unfold a storage read
  (``Core.Taclet.storageFieldRead_unfold_rightFst, .taclet .storageFieldRead_unfold_rightFst),
  (``Core.Taclet.storageIndexRead_unfold_rightFst, .taclet .storageIndexRead_unfold_rightFst),
  (``Core.Taclet.storageIndexRead_unfold_rightSndIndex, .taclet .storageIndexRead_unfold_rightSndIndex),
  (``Core.Taclet.storageFieldRead_unfold_rightSndResult,
    .merged [.storageFieldRead_unfold_rightSndResult, .storageFieldWriteCaptureSrc]),
  (``Core.Taclet.storageIndexRead_unfold_rightSndResult,
    .merged [.storageIndexRead_unfold_rightSndResult, .storageIndexWriteStorageRefRhsCapture]),
  -- Step 2: decompose a storage write
  (``Core.Taclet.storageFieldWrite_unfold_leftFst, .taclet .storageFieldWrite_unfold_leftFst),
  (``Core.Taclet.storageFieldWriteStorageRef_unfold_leftFst,
    .taclet .storageFieldWriteStorageRef_unfold_leftFst),
  (``Core.Taclet.storageIndexWriteCaptureAllComplexRecv,
    .taclet .storageIndexWriteCaptureAllComplexRecv),
  (``Core.Taclet.storageIndexWriteStorageRefCaptureAllComplexRecv,
    .taclet .storageIndexWriteStorageRefCaptureAllComplexRecv),
  (``Core.Taclet.storageIndexWriteCaptureAllNonSimpleIndex,
    .taclet .storageIndexWriteCaptureAllNonSimpleIndex),
  (``Core.Taclet.storageIndexWriteStorageRefCaptureAllNonSimpleIndex,
    .taclet .storageIndexWriteStorageRefCaptureAllNonSimpleIndex),
  (``Core.Taclet.storageRootWriteValueRhsCapture, .taclet .storageRootWriteValueRhsCapture),
  (``Core.Taclet.fieldWriteValueRhsCapture, .taclet .fieldWriteValueRhsCapture),
  (``Core.Taclet.indexWriteValueRhsCapture, .taclet .indexWriteValueRhsCapture),
  (``Core.Taclet.storageFieldDelete_unfold_leftFst, .taclet .storageFieldDelete_unfold_leftFst),
  (``Core.Taclet.storageIndexDelete_unfold_leftFst, .taclet .storageIndexDelete_unfold_leftFst),
  (``Core.Taclet.storageIndexDeleteNonSimpleIndexCapture,
    .taclet .storageIndexDeleteNonSimpleIndexCapture),
  -- Declarations
  (``Core.Taclet.localValueDeclInitDrop, .taclet .localValueDeclInitDrop),
  (``Core.Taclet.valueDeclSkip, .taclet .valueDeclSkip),
  (``Core.Taclet.storageLocalDeclInitDrop, .taclet .storageLocalDeclInitDrop),
  (``Core.Taclet.storageLocalDeclSkip, .taclet .storageLocalDeclSkip),
  (``Core.Taclet.memoryLocalDeclInitDrop, .taclet .memoryLocalDeclInitDrop),
  (``Core.Taclet.memoryReferenceDeclFreshAlloc, .taclet .memoryReferenceDeclFreshAlloc),
  -- Step 3: storage reads and writes as updates
  (``Core.Taclet.localValueAssign, .taclet .localValueAssign),
  (``Core.Taclet.storageRootReadSelect, .taclet .storageRootReadSelect),
  (``Core.Taclet.storageFieldReadFind, .taclet .storageFieldReadFind),
  (``Core.Taclet.storageIndexReadMappingFind, .taclet .storageIndexReadMappingFind),
  (``Core.Taclet.storageIndexReadArrayFind, .taclet .storageIndexReadArrayFind),
  (``Core.Taclet.storageRootWriteStore, .taclet .storageRootWriteStore),
  (``Core.Taclet.storageRootWriteCopySource, .taclet .storageRootWriteCopySource),
  (``Core.Taclet.storageFieldReadStoreRoot, .taclet .storageFieldReadStoreRoot),
  (``Core.Taclet.storageIndexReadMappingStoreRoot, .taclet .storageIndexReadMappingStoreRoot),
  (``Core.Taclet.storageIndexReadArrayStoreRoot, .taclet .storageIndexReadArrayStoreRoot),
  (``Core.Taclet.storageFieldWriteSave, .taclet .storageFieldWriteSave),
  (``Core.Taclet.storageFieldWriteCopySource, .taclet .storageFieldWriteCopySource),
  (``Core.Taclet.storageIndexWriteMappingSave, .taclet .storageIndexWriteMappingSave),
  (``Core.Taclet.storageIndexWriteArraySave, .taclet .storageIndexWriteArraySave),
  (``Core.Taclet.storageIndexWriteMappingCopySource, .taclet .storageIndexWriteMappingCopySource),
  (``Core.Taclet.storageIndexWriteArrayCopySource, .taclet .storageIndexWriteArrayCopySource),
  (``Core.Taclet.storageLocalRootRebind, .taclet .storageLocalRootRebind),
  (``Core.Taclet.storageFieldReadBindLocalRoot, .taclet .storageFieldReadBindLocalRoot),
  (``Core.Taclet.storageIndexReadMappingBindLocalRoot, .taclet .storageIndexReadMappingBindLocalRoot),
  (``Core.Taclet.storageIndexReadArrayBindLocalRoot, .taclet .storageIndexReadArrayBindLocalRoot),
  (``Core.Taclet.storageIndexReadArrayBindLocalRootMappingElement,
    .taclet .storageIndexReadArrayBindLocalRootMappingElement),
  (``Core.Taclet.storageRootDelete, .taclet .storageRootDelete),
  (``Core.Taclet.storageFieldDelete, .taclet .storageFieldDelete),
  (``Core.Taclet.storageIndexDelete, .taclet .storageIndexDelete),
  (``Core.Taclet.storageIndexArrayDelete, .taclet .storageIndexArrayDelete),
  -- Lengths: KeY reads `sp.length` as the member `length`, so the member-read taclets
  (``Core.Taclet.storageLengthRead, .taclet .storageFieldReadFind),
  (``Core.Taclet.storageLengthRead_unfold_rightFst, .taclet .storageFieldRead_unfold_rightFst),
  (``Core.Taclet.memoryLengthRead, .taclet .memoryFieldRead),
  (``Core.Taclet.memoryLengthRead_unfold_rightFst, .taclet .memoryFieldRead_unfold_rightFst),
  -- Operators: `+ - * ** / %`, then the comparisons, then `&& ||`
  (``Core.Taclet.binopAssignment, .merged [.additionAssignment, .subtractionAssignment,
    .multiplicationAssignment, .powerAssignment, .divisionAssignment, .moduloAssignment,
    .lessThanAssignment, .greaterThanAssignment, .lessEqualAssignment, .greaterEqualAssignment,
    .boolEqualityAssignment, .boolInequalityAssignment,
    .logicalAndAssignment, .logicalOrAssignment]),
  (``Core.Taclet.binopUnfoldLeft, .merged [.addition_unfold_left, .subtraction_unfold_left,
    .multiplication_unfold_left, .power_unfold_left, .division_unfold_left, .modulo_unfold_left,
    .lessThanCaptureLhs, .greaterThanCaptureLhs, .lessEqualCaptureLhs, .greaterEqualCaptureLhs,
    .boolEqualityCaptureLhs, .boolInequalityCaptureLhs,
    .logicalAndCaptureLhs, .logicalOrCaptureLhs]),
  -- no `&&`/`||` instance: those are the short-circuit rows below
  (``Core.Taclet.binopUnfoldRight, .merged [.addition_unfold_right, .subtraction_unfold_right,
    .multiplication_unfold_right, .power_unfold_right, .division_unfold_right,
    .modulo_unfold_right,
    .lessThanCaptureRhs, .greaterThanCaptureRhs, .lessEqualCaptureRhs, .greaterEqualCaptureRhs,
    .boolEqualityCaptureRhs, .boolInequalityCaptureRhs]),
  (``Core.Taclet.logicalAndShortCircuitRhs, .taclet .logicalAndShortCircuitRhs),
  (``Core.Taclet.logicalOrShortCircuitRhs, .taclet .logicalOrShortCircuitRhs),
  (``Core.Taclet.unopAssignment, .merged [.unaryMinusAssignment, .logicalNotAssignment]),
  (``Core.Taclet.unopCapture, .merged [.unaryMinusCapture, .logicalNotCapture]),
  -- The conditional: `lhs` is a local, a storage or a memory location
  (``Core.Taclet.ternaryToIf, .merged [.ternaryToIf, .ternaryToIfStorage]),
  (``Core.Taclet.ternaryCaptureCond, .taclet .ternaryCaptureCond),
  -- Compound assignment (`+= -= *= /= %=`) and `++`/`--` (pre, post)
  (``Core.Taclet.localOpAssign, .merged [.localAddAssign, .localSubAssign, .localMulAssign,
    .localDivAssign, .localModAssign]),
  (``Core.Taclet.storageRootOpAssign, .merged [.storageRootAddAssign, .storageRootSubAssign,
    .storageRootMulAssign, .storageRootDivAssign, .storageRootModAssign]),
  (``Core.Taclet.storageFieldOpAssign, .merged [.storageFieldAddAssign, .storageFieldSubAssign,
    .storageFieldMulAssign, .storageFieldDivAssign, .storageFieldModAssign]),
  (``Core.Taclet.storageIndexMappingOpAssign, .merged [.storageIndexMappingAddAssign,
    .storageIndexMappingSubAssign, .storageIndexMappingMulAssign, .storageIndexMappingDivAssign,
    .storageIndexMappingModAssign]),
  (``Core.Taclet.storageIndexArrayOpAssign, .merged [.storageIndexArrayAddAssign,
    .storageIndexArraySubAssign, .storageIndexArrayMulAssign, .storageIndexArrayDivAssign,
    .storageIndexArrayModAssign]),
  (``Core.Taclet.memoryFieldOpAssign, .merged [.memoryFieldAddAssign, .memoryFieldSubAssign,
    .memoryFieldMulAssign, .memoryFieldDivAssign, .memoryFieldModAssign]),
  (``Core.Taclet.memoryIndexArrayOpAssign, .merged [.memoryIndexArrayAddAssign,
    .memoryIndexArraySubAssign, .memoryIndexArrayMulAssign, .memoryIndexArrayDivAssign,
    .memoryIndexArrayModAssign]),
  (``Core.Taclet.storageFieldOpAssignUnfoldLeftFst, .merged [.storageFieldAddAssign_unfold_leftFst,
    .storageFieldSubAssign_unfold_leftFst, .storageFieldMulAssign_unfold_leftFst,
    .storageFieldDivAssign_unfold_leftFst, .storageFieldModAssign_unfold_leftFst]),
  (``Core.Taclet.storageIndexOpAssignUnfoldLeftFst, .merged [.storageIndexAddAssign_unfold_leftFst,
    .storageIndexSubAssign_unfold_leftFst, .storageIndexMulAssign_unfold_leftFst,
    .storageIndexDivAssign_unfold_leftFst, .storageIndexModAssign_unfold_leftFst]),
  (``Core.Taclet.memoryFieldOpAssignUnfoldLeftFst, .merged [.memoryFieldAddAssign_unfold_leftFst,
    .memoryFieldSubAssign_unfold_leftFst, .memoryFieldMulAssign_unfold_leftFst,
    .memoryFieldDivAssign_unfold_leftFst, .memoryFieldModAssign_unfold_leftFst]),
  (``Core.Taclet.memoryIndexOpAssignUnfoldLeftFst, .merged [.memoryIndexAddAssign_unfold_leftFst,
    .memoryIndexSubAssign_unfold_leftFst, .memoryIndexMulAssign_unfold_leftFst,
    .memoryIndexDivAssign_unfold_leftFst, .memoryIndexModAssign_unfold_leftFst]),
  (``Core.Taclet.compoundAssignValueRhsCapture, .merged [.addAssignValueRhsCapture,
    .subAssignValueRhsCapture, .mulAssignValueRhsCapture, .divAssignValueRhsCapture,
    .modAssignValueRhsCapture]),
  (``Core.Taclet.localIncrement, .merged [.localPreincrement, .localPredecrement,
    .localPostincrement, .localPostdecrement]),
  (``Core.Taclet.storageRootIncrement, .merged [.storageRootPreincrement, .storageRootPredecrement,
    .storageRootPostincrement, .storageRootPostdecrement]),
  (``Core.Taclet.storageFieldIncrement, .merged [.storageFieldPreincrement,
    .storageFieldPredecrement, .storageFieldPostincrement, .storageFieldPostdecrement]),
  (``Core.Taclet.storageIndexIncrement, .merged [
    .storageIndexMappingPreincrement, .storageIndexMappingPredecrement,
    .storageIndexMappingPostincrement, .storageIndexMappingPostdecrement,
    .storageIndexArrayPreincrement, .storageIndexArrayPredecrement,
    .storageIndexArrayPostincrement, .storageIndexArrayPostdecrement]),
  (``Core.Taclet.memoryFieldIncrement, .merged [.memoryFieldPreincrement, .memoryFieldPredecrement,
    .memoryFieldPostincrement, .memoryFieldPostdecrement]),
  (``Core.Taclet.memoryIndexArrayIncrement, .merged [.memoryIndexArrayPreincrement,
    .memoryIndexArrayPredecrement, .memoryIndexArrayPostincrement,
    .memoryIndexArrayPostdecrement]),
  (``Core.Taclet.storageFieldIncrementUnfoldLeftFst, .merged [
    .storageFieldPreincrement_unfold_leftFst, .storageFieldPredecrement_unfold_leftFst,
    .storageFieldPostincrement_unfold_leftFst, .storageFieldPostdecrement_unfold_leftFst]),
  (``Core.Taclet.storageIndexIncrementUnfoldLeftFst, .merged [
    .storageIndexPreincrement_unfold_leftFst, .storageIndexPredecrement_unfold_leftFst,
    .storageIndexPostincrement_unfold_leftFst, .storageIndexPostdecrement_unfold_leftFst]),
  (``Core.Taclet.memoryFieldIncrementUnfoldLeftFst, .merged [
    .memoryFieldPreincrement_unfold_leftFst, .memoryFieldPredecrement_unfold_leftFst,
    .memoryFieldPostincrement_unfold_leftFst, .memoryFieldPostdecrement_unfold_leftFst]),
  (``Core.Taclet.memoryIndexIncrementUnfoldLeftFst, .merged [
    .memoryIndexPreincrement_unfold_leftFst, .memoryIndexPredecrement_unfold_leftFst,
    .memoryIndexPostincrement_unfold_leftFst, .memoryIndexPostdecrement_unfold_leftFst]),
  -- `vp = v++`: KeY has one taclet for the assignment and one for the declaration
  (``Core.Taclet.localAssignIncrement, .merged [
    .localAssignPreincrement, .localAssignPredecrement,
    .localAssignPostincrement, .localAssignPostdecrement,
    .localDeclPreincrement, .localDeclPredecrement,
    .localDeclPostincrement, .localDeclPostdecrement]),
  (``Core.Taclet.storageRootIncrementAssignment, .merged [
    .storageRootPreincrementAssignment, .storageRootPredecrementAssignment,
    .storageRootPostincrementAssignment, .storageRootPostdecrementAssignment]),
  (``Core.Taclet.storageFieldIncrementAssignment, .merged [
    .storageFieldPreincrementAssignment, .storageFieldPredecrementAssignment,
    .storageFieldPostincrementAssignment, .storageFieldPostdecrementAssignment]),
  (``Core.Taclet.storageIndexIncrementAssignment, .merged [
    .storageIndexMappingPreincrementAssignment, .storageIndexMappingPredecrementAssignment,
    .storageIndexMappingPostincrementAssignment, .storageIndexMappingPostdecrementAssignment,
    .storageIndexArrayPreincrementAssignment, .storageIndexArrayPredecrementAssignment,
    .storageIndexArrayPostincrementAssignment, .storageIndexArrayPostdecrementAssignment]),
  (``Core.Taclet.memoryFieldIncrementAssignment, .merged [
    .memoryFieldPreincrementAssignment, .memoryFieldPredecrementAssignment,
    .memoryFieldPostincrementAssignment, .memoryFieldPostdecrementAssignment]),
  (``Core.Taclet.memoryIndexArrayIncrementAssignment, .merged [
    .memoryIndexArrayPreincrementAssignment, .memoryIndexArrayPredecrementAssignment,
    .memoryIndexArrayPostincrementAssignment, .memoryIndexArrayPostdecrementAssignment]),
  -- Arrays
  (``Core.Taclet.storagePushValueSave, .taclet .storagePushValueSave),
  (``Core.Taclet.storagePushValueCopySource, .taclet .storagePushValueCopySource),
  (``Core.Taclet.storagePushLengthSave, .taclet .storagePushLengthSave),
  (``Core.Taclet.storagePushLengthSaveReferenceElement,
    .taclet .storagePushLengthSaveReferenceElement),
  (``Core.Taclet.storagePushValue_unfold_rightSndArgument,
    .taclet .storagePushValue_unfold_rightSndArgument),
  (``Core.Taclet.storagePushValue_unfold_leftFstReceiver,
    .taclet .storagePushValue_unfold_leftFstReceiver),
  (``Core.Taclet.storagePush_unfold_leftFstReceiver, .taclet .storagePush_unfold_leftFstReceiver),
  (``Core.Taclet.storagePop_unfold_leftFstReceiver, .taclet .storagePop_unfold_leftFstReceiver),
  (``Core.Taclet.storagePopSave, .taclet .storagePopSave),
  (``Core.Taclet.storagePopSaveMappingElement, .taclet .storagePopSaveMappingElement),
  (``Core.Taclet.storageLocalRootPush_unfold_leftFstReceiver,
    .taclet .storageLocalRootPush_unfold_leftFstReceiver),
  (``Core.Taclet.storageLocalRootPushBind, .taclet .storageLocalRootPushBind),
  (``Core.Taclet.storageLocalRootPushBindMappingElement,
    .taclet .storageLocalRootPushBindMappingElement),
  -- Transfer
  (``Core.Taclet.transfer_unfold_leftFstReceiver, .taclet .transfer_unfold_leftFstReceiver),
  (``Core.Taclet.transfer_unfold_rightSndArgument, .taclet .transfer_unfold_rightSndArgument),
  (``Core.Taclet.transferNoCallbackBox, .taclet .transferNoCallbackBox),
  (``Core.Taclet.send_unfold_leftFstReceiver, .taclet .send_unfold_leftFstReceiver),
  (``Core.Taclet.send_unfold_rightSndArgument, .taclet .send_unfold_rightSndArgument),
  (``Core.Taclet.sendNoCallbackBox, .taclet .sendNoCallbackBox),
  (``Core.Taclet.sendNoCallbackDiamond, .taclet .sendNoCallbackDiamond),
  -- Memory: `msrc` is a value or a memory reference, so a row covers `…MemRef…` except
  -- for the index captures, which KeY and the table split by the source
  (``Core.Taclet.memoryFieldRead_unfold_rightFst, .taclet .memoryFieldRead_unfold_rightFst),
  (``Core.Taclet.memoryIndexRead_unfold_rightFst, .taclet .memoryIndexRead_unfold_rightFst),
  (``Core.Taclet.memoryIndexRead_unfold_rightSndIndex, .taclet .memoryIndexRead_unfold_rightSndIndex),
  (``Core.Taclet.memoryFieldRead, .taclet .memoryFieldRead),
  (``Core.Taclet.memoryIndexReadArrayValue, .taclet .memoryIndexReadArrayValue),
  (``Core.Taclet.memoryRootRebind, .taclet .memoryRootRebind),
  (``Core.Taclet.memoryFieldReadAliasRoot, .taclet .memoryFieldRead),
  (``Core.Taclet.memoryIndexReadArrayMemory, .taclet .memoryIndexReadArrayMemory),
  (``Core.Taclet.memoryFieldWrite, .taclet .memoryFieldWrite),
  (``Core.Taclet.memoryIndexWriteArray, .taclet .memoryIndexWriteArray),
  (``Core.Taclet.memoryFieldWriteCopy, .taclet .memoryFieldWrite),
  (``Core.Taclet.memoryIndexWriteCopy, .taclet .memoryIndexWriteArray),
  (``Core.Taclet.memoryFieldWrite_unfold_leftFst,
    .merged [.memoryFieldWrite_unfold_leftFst, .memoryFieldWriteMemRef_unfold_leftFst]),
  (``Core.Taclet.memoryIndexWriteCaptureAllComplexRecv,
    .taclet .memoryIndexWriteCaptureAllComplexRecv),
  (``Core.Taclet.memoryIndexWriteMemRefCaptureAllComplexRecv,
    .taclet .memoryIndexWriteMemRefCaptureAllComplexRecv),
  (``Core.Taclet.memoryIndexWriteCaptureAllNonSimpleIndex,
    .taclet .memoryIndexWriteCaptureAllNonSimpleIndex),
  (``Core.Taclet.memoryIndexWriteMemRefCaptureAllNonSimpleIndex,
    .taclet .memoryIndexWriteMemRefCaptureAllNonSimpleIndex),
  (``Core.Taclet.memoryFieldWriteUnfoldSource, .taclet .fieldWriteValueRhsCapture),
  (``Core.Taclet.memoryIndexWriteUnfoldSource, .taclet .indexWriteValueRhsCapture),
  (``Core.Taclet.memoryRootDeleteFreshRebind, .taclet .memoryRootDeleteFreshRebind),
  (``Core.Taclet.memoryFieldDeletePrimitive, .taclet .memoryFieldDeletePrimitive),
  (``Core.Taclet.memoryFieldDeleteReference, .taclet .memoryFieldDeleteReference),
  (``Core.Taclet.memoryIndexDeletePrimitive, .taclet .memoryIndexDeletePrimitive),
  (``Core.Taclet.memoryIndexDeleteReference, .taclet .memoryIndexDeleteReference),
  (``Core.Taclet.memoryFieldDelete_unfold_leftFst, .taclet .memoryFieldDelete_unfold_leftFst),
  (``Core.Taclet.memoryIndexDelete_unfold_leftFst, .taclet .memoryIndexDelete_unfold_leftFst),
  (``Core.Taclet.memoryIndexDeleteNonSimpleIndexCapture,
    .taclet .memoryIndexDeleteNonSimpleIndexCapture),
  (``Core.Taclet.memoryArrayFreshAlloc, .taclet .memoryArrayFreshAlloc),
  (``Core.Taclet.newArrayCapture, .taclet .newArrayCapture),
  -- Storage and memory: `mpath` is any memory path, a member one included
  (``Core.Taclet.memoryStorageCopy, .taclet .memoryStorageCopy),
  (``Core.Taclet.memoryStorageCopyUnfold, .taclet .memoryStorageCopyUnfold),
  (``Core.Taclet.memoryToStorageStoreRoot, .taclet .memoryToStorageStoreRoot),
  (``Core.Taclet.memoryToStorageFieldCopyRoot,
    .merged [.memoryToStorageFieldCopyRoot, .memoryToStorageFieldCopyField]),
  (``Core.Taclet.memoryToStorageIndexMappingCopyRoot, .taclet .memoryToStorageIndexMappingCopyRoot),
  (``Core.Taclet.memoryToStorageIndexArrayCopyRoot, .taclet .memoryToStorageIndexArrayCopyRoot),
  (``Core.Taclet.memoryToStorageField_unfold_leftFst, .taclet .memoryToStorageField_unfold_leftFst),
  (``Core.Taclet.memoryToStorageIndexCaptureAllComplexRecv,
    .taclet .memoryToStorageIndexCaptureAllComplexRecv),
  (``Core.Taclet.memoryToStorageIndexCaptureAllNonSimpleIndex,
    .taclet .memoryToStorageIndexCaptureAllNonSimpleIndex),
  -- Control flow: an `if` without `else` is one with an empty `else`
  (``Core.Taclet.ifElseUnfold, .merged [.ifUnfold, .ifElseUnfold]),
  (``Core.Taclet.ifElseSplit, .merged [.ifSplit, .ifElseSplit]),
  (``Core.Taclet.requireConditionCapture, .taclet .requireConditionCapture),
  (``Core.Taclet.requireSimple, .taclet .requireSimple),
  (``Core.Taclet.assertConditionCapture, .taclet .assertConditionCapture),
  (``Core.Taclet.assertSimple, .taclet .assertSimple),
  (``Core.Taclet.revertBox, .taclet .revertBox),
  (``Core.Taclet.revertDiamond, .taclet .revertDiamond),
  -- Calls
  -- a call's body runs as a block of its own frame, popped (or dropped from
  -- under its return variables) after it: the expansion claims `functionFrameEmpty`
  (``Core.Taclet.functionBodyExpand, .merged [.functionBodyExpand, .functionFrameEmpty]),
  -- solkey `671f6762a9` splits it off `functionBodyExpand`: a call without targets
  (``Core.Taclet.internalCallExpand, .merged [.internalCallExpand, .functionFrameEmpty]),
  (``Core.Taclet.tryCallNoCallbackBox, .taclet .tryCallNoCallbackBox),
  -- Blocks: a block is a statement (`Stmt.block`), its end a frame (`Frames.pop .block`)
  (``Core.Taclet.blockEmpty, .taclet .blockEmpty) ]

#check_constructor_table Core.Taclet, tacletOrigins.map Prod.fst

/-- The callback taclets (`Calculus/Core/Callback.lean`'s `CallbackTaclet`, the other
`transferSemantics`), and the solkey taclets they transcribe. -/
def callbackOrigins : List (Lean.Name × KeyOrigin) := [
  (``Core.CallbackTaclet.transferWithCallbackBox, .taclet .transferWithCallbackBox),
  (``Core.CallbackTaclet.sendWithCallbackBox, .taclet .sendWithCallbackBox),
  (``Core.CallbackTaclet.tryCallWithCallbackBox, .taclet .tryCallWithCallbackBox) ]

#check_constructor_table Core.CallbackTaclet, callbackOrigins.map Prod.fst

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
  [(``Core.Taclet.binopAssignment, arith ++ cmp ++ [``BinOp.and, ``BinOp.or]),
   (``Core.Taclet.binopUnfoldLeft, arith ++ cmp ++ [``BinOp.and, ``BinOp.or]),
   (``Core.Taclet.binopUnfoldRight, arith ++ cmp),
   (``Core.Taclet.unopAssignment, [``UnOp.neg, ``UnOp.not]),
   (``Core.Taclet.unopCapture, [``UnOp.neg, ``UnOp.not])] ++
  ([``Core.Taclet.localOpAssign, ``Core.Taclet.storageRootOpAssign, ``Core.Taclet.storageFieldOpAssign,
    ``Core.Taclet.storageIndexMappingOpAssign, ``Core.Taclet.storageIndexArrayOpAssign,
    ``Core.Taclet.memoryFieldOpAssign, ``Core.Taclet.memoryIndexArrayOpAssign,
    ``Core.Taclet.storageFieldOpAssignUnfoldLeftFst, ``Core.Taclet.storageIndexOpAssignUnfoldLeftFst,
    ``Core.Taclet.memoryFieldOpAssignUnfoldLeftFst, ``Core.Taclet.memoryIndexOpAssignUnfoldLeftFst,
    ``Core.Taclet.compoundAssignValueRhsCapture].map (·, compound)) ++
  ([``Core.Taclet.localIncrement, ``Core.Taclet.storageRootIncrement, ``Core.Taclet.storageFieldIncrement,
    ``Core.Taclet.memoryFieldIncrement, ``Core.Taclet.memoryIndexArrayIncrement,
    ``Core.Taclet.storageFieldIncrementUnfoldLeftFst, ``Core.Taclet.storageIndexIncrementUnfoldLeftFst,
    ``Core.Taclet.memoryFieldIncrementUnfoldLeftFst, ``Core.Taclet.memoryIndexIncrementUnfoldLeftFst,
    ``Core.Taclet.storageRootIncrementAssignment, ``Core.Taclet.storageFieldIncrementAssignment,
    ``Core.Taclet.memoryFieldIncrementAssignment, ``Core.Taclet.memoryIndexArrayIncrementAssignment,
    ``Core.Taclet.localAssignIncrement].map
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
    ts.length == ops.length || (c == ``Core.Taclet.localAssignIncrement && ts.length == 2 * ops.length)
  | _ => false

#guard keyTacletAt ``Core.Taclet.binopAssignment ``BinOp.eqB == some .boolEqualityAssignment
#guard keyTacletAt ``Core.Taclet.storageFieldIncrement ``IncDec.postDec ==
  some .storageFieldPostdecrement
#guard keyTacletAt ``Core.Taclet.localAssignIncrement ``IncDec.postInc ==
  some .localAssignPostincrement

/-! ## Which KeY taclets the table claims -/

/-- Whether some row names the taclet. -/
def claims (t : KeyTaclet) : Bool :=
  (tacletOrigins ++ callbackOrigins).any fun r => r.2.taclets.contains t

/-- Every taclet some row names, in `KeyTaclet.all`'s order. -/
def claimedTaclets : List KeyTaclet := KeyTaclet.all.filter claims

/-- The taclets of `solidityProgramRules.key` that **no** row claims, and why.

* `emptyModality` — a rule of `⊢`, not of a statement: `Core.Proves.empty`
  (`emptyModality`), which the proof tree prints under this name.  The
  table lists `Taclet` constructors only, so it does not claim it.
* `blockReturn`, `functionFrameReturn` — architectural.  Returns are
  lowered at elaboration (`lowerReturns`: a `return` in a block splices the
  block into the statements after it, which is `blockReturn`'s effect), so
  there is no `return` in `Stmt` to rewrite.
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
  diamond closes to `false` (`Core.LeanTaclet.transferDiamond`): whether the world
  pays is the compiler theorem's, not the calculus's.
* `sendWithCallbackDiamond` — a send that may call back, under the diamond:
  the callback reading is the box's only (`Calculus/Core/Callback.lean`).  A send
  with no callback has its diamond (`sendNoCallbackDiamond`): a refused send
  is an outcome of the run (`Semantics.sendAt`), not the world's.

The other semantics of `transfer` and `send`, `transferWithCallbackBox` and
`sendWithCallbackBox`, are claimed by `callbackOrigins`. -/
def unclaimedTaclets : List KeyTaclet :=
  [ .emptyModality, .blockReturn, .functionFrameReturn,
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

theorem claimedTaclets_count : claimedTaclets.length = 308 := by decide +kernel

theorem unclaimedTaclets_count : unclaimedTaclets.length = 15 := by decide +kernel

/-! ## The rules with no taclet

A rule upstream has no counterpart for is a `LeanTaclet`, not a `Taclet`, so
every row above claims a taclet.  There are nine:
`functionCallArgCapture`, printed as `unfoldArgument`, which solkey's
`docs/net.md` lists as missing (its `ExpandFunctionBody` binds the parameters
to the arguments as they are; here a parameter is bound to a ready argument
only, so that inlining is exact); `tryCallDiamond`, a `try` under the
diamond closed to `false`, where solkey has no rule (a call may revert in the
caller, which no formula rules out); and `transferDiamond`, a payment under
the diamond closed to `false`, where solkey's diamond rules are not ported;
`whileUnwind`, `whileInvariantBox` and `whileInvariantDiamond`, solkey's
taclets of those names, added in `ed7849d5b6` after the pinned `1b4341a303`,
the first with a bound on the unwinding; `loopExit`, the loop at its bound; and
`whileClose` and `whileNoVariantDiamond`, a loop with an invariant closed to
`false` where its body has no frame or, under the diamond, it has no
variant (solkey unwinds those).  The list is checked against the
constructors, so one added later has to say so here. -/

/-- Every `LeanTaclet` constructor. -/
def leanTaclets : List Lean.Name :=
  [``Core.LeanTaclet.functionCallArgCapture, ``Core.LeanTaclet.tryCallDiamond, ``Core.LeanTaclet.transferDiamond,
    ``Core.LeanTaclet.whileUnwind, ``Core.LeanTaclet.loopExit, ``Core.LeanTaclet.whileInvariantBox,
    ``Core.LeanTaclet.whileInvariantDiamond, ``Core.LeanTaclet.whileClose, ``Core.LeanTaclet.whileNoVariantDiamond]

#check_constructor_table Core.LeanTaclet, leanTaclets

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
