import Solidity.Kernel.Taclet
import Solidity.Calculus.Uniqueness
import Solidity.Kernel.Step
import Solidity.Kernel.Print

/-!
# The bridge to the rule table

Each `Taclet` constructor names the solkey taclet it is (`Taclet.origin`,
a `KeyTaclet` of `Calculus/KeyTaclets.lean`), and the rule of the old table
that transcribes it (`Taclet.rule`, a `RuleName` of `Calculus/Rules.lean`).
`Taclet.origin_claimed` checks the two against each other: the old rule's
recorded origin claims the constructor's taclet.  A family (`binopAssignment
op`) keeps its `RuleName` and takes its origin from it.

Where the old table has box/diamond twins, the rule follows the modality.
`ifElseSplit` is the one constructor without a rule: the old table splits a
branch in the sequent, not by a rule (`RuleShapes` excuses the taclet).

`Prog.disagreements` runs both tables on a block, the kernel's
`Stmt.step` against the old `candidate` on the erasure, and the tour below
pins the answer: the two agree except on a state-variable operand or
receiver (`x = total + 1;`, `owner.transfer(1);`, where the kernel captures
the state variable as KeY's `addition_unfold_left` and
`transfer_unfold_leftFstReceiver` do, a state variable being a `Path`, not a
`SimpleExpression`) and on a storage declaration whose path is not bindable
(`Person storage r = persons[x + 1];`, which KeY drops to an assignment and
the kernel, having no `T storage x;`, captures the index of first), and on a
scratch alias (`Person storage sp = folks[x];`, which `ksol` writes before
`y = sp.age++;`: the old table binds its own scratch aliases by the Lean-only
`storagePlaceAlias`, KeY and the kernel by `storageLocalDeclInitDrop`), and on a
memory reference copied from a member (`mp.account = mq.account;`,
`folks[x].account = mp.account;`), which the old table first captures into a
scratch memory local and the kernel copies directly: the capture needs the slot to hold a reference, which the
interpreter does not check when it copies one.  One statement the old table
has no rule for: `Person memory md = folks[x];`, a copy into memory from an
entry, which the kernel captures into a storage alias first.  A storage
declaration from a push place (`Person storage pp = people.push();`) the old
table and KeY first drop to an assignment (`storageLocalDeclInitDrop`); the
kernel, with no `T storage x;` to drop to, binds it as the assignment would. -/

namespace Solidity
namespace Kernel

open Semantics Rules

variable {C : Contract} {m : Modality}

/-- The rule of the old table a derivation's last step is. -/
def Taclet.rule {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {pr : Premise C Γ Γ'} : Taclet C m s pr → Option RuleName
  | .storageFieldRead_unfold_rightFst .. => some .storageFieldReadUnfoldRightFst
  | .storageIndexRead_unfold_rightFst .. => some .storageIndexReadUnfoldRightFst
  | .storageIndexRead_unfold_rightSndIndex .. => some .storageIndexReadUnfoldRightSndIndex
  | .storageFieldRead_unfold_rightSndResult .. => some .storageFieldReadUnfoldRightSndResult
  | .storageIndexRead_unfold_rightSndResult .. => some .storageIndexReadUnfoldRightSndResult
  | .storageFieldWrite_unfold_leftFst .. => some .storageFieldWriteUnfoldLeftFst
  | .storageFieldWriteStorageRef_unfold_leftFst .. => some .storageFieldWriteRefUnfoldLeftFst
  | .storageIndexWrite_unfold_leftFst .. => some .storageIndexWriteUnfoldLeftFst
  | .storageIndexWriteStorageRef_unfold_leftFst .. => some .storageIndexWriteRefUnfoldLeftFst
  | .storageIndexWriteNonSimpleIndexCapture .. => some .storageIndexWriteUnfoldLeftSndIndex
  | .storageIndexWriteStorageRefNonSimpleIndexCapture .. => some .storageIndexWriteRefUnfoldLeftSndIndex
  | .storageRootWriteValueRhsCapture .. => some .storageRootWriteUnfoldSource
  | .fieldWriteValueRhsCapture .. => some .storageFieldWriteUnfoldSource
  | .indexWriteValueRhsCapture .. => some .storageIndexWriteUnfoldSource
  | .storageFieldDelete_unfold_leftFst .. => some .storageFieldDeleteUnfoldLeftFst
  | .storageIndexDelete_unfold_leftFst .. => some .storageIndexDeleteUnfoldLeftFst
  | .storageIndexDeleteNonSimpleIndexCapture .. => some .storageIndexDeleteNonSimpleIndexCapture
  | .localValueDeclInitDrop .. => some .localValueDeclInitDrop
  | .valueDeclSkip .. => some .valueDeclSkip
  | .localValueAssign .. => some .localValueAssign
  | .storageRootReadSelect .. => some .storageRootReadSelect
  | .storageFieldReadFind .. => some .storageFieldReadFind
  | .storageIndexReadMappingFind .. => some .storageIndexReadMappingFind
  | .storageIndexReadArrayFind .. => some (match m with | .box => .storageIndexReadArrayFindBox | .diamond => .storageIndexReadArrayFindDiamond)
  | .storageRootWriteStore .. => some .storageRootWriteStore
  | .storageRootWriteCopySource .. => some .storageRootWriteCopySource
  | .storageFieldReadStoreRoot .. => some .storageFieldReadStoreRoot
  | .storageIndexReadMappingStoreRoot .. => some .storageIndexReadMappingStoreRoot
  | .storageIndexReadArrayStoreRoot .. => some (match m with | .box => .storageIndexReadArrayStoreRootBox | .diamond => .storageIndexReadArrayStoreRootDiamond)
  | .storageFieldWriteSave .. => some .storageFieldWriteSave
  | .storageFieldWriteCopySource .. => some .storageFieldWriteCopySource
  | .storageIndexWriteMappingSave .. => some .storageIndexWriteMappingSave
  | .storageIndexWriteArraySave .. => some (match m with | .box => .storageIndexWriteArraySaveBox | .diamond => .storageIndexWriteArraySaveDiamond)
  | .storageIndexWriteMappingCopySource .. => some .storageIndexWriteMappingCopySource
  | .storageIndexWriteArrayCopySource .. => some (match m with | .box => .storageIndexWriteArrayCopySourceBox | .diamond => .storageIndexWriteArrayCopySourceDiamond)
  | .storageLocalRootRebind .. => some .storageLocalRootRebind
  | .storageFieldReadBindLocalRoot .. => some .storageFieldReadBindLocalRoot
  | .storageIndexReadMappingBindLocalRoot .. => some .storageIndexReadMappingBindLocalRoot
  | .storageIndexReadArrayBindLocalRoot .. => some (match m with | .box => .storageIndexReadArrayBindLocalRootBox | .diamond => .storageIndexReadArrayBindLocalRootDiamond)
  | .storageLocalDeclInitDrop .. => some .storageLocalDeclInitDrop
  | .storageRootDelete .. => some .storageRootDelete
  | .storageFieldDelete .. => some .storageFieldDelete
  | .storageIndexDelete .. => some .storageIndexDelete
  | .binopAssignment op .. => some (.binopAssignment op)
  | .binopUnfoldLeft op .. => some (.binopUnfoldLeft op)
  | .binopUnfoldRight op .. => some (.binopUnfoldRight op)
  | .logicalAndShortCircuitRhs .. => some .logicalAndShortCircuitRhs
  | .logicalOrShortCircuitRhs .. => some .logicalOrShortCircuitRhs
  | .unopAssignment op .. => some (.unopAssignment op)
  | .unopCapture op .. => some (.unopCapture op)
  | .localOpAssign op .. => some (.localOpAssign op)
  | .storageRootOpAssign op .. => some (.storageRootOpAssign op)
  | .storageFieldOpAssign op .. => some (.storageFieldOpAssign op)
  | .storageIndexMappingOpAssign op .. => some (.storageIndexMappingOpAssign op)
  | .storageIndexArrayOpAssign op .. => some (.storageIndexArrayOpAssign op)
  | .storageFieldOpAssignUnfoldLeftFst op .. => some (.storageFieldOpAssignUnfoldLeftFst op)
  | .storageIndexOpAssignUnfoldLeftFst op .. => some (.storageIndexOpAssignUnfoldLeftFst op)
  | .compoundAssignValueRhsCapture op .. => some (.compoundAssignValueRhsCapture op)
  | Taclet.localIncrement (op := op) .. => some (.localIncrement op)
  | Taclet.storageRootIncrement (op := op) .. => some (.storageRootIncrement op)
  | Taclet.storageFieldIncrement (op := op) .. => some (.storageFieldIncrement op)
  | Taclet.storageIndexIncrement (op := op) .. => some (.storageIndexIncrement op)
  | Taclet.storageFieldIncrementUnfoldLeftFst (op := op) .. => some (.storageFieldIncrementUnfoldLeftFst op)
  | Taclet.storageIndexIncrementUnfoldLeftFst (op := op) .. => some (.storageIndexIncrementUnfoldLeftFst op)
  | Taclet.localAssignIncrement (op := op) .. => some (.localAssignIncrement op)
  | Taclet.storageRootIncrementAssignment (op := op) .. => some (.storageRootIncrementAssignment op)
  | Taclet.storageFieldIncrementAssignment (op := op) .. => some (.storageFieldIncrementAssignment op)
  | Taclet.storageIndexIncrementAssignment (op := op) .. => some (.storageIndexIncrementAssignment op)
  | .ternaryToIf .. => some .ternaryToIf
  | .ternaryToIfStorage .. => some .ternaryToIfStorage
  | .ternaryCaptureCond .. => some .ternaryCaptureCond
  | .storagePushValueSave .. => some .storagePushValueSave
  | .storagePushValueCopySource .. => some .storagePushValueCopySource
  | .storagePushLengthSave .. => some .storagePushLengthSave
  | .storagePushValue_unfold_rightSndArgument .. => some .storagePushValueUnfoldRightSndArgument
  | .storagePushValue_unfold_leftFstReceiver .. => some .storagePushValueUnfoldLeftFstReceiver
  | .storagePush_unfold_leftFstReceiver .. => some .storagePushUnfoldLeftFstReceiver
  | .storagePop_unfold_leftFstReceiver .. => some .storagePopUnfoldLeftFstReceiver
  | .storagePopSave .. => some (match m with | .box => .storagePopSaveBox | .diamond => .storagePopSaveDiamond)
  | .storageLocalRootPush_unfold_leftFstReceiver .. => some .storageLocalRootPushUnfoldLeftFstReceiver
  | .storageLocalRootPushBind .. => some .storageLocalRootPushBind
  | .transfer_unfold_leftFstReceiver .. => some .transferUnfoldLeftFstReceiver
  | .transfer_unfold_rightSndArgument .. => some .transferUnfoldRightSndArgument
  | .transferNoCallback .. => some (match m with | .box => .transferNoCallbackBox | .diamond => .transferNoCallbackDiamond)
  | .memoryFieldRead_unfold_rightFst .. => some .memoryFieldReadUnfoldRightFst
  | .memoryIndexRead_unfold_rightFst .. => some .memoryIndexReadUnfoldRightFst
  | .memoryIndexRead_unfold_rightSndIndex .. => some .memoryIndexReadUnfoldRightSndIndex
  | .memoryFieldReadHeap .. => some .memoryFieldReadHeap
  | .memoryIndexReadHeap .. => some (match m with | .box => .memoryIndexReadHeapBox | .diamond => .memoryIndexReadHeapDiamond)
  | .memoryRootAlias .. => some .memoryRootAlias
  | .memoryFieldReadAliasRoot .. => some .memoryFieldReadAliasRoot
  | .memoryIndexReadAliasRoot .. => some (match m with | .box => .memoryIndexReadAliasRootBox | .diamond => .memoryIndexReadAliasRootDiamond)
  | .memoryLocalDeclInitDrop .. => some .memoryLocalDeclInitDrop
  | .memoryDeclFreshAlloc .. => some .memoryDeclFreshAlloc
  | .memoryFieldWriteStore .. => some .memoryFieldWriteStore
  | .memoryIndexWriteStore .. => some (match m with | .box => .memoryIndexWriteStoreBox | .diamond => .memoryIndexWriteStoreDiamond)
  | .memoryFieldWriteCopy .. => some .memoryFieldWriteCopy
  | .memoryIndexWriteCopy .. => some (match m with | .box => .memoryIndexWriteCopyBox | .diamond => .memoryIndexWriteCopyDiamond)
  | .memoryFieldWrite_unfold_leftFst .. => some .memoryFieldWriteUnfoldLeftFst
  | .memoryIndexWrite_unfold_leftFst .. => some .memoryIndexWriteUnfoldLeftFst
  | .memoryFieldWriteMemRef_unfold_leftFst .. => some .memoryFieldWriteRefUnfoldLeftFst
  | .memoryIndexWriteMemRef_unfold_leftFst .. => some .memoryIndexWriteRefUnfoldLeftFst
  | .memoryIndexWriteNonSimpleIndexCapture .. => some .memoryIndexWriteUnfoldLeftSndIndex
  | .memoryIndexWriteMemRefNonSimpleIndexCapture .. => some .memoryIndexWriteRefUnfoldLeftSndIndex
  | .memoryFieldWriteUnfoldSource .. => some .memoryFieldWriteUnfoldSource
  | .memoryIndexWriteUnfoldSource .. => some .memoryIndexWriteUnfoldSource
  | .storageToMemoryDeclCopyRoot .. => some .storageToMemoryDeclCopyRoot
  | .storageToMemoryDeclCopyField .. => some .storageToMemoryDeclCopyField
  | .storageToMemoryDeclUnfoldRightFst .. => some .storageToMemoryDeclUnfoldRightFst
  | .memoryStorageCopy .. => some .memoryStorageCopy
  | .memoryStorageCopyUnfold .. => some .memoryStorageCopyUnfold
  | .memoryToStorageStoreRoot .. => some .memoryToStorageStoreRoot
  | .memoryToStorageFieldCopyRoot .. => some .memoryToStorageFieldCopyRoot
  | .memoryToStorageFieldCopyField .. => some .memoryToStorageFieldCopyField
  | .memoryToStorageIndexMappingCopyRoot .. => some .memoryToStorageIndexMappingCopyRoot
  | .memoryToStorageIndexArrayCopyRoot .. => some (match m with | .box => .memoryToStorageIndexArrayCopyRootBox | .diamond => .memoryToStorageIndexArrayCopyRootDiamond)
  | .memoryToStorageField_unfold_leftFst .. => some .memoryToStorageFieldUnfoldLeftFst
  | .memoryToStorageIndex_unfold_leftFst .. => some .memoryToStorageIndexUnfoldLeftFst
  | .memoryToStorageIndexNonSimpleIndexCapture .. => some .memoryToStorageIndexUnfoldLeftSndIndex
  | Taclet.memoryFieldOpAssign (op := op) .. => some (.memoryFieldOpAssign op)
  | Taclet.memoryIndexArrayOpAssign (op := op) .. => some (.memoryIndexArrayOpAssign op)
  | Taclet.memoryFieldOpAssignUnfoldLeftFst (op := op) .. => some (.memoryFieldOpAssignUnfoldLeftFst op)
  | Taclet.memoryIndexOpAssignUnfoldLeftFst (op := op) .. => some (.memoryIndexOpAssignUnfoldLeftFst op)
  | Taclet.memoryFieldIncrement (op := op) .. => some (.memoryFieldIncrement op)
  | Taclet.memoryIndexArrayIncrement (op := op) .. => some (.memoryIndexArrayIncrement op)
  | Taclet.memoryFieldIncrementUnfoldLeftFst (op := op) .. => some (.memoryFieldIncrementUnfoldLeftFst op)
  | Taclet.memoryIndexIncrementUnfoldLeftFst (op := op) .. => some (.memoryIndexIncrementUnfoldLeftFst op)
  | Taclet.memoryFieldIncrementAssignment (op := op) .. => some (.memoryFieldIncrementAssignment op)
  | Taclet.memoryIndexArrayIncrementAssignment (op := op) .. => some (.memoryIndexArrayIncrementAssignment op)
  | .ternaryToIfMemory .. => some .ternaryToIfMemory
  | .ifElseSplit .. => none
  | .requireSimple .. => some .requireSimple
  | .assertSimple .. => some .assertSimple
  | .revertBox .. => some .revertBox
  | .revertDiamond .. => some .revertDiamond

/-- The solkey taclet a derivation's last step is. -/
def Taclet.origin {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {pr : Premise C Γ Γ'} : Taclet C m s pr → KeyOrigin
  | .storageFieldRead_unfold_rightFst .. => .taclet .storageFieldRead_unfold_rightFst
  | .storageIndexRead_unfold_rightFst .. => .taclet .storageIndexRead_unfold_rightFst
  | .storageIndexRead_unfold_rightSndIndex .. => .taclet .storageIndexRead_unfold_rightSndIndex
  | .storageFieldRead_unfold_rightSndResult .. => .taclet .storageFieldRead_unfold_rightSndResult
  | .storageIndexRead_unfold_rightSndResult .. => .taclet .storageIndexRead_unfold_rightSndResult
  | .storageFieldWrite_unfold_leftFst .. => .taclet .storageFieldWrite_unfold_leftFst
  | .storageFieldWriteStorageRef_unfold_leftFst .. => .taclet .storageFieldWriteStorageRef_unfold_leftFst
  | .storageIndexWrite_unfold_leftFst .. => .taclet .storageIndexWrite_unfold_leftFst
  | .storageIndexWriteStorageRef_unfold_leftFst .. => .taclet .storageIndexWriteStorageRef_unfold_leftFst
  | .storageIndexWriteNonSimpleIndexCapture .. => .taclet .storageIndexWriteNonSimpleIndexCapture
  | .storageIndexWriteStorageRefNonSimpleIndexCapture .. => .taclet .storageIndexWriteStorageRefNonSimpleIndexCapture
  | .storageRootWriteValueRhsCapture .. => .taclet .storageRootWriteValueRhsCapture
  | .fieldWriteValueRhsCapture .. => .taclet .fieldWriteValueRhsCapture
  | .indexWriteValueRhsCapture .. => .taclet .indexWriteValueRhsCapture
  | .storageFieldDelete_unfold_leftFst .. => .taclet .storageFieldDelete_unfold_leftFst
  | .storageIndexDelete_unfold_leftFst .. => .taclet .storageIndexDelete_unfold_leftFst
  | .storageIndexDeleteNonSimpleIndexCapture .. => .taclet .storageIndexDeleteNonSimpleIndexCapture
  | .localValueDeclInitDrop .. => .taclet .localValueDeclInitDrop
  | .valueDeclSkip .. => .taclet .valueDeclSkip
  | .localValueAssign .. => .taclet .localValueAssign
  | .storageRootReadSelect .. => .taclet .storageRootReadSelect
  | .storageFieldReadFind .. => .taclet .storageFieldReadFind
  | .storageIndexReadMappingFind .. => .taclet .storageIndexReadMappingFind
  | .storageIndexReadArrayFind .. => .taclet .storageIndexReadArrayFind
  | .storageRootWriteStore .. => .taclet .storageRootWriteStore
  | .storageRootWriteCopySource .. => .taclet .storageRootWriteCopySource
  | .storageFieldReadStoreRoot .. => .taclet .storageFieldReadStoreRoot
  | .storageIndexReadMappingStoreRoot .. => .taclet .storageIndexReadMappingStoreRoot
  | .storageIndexReadArrayStoreRoot .. => .taclet .storageIndexReadArrayStoreRoot
  | .storageFieldWriteSave .. => .taclet .storageFieldWriteSave
  | .storageFieldWriteCopySource .. => .taclet .storageFieldWriteCopySource
  | .storageIndexWriteMappingSave .. => .taclet .storageIndexWriteMappingSave
  | .storageIndexWriteArraySave .. => .taclet .storageIndexWriteArraySave
  | .storageIndexWriteMappingCopySource .. => .taclet .storageIndexWriteMappingCopySource
  | .storageIndexWriteArrayCopySource .. => .taclet .storageIndexWriteArrayCopySource
  | .storageLocalRootRebind .. => .taclet .storageLocalRootRebind
  | .storageFieldReadBindLocalRoot .. => .taclet .storageFieldReadBindLocalRoot
  | .storageIndexReadMappingBindLocalRoot .. => .taclet .storageIndexReadMappingBindLocalRoot
  | .storageIndexReadArrayBindLocalRoot .. => .taclet .storageIndexReadArrayBindLocalRoot
  | .storageLocalDeclInitDrop .. => .taclet .storageLocalDeclInitDrop
  | .storageRootDelete .. => .taclet .storageRootDelete
  | .storageFieldDelete .. => .taclet .storageFieldDelete
  | .storageIndexDelete .. => .taclet .storageIndexDelete
  | .binopAssignment op .. => (ruleEffect (.binopAssignment op)).origin
  | .binopUnfoldLeft op .. => (ruleEffect (.binopUnfoldLeft op)).origin
  | .binopUnfoldRight op .. => (ruleEffect (.binopUnfoldRight op)).origin
  | .logicalAndShortCircuitRhs .. => .taclet .logicalAndShortCircuitRhs
  | .logicalOrShortCircuitRhs .. => .taclet .logicalOrShortCircuitRhs
  | .unopAssignment op .. => (ruleEffect (.unopAssignment op)).origin
  | .unopCapture op .. => (ruleEffect (.unopCapture op)).origin
  | .localOpAssign op .. => (ruleEffect (.localOpAssign op)).origin
  | .storageRootOpAssign op .. => (ruleEffect (.storageRootOpAssign op)).origin
  | .storageFieldOpAssign op .. => (ruleEffect (.storageFieldOpAssign op)).origin
  | .storageIndexMappingOpAssign op .. => (ruleEffect (.storageIndexMappingOpAssign op)).origin
  | .storageIndexArrayOpAssign op .. => (ruleEffect (.storageIndexArrayOpAssign op)).origin
  | .storageFieldOpAssignUnfoldLeftFst op .. => (ruleEffect (.storageFieldOpAssignUnfoldLeftFst op)).origin
  | .storageIndexOpAssignUnfoldLeftFst op .. => (ruleEffect (.storageIndexOpAssignUnfoldLeftFst op)).origin
  | .compoundAssignValueRhsCapture op .. => (ruleEffect (.compoundAssignValueRhsCapture op)).origin
  | Taclet.localIncrement (op := op) .. => (ruleEffect (.localIncrement op)).origin
  | Taclet.storageRootIncrement (op := op) .. => (ruleEffect (.storageRootIncrement op)).origin
  | Taclet.storageFieldIncrement (op := op) .. => (ruleEffect (.storageFieldIncrement op)).origin
  | Taclet.storageIndexIncrement (op := op) .. => (ruleEffect (.storageIndexIncrement op)).origin
  | Taclet.storageFieldIncrementUnfoldLeftFst (op := op) .. => (ruleEffect (.storageFieldIncrementUnfoldLeftFst op)).origin
  | Taclet.storageIndexIncrementUnfoldLeftFst (op := op) .. => (ruleEffect (.storageIndexIncrementUnfoldLeftFst op)).origin
  | Taclet.localAssignIncrement (op := op) .. => (ruleEffect (.localAssignIncrement op)).origin
  | Taclet.storageRootIncrementAssignment (op := op) .. => (ruleEffect (.storageRootIncrementAssignment op)).origin
  | Taclet.storageFieldIncrementAssignment (op := op) .. => (ruleEffect (.storageFieldIncrementAssignment op)).origin
  | Taclet.storageIndexIncrementAssignment (op := op) .. => (ruleEffect (.storageIndexIncrementAssignment op)).origin
  | .ternaryToIf .. => .taclet .ternaryToIf
  | .ternaryToIfStorage .. => .taclet .ternaryToIfStorage
  | .ternaryCaptureCond .. => .taclet .ternaryCaptureCond
  | .storagePushValueSave .. => .taclet .storagePushValueSave
  | .storagePushValueCopySource .. => .taclet .storagePushValueCopySource
  | .storagePushLengthSave .. => .taclet .storagePushLengthSave
  | .storagePushValue_unfold_rightSndArgument .. => .taclet .storagePushValue_unfold_rightSndArgument
  | .storagePushValue_unfold_leftFstReceiver .. => .taclet .storagePushValue_unfold_leftFstReceiver
  | .storagePush_unfold_leftFstReceiver .. => .taclet .storagePush_unfold_leftFstReceiver
  | .storagePop_unfold_leftFstReceiver .. => .taclet .storagePop_unfold_leftFstReceiver
  | .storagePopSave .. => .taclet .storagePopSave
  | .storageLocalRootPush_unfold_leftFstReceiver .. => .taclet .storageLocalRootPush_unfold_leftFstReceiver
  | .storageLocalRootPushBind .. => .taclet .storageLocalRootPushBind
  | .transfer_unfold_leftFstReceiver .. => .taclet .transfer_unfold_leftFstReceiver
  | .transfer_unfold_rightSndArgument .. => .taclet .transfer_unfold_rightSndArgument
  | .transferNoCallback .. =>
    .taclet (match m with | .box => .transferNoCallbackBox | .diamond => .transferNoCallbackDiamond)
  | .memoryFieldRead_unfold_rightFst .. => (ruleEffect .memoryFieldReadUnfoldRightFst).origin
  | .memoryIndexRead_unfold_rightFst .. => (ruleEffect .memoryIndexReadUnfoldRightFst).origin
  | .memoryIndexRead_unfold_rightSndIndex .. => (ruleEffect .memoryIndexReadUnfoldRightSndIndex).origin
  | .memoryFieldReadHeap .. => (ruleEffect .memoryFieldReadHeap).origin
  | .memoryIndexReadHeap .. => (ruleEffect (match m with | .box => .memoryIndexReadHeapBox | .diamond => .memoryIndexReadHeapDiamond)).origin
  | .memoryRootAlias .. => (ruleEffect .memoryRootAlias).origin
  | .memoryFieldReadAliasRoot .. => (ruleEffect .memoryFieldReadAliasRoot).origin
  | .memoryIndexReadAliasRoot .. => (ruleEffect (match m with | .box => .memoryIndexReadAliasRootBox | .diamond => .memoryIndexReadAliasRootDiamond)).origin
  | .memoryLocalDeclInitDrop .. => (ruleEffect .memoryLocalDeclInitDrop).origin
  | .memoryDeclFreshAlloc .. => (ruleEffect .memoryDeclFreshAlloc).origin
  | .memoryFieldWriteStore .. => (ruleEffect .memoryFieldWriteStore).origin
  | .memoryIndexWriteStore .. => (ruleEffect (match m with | .box => .memoryIndexWriteStoreBox | .diamond => .memoryIndexWriteStoreDiamond)).origin
  | .memoryFieldWriteCopy .. => (ruleEffect .memoryFieldWriteCopy).origin
  | .memoryIndexWriteCopy .. => (ruleEffect (match m with | .box => .memoryIndexWriteCopyBox | .diamond => .memoryIndexWriteCopyDiamond)).origin
  | .memoryFieldWrite_unfold_leftFst .. => (ruleEffect .memoryFieldWriteUnfoldLeftFst).origin
  | .memoryIndexWrite_unfold_leftFst .. => (ruleEffect .memoryIndexWriteUnfoldLeftFst).origin
  | .memoryFieldWriteMemRef_unfold_leftFst .. => (ruleEffect .memoryFieldWriteRefUnfoldLeftFst).origin
  | .memoryIndexWriteMemRef_unfold_leftFst .. => (ruleEffect .memoryIndexWriteRefUnfoldLeftFst).origin
  | .memoryIndexWriteNonSimpleIndexCapture .. => (ruleEffect .memoryIndexWriteUnfoldLeftSndIndex).origin
  | .memoryIndexWriteMemRefNonSimpleIndexCapture .. => (ruleEffect .memoryIndexWriteRefUnfoldLeftSndIndex).origin
  | .memoryFieldWriteUnfoldSource .. => (ruleEffect .memoryFieldWriteUnfoldSource).origin
  | .memoryIndexWriteUnfoldSource .. => (ruleEffect .memoryIndexWriteUnfoldSource).origin
  | .storageToMemoryDeclCopyRoot .. => (ruleEffect .storageToMemoryDeclCopyRoot).origin
  | .storageToMemoryDeclCopyField .. => (ruleEffect .storageToMemoryDeclCopyField).origin
  | .storageToMemoryDeclUnfoldRightFst .. => (ruleEffect .storageToMemoryDeclUnfoldRightFst).origin
  | .memoryStorageCopy .. => (ruleEffect .memoryStorageCopy).origin
  | .memoryStorageCopyUnfold .. => (ruleEffect .memoryStorageCopyUnfold).origin
  | .memoryToStorageStoreRoot .. => (ruleEffect .memoryToStorageStoreRoot).origin
  | .memoryToStorageFieldCopyRoot .. => (ruleEffect .memoryToStorageFieldCopyRoot).origin
  | .memoryToStorageFieldCopyField .. => (ruleEffect .memoryToStorageFieldCopyField).origin
  | .memoryToStorageIndexMappingCopyRoot .. => (ruleEffect .memoryToStorageIndexMappingCopyRoot).origin
  | .memoryToStorageIndexArrayCopyRoot .. => (ruleEffect (match m with | .box => .memoryToStorageIndexArrayCopyRootBox | .diamond => .memoryToStorageIndexArrayCopyRootDiamond)).origin
  | .memoryToStorageField_unfold_leftFst .. => (ruleEffect .memoryToStorageFieldUnfoldLeftFst).origin
  | .memoryToStorageIndex_unfold_leftFst .. => (ruleEffect .memoryToStorageIndexUnfoldLeftFst).origin
  | .memoryToStorageIndexNonSimpleIndexCapture .. => (ruleEffect .memoryToStorageIndexUnfoldLeftSndIndex).origin
  | Taclet.memoryFieldOpAssign (op := op) .. => (ruleEffect (.memoryFieldOpAssign op)).origin
  | Taclet.memoryIndexArrayOpAssign (op := op) .. => (ruleEffect (.memoryIndexArrayOpAssign op)).origin
  | Taclet.memoryFieldOpAssignUnfoldLeftFst (op := op) .. => (ruleEffect (.memoryFieldOpAssignUnfoldLeftFst op)).origin
  | Taclet.memoryIndexOpAssignUnfoldLeftFst (op := op) .. => (ruleEffect (.memoryIndexOpAssignUnfoldLeftFst op)).origin
  | Taclet.memoryFieldIncrement (op := op) .. => (ruleEffect (.memoryFieldIncrement op)).origin
  | Taclet.memoryIndexArrayIncrement (op := op) .. => (ruleEffect (.memoryIndexArrayIncrement op)).origin
  | Taclet.memoryFieldIncrementUnfoldLeftFst (op := op) .. => (ruleEffect (.memoryFieldIncrementUnfoldLeftFst op)).origin
  | Taclet.memoryIndexIncrementUnfoldLeftFst (op := op) .. => (ruleEffect (.memoryIndexIncrementUnfoldLeftFst op)).origin
  | Taclet.memoryFieldIncrementAssignment (op := op) .. => (ruleEffect (.memoryFieldIncrementAssignment op)).origin
  | Taclet.memoryIndexArrayIncrementAssignment (op := op) .. => (ruleEffect (.memoryIndexArrayIncrementAssignment op)).origin
  | .ternaryToIfMemory .. => (ruleEffect .ternaryToIfMemory).origin
  | .ifElseSplit .. => .taclet .ifElseSplit
  | .requireSimple .. => .taclet .requireSimple
  | .assertSimple .. => .taclet .assertSimple
  | .revertBox .. => .taclet .revertBox
  | .revertDiamond .. => .taclet .revertDiamond

/-- **The names agree**: the old rule a step bridges to records the step's
taclet as (one of) its origins.  `alice.age = 10;` is
`storageFieldWriteSave`, whose old rule `storageFieldWriteSave` has that
origin. -/
theorem Taclet.origin_claimed {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {pr : Premise C Γ Γ'}
    (d : Taclet C m s pr) {r : RuleName} (h : d.rule = some r) :
    ∀ t ∈ d.origin.taclets, t ∈ (ruleEffect r).origin.taclets := by
  cases d <;> (try cases m) <;>
    first
    | (injection h with h; subst h; first | exact fun _ h => h | (delta Taclet.origin; dsimp only; decide))
    | injection h

/-- The one step without a rule is the branch split. -/
theorem Taclet.rule_none {Γ Γ' : Ctx} {s : Stmt C Γ Γ'} {pr : Premise C Γ Γ'}
    (d : Taclet C m s pr) (h : d.rule = none) : d.origin = .taclet .ifElseSplit := by
  cases d <;> (try cases m) <;> first | rfl | injection h

/-! ## Agreement with the old table, run -/

open UniquenessAux in
/-- The statements of a block on which the kernel's rule and the old table's
`candidate` differ, printed. -/
def Prog.disagreements (m : Modality) : {Γ Γ' : Ctx} → Prog C Γ Γ' → List String
  | _, _, .nil => []
  | _, _, .cons s P =>
    let k := (s.step m).2.rule
    let o := candidate m s.erase
    (if k == o then [] else [s!"{s.toStr} kernel={repr k} old={repr o}"]) ++ Prog.disagreements m P

section Tour

local instance instBridgeContract : InContract := ⟨StandardExample⟩

/-- Every statement form of the kernel, over `StandardExample`. -/
def bridgeTour := ksol{
  uint x = 1; uint y; bool b = true;
  x = total; x = alice.age; x = folks[x].age; x = balances[x]; x = values[1];
  x = persons[x + 1].age; x = x + 1; x = total + 1; x = x + total; x = x + (x * 2);
  x = (x + 1) * 2; b = b && flags[x]; b = b || flags[x]; b = !b; b = !flags[x];
  total = 5; total = x + 1; alice.age = 3; alice.age = x + 1; folks[x].age = 3;
  folks[x + 1].age = 3; persons[x].age = x * 2; balances[x] = 1; balances[x + 1] = 2;
  values[x] = 1; values[x + 1] = x; matrix[x][x] = 1;
  alice = bob; folks[x] = bob; persons[x] = alice; bob = folks[x];
  Person storage p = alice; Person storage q = folks[x]; Person storage r = persons[x + 1];
  p.age = 7; p = bob; x = p.age;
  delete total; delete alice.age; delete folks[x]; delete folks[x + 1]; delete persons[x].age;
  delete alice;
  x += 1; x -= y; total *= 2; alice.age /= x; balances[x] %= 3; values[x] += 1;
  folks[x].age += 1; persons[x + 1].age -= 1; matrix[x][x] += 1; x += total + 1;
  x++; ++total; alice.age++; ++balances[x]; values[x]++; folks[x].age++; persons[x + 1].age++;
  y = x++; y = ++total; y = alice.age++; y = ++balances[x]; y = folks[x].age++;
  x = b ? 1 : 2; x = (x > 1) ? x : total; total = b ? x : 3; alice.age = (x == 1) ? 2 : x;
  folks[x + 1].age = b ? 1 : 2; x = (b ? 1 : 2) + 1; x += b ? 1 : 2;
  values.push(x); values.push(x + 1); values.push(); persons.push(alice); persons.push(folks[x]);
  persons.push(); values.pop(); matrix[x].push(1); matrix[x + 1].push(); matrix[x].pop();
  Person storage pp = people.push(); pp = persons.push(); uint[] storage row = matrix.push();
  owner.transfer(1); owner.transfer(x + 1); (x + 1).transfer(2); balances[x].transfer(x);
  Person memory mp; Person memory mq = mp; Account memory ma = mp.account; mq = mp;
  x = mp.age; x = mp.account.balance; mp.age = 3; mp.age = x + 1; mp.account.balance = x;
  mp.account = mq.account; mp.account = ma; mq.account.token = ma.token;
  Person memory mc = alice; Person memory md = folks[x]; Account memory me = alice.account;
  Account memory mf = folks[x + 1].account; mq = bob; mq = persons[x]; ma = bob.account;
  alice = mp; alice.account = ma; alice.account = mp.account; folks[x] = mp; persons[x] = mq;
  folks[x + 1].account = ma; persons[x + 1] = mp; folks[x].account = mp.account;
  mp.age += 1; mp.account.balance -= x; mp.age++; ++mp.account.balance; y = mp.age++;
  mp.age = b ? 1 : 2; mp.account.balance = (x > 1) ? x : 0;
  if (b) { x = 1; } else { x = 2; }; require(b); assert(b); require(x == 1); revert();
}

-- Under a box, the two tables pick the same rule for every statement but
-- the ones the module docstring names.
#guard bridgeTour.disagreements .box = [
  "x = total + 1; kernel=some (Solidity.RuleName.binopUnfoldLeft (Solidity.BinOp.add)) old=some (Solidity.RuleName.binopAssignment (Solidity.BinOp.add))",
  "x = x + total; kernel=some (Solidity.RuleName.binopUnfoldRight (Solidity.BinOp.add)) old=some (Solidity.RuleName.binopAssignment (Solidity.BinOp.add))",
  "Person storage r = persons[x + 1]; kernel=some (Solidity.RuleName.storageIndexReadUnfoldRightSndIndex) old=some (Solidity.RuleName.storageLocalDeclInitDrop)",
  "Person storage sp = folks[x]; kernel=some (Solidity.RuleName.storageLocalDeclInitDrop) old=some (Solidity.RuleName.storagePlaceAlias)",
  "Person storage pp = people.push(); kernel=some (Solidity.RuleName.storageLocalRootPushBind) old=some (Solidity.RuleName.storageLocalDeclInitDrop)",
  "uint[] storage row = matrix.push(); kernel=some (Solidity.RuleName.storageLocalRootPushBind) old=some (Solidity.RuleName.storageLocalDeclInitDrop)",
  "owner.transfer(1); kernel=some (Solidity.RuleName.transferUnfoldLeftFstReceiver) old=some (Solidity.RuleName.transferNoCallbackBox)",
  "owner.transfer(x + 1); kernel=some (Solidity.RuleName.transferUnfoldLeftFstReceiver) old=some (Solidity.RuleName.transferUnfoldRightSndArgument)",
  "mp.account = mq.account; kernel=some (Solidity.RuleName.memoryFieldWriteCopy) old=some (Solidity.RuleName.memoryFieldReadUnfoldRightSndResult)",
  "mq.account.token = ma.token; kernel=some (Solidity.RuleName.memoryFieldWriteRefUnfoldLeftFst) old=some (Solidity.RuleName.memoryFieldReadUnfoldRightSndResult)",
  "Person memory md = folks[x]; kernel=some (Solidity.RuleName.storageToMemoryDeclUnfoldRightFst) old=none",
  "folks[x].account = mp.account; kernel=some (Solidity.RuleName.memoryToStorageFieldUnfoldLeftFst) old=some (Solidity.RuleName.memoryToStorageUnfoldRightFstSource)"]

-- And under a diamond, up to the old table's box/diamond twins.
#guard (bridgeTour.disagreements .diamond).map (·.replace "Diamond" "Box") =
  bridgeTour.disagreements .box

/-- A push place on a member: `TestSuite`'s `bucket.tokens`. -/
def pushTour := ksol[TestSuite]{
  Token storage t = bucket.tokens.push(); t = tokens.push(); t = bucket.tokens.push();
}

#guard pushTour.disagreements .box = [
  "Token storage t = bucket.tokens.push(); kernel=some (Solidity.RuleName.storageLocalRootPushUnfoldLeftFstReceiver) old=some (Solidity.RuleName.storageLocalDeclInitDrop)"]

end Tour

end Kernel
end Solidity
