import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived (7 of 8)

`⊢` of each obligation the closer of arrays and copies added (arrays
pushed and popped, the slot a `push()` recycles, copies between storage
locations), from `storageIndexWriteComplexReceiverCopySource` to `testStorageNestedPushReturnAlias` in the
order of the source; the replays are what `#solkey_derive? … pending`
(`Frontend/Problems.lean`) prints.  A leaf the closer leaves sets the
`wt(storage)` premise aside (`Proves.close_dropWt`).
-/

open Solidity Proves

theorem Solkey.TestSuite.storageIndexWriteComplexReceiverCopySource.proved : ⊢ Solkey.TestSuite.storageIndexWriteComplexReceiverCopySource.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldWriteRootRhsComplexReceiver.proved : ⊢ Solkey.TestSuite.storageFieldWriteRootRhsComplexReceiver.problem := by
  sol_prove

theorem Solkey.TestSuite.storagePushValue.proved : ⊢ Solkey.TestSuite.storagePushValue.problem := by
  sol_prove

theorem Solkey.TestSuite.storagePushComplexReceiverNonsimpleArg.proved : ⊢ Solkey.TestSuite.storagePushComplexReceiverNonsimpleArg.problem := by
  sol_prove

theorem Solkey.TestSuite.storagePushValueCopySource.proved : ⊢ Solkey.TestSuite.storagePushValueCopySource.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageComplexReceiverEmptyPush.proved : ⊢ Solkey.TestSuite.testStorageComplexReceiverEmptyPush.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldCopyStruct.proved : ⊢ Solkey.TestSuite.storageFieldCopyStruct.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldDeleteThenCopy.proved : ⊢ Solkey.TestSuite.storageFieldDeleteThenCopy.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldDeleteThenCopyDeep.proved : ⊢ Solkey.TestSuite.storageFieldDeleteThenCopyDeep.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldWriteCaptureSrc.proved : ⊢ Solkey.TestSuite.storageFieldWriteCaptureSrc.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexCopysourceAfterPush.proved : ⊢ Solkey.TestSuite.storageIndexCopysourceAfterPush.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexDecomposeAfterPush.proved : ⊢ Solkey.TestSuite.storageIndexDecomposeAfterPush.problem := by
  sol_prove

theorem Solkey.TestSuite.storagePopAfterPush.proved : ⊢ Solkey.TestSuite.storagePopAfterPush.problem := by
  sol_prove

theorem Solkey.TestSuite.storagePopNonempty.proved : ⊢ Solkey.TestSuite.storagePopNonempty.problem := by
  sol_prove

theorem Solkey.TestSuite.storagePopUnknownLength.proved : ⊢ Solkey.TestSuite.storagePopUnknownLength.problem := by
  sol_prove

theorem Solkey.TestSuite.storagePushEmpty.proved : ⊢ Solkey.TestSuite.storagePushEmpty.problem := by
  sol_prove

theorem Solkey.TestSuite.storagePushLengthPositive.proved : ⊢ Solkey.TestSuite.storagePushLengthPositive.problem := by
  sol_prove

theorem Solkey.TestSuite.storagePushLocalBind.proved : ⊢ Solkey.TestSuite.storagePushLocalBind.problem := by
  sol_prove

theorem Solkey.TestSuite.storagePushNonsimpleArg.proved : ⊢ Solkey.TestSuite.storagePushNonsimpleArg.problem := by
  sol_prove

theorem Solkey.TestSuite.storagePushReturnAssign.proved : ⊢ Solkey.TestSuite.storagePushReturnAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootCopyStruct.proved : ⊢ Solkey.TestSuite.storageRootCopyStruct.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootDeleteThenCopy.proved : ⊢ Solkey.TestSuite.storageRootDeleteThenCopy.problem := by
  sol_prove

theorem Solkey.TestSuite.testDeepPopDoesNotResetMappingMember.proved : ⊢ Solkey.TestSuite.testDeepPopDoesNotResetMappingMember.problem := by
  sol_prove

theorem Solkey.TestSuite.testDeleteArrayDoesNotResetElementMappingMember.proved : ⊢ Solkey.TestSuite.testDeleteArrayDoesNotResetElementMappingMember.problem := by
  sol_prove

theorem Solkey.TestSuite.testNestedIndexWriteImpureIndexPrimitiveRhs.proved : ⊢ Solkey.TestSuite.testNestedIndexWriteImpureIndexPrimitiveRhs.problem := by
  sol_prove

theorem Solkey.TestSuite.testNestedIndexReadImpureIndex.proved : ⊢ Solkey.TestSuite.testNestedIndexReadImpureIndex.problem := by
  sol_prove

theorem Solkey.TestSuite.testNestedIndexWriteImpureReceiverAndIndex.proved : ⊢ Solkey.TestSuite.testNestedIndexWriteImpureReceiverAndIndex.problem := by
  sol_prove

theorem Solkey.TestSuite.testNestedIndexReadImpureReceiverAndIndex.proved : ⊢ Solkey.TestSuite.testNestedIndexReadImpureReceiverAndIndex.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageDeleteImpureReceiver.proved : ⊢ Solkey.TestSuite.testStorageDeleteImpureReceiver.problem := by
  sol_prove

theorem Solkey.TestSuite.testStoragePushImpureReceiver.proved : ⊢ Solkey.TestSuite.testStoragePushImpureReceiver.problem := by
  sol_prove

theorem Solkey.TestSuite.testCompoundAssignImpureReceiver.proved : ⊢ Solkey.TestSuite.testCompoundAssignImpureReceiver.problem := by
  sol_prove

theorem Solkey.TestSuite.testIndexWriteReceiverReadsMutatedVar.proved : ⊢ Solkey.TestSuite.testIndexWriteReceiverReadsMutatedVar.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageComplexReceiverPushFieldLvalue.proved : ⊢ Solkey.TestSuite.testStorageComplexReceiverPushFieldLvalue.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageComplexReceiverPushLvalueCopy.proved : ⊢ Solkey.TestSuite.testStorageComplexReceiverPushLvalueCopy.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageIndexWriteImpureIndexPrimitiveRhs.proved : ⊢ Solkey.TestSuite.testStorageIndexWriteImpureIndexPrimitiveRhs.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageIndexWriteImpureIndexRefRhs.proved : ⊢ Solkey.TestSuite.testStorageIndexWriteImpureIndexRefRhs.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageEvaluationOrder.proved : ⊢ Solkey.TestSuite.testStorageEvaluationOrder.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageFieldDeepCopy.proved : ⊢ Solkey.TestSuite.testStorageFieldDeepCopy.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageMapStructCopy.proved : ⊢ Solkey.TestSuite.testStorageMapStructCopy.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageNestedPushReturnAlias.proved : ⊢ Solkey.TestSuite.testStorageNestedPushReturnAlias.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
