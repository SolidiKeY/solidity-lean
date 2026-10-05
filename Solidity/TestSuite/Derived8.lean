import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived (8 of 8)

`⊢` of each obligation the M5 closer added (arrays pushed and popped,
copies between storage locations), from `testStoragePushReturnAlias` to `indexWriteBothImpureStorageRef` in the
order of the source; the replays are what `#solkey_derive? … pending`
(`Frontend/Problems.lean`) prints.  A leaf the closer leaves sets the
`wt(storage)` premise aside (`Proves.close_dropWt`).
-/

open Solidity Proves

theorem Solkey.TestSuite.testStoragePushReturnAlias.proved : ⊢ Solkey.TestSuite.testStoragePushReturnAlias.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageRootDeepCopy.proved : ⊢ Solkey.TestSuite.testStorageRootDeepCopy.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldWriteStorageRefImpureReceiver.proved : ⊢ Solkey.TestSuite.storageFieldWriteStorageRefImpureReceiver.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldWriteRootRefImpureReceiver.proved : ⊢ Solkey.TestSuite.storageFieldWriteRootRefImpureReceiver.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexWriteRootRefImpureReceiver.proved : ⊢ Solkey.TestSuite.storageIndexWriteRootRefImpureReceiver.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexWriteStorageRefImpureReceiver.proved : ⊢ Solkey.TestSuite.storageIndexWriteStorageRefImpureReceiver.problem := by
  sol_prove

theorem Solkey.TestSuite.testCopyRootKeepsValueMembers.proved : ⊢ Solkey.TestSuite.testCopyRootKeepsValueMembers.problem := by
  sol_prove

theorem Solkey.TestSuite.testCopyFieldNested.proved : ⊢ Solkey.TestSuite.testCopyFieldNested.problem := by
  sol_prove

theorem Solkey.TestSuite.testCopyOfCopy.proved : ⊢ Solkey.TestSuite.testCopyOfCopy.problem := by
  sol_prove

theorem Solkey.TestSuite.testCopyIntoMappingEntry.proved : ⊢ Solkey.TestSuite.testCopyIntoMappingEntry.problem := by
  sol_prove

theorem Solkey.TestSuite.testCopyStoreRootFromField.proved : ⊢ Solkey.TestSuite.testCopyStoreRootFromField.problem := by
  sol_prove

theorem Solkey.TestSuite.testCopyStoreRootFromIndex.proved : ⊢ Solkey.TestSuite.testCopyStoreRootFromIndex.problem := by
  sol_prove

theorem Solkey.TestSuite.testPushCopyThenDeleteTarget.proved : ⊢ Solkey.TestSuite.testPushCopyThenDeleteTarget.problem := by
  sol_prove

theorem Solkey.TestSuite.indexWriteBothImpureStorageRef.proved : ⊢ Solkey.TestSuite.indexWriteBothImpureStorageRef.problem := by
  sol_prove
