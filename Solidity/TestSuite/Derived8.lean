import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived (8 of 8)

`⊢` of each obligation the closer of arrays and copies added (arrays
pushed and popped, the slot a `push()` recycles, copies between storage
locations), from `testStoragePushFieldLvalue` to `arrayOfMappingsIndex` in the
order of the source; the replays are what `#solkey_derive? … pending`
(`Frontend/Problems.lean`) prints.  A leaf the closer leaves sets the
`wt(storage)` premise aside (`Proves.close_dropWt`).
-/

open Solidity Proves

theorem Solkey.TestSuite.testStoragePushFieldLvalue.proved : ⊢ Solkey.TestSuite.testStoragePushFieldLvalue.problem := by
  sol_prove

theorem Solkey.TestSuite.testStoragePushLvalueCopiesStorageSource.proved : ⊢ Solkey.TestSuite.testStoragePushLvalueCopiesStorageSource.problem := by
  sol_prove

theorem Solkey.TestSuite.testStoragePushLvaluePrimitive.proved : ⊢ Solkey.TestSuite.testStoragePushLvaluePrimitive.problem := by
  sol_prove

theorem Solkey.TestSuite.testStoragePushReturnAlias.proved : ⊢ Solkey.TestSuite.testStoragePushReturnAlias.problem := by
  sol_prove

theorem Solkey.TestSuite.testStructWithFixedArrayCopy.proved : ⊢ Solkey.TestSuite.testStructWithFixedArrayCopy.problem := by
  sol_prove

theorem Solkey.TestSuite.testPopKeepsMappingElementEntries.proved : ⊢ Solkey.TestSuite.testPopKeepsMappingElementEntries.problem := by
  sol_prove

theorem Solkey.TestSuite.testDeleteKeepsMappingElementEntries.proved : ⊢ Solkey.TestSuite.testDeleteKeepsMappingElementEntries.problem := by
  sol_prove

theorem Solkey.TestSuite.testPushBindMappingElement.proved : ⊢ Solkey.TestSuite.testPushBindMappingElement.problem := by
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

theorem Solkey.TestSuite.testCopyArrayMemberElements.proved : ⊢ Solkey.TestSuite.testCopyArrayMemberElements.problem := by
  sol_prove

theorem Solkey.TestSuite.testCopyStoreRootFromField.proved : ⊢ Solkey.TestSuite.testCopyStoreRootFromField.problem := by
  sol_prove

theorem Solkey.TestSuite.testCopyStoreRootFromIndex.proved : ⊢ Solkey.TestSuite.testCopyStoreRootFromIndex.problem := by
  sol_prove

theorem Solkey.TestSuite.testPushCopyThenDeleteTarget.proved : ⊢ Solkey.TestSuite.testPushCopyThenDeleteTarget.problem := by
  sol_prove

theorem Solkey.TestSuite.indexWriteBothImpureStorageRef.proved : ⊢ Solkey.TestSuite.indexWriteBothImpureStorageRef.problem := by
  sol_prove

theorem Solkey.TestSuite.arrayOfMappingsIndex.proved : ⊢ Solkey.TestSuite.arrayOfMappingsIndex.problem := by
  sol_prove
