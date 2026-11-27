import Solidity.TestSuite.ScopedProblems


open Solidity
open scoped Scoped

theorem Solkey.TestSuite.storageToMemory.proved : ⊢ Solkey.TestSuite.storageToMemory.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageToMemoryCopyComplexPath.proved : ⊢ Solkey.TestSuite.testStorageToMemoryCopyComplexPath.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageToMemoryCopyField.proved : ⊢ Solkey.TestSuite.testStorageToMemoryCopyField.problem := by
  sol_prove

theorem Solkey.TestSuite.testStorageToMemoryCopyRoot.proved : ⊢ Solkey.TestSuite.testStorageToMemoryCopyRoot.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryAssignForms.proved : ⊢ Solkey.TestSuite.memoryAssignForms.problem := by
  sol_prove

theorem Solkey.TestSuite.storageNewIntoField.proved : ⊢ Solkey.TestSuite.storageNewIntoField.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryToStorage.proved : ⊢ Solkey.TestSuite.memoryToStorage.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryToStorageIndexMappingCopyRootExample.proved : ⊢ Solkey.TestSuite.memoryToStorageIndexMappingCopyRootExample.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryToStorageIndexArrayCopyRootExample.proved : ⊢ Solkey.TestSuite.memoryToStorageIndexArrayCopyRootExample.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryToStorageIndexArrayCopyRootOutOfBoundsReverts.proved : ⊢ Solkey.TestSuite.memoryToStorageIndexArrayCopyRootOutOfBoundsReverts.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryToStorageCopyComplexSource.proved : ⊢ Solkey.TestSuite.testMemoryToStorageCopyComplexSource.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryToStorageCopyComplexTarget.proved : ⊢ Solkey.TestSuite.testMemoryToStorageCopyComplexTarget.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryToStorageCopyField.proved : ⊢ Solkey.TestSuite.testMemoryToStorageCopyField.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryToStorageCopyRoot.proved : ⊢ Solkey.TestSuite.testMemoryToStorageCopyRoot.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryToStorageIndexCopyImpureIndex.proved : ⊢ Solkey.TestSuite.testMemoryToStorageIndexCopyImpureIndex.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexWriteRefSourceImpureIndex.proved : ⊢ Solkey.TestSuite.storageIndexWriteRefSourceImpureIndex.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldWriteRefSourceImpureReceiver.proved : ⊢ Solkey.TestSuite.storageFieldWriteRefSourceImpureReceiver.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryToStorageIndexImpureReceiver.proved : ⊢ Solkey.TestSuite.memoryToStorageIndexImpureReceiver.problem := by
  sol_prove

theorem Solkey.TestSuite.indexWriteBothImpureMemToStorage.proved : ⊢ Solkey.TestSuite.indexWriteBothImpureMemToStorage.problem := by
  sol_prove

theorem Solkey.TestSuite.mappingEntryThroughMemoryToMappingEntry.proved : ⊢ Solkey.TestSuite.mappingEntryThroughMemoryToMappingEntry.problem := by
  sol_prove
