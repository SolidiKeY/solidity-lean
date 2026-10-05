import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived (12 of 12)

`⊢` of each obligation the copies between storage and memory added, in
the order of the source; the replays are what `#solkey_derive? … pending`
(`Frontend/Problems.lean`) prints.  First the copies from storage into
memory (`memoryStorageCopy`, then `readFromCopyToStorage`: a later write to
the storage is not seen), from `storageToMemory` to `memoryAssignForms`;
then the copies from memory into storage (`memoryToStorage*CopyRoot`, read
through the view by `findOnCopy` and `selectOnCopyMem*`: a later write to
memory is not seen), from `storageNewIntoField` to
`mappingEntryThroughMemoryToMappingEntry`.
-/

open Solidity Proves

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
  refine Proves.close_dropWt ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

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
