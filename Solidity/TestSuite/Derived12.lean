import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived (12 of 12)

`⊢` of each obligation the copies from storage into memory added
(`memoryStorageCopy`, then `readFromCopyToStorage`: a later write to the
storage is not seen), from `storageToMemory` to `memoryAssignForms` in the
order of the source; the replays are what `#solkey_derive? … pending`
(`Frontend/Problems.lean`) prints.
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
