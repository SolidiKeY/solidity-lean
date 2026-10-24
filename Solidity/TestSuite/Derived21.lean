import Solidity.TestSuite.ScopedProblems
import Solidity.Calculus.Closers

/-! Obligations whose leaves read memory through a copy of storage below
its root (`docs/solkey-migration.md`): an identity member of a copy read
at the copy (`readFromCopyToStorageIdentity`, `copyObjN`), a word of it or
an element of a copied array read as the storage copied it
(`readFromCopyToStorage`, `copyPathRd?`), each read's guards out of its
address (`LTm.hoistA`), `Calculus/MemRead.lean`. -/

open Solidity
open scoped Scoped

theorem Solkey.TestSuite.memoryIndexWriteStorageRefRhsCapture.proved : ⊢ Solkey.TestSuite.memoryIndexWriteStorageRefRhsCapture.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexWriteStorageStructCopy.proved : ⊢ Solkey.TestSuite.memoryIndexWriteStorageStructCopy.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexWriteStorageRefImpureIndex.proved : ⊢ Solkey.TestSuite.memoryIndexWriteStorageRefImpureIndex.problem := by
  sol_prove

