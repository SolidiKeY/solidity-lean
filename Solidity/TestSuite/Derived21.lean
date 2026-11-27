import Solidity.TestSuite.ScopedProblems
import Solidity.Calculus.Closers


open Solidity
open scoped Scoped

theorem Solkey.TestSuite.memoryIndexWriteStorageRefRhsCapture.proved : ⊢ Solkey.TestSuite.memoryIndexWriteStorageRefRhsCapture.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexWriteStorageStructCopy.proved : ⊢ Solkey.TestSuite.memoryIndexWriteStorageStructCopy.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexWriteStorageRefImpureIndex.proved : ⊢ Solkey.TestSuite.memoryIndexWriteStorageRefImpureIndex.problem := by
  sol_prove

