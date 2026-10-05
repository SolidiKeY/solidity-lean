import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived (11 of 11)

`⊢` of each obligation the closer of memory added (objects allocated by
the updates, read and written through members and indices, copied between
memory and storage), from `memoryIndexArrayMulAssignUnfold` to `memoryIndexArrayPostdecrementAssignment` in the
order of the source; the replays are what `#solkey_derive? … pending`
(`Frontend/Problems.lean`) prints.
-/

open Solidity Proves

theorem Solkey.TestSuite.memoryIndexArrayMulAssignUnfold.proved : ⊢ Solkey.TestSuite.memoryIndexArrayMulAssignUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayDivAssignUnfold.proved : ⊢ Solkey.TestSuite.memoryIndexArrayDivAssignUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayModAssignUnfold.proved : ⊢ Solkey.TestSuite.memoryIndexArrayModAssignUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPostincrementUnfold.proved : ⊢ Solkey.TestSuite.memoryIndexArrayPostincrementUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPredecrementUnfold.proved : ⊢ Solkey.TestSuite.memoryIndexArrayPredecrementUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPostdecrementUnfold.proved : ⊢ Solkey.TestSuite.memoryIndexArrayPostdecrementUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayDeleteUnfold.proved : ⊢ Solkey.TestSuite.memoryIndexArrayDeleteUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPostincrement.proved : ⊢ Solkey.TestSuite.memoryIndexArrayPostincrement.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPredecrement.proved : ⊢ Solkey.TestSuite.memoryIndexArrayPredecrement.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPreincrementAssignment.proved : ⊢ Solkey.TestSuite.memoryIndexArrayPreincrementAssignment.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPostdecrementAssignment.proved : ⊢ Solkey.TestSuite.memoryIndexArrayPostdecrementAssignment.problem := by
  sol_prove
