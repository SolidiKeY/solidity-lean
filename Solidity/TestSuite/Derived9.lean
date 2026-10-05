import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived (9 of 11)

`⊢` of each obligation the closer of memory added (objects allocated by
the updates, read and written through members and indices, copied between
memory and storage), from `memoryDeclDefault` to `testMemoryAliasing` in the
order of the source; the replays are what `#solkey_derive? … pending`
(`Frontend/Problems.lean`) prints.
-/

open Solidity Proves

theorem Solkey.TestSuite.memoryDeclDefault.proved : ⊢ Solkey.TestSuite.memoryDeclDefault.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryArrayIndex.proved : ⊢ Solkey.TestSuite.memoryArrayIndex.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryNewIntoStructField.proved : ⊢ Solkey.TestSuite.memoryNewIntoStructField.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryNewIntoNestedField.proved : ⊢ Solkey.TestSuite.memoryNewIntoNestedField.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryNewIntoIndex.proved : ⊢ Solkey.TestSuite.memoryNewIntoIndex.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryDeepField.proved : ⊢ Solkey.TestSuite.memoryDeepField.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldAddAssign.proved : ⊢ Solkey.TestSuite.memoryFieldAddAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldSubAssign.proved : ⊢ Solkey.TestSuite.memoryFieldSubAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldMulAssign.proved : ⊢ Solkey.TestSuite.memoryFieldMulAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldDivAssign.proved : ⊢ Solkey.TestSuite.memoryFieldDivAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldModAssign.proved : ⊢ Solkey.TestSuite.memoryFieldModAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldAddAssignUnfold.proved : ⊢ Solkey.TestSuite.memoryFieldAddAssignUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldAddAssignNse.proved : ⊢ Solkey.TestSuite.memoryFieldAddAssignNse.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPreincrement.proved : ⊢ Solkey.TestSuite.memoryFieldPreincrement.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPostincrement.proved : ⊢ Solkey.TestSuite.memoryFieldPostincrement.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPredecrement.proved : ⊢ Solkey.TestSuite.memoryFieldPredecrement.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPostdecrement.proved : ⊢ Solkey.TestSuite.memoryFieldPostdecrement.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPreincrementAssignment.proved : ⊢ Solkey.TestSuite.memoryFieldPreincrementAssignment.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPostincrementAssignment.proved : ⊢ Solkey.TestSuite.memoryFieldPostincrementAssignment.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPredecrementAssignment.proved : ⊢ Solkey.TestSuite.memoryFieldPredecrementAssignment.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPostdecrementAssignment.proved : ⊢ Solkey.TestSuite.memoryFieldPostdecrementAssignment.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPreincrementUnfold.proved : ⊢ Solkey.TestSuite.memoryFieldPreincrementUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldAlias.proved : ⊢ Solkey.TestSuite.memoryFieldAlias.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldReferenceAssign.proved : ⊢ Solkey.TestSuite.memoryFieldReferenceAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayAddAssign.proved : ⊢ Solkey.TestSuite.memoryIndexArrayAddAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArraySubAssign.proved : ⊢ Solkey.TestSuite.memoryIndexArraySubAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayMulAssign.proved : ⊢ Solkey.TestSuite.memoryIndexArrayMulAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayDivAssign.proved : ⊢ Solkey.TestSuite.memoryIndexArrayDivAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayModAssign.proved : ⊢ Solkey.TestSuite.memoryIndexArrayModAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayAddAssignUnfold.proved : ⊢ Solkey.TestSuite.memoryIndexArrayAddAssignUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPreincrementUnfold.proved : ⊢ Solkey.TestSuite.memoryIndexArrayPreincrementUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPreincrement.proved : ⊢ Solkey.TestSuite.memoryIndexArrayPreincrement.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPostdecrement.proved : ⊢ Solkey.TestSuite.memoryIndexArrayPostdecrement.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPostincrementAssignment.proved : ⊢ Solkey.TestSuite.memoryIndexArrayPostincrementAssignment.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPredecrementAssignment.proved : ⊢ Solkey.TestSuite.memoryIndexArrayPredecrementAssignment.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexWriteNse.proved : ⊢ Solkey.TestSuite.memoryIndexWriteNse.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryRootAlias.proved : ⊢ Solkey.TestSuite.memoryRootAlias.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryRootDeleteFresh.proved : ⊢ Solkey.TestSuite.memoryRootDeleteFresh.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryStructArrayIndex.proved : ⊢ Solkey.TestSuite.memoryStructArrayIndex.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryAliasing.proved : ⊢ Solkey.TestSuite.testMemoryAliasing.problem := by
  sol_prove
