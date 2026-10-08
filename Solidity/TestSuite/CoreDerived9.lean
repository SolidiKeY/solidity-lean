import Solidity.TestSuite.CoreProblems

/-!
# `Derived9`, scoped

The obligations of `Derived9.lean`, scoped (`CoreProblems.lean`), each by the scoped
`sol_prove` (`Calculus/Core/Derive.lean`): the early gate of `docs/intrinsic.md`'s W2
`symex` lane.  W3 `testsuite` flips the `Derived` modules themselves and deletes
these twins (the gate: `docs/intrinsic.md`).
-/

open Solidity

theorem Solkey.TestSuite.memoryDeclDefault.proved_core : Core.Valid Solkey.TestSuite.memoryDeclDefault.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryArrayIndex.proved_core : Core.Valid Solkey.TestSuite.memoryArrayIndex.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryNewIntoStructField.proved_core : Core.Valid Solkey.TestSuite.memoryNewIntoStructField.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryNewIntoNestedField.proved_core : Core.Valid Solkey.TestSuite.memoryNewIntoNestedField.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryNewIntoIndex.proved_core : Core.Valid Solkey.TestSuite.memoryNewIntoIndex.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryDeepField.proved_core : Core.Valid Solkey.TestSuite.memoryDeepField.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldAddAssign.proved_core : Core.Valid Solkey.TestSuite.memoryFieldAddAssign.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldSubAssign.proved_core : Core.Valid Solkey.TestSuite.memoryFieldSubAssign.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldMulAssign.proved_core : Core.Valid Solkey.TestSuite.memoryFieldMulAssign.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldDivAssign.proved_core : Core.Valid Solkey.TestSuite.memoryFieldDivAssign.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldModAssign.proved_core : Core.Valid Solkey.TestSuite.memoryFieldModAssign.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldAddAssignUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryFieldAddAssignUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldAddAssignNse.proved_core : Core.Valid Solkey.TestSuite.memoryFieldAddAssignNse.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPreincrement.proved_core : Core.Valid Solkey.TestSuite.memoryFieldPreincrement.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPostincrement.proved_core : Core.Valid Solkey.TestSuite.memoryFieldPostincrement.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPredecrement.proved_core : Core.Valid Solkey.TestSuite.memoryFieldPredecrement.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPostdecrement.proved_core : Core.Valid Solkey.TestSuite.memoryFieldPostdecrement.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPreincrementAssignment.proved_core : Core.Valid Solkey.TestSuite.memoryFieldPreincrementAssignment.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPostincrementAssignment.proved_core : Core.Valid Solkey.TestSuite.memoryFieldPostincrementAssignment.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPredecrementAssignment.proved_core : Core.Valid Solkey.TestSuite.memoryFieldPredecrementAssignment.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPostdecrementAssignment.proved_core : Core.Valid Solkey.TestSuite.memoryFieldPostdecrementAssignment.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPreincrementUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryFieldPreincrementUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldAlias.proved_core : Core.Valid Solkey.TestSuite.memoryFieldAlias.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldReferenceAssign.proved_core : Core.Valid Solkey.TestSuite.memoryFieldReferenceAssign.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayAddAssign.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayAddAssign.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArraySubAssign.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArraySubAssign.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayMulAssign.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayMulAssign.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayDivAssign.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayDivAssign.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayModAssign.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayModAssign.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayAddAssignUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayAddAssignUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPreincrementUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayPreincrementUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPreincrement.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayPreincrement.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPostdecrement.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayPostdecrement.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPostincrementAssignment.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayPostincrementAssignment.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPredecrementAssignment.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayPredecrementAssignment.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexWriteNse.proved_core : Core.Valid Solkey.TestSuite.memoryIndexWriteNse.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryRootAlias.proved_core : Core.Valid Solkey.TestSuite.memoryRootAlias.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryRootDeleteFresh.proved_core : Core.Valid Solkey.TestSuite.memoryRootDeleteFresh.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryStructArrayIndex.proved_core : Core.Valid Solkey.TestSuite.memoryStructArrayIndex.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryAliasing.proved_core : Core.Valid Solkey.TestSuite.testMemoryAliasing.problem.core := by
  sol_prove

/--
info: 'Solkey.TestSuite.memoryDeclDefault.proved_core' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Solkey.TestSuite.memoryDeclDefault.proved_core
