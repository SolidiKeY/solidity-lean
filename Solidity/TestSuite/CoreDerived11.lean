import Solidity.TestSuite.CoreProblems

/-!
# `Derived11`, scoped

The obligations of `Derived11.lean`, scoped (`CoreProblems.lean`), each by the scoped
`sol_prove` (`Calculus/Core/Derive.lean`): the early gate of `docs/intrinsic.md`'s W2
`symex` lane.  W3 `testsuite` flips the `Derived` modules themselves and deletes
these twins.
-/

open Solidity

theorem Solkey.TestSuite.memoryIndexArrayMulAssignUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayMulAssignUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayDivAssignUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayDivAssignUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayModAssignUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayModAssignUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPostincrementUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayPostincrementUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPredecrementUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayPredecrementUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPostdecrementUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayPostdecrementUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayDeleteUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayDeleteUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPostincrement.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayPostincrement.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPredecrement.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayPredecrement.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPreincrementAssignment.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayPreincrementAssignment.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArrayPostdecrementAssignment.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArrayPostdecrementAssignment.problem.core := by
  sol_prove
