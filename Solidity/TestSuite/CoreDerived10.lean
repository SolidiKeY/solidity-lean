import Solidity.TestSuite.CoreProblems

/-!
# `Derived10`, scoped

The obligations of `Derived10.lean`, scoped (`CoreProblems.lean`), each by the scoped
`sol_prove` (`Calculus/Core/Derive.lean`): the early gate of `docs/intrinsic.md`'s W2
`symex` lane.  W3 `testsuite` flips the `Derived` modules themselves and deletes
these twins.
-/

open Solidity

theorem Solkey.TestSuite.testMemoryDeleteAlias.proved_core : Core.Valid Solkey.TestSuite.testMemoryDeleteAlias.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryDeleteIdentityFieldFreshensSlot.proved_core : Core.Valid Solkey.TestSuite.testMemoryDeleteIdentityFieldFreshensSlot.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryDeletePrimitiveField.proved_core : Core.Valid Solkey.TestSuite.testMemoryDeletePrimitiveField.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryEvaluationOrder.proved_core : Core.Valid Solkey.TestSuite.testMemoryEvaluationOrder.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryFieldShallowCopy.proved_core : Core.Valid Solkey.TestSuite.testMemoryFieldShallowCopy.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryIndexWriteImpureIndexPrimitiveRhs.proved_core : Core.Valid Solkey.TestSuite.testMemoryIndexWriteImpureIndexPrimitiveRhs.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryIndexWriteImpureIndexRefRhs.proved_core : Core.Valid Solkey.TestSuite.testMemoryIndexWriteImpureIndexRefRhs.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryRootAlias.proved_core : Core.Valid Solkey.TestSuite.testMemoryRootAlias.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryRootDeleteRebindsOnlyLocal.proved_core : Core.Valid Solkey.TestSuite.testMemoryRootDeleteRebindsOnlyLocal.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryTokenArrayAuxiliaryCases.proved_core : Core.Valid Solkey.TestSuite.testMemoryTokenArrayAuxiliaryCases.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryUintArrayAuxiliaryCases.proved_core : Core.Valid Solkey.TestSuite.testMemoryUintArrayAuxiliaryCases.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryUintArrayPostdecrement.proved_core : Core.Valid Solkey.TestSuite.testMemoryUintArrayPostdecrement.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryUintArrayPostincrement.proved_core : Core.Valid Solkey.TestSuite.testMemoryUintArrayPostincrement.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryUintArrayPredecrement.proved_core : Core.Valid Solkey.TestSuite.testMemoryUintArrayPredecrement.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryFieldWriteImpureReceiver.proved_core : Core.Valid Solkey.TestSuite.testMemoryFieldWriteImpureReceiver.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryStructFixedMemberLength.proved_core : Core.Valid Solkey.TestSuite.testMemoryStructFixedMemberLength.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryFixedArrayLength.proved_core : Core.Valid Solkey.TestSuite.testMemoryFixedArrayLength.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryNestedFixedArrayLength.proved_core : Core.Valid Solkey.TestSuite.testMemoryNestedFixedArrayLength.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testNewArrayOfFixedElementLength.proved_core : Core.Valid Solkey.TestSuite.testNewArrayOfFixedElementLength.problem.core := by
  sol_prove

theorem Solkey.TestSuite.testMemoryDynamicArrayDefaultLength.proved_core : Core.Valid Solkey.TestSuite.testMemoryDynamicArrayDefaultLength.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryDelete.proved_core : Core.Valid Solkey.TestSuite.memoryDelete.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldWriteMemRefImpureReceiver.proved_core : Core.Valid Solkey.TestSuite.memoryFieldWriteMemRefImpureReceiver.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexWriteMemRefImpureReceiver.proved_core : Core.Valid Solkey.TestSuite.memoryIndexWriteMemRefImpureReceiver.problem.core := by
  sol_prove

theorem Solkey.TestSuite.indexWriteBothImpureMemoryValue.proved_core : Core.Valid Solkey.TestSuite.indexWriteBothImpureMemoryValue.problem.core := by
  sol_prove

theorem Solkey.TestSuite.indexWriteBothImpureMemRef.proved_core : Core.Valid Solkey.TestSuite.indexWriteBothImpureMemRef.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldAsMappingKey.proved_core : Core.Valid Solkey.TestSuite.memoryFieldAsMappingKey.problem.core := by
  sol_prove

theorem Solkey.TestSuite.indexWriteValueRhsCapture.proved_core : Core.Valid Solkey.TestSuite.indexWriteValueRhsCapture.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexWriteMemRefRhsCapture.proved_core : Core.Valid Solkey.TestSuite.memoryIndexWriteMemRefRhsCapture.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexDeleteNonSimpleIndexCapture.proved_core : Core.Valid Solkey.TestSuite.memoryIndexDeleteNonSimpleIndexCapture.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldSubAssignUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryFieldSubAssignUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldMulAssignUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryFieldMulAssignUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldDivAssignUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryFieldDivAssignUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldModAssignUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryFieldModAssignUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPostincrementUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryFieldPostincrementUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPredecrementUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryFieldPredecrementUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPostdecrementUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryFieldPostdecrementUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldDeleteUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryFieldDeleteUnfold.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldReadUnfoldResult.proved_core : Core.Valid Solkey.TestSuite.memoryFieldReadUnfoldResult.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexReadUnfoldResult.proved_core : Core.Valid Solkey.TestSuite.memoryIndexReadUnfoldResult.problem.core := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArraySubAssignUnfold.proved_core : Core.Valid Solkey.TestSuite.memoryIndexArraySubAssignUnfold.problem.core := by
  sol_prove
