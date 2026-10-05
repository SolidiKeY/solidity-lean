import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived (10 of 11)

`⊢` of each obligation the closer of memory added (objects allocated by
the updates, read and written through members and indices, aliased
and copied within memory), from `testMemoryDeleteAlias` to `memoryIndexArraySubAssignUnfold` in the
order of the source; the replays are what `#solkey_derive? … pending`
(`Frontend/Problems.lean`) prints.
-/

open Solidity Proves

theorem Solkey.TestSuite.testMemoryDeleteAlias.proved : ⊢ Solkey.TestSuite.testMemoryDeleteAlias.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryDeleteIdentityFieldFreshensSlot.proved : ⊢ Solkey.TestSuite.testMemoryDeleteIdentityFieldFreshensSlot.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryDeletePrimitiveField.proved : ⊢ Solkey.TestSuite.testMemoryDeletePrimitiveField.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryEvaluationOrder.proved : ⊢ Solkey.TestSuite.testMemoryEvaluationOrder.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryFieldShallowCopy.proved : ⊢ Solkey.TestSuite.testMemoryFieldShallowCopy.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryIndexWriteImpureIndexPrimitiveRhs.proved : ⊢ Solkey.TestSuite.testMemoryIndexWriteImpureIndexPrimitiveRhs.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryIndexWriteImpureIndexRefRhs.proved : ⊢ Solkey.TestSuite.testMemoryIndexWriteImpureIndexRefRhs.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryRootAlias.proved : ⊢ Solkey.TestSuite.testMemoryRootAlias.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryRootDeleteRebindsOnlyLocal.proved : ⊢ Solkey.TestSuite.testMemoryRootDeleteRebindsOnlyLocal.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryTokenArrayAuxiliaryCases.proved : ⊢ Solkey.TestSuite.testMemoryTokenArrayAuxiliaryCases.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryUintArrayAuxiliaryCases.proved : ⊢ Solkey.TestSuite.testMemoryUintArrayAuxiliaryCases.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryUintArrayPostdecrement.proved : ⊢ Solkey.TestSuite.testMemoryUintArrayPostdecrement.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryUintArrayPostincrement.proved : ⊢ Solkey.TestSuite.testMemoryUintArrayPostincrement.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryUintArrayPredecrement.proved : ⊢ Solkey.TestSuite.testMemoryUintArrayPredecrement.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryFieldWriteImpureReceiver.proved : ⊢ Solkey.TestSuite.testMemoryFieldWriteImpureReceiver.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryStructFixedMemberLength.proved : ⊢ Solkey.TestSuite.testMemoryStructFixedMemberLength.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryFixedArrayLength.proved : ⊢ Solkey.TestSuite.testMemoryFixedArrayLength.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryNestedFixedArrayLength.proved : ⊢ Solkey.TestSuite.testMemoryNestedFixedArrayLength.problem := by
  sol_prove

theorem Solkey.TestSuite.testNewArrayOfFixedElementLength.proved : ⊢ Solkey.TestSuite.testNewArrayOfFixedElementLength.problem := by
  sol_prove

theorem Solkey.TestSuite.testMemoryDynamicArrayDefaultLength.proved : ⊢ Solkey.TestSuite.testMemoryDynamicArrayDefaultLength.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryDelete.proved : ⊢ Solkey.TestSuite.memoryDelete.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldWriteMemRefImpureReceiver.proved : ⊢ Solkey.TestSuite.memoryFieldWriteMemRefImpureReceiver.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexWriteMemRefImpureReceiver.proved : ⊢ Solkey.TestSuite.memoryIndexWriteMemRefImpureReceiver.problem := by
  sol_prove

theorem Solkey.TestSuite.indexWriteBothImpureMemoryValue.proved : ⊢ Solkey.TestSuite.indexWriteBothImpureMemoryValue.problem := by
  sol_prove

theorem Solkey.TestSuite.indexWriteBothImpureMemRef.proved : ⊢ Solkey.TestSuite.indexWriteBothImpureMemRef.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldAsMappingKey.proved : ⊢ Solkey.TestSuite.memoryFieldAsMappingKey.problem := by
  sol_prove

theorem Solkey.TestSuite.indexWriteValueRhsCapture.proved : ⊢ Solkey.TestSuite.indexWriteValueRhsCapture.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexWriteMemRefRhsCapture.proved : ⊢ Solkey.TestSuite.memoryIndexWriteMemRefRhsCapture.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexDeleteNonSimpleIndexCapture.proved : ⊢ Solkey.TestSuite.memoryIndexDeleteNonSimpleIndexCapture.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldSubAssignUnfold.proved : ⊢ Solkey.TestSuite.memoryFieldSubAssignUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldMulAssignUnfold.proved : ⊢ Solkey.TestSuite.memoryFieldMulAssignUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldDivAssignUnfold.proved : ⊢ Solkey.TestSuite.memoryFieldDivAssignUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldModAssignUnfold.proved : ⊢ Solkey.TestSuite.memoryFieldModAssignUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPostincrementUnfold.proved : ⊢ Solkey.TestSuite.memoryFieldPostincrementUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPredecrementUnfold.proved : ⊢ Solkey.TestSuite.memoryFieldPredecrementUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldPostdecrementUnfold.proved : ⊢ Solkey.TestSuite.memoryFieldPostdecrementUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldDeleteUnfold.proved : ⊢ Solkey.TestSuite.memoryFieldDeleteUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryFieldReadUnfoldResult.proved : ⊢ Solkey.TestSuite.memoryFieldReadUnfoldResult.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexReadUnfoldResult.proved : ⊢ Solkey.TestSuite.memoryIndexReadUnfoldResult.problem := by
  sol_prove

theorem Solkey.TestSuite.memoryIndexArraySubAssignUnfold.proved : ⊢ Solkey.TestSuite.memoryIndexArraySubAssignUnfold.problem := by
  sol_prove
