import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived (2 of 8)

`⊢` of each obligation `sol_prove` and its leaf tactics close, from
`ifTrue` to `storageIndexDeleteMappingStruct` in the order of the source; the replays are what
`#solkey_derive?` (`Frontend/Problems.lean`) prints.  The closer reads
`wt(storage)` as the layout a well-formed storage holds; a leaf it leaves
sets the premise aside (`Proves.close_dropWt`).
-/

open Solidity Proves

theorem Solkey.TestSuite.ifTrue.proved : ⊢ Solkey.TestSuite.ifTrue.problem := by
  sol_prove

theorem Solkey.TestSuite.ifFalse.proved : ⊢ Solkey.TestSuite.ifFalse.problem := by
  sol_prove

theorem Solkey.TestSuite.ifElseTrue.proved : ⊢ Solkey.TestSuite.ifElseTrue.problem := by
  sol_prove

theorem Solkey.TestSuite.ifElseFalse.proved : ⊢ Solkey.TestSuite.ifElseFalse.problem := by
  sol_prove

theorem Solkey.TestSuite.ifElseNegated.proved : ⊢ Solkey.TestSuite.ifElseNegated.problem := by
  sol_prove

theorem Solkey.TestSuite.moduloSimple.proved : ⊢ Solkey.TestSuite.moduloSimple.problem := by
  sol_prove

theorem Solkey.TestSuite.multiplicationSimple.proved : ⊢ Solkey.TestSuite.multiplicationSimple.problem := by
  sol_prove

theorem Solkey.TestSuite.notEqualSimple.proved : ⊢ Solkey.TestSuite.notEqualSimple.problem := by
  sol_prove

theorem Solkey.TestSuite.powerSimple.proved : ⊢ Solkey.TestSuite.powerSimple.problem := by
  sol_prove

theorem Solkey.TestSuite.requireGuardBox.proved : ⊢ Solkey.TestSuite.requireGuardBox.problem := by
  sol_prove

theorem Solkey.TestSuite.requireHoldsDiamond.proved : ⊢ Solkey.TestSuite.requireHoldsDiamond.problem := by
  sol_prove

theorem Solkey.TestSuite.storageAliasRebindAlias.proved : ⊢ Solkey.TestSuite.storageAliasRebindAlias.problem := by
  sol_prove

theorem Solkey.TestSuite.storageDeepFieldPostincrement.proved : ⊢ Solkey.TestSuite.storageDeepFieldPostincrement.problem := by
  sol_prove

theorem Solkey.TestSuite.storageDeepFieldPreincrement.proved : ⊢ Solkey.TestSuite.storageDeepFieldPreincrement.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldAddAssign.proved : ⊢ Solkey.TestSuite.storageFieldAddAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldCopyValueField.proved : ⊢ Solkey.TestSuite.storageFieldCopyValueField.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldDeepDivAssign.proved : ⊢ Solkey.TestSuite.storageFieldDeepDivAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldDeepModAssign.proved : ⊢ Solkey.TestSuite.storageFieldDeepModAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldDeepMulAssign.proved : ⊢ Solkey.TestSuite.storageFieldDeepMulAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldDeepSubAssign.proved : ⊢ Solkey.TestSuite.storageFieldDeepSubAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldDeepWriteRead.proved : ⊢ Solkey.TestSuite.storageFieldDeepWriteRead.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldDelete.proved : ⊢ Solkey.TestSuite.storageFieldDelete.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldDivAssign.proved : ⊢ Solkey.TestSuite.storageFieldDivAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldModAssign.proved : ⊢ Solkey.TestSuite.storageFieldModAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldMulAssign.proved : ⊢ Solkey.TestSuite.storageFieldMulAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldPostdecrementAssign.proved : ⊢ Solkey.TestSuite.storageFieldPostdecrementAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldPostdecrement.proved : ⊢ Solkey.TestSuite.storageFieldPostdecrement.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldPostincrementAssign.proved : ⊢ Solkey.TestSuite.storageFieldPostincrementAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldPostincrement.proved : ⊢ Solkey.TestSuite.storageFieldPostincrement.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldPredecrementAssign.proved : ⊢ Solkey.TestSuite.storageFieldPredecrementAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldPredecrement.proved : ⊢ Solkey.TestSuite.storageFieldPredecrement.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldPreincrementAssign.proved : ⊢ Solkey.TestSuite.storageFieldPreincrementAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldPreincrement.proved : ⊢ Solkey.TestSuite.storageFieldPreincrement.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldReadBindLocal.proved : ⊢ Solkey.TestSuite.storageFieldReadBindLocal.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldReadStoreRoot.proved : ⊢ Solkey.TestSuite.storageFieldReadStoreRoot.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldSubAssign.proved : ⊢ Solkey.TestSuite.storageFieldSubAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldWriteRhsCapture.proved : ⊢ Solkey.TestSuite.storageFieldWriteRhsCapture.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexCopyValue.proved : ⊢ Solkey.TestSuite.storageIndexCopyValue.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexDeleteMappingBool.proved : ⊢ Solkey.TestSuite.storageIndexDeleteMappingBool.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexDeleteMappingStruct.proved : ⊢ Solkey.TestSuite.storageIndexDeleteMappingStruct.problem := by
  sol_prove
