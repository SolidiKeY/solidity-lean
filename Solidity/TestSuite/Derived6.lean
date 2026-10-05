import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived (6 of 6)

`⊢` of each obligation `sol_prove` and its leaf tactics close, from
`parenthesizedLeftOperand` to `tryCallUnmatchedFailureReverts` in the order of the source; the replays are what
`#solkey_derive?` (`Frontend/Problems.lean`) prints.  The closer reads
`wt(storage)` as the layout a well-formed storage holds; a leaf it leaves
sets the premise aside (`Proves.close_dropWt`).
-/

open Solidity Proves

theorem Solkey.TestSuite.parenthesizedLeftOperand.proved : ⊢ Solkey.TestSuite.parenthesizedLeftOperand.problem := by
  sol_prove

theorem Solkey.TestSuite.parenthesizedCondition.proved : ⊢ Solkey.TestSuite.parenthesizedCondition.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldDeleteUnfold.proved : ⊢ Solkey.TestSuite.storageFieldDeleteUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldPredecrementUnfold.proved : ⊢ Solkey.TestSuite.storageFieldPredecrementUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldPostdecrementUnfold.proved : ⊢ Solkey.TestSuite.storageFieldPostdecrementUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexAddAssignUnfold.proved : ⊢ Solkey.TestSuite.storageIndexAddAssignUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexSubAssignUnfold.proved : ⊢ Solkey.TestSuite.storageIndexSubAssignUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexMulAssignUnfold.proved : ⊢ Solkey.TestSuite.storageIndexMulAssignUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexDivAssignUnfold.proved : ⊢ Solkey.TestSuite.storageIndexDivAssignUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexModAssignUnfold.proved : ⊢ Solkey.TestSuite.storageIndexModAssignUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexPreincrementUnfold.proved : ⊢ Solkey.TestSuite.storageIndexPreincrementUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexPostincrementUnfold.proved : ⊢ Solkey.TestSuite.storageIndexPostincrementUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexPredecrementUnfold.proved : ⊢ Solkey.TestSuite.storageIndexPredecrementUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexPostdecrementUnfold.proved : ⊢ Solkey.TestSuite.storageIndexPostdecrementUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexMappingSubAssign.proved : ⊢ Solkey.TestSuite.storageIndexMappingSubAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexMappingMulAssign.proved : ⊢ Solkey.TestSuite.storageIndexMappingMulAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexMappingDivAssign.proved : ⊢ Solkey.TestSuite.storageIndexMappingDivAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexMappingModAssign.proved : ⊢ Solkey.TestSuite.storageIndexMappingModAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexMappingPreincrement.proved : ⊢ Solkey.TestSuite.storageIndexMappingPreincrement.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexMappingPostincrement.proved : ⊢ Solkey.TestSuite.storageIndexMappingPostincrement.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexMappingPredecrement.proved : ⊢ Solkey.TestSuite.storageIndexMappingPredecrement.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexMappingPostdecrement.proved : ⊢ Solkey.TestSuite.storageIndexMappingPostdecrement.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexMappingPreincrementAssignment.proved : ⊢ Solkey.TestSuite.storageIndexMappingPreincrementAssignment.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexMappingPostincrementAssignment.proved : ⊢ Solkey.TestSuite.storageIndexMappingPostincrementAssignment.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexMappingPredecrementAssignment.proved : ⊢ Solkey.TestSuite.storageIndexMappingPredecrementAssignment.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexMappingPostdecrementAssignment.proved : ⊢ Solkey.TestSuite.storageIndexMappingPostdecrementAssignment.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexReadArrayStoreRoot.proved : ⊢ Solkey.TestSuite.storageIndexReadArrayStoreRoot.problem := by
  sol_prove

theorem Solkey.TestSuite.storagePopUnfold.proved : ⊢ Solkey.TestSuite.storagePopUnfold.problem := by
  sol_prove
  refine Proves.close_dropWt ?_
  sol_symex
  sol_close

theorem Solkey.TestSuite.storageRootPostdecrement.proved : ⊢ Solkey.TestSuite.storageRootPostdecrement.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootPredecrementAssign.proved : ⊢ Solkey.TestSuite.storageRootPredecrementAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.ternaryToIfStorage.proved : ⊢ Solkey.TestSuite.ternaryToIfStorage.problem := by
  sol_prove

theorem Solkey.TestSuite.transferToOwner.proved : ⊢ Solkey.TestSuite.transferToOwner.problem := by
  sol_prove

theorem Solkey.TestSuite.transferUnfoldReceiver.proved : ⊢ Solkey.TestSuite.transferUnfoldReceiver.problem := by
  sol_prove

theorem Solkey.TestSuite.transferUnfoldArgument.proved : ⊢ Solkey.TestSuite.transferUnfoldArgument.problem := by
  sol_prove

theorem Solkey.TestSuite.tryCallCatchKeepsState.proved : ⊢ Solkey.TestSuite.tryCallCatchKeepsState.problem := by
  sol_prove

theorem Solkey.TestSuite.tryCallBindsReturnAndPanicCode.proved : ⊢ Solkey.TestSuite.tryCallBindsReturnAndPanicCode.problem := by
  sol_prove

theorem Solkey.TestSuite.tryCallUnmatchedFailureReverts.proved : ⊢ Solkey.TestSuite.tryCallUnmatchedFailureReverts.problem := by
  sol_prove
