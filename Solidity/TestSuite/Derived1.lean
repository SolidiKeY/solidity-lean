import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived (1 of 12)

`⊢` of each obligation `sol_prove` and its leaf tactics close, from
`additionStorageWrite` to `ifElseSplit` in the order of the source; the replays are what
`#solkey_derive?` (`Frontend/Problems.lean`) prints.  The closer reads
`wt(storage)` as the layout a well-formed storage holds; a leaf it leaves
sets the premise aside (`Proves.close_dropWt`).
-/

open Solidity Proves

theorem Solkey.TestSuite.additionStorageWrite.proved : ⊢ Solkey.TestSuite.additionStorageWrite.problem := by
  sol_prove

theorem Solkey.TestSuite.storageRootReadWrite.proved : ⊢ Solkey.TestSuite.storageRootReadWrite.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldWriteRead.proved : ⊢ Solkey.TestSuite.storageFieldWriteRead.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldDeepAddAssign.proved : ⊢ Solkey.TestSuite.storageFieldDeepAddAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageFieldGlobalAge.proved : ⊢ Solkey.TestSuite.storageFieldGlobalAge.problem := by
  sol_prove

theorem Solkey.TestSuite.storageAliasWrite.proved : ⊢ Solkey.TestSuite.storageAliasWrite.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexRootMapping.proved : ⊢ Solkey.TestSuite.storageIndexRootMapping.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexAddAssign.proved : ⊢ Solkey.TestSuite.storageIndexAddAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexMappingAddAssign.proved : ⊢ Solkey.TestSuite.storageIndexMappingAddAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexArrayAddAssignOutOfBoundsReverts.proved : ⊢ Solkey.TestSuite.storageIndexArrayAddAssignOutOfBoundsReverts.problem := by
  sol_prove
  refine Proves.close_dropWt ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.storageIndexArrayReadOutOfBoundsReverts.proved : ⊢ Solkey.TestSuite.storageIndexArrayReadOutOfBoundsReverts.problem := by
  sol_prove
  refine Proves.close_dropWt ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.storageIndexReadComplexReceiverBindLocalRoot.proved : ⊢ Solkey.TestSuite.storageIndexReadComplexReceiverBindLocalRoot.problem := by
  sol_prove

theorem Solkey.TestSuite.storageIndexWriteRootRhsComplexReceiver.proved : ⊢ Solkey.TestSuite.storageIndexWriteRootRhsComplexReceiver.problem := by
  sol_prove

theorem Solkey.TestSuite.requireTrueLiteral.proved : ⊢ Solkey.TestSuite.requireTrueLiteral.problem := by
  sol_prove

theorem Solkey.TestSuite.requireFalseLiteral.proved : ⊢ Solkey.TestSuite.requireFalseLiteral.problem := by
  sol_prove

theorem Solkey.TestSuite.storageBoolRootReadWrite.proved : ⊢ Solkey.TestSuite.storageBoolRootReadWrite.problem := by
  sol_prove

theorem Solkey.TestSuite.storageBoolRootCopy.proved : ⊢ Solkey.TestSuite.storageBoolRootCopy.problem := by
  sol_prove

theorem Solkey.TestSuite.storageBoolFieldRead.proved : ⊢ Solkey.TestSuite.storageBoolFieldRead.problem := by
  sol_prove

theorem Solkey.TestSuite.storageBoolMappingRead.proved : ⊢ Solkey.TestSuite.storageBoolMappingRead.problem := by
  sol_prove

theorem Solkey.TestSuite.storageBoolArrayRead.proved : ⊢ Solkey.TestSuite.storageBoolArrayRead.problem := by
  sol_prove

theorem Solkey.TestSuite.storageBoolFieldStoreRoot.proved : ⊢ Solkey.TestSuite.storageBoolFieldStoreRoot.problem := by
  sol_prove

theorem Solkey.TestSuite.additionBothStorage.proved : ⊢ Solkey.TestSuite.additionBothStorage.problem := by
  sol_prove

theorem Solkey.TestSuite.additionSimple.proved : ⊢ Solkey.TestSuite.additionSimple.problem := by
  sol_prove

theorem Solkey.TestSuite.additionStorageRead.proved : ⊢ Solkey.TestSuite.additionStorageRead.problem := by
  sol_prove

theorem Solkey.TestSuite.divisionSimple.proved : ⊢ Solkey.TestSuite.divisionSimple.problem := by
  sol_prove

theorem Solkey.TestSuite.greaterEqualSimple.proved : ⊢ Solkey.TestSuite.greaterEqualSimple.problem := by
  sol_prove

theorem Solkey.TestSuite.greaterThanSimple.proved : ⊢ Solkey.TestSuite.greaterThanSimple.problem := by
  sol_prove

theorem Solkey.TestSuite.lessEqualSimple.proved : ⊢ Solkey.TestSuite.lessEqualSimple.problem := by
  sol_prove

theorem Solkey.TestSuite.lessThanSimple.proved : ⊢ Solkey.TestSuite.lessThanSimple.problem := by
  sol_prove

theorem Solkey.TestSuite.logicalAndSimple.proved : ⊢ Solkey.TestSuite.logicalAndSimple.problem := by
  sol_prove

theorem Solkey.TestSuite.logicalAndShortCircuitRhs.proved : ⊢ Solkey.TestSuite.logicalAndShortCircuitRhs.problem := by
  sol_prove

theorem Solkey.TestSuite.logicalNotSimple.proved : ⊢ Solkey.TestSuite.logicalNotSimple.problem := by
  sol_prove

theorem Solkey.TestSuite.logicalOrSimple.proved : ⊢ Solkey.TestSuite.logicalOrSimple.problem := by
  sol_prove

theorem Solkey.TestSuite.logicalOrShortCircuitRhs.proved : ⊢ Solkey.TestSuite.logicalOrShortCircuitRhs.problem := by
  sol_prove

theorem Solkey.TestSuite.ternaryCaptureCond.proved : ⊢ Solkey.TestSuite.ternaryCaptureCond.problem := by
  sol_prove

theorem Solkey.TestSuite.ternaryToIf.proved : ⊢ Solkey.TestSuite.ternaryToIf.problem := by
  sol_prove

theorem Solkey.TestSuite.ifUnfold.proved : ⊢ Solkey.TestSuite.ifUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.ifElseUnfold.proved : ⊢ Solkey.TestSuite.ifElseUnfold.problem := by
  sol_prove

theorem Solkey.TestSuite.ifSplit.proved : ⊢ Solkey.TestSuite.ifSplit.problem := by
  sol_prove

theorem Solkey.TestSuite.ifElseSplit.proved : ⊢ Solkey.TestSuite.ifElseSplit.problem := by
  sol_prove
