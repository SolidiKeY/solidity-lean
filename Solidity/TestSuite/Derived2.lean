import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived (2 of 3)

`⊢` of each obligation `sol_prove` and its leaf tactics close, from
`storageIndexModAssign` to `localPredecrement` in the order of the source; the replays are what
`#solkey_derive?` (`Frontend/Problems.lean`) prints.  A diamond's leaves
set `wt(storage)` aside (`Proves.close_dropWt`).
-/

open Solidity Proves

theorem Solkey.TestSuite.storageIndexModAssign.proved : ⊢ Solkey.TestSuite.storageIndexModAssign.problem := by
  sol_prove
  refine Proves.close ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.storageIndexMulAssign.proved : ⊢ Solkey.TestSuite.storageIndexMulAssign.problem := by
  sol_prove
  refine Proves.close ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.storageIndexMultipleWrites.proved : ⊢ Solkey.TestSuite.storageIndexMultipleWrites.problem := by
  sol_prove
  refine Proves.close ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.storageIndexPostdecrement.proved : ⊢ Solkey.TestSuite.storageIndexPostdecrement.problem := by
  sol_prove
  refine Proves.close ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.storageIndexPostincrement.proved : ⊢ Solkey.TestSuite.storageIndexPostincrement.problem := by
  sol_prove
  refine Proves.close ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.storageIndexPredecrement.proved : ⊢ Solkey.TestSuite.storageIndexPredecrement.problem := by
  sol_prove
  refine Proves.close ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.storageIndexPreincrement.proved : ⊢ Solkey.TestSuite.storageIndexPreincrement.problem := by
  sol_prove
  refine Proves.close ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.storageIndexReadMappingStoreRoot.proved : ⊢ Solkey.TestSuite.storageIndexReadMappingStoreRoot.problem := by
  sol_prove
  refine Proves.close ?_
  sol_symex
  sol_close

theorem Solkey.TestSuite.storageIndexReadNseIndex.proved : ⊢ Solkey.TestSuite.storageIndexReadNseIndex.problem := by
  sol_prove
  refine Proves.close ?_
  sol_symex
  sol_close

theorem Solkey.TestSuite.storageIndexSubAssign.proved : ⊢ Solkey.TestSuite.storageIndexSubAssign.problem := by
  sol_prove
  refine Proves.close ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.storageMatrixWriteRead.proved : ⊢ Solkey.TestSuite.storageMatrixWriteRead.problem := by
  sol_prove
  refine Proves.close ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.subtractionSimple.proved : ⊢ Solkey.TestSuite.subtractionSimple.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons

theorem Solkey.TestSuite.unaryMinusSimple.proved : ⊢ Solkey.TestSuite.unaryMinusSimple.problem := by
  sol_prove
  refine Proves.close ?_
  sol_symex
  sol_close

theorem Solkey.TestSuite.testStorageArrayReadWrite.proved : ⊢ Solkey.TestSuite.testStorageArrayReadWrite.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close ?_
    sol_symex
    sol_close
  case leaf2 =>
    refine Proves.close ?_
    sol_symex
    sol_close

theorem Solkey.TestSuite.testFixedArrayLength.proved : ⊢ Solkey.TestSuite.testFixedArrayLength.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons

theorem Solkey.TestSuite.testFixedStructArrayLength.proved : ⊢ Solkey.TestSuite.testFixedStructArrayLength.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons

theorem Solkey.TestSuite.testStructFixedMemberLength.proved : ⊢ Solkey.TestSuite.testStructFixedMemberLength.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons

theorem Solkey.TestSuite.testFixedElementOfDynamicArrayLength.proved : ⊢ Solkey.TestSuite.testFixedElementOfDynamicArrayLength.problem := by
  sol_prove
  refine Proves.close ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.storageIndexDecomposition.proved : ⊢ Solkey.TestSuite.storageIndexDecomposition.problem := by
  sol_prove
  refine Proves.close ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.storageIndexRootArray.proved : ⊢ Solkey.TestSuite.storageIndexRootArray.problem := by
  sol_prove
  refine Proves.close ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.localArithmeticInRange.proved : ⊢ Solkey.TestSuite.localArithmeticInRange.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close ?_
    sol_symex
    sol_close
  case leaf2 =>
    refine Proves.close ?_
    sol_symex
    sol_close

theorem Solkey.TestSuite.signedUnaryMinusInRange.proved : ⊢ Solkey.TestSuite.signedUnaryMinusInRange.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close ?_
    sol_symex
    sol_close
  case leaf2 =>
    refine Proves.close ?_
    sol_symex
    sol_close

theorem Solkey.TestSuite.additionLeftImpureRightReadFirst.proved : ⊢ Solkey.TestSuite.additionLeftImpureRightReadFirst.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
  case leaf3 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close

theorem Solkey.TestSuite.additionRightImpure.proved : ⊢ Solkey.TestSuite.additionRightImpure.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
  case leaf3 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close

theorem Solkey.TestSuite.additionBothOperandsImpure.proved : ⊢ Solkey.TestSuite.additionBothOperandsImpure.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
  case leaf3 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close

theorem Solkey.TestSuite.subtractionLeftImpureRightReadFirst.proved : ⊢ Solkey.TestSuite.subtractionLeftImpureRightReadFirst.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
  case leaf3 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close

theorem Solkey.TestSuite.lessThanLeftImpureRightReadFirst.proved : ⊢ Solkey.TestSuite.lessThanLeftImpureRightReadFirst.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
  case leaf3 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close

theorem Solkey.TestSuite.boolIsTrueOrFalse.proved : ⊢ Solkey.TestSuite.boolIsTrueOrFalse.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close

theorem Solkey.TestSuite.numberLiteralForms.proved : ⊢ Solkey.TestSuite.numberLiteralForms.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
  case leaf3 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
  case leaf4 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
  case leaf5 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
  case leaf6 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons

theorem Solkey.TestSuite.localAddAssign.proved : ⊢ Solkey.TestSuite.localAddAssign.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons

theorem Solkey.TestSuite.localMulAssign.proved : ⊢ Solkey.TestSuite.localMulAssign.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons

theorem Solkey.TestSuite.localDivAssign.proved : ⊢ Solkey.TestSuite.localDivAssign.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons

theorem Solkey.TestSuite.localModAssign.proved : ⊢ Solkey.TestSuite.localModAssign.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons

theorem Solkey.TestSuite.localPostincrement.proved : ⊢ Solkey.TestSuite.localPostincrement.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons

theorem Solkey.TestSuite.localPreincrementAssign.proved : ⊢ Solkey.TestSuite.localPreincrementAssign.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
  case leaf3 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close

theorem Solkey.TestSuite.localPostdecrement.proved : ⊢ Solkey.TestSuite.localPostdecrement.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons

theorem Solkey.TestSuite.localPredecrement.proved : ⊢ Solkey.TestSuite.localPredecrement.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
