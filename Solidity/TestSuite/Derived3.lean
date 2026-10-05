import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived (3 of 3)

`⊢` of each obligation `sol_prove` and its leaf tactics close, from
`localDeclPostdecrement` to `tryCallUnmatchedFailureReverts` in the order of the source; the replays are what
`#solkey_derive?` (`Frontend/Problems.lean`) prints.  Every leaf sets
`wt(storage)` aside (`Proves.close_dropWt`).
-/

open Solidity Proves

theorem Solkey.TestSuite.localDeclPostdecrement.proved : ⊢ Solkey.TestSuite.localDeclPostdecrement.problem := by
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

theorem Solkey.TestSuite.localDeclPredecrement.proved : ⊢ Solkey.TestSuite.localDeclPredecrement.problem := by
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

theorem Solkey.TestSuite.subAssignValueRhsCapture.proved : ⊢ Solkey.TestSuite.subAssignValueRhsCapture.problem := by
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

theorem Solkey.TestSuite.mulAssignValueRhsCapture.proved : ⊢ Solkey.TestSuite.mulAssignValueRhsCapture.problem := by
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

theorem Solkey.TestSuite.divAssignValueRhsCapture.proved : ⊢ Solkey.TestSuite.divAssignValueRhsCapture.problem := by
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

theorem Solkey.TestSuite.modAssignValueRhsCapture.proved : ⊢ Solkey.TestSuite.modAssignValueRhsCapture.problem := by
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

theorem Solkey.TestSuite.boolInequalityCaptureLhs.proved : ⊢ Solkey.TestSuite.boolInequalityCaptureLhs.problem := by
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

theorem Solkey.TestSuite.boolInequalityCaptureRhs.proved : ⊢ Solkey.TestSuite.boolInequalityCaptureRhs.problem := by
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

theorem Solkey.TestSuite.greaterThanCaptureRhs.proved : ⊢ Solkey.TestSuite.greaterThanCaptureRhs.problem := by
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

theorem Solkey.TestSuite.greaterEqualCaptureLhs.proved : ⊢ Solkey.TestSuite.greaterEqualCaptureLhs.problem := by
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

theorem Solkey.TestSuite.greaterEqualCaptureRhs.proved : ⊢ Solkey.TestSuite.greaterEqualCaptureRhs.problem := by
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

theorem Solkey.TestSuite.lessEqualCaptureLhs.proved : ⊢ Solkey.TestSuite.lessEqualCaptureLhs.problem := by
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

theorem Solkey.TestSuite.lessEqualCaptureRhs.proved : ⊢ Solkey.TestSuite.lessEqualCaptureRhs.problem := by
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

theorem Solkey.TestSuite.logicalNotCapture.proved : ⊢ Solkey.TestSuite.logicalNotCapture.problem := by
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

theorem Solkey.TestSuite.unaryMinusCapture.proved : ⊢ Solkey.TestSuite.unaryMinusCapture.problem := by
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

theorem Solkey.TestSuite.multiplicationUnfoldLeft.proved : ⊢ Solkey.TestSuite.multiplicationUnfoldLeft.problem := by
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

theorem Solkey.TestSuite.multiplicationUnfoldRight.proved : ⊢ Solkey.TestSuite.multiplicationUnfoldRight.problem := by
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

theorem Solkey.TestSuite.divisionUnfoldLeft.proved : ⊢ Solkey.TestSuite.divisionUnfoldLeft.problem := by
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

theorem Solkey.TestSuite.divisionUnfoldRight.proved : ⊢ Solkey.TestSuite.divisionUnfoldRight.problem := by
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

theorem Solkey.TestSuite.moduloUnfoldLeft.proved : ⊢ Solkey.TestSuite.moduloUnfoldLeft.problem := by
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

theorem Solkey.TestSuite.moduloUnfoldRight.proved : ⊢ Solkey.TestSuite.moduloUnfoldRight.problem := by
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

theorem Solkey.TestSuite.signedDivisionTruncates.proved : ⊢ Solkey.TestSuite.signedDivisionTruncates.problem := by
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

theorem Solkey.TestSuite.signedModuloTakesDividendSign.proved : ⊢ Solkey.TestSuite.signedModuloTakesDividendSign.problem := by
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

theorem Solkey.TestSuite.powerUnfoldLeft.proved : ⊢ Solkey.TestSuite.powerUnfoldLeft.problem := by
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

theorem Solkey.TestSuite.powerUnfoldRight.proved : ⊢ Solkey.TestSuite.powerUnfoldRight.problem := by
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

theorem Solkey.TestSuite.subtractionUnfoldRight.proved : ⊢ Solkey.TestSuite.subtractionUnfoldRight.problem := by
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

theorem Solkey.TestSuite.parenthesizedRightOperand.proved : ⊢ Solkey.TestSuite.parenthesizedRightOperand.problem := by
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

theorem Solkey.TestSuite.parenthesizedLeftOperand.proved : ⊢ Solkey.TestSuite.parenthesizedLeftOperand.problem := by
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

theorem Solkey.TestSuite.parenthesizedCondition.proved : ⊢ Solkey.TestSuite.parenthesizedCondition.problem := by
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

theorem Solkey.TestSuite.storageIndexReadArrayStoreRoot.proved : ⊢ Solkey.TestSuite.storageIndexReadArrayStoreRoot.problem := by
  sol_prove
  refine Proves.close_dropWt ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.storagePopUnfold.proved : ⊢ Solkey.TestSuite.storagePopUnfold.problem := by
  sol_prove
  refine Proves.close_dropWt ?_
  sol_symex
  sol_close

theorem Solkey.TestSuite.transferToOwner.proved : ⊢ Solkey.TestSuite.transferToOwner.problem := by
  sol_prove

theorem Solkey.TestSuite.transferUnfoldReceiver.proved : ⊢ Solkey.TestSuite.transferUnfoldReceiver.problem := by
  sol_prove

theorem Solkey.TestSuite.transferUnfoldArgument.proved : ⊢ Solkey.TestSuite.transferUnfoldArgument.problem := by
  sol_prove

theorem Solkey.TestSuite.tryCallCatchKeepsState.proved : ⊢ Solkey.TestSuite.tryCallCatchKeepsState.problem := by
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
  case leaf7 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons

theorem Solkey.TestSuite.tryCallBindsReturnAndPanicCode.proved : ⊢ Solkey.TestSuite.tryCallBindsReturnAndPanicCode.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
    sol_reduce
    sol_decide_cons
  case leaf3 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close

theorem Solkey.TestSuite.tryCallUnmatchedFailureReverts.proved : ⊢ Solkey.TestSuite.tryCallUnmatchedFailureReverts.problem := by
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
