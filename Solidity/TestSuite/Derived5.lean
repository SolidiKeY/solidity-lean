import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived (5 of 12)

`⊢` of each obligation `sol_prove` and its leaf tactics close, from
`boolKeyMapping` to `parenthesizedRightOperand` in the order of the source; the replays are what
`#solkey_derive?` (`Frontend/Problems.lean`) prints.  The closer reads
`wt(storage)` as the layout a well-formed storage holds; a leaf it leaves
sets the premise aside (`Proves.close_dropWt`).
-/

open Solidity Proves

theorem Solkey.TestSuite.boolKeyMapping.proved : ⊢ Solkey.TestSuite.boolKeyMapping.problem := by
  sol_prove

theorem Solkey.TestSuite.boolIsTrueOrFalse.proved : ⊢ Solkey.TestSuite.boolIsTrueOrFalse.problem := by
  sol_prove

theorem Solkey.TestSuite.boolKeyMappingSymbolicKey.proved : ⊢ Solkey.TestSuite.boolKeyMappingSymbolicKey.problem := by
  sol_prove

theorem Solkey.TestSuite.numberLiteralForms.proved : ⊢ Solkey.TestSuite.numberLiteralForms.problem := by
  sol_prove

theorem Solkey.TestSuite.localAddAssign.proved : ⊢ Solkey.TestSuite.localAddAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.localMulAssign.proved : ⊢ Solkey.TestSuite.localMulAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.localDivAssign.proved : ⊢ Solkey.TestSuite.localDivAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.localModAssign.proved : ⊢ Solkey.TestSuite.localModAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.localPostincrement.proved : ⊢ Solkey.TestSuite.localPostincrement.problem := by
  sol_prove

theorem Solkey.TestSuite.localPreincrementAssign.proved : ⊢ Solkey.TestSuite.localPreincrementAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.localPostdecrement.proved : ⊢ Solkey.TestSuite.localPostdecrement.problem := by
  sol_prove

theorem Solkey.TestSuite.localPredecrement.proved : ⊢ Solkey.TestSuite.localPredecrement.problem := by
  sol_prove

theorem Solkey.TestSuite.localDeclPostdecrement.proved : ⊢ Solkey.TestSuite.localDeclPostdecrement.problem := by
  sol_prove

theorem Solkey.TestSuite.localDeclPredecrement.proved : ⊢ Solkey.TestSuite.localDeclPredecrement.problem := by
  sol_prove

theorem Solkey.TestSuite.subAssignValueRhsCapture.proved : ⊢ Solkey.TestSuite.subAssignValueRhsCapture.problem := by
  sol_prove

theorem Solkey.TestSuite.mulAssignValueRhsCapture.proved : ⊢ Solkey.TestSuite.mulAssignValueRhsCapture.problem := by
  sol_prove

theorem Solkey.TestSuite.divAssignValueRhsCapture.proved : ⊢ Solkey.TestSuite.divAssignValueRhsCapture.problem := by
  sol_prove

theorem Solkey.TestSuite.modAssignValueRhsCapture.proved : ⊢ Solkey.TestSuite.modAssignValueRhsCapture.problem := by
  sol_prove

theorem Solkey.TestSuite.boolInequalityCaptureLhs.proved : ⊢ Solkey.TestSuite.boolInequalityCaptureLhs.problem := by
  sol_prove

theorem Solkey.TestSuite.boolInequalityCaptureRhs.proved : ⊢ Solkey.TestSuite.boolInequalityCaptureRhs.problem := by
  sol_prove

theorem Solkey.TestSuite.greaterThanCaptureRhs.proved : ⊢ Solkey.TestSuite.greaterThanCaptureRhs.problem := by
  sol_prove

theorem Solkey.TestSuite.greaterEqualCaptureLhs.proved : ⊢ Solkey.TestSuite.greaterEqualCaptureLhs.problem := by
  sol_prove

theorem Solkey.TestSuite.greaterEqualCaptureRhs.proved : ⊢ Solkey.TestSuite.greaterEqualCaptureRhs.problem := by
  sol_prove

theorem Solkey.TestSuite.lessEqualCaptureLhs.proved : ⊢ Solkey.TestSuite.lessEqualCaptureLhs.problem := by
  sol_prove

theorem Solkey.TestSuite.lessEqualCaptureRhs.proved : ⊢ Solkey.TestSuite.lessEqualCaptureRhs.problem := by
  sol_prove

theorem Solkey.TestSuite.logicalNotCapture.proved : ⊢ Solkey.TestSuite.logicalNotCapture.problem := by
  sol_prove

theorem Solkey.TestSuite.unaryMinusCapture.proved : ⊢ Solkey.TestSuite.unaryMinusCapture.problem := by
  sol_prove

theorem Solkey.TestSuite.multiplicationUnfoldLeft.proved : ⊢ Solkey.TestSuite.multiplicationUnfoldLeft.problem := by
  sol_prove

theorem Solkey.TestSuite.multiplicationUnfoldRight.proved : ⊢ Solkey.TestSuite.multiplicationUnfoldRight.problem := by
  sol_prove

theorem Solkey.TestSuite.divisionUnfoldLeft.proved : ⊢ Solkey.TestSuite.divisionUnfoldLeft.problem := by
  sol_prove

theorem Solkey.TestSuite.divisionUnfoldRight.proved : ⊢ Solkey.TestSuite.divisionUnfoldRight.problem := by
  sol_prove

theorem Solkey.TestSuite.moduloUnfoldLeft.proved : ⊢ Solkey.TestSuite.moduloUnfoldLeft.problem := by
  sol_prove

theorem Solkey.TestSuite.moduloUnfoldRight.proved : ⊢ Solkey.TestSuite.moduloUnfoldRight.problem := by
  sol_prove

theorem Solkey.TestSuite.signedDivisionTruncates.proved : ⊢ Solkey.TestSuite.signedDivisionTruncates.problem := by
  sol_prove

theorem Solkey.TestSuite.signedModuloTakesDividendSign.proved : ⊢ Solkey.TestSuite.signedModuloTakesDividendSign.problem := by
  sol_prove

theorem Solkey.TestSuite.storageSignedDivModAssign.proved : ⊢ Solkey.TestSuite.storageSignedDivModAssign.problem := by
  sol_prove

theorem Solkey.TestSuite.powerUnfoldLeft.proved : ⊢ Solkey.TestSuite.powerUnfoldLeft.problem := by
  sol_prove

theorem Solkey.TestSuite.powerUnfoldRight.proved : ⊢ Solkey.TestSuite.powerUnfoldRight.problem := by
  sol_prove

theorem Solkey.TestSuite.subtractionUnfoldRight.proved : ⊢ Solkey.TestSuite.subtractionUnfoldRight.problem := by
  sol_prove

theorem Solkey.TestSuite.parenthesizedRightOperand.proved : ⊢ Solkey.TestSuite.parenthesizedRightOperand.problem := by
  sol_prove
