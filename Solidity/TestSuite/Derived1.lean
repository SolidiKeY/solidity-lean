import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived (1 of 3)

`⊢` of each obligation `sol_prove` and its leaf tactics close, from
`additionStorageWrite` to `storageIndexDivAssign` in the order of the source; the replays are what
`#solkey_derive?` (`Frontend/Problems.lean`) prints.  Every leaf sets
`wt(storage)` aside (`Proves.close_dropWt`).
-/

open Solidity Proves

theorem Solkey.TestSuite.additionStorageWrite.proved : ⊢ Solkey.TestSuite.additionStorageWrite.problem := by
  sol_prove
  case leaf1 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close
  case leaf2 =>
    refine Proves.close_dropWt ?_
    sol_symex
    sol_close

theorem Solkey.TestSuite.storageIndexAddAssign.proved : ⊢ Solkey.TestSuite.storageIndexAddAssign.problem := by
  sol_prove
  refine Proves.close_dropWt ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

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
  refine Proves.close_dropWt ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.requireTrueLiteral.proved : ⊢ Solkey.TestSuite.requireTrueLiteral.problem := by
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

theorem Solkey.TestSuite.requireFalseLiteral.proved : ⊢ Solkey.TestSuite.requireFalseLiteral.problem := by
  sol_prove

theorem Solkey.TestSuite.storageBoolArrayRead.proved : ⊢ Solkey.TestSuite.storageBoolArrayRead.problem := by
  sol_prove

theorem Solkey.TestSuite.additionSimple.proved : ⊢ Solkey.TestSuite.additionSimple.problem := by
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

theorem Solkey.TestSuite.divisionSimple.proved : ⊢ Solkey.TestSuite.divisionSimple.problem := by
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

theorem Solkey.TestSuite.greaterEqualSimple.proved : ⊢ Solkey.TestSuite.greaterEqualSimple.problem := by
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

theorem Solkey.TestSuite.greaterThanSimple.proved : ⊢ Solkey.TestSuite.greaterThanSimple.problem := by
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

theorem Solkey.TestSuite.lessEqualSimple.proved : ⊢ Solkey.TestSuite.lessEqualSimple.problem := by
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

theorem Solkey.TestSuite.lessThanSimple.proved : ⊢ Solkey.TestSuite.lessThanSimple.problem := by
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

theorem Solkey.TestSuite.logicalAndSimple.proved : ⊢ Solkey.TestSuite.logicalAndSimple.problem := by
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

theorem Solkey.TestSuite.logicalAndShortCircuitRhs.proved : ⊢ Solkey.TestSuite.logicalAndShortCircuitRhs.problem := by
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

theorem Solkey.TestSuite.logicalNotSimple.proved : ⊢ Solkey.TestSuite.logicalNotSimple.problem := by
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

theorem Solkey.TestSuite.logicalOrSimple.proved : ⊢ Solkey.TestSuite.logicalOrSimple.problem := by
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

theorem Solkey.TestSuite.logicalOrShortCircuitRhs.proved : ⊢ Solkey.TestSuite.logicalOrShortCircuitRhs.problem := by
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

theorem Solkey.TestSuite.ternaryCaptureCond.proved : ⊢ Solkey.TestSuite.ternaryCaptureCond.problem := by
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

theorem Solkey.TestSuite.ternaryToIf.proved : ⊢ Solkey.TestSuite.ternaryToIf.problem := by
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

theorem Solkey.TestSuite.ifUnfold.proved : ⊢ Solkey.TestSuite.ifUnfold.problem := by
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

theorem Solkey.TestSuite.ifElseUnfold.proved : ⊢ Solkey.TestSuite.ifElseUnfold.problem := by
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

theorem Solkey.TestSuite.ifSplit.proved : ⊢ Solkey.TestSuite.ifSplit.problem := by
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

theorem Solkey.TestSuite.ifElseSplit.proved : ⊢ Solkey.TestSuite.ifElseSplit.problem := by
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

theorem Solkey.TestSuite.ifTrue.proved : ⊢ Solkey.TestSuite.ifTrue.problem := by
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

theorem Solkey.TestSuite.ifFalse.proved : ⊢ Solkey.TestSuite.ifFalse.problem := by
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

theorem Solkey.TestSuite.ifElseTrue.proved : ⊢ Solkey.TestSuite.ifElseTrue.problem := by
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

theorem Solkey.TestSuite.ifElseFalse.proved : ⊢ Solkey.TestSuite.ifElseFalse.problem := by
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

theorem Solkey.TestSuite.ifElseNegated.proved : ⊢ Solkey.TestSuite.ifElseNegated.problem := by
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

theorem Solkey.TestSuite.moduloSimple.proved : ⊢ Solkey.TestSuite.moduloSimple.problem := by
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

theorem Solkey.TestSuite.multiplicationSimple.proved : ⊢ Solkey.TestSuite.multiplicationSimple.problem := by
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

theorem Solkey.TestSuite.notEqualSimple.proved : ⊢ Solkey.TestSuite.notEqualSimple.problem := by
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

theorem Solkey.TestSuite.powerSimple.proved : ⊢ Solkey.TestSuite.powerSimple.problem := by
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

theorem Solkey.TestSuite.requireGuardBox.proved : ⊢ Solkey.TestSuite.requireGuardBox.problem := by
  sol_prove
  refine Proves.close_dropWt ?_
  sol_symex
  sol_close

theorem Solkey.TestSuite.storageIndexDelete.proved : ⊢ Solkey.TestSuite.storageIndexDelete.problem := by
  sol_prove
  refine Proves.close_dropWt ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons

theorem Solkey.TestSuite.storageIndexDivAssign.proved : ⊢ Solkey.TestSuite.storageIndexDivAssign.problem := by
  sol_prove
  refine Proves.close_dropWt ?_
  sol_symex
  refine (Fml.valid_iff_reduce _ (by decide +kernel)).2 ?_
  sol_reduce
  sol_decide_cons
