import Solidity.TestSuite.Problems

/-!
# solkey's `TestSuite`, derived: `send`, internal calls, `return`, tuples

`⊢` of each obligation solkey `1b4341a303` added, in the order of the
source; the replays are what `#solkey_derive? … pending`
(`Frontend/Problems.lean`) prints.  A `send` (and the `call{value}` form
the import lowers to one) splits into solkey's goals "send succeeded" and
"send failed" (`sendNoCallbackBox`, `sendNoCallbackDiamond`); an internal
call is inlined (`internalCallExpand`, `functionBodyExpand` for a call with
targets), its `return`s lowered at elaboration (`lowerReturns`); a tuple
declaration or assignment writes its components in order.

`returnEarly` (three calls of `returnSign`, three paths each) and
`tupleReturnDiscardsComponents` (`returnStats`' four conditionals and its
`&&`) close with no leaf, but their kernel check counts past
`maxHeartbeats` (about 270k and 490k), so `#solkey_derive?` prints them as
pending (`Derive.replayFits`).  A bare `sol_prove` passes at the default
limit: the kernel's work raises the counter but the limit does not stop it,
and nothing follows it in the declaration (`docs/testsuite-proofs.md`).
-/

open Solidity Proves

theorem Solkey.TestSuite.sendToOwner.proved : ⊢ Solkey.TestSuite.sendToOwner.problem := by
  sol_prove

theorem Solkey.TestSuite.sendUnfoldReceiver.proved : ⊢ Solkey.TestSuite.sendUnfoldReceiver.problem := by
  sol_prove

theorem Solkey.TestSuite.sendUnfoldArgument.proved : ⊢ Solkey.TestSuite.sendUnfoldArgument.problem := by
  sol_prove

theorem Solkey.TestSuite.callToSender.proved : ⊢ Solkey.TestSuite.callToSender.problem := by
  sol_prove

theorem Solkey.TestSuite.internalCallDeclaration.proved : ⊢ Solkey.TestSuite.internalCallDeclaration.problem := by
  sol_prove

theorem Solkey.TestSuite.internalCallInExpression.proved : ⊢ Solkey.TestSuite.internalCallInExpression.problem := by
  sol_prove

theorem Solkey.TestSuite.internalCallToStorage.proved : ⊢ Solkey.TestSuite.internalCallToStorage.problem := by
  sol_prove

theorem Solkey.TestSuite.returnEarly.proved : ⊢ Solkey.TestSuite.returnEarly.problem := by
  sol_prove

theorem Solkey.TestSuite.tupleReturnPair.proved : ⊢ Solkey.TestSuite.tupleReturnPair.problem := by
  sol_prove

theorem Solkey.TestSuite.tupleReturnReadsReturnVariables.proved : ⊢ Solkey.TestSuite.tupleReturnReadsReturnVariables.problem := by
  sol_prove

theorem Solkey.TestSuite.tupleReturnDiscardsComponents.proved : ⊢ Solkey.TestSuite.tupleReturnDiscardsComponents.problem := by
  sol_prove

theorem Solkey.TestSuite.tupleReturnAssignsExisting.proved : ⊢ Solkey.TestSuite.tupleReturnAssignsExisting.problem := by
  sol_prove

theorem Solkey.TestSuite.tupleAssignmentRotates.proved : ⊢ Solkey.TestSuite.tupleAssignmentRotates.problem := by
  sol_prove

theorem Solkey.TestSuite.tupleDeclaration.proved : ⊢ Solkey.TestSuite.tupleDeclaration.problem := by
  sol_prove

theorem Solkey.TestSuite.returnLeavesNestedBlocks.proved : ⊢ Solkey.TestSuite.returnLeavesNestedBlocks.problem := by
  sol_prove

theorem Solkey.TestSuite.returnOrFallThroughNamed.proved : ⊢ Solkey.TestSuite.returnOrFallThroughNamed.problem := by
  sol_prove

theorem Solkey.TestSuite.returnFromNestedCall.proved : ⊢ Solkey.TestSuite.returnFromNestedCall.problem := by
  sol_prove

theorem Solkey.TestSuite.returnAfterRevertGuard.proved : ⊢ Solkey.TestSuite.returnAfterRevertGuard.problem := by
  sol_prove

theorem Solkey.TestSuite.returnFromTryBranches.proved : ⊢ Solkey.TestSuite.returnFromTryBranches.problem := by
  sol_prove

theorem Solkey.TestSuite.returnFromVoidFunction.proved : ⊢ Solkey.TestSuite.returnFromVoidFunction.problem := by
  sol_prove
