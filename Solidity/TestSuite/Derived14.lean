import Solidity.TestSuite.ScopedProblems


open Solidity
open scoped Scoped

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
