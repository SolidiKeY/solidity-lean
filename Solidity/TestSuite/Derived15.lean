import Solidity.TestSuite.ScopedProblems

/-! New obligations from the pinned SolKey migration source, derived in source order. -/

open Solidity
open scoped Scoped

theorem Solkey.TestSuite.newArrayCaptureStorageRoot.proved : ⊢ Solkey.TestSuite.newArrayCaptureStorageRoot.problem := by
  sol_prove

theorem Solkey.TestSuite.storagePushMemoryCopySource.proved : ⊢ Solkey.TestSuite.storagePushMemoryCopySource.problem := by
  sol_prove

theorem Solkey.TestSuite.storagePushMemoryStructCopySource.proved : ⊢ Solkey.TestSuite.storagePushMemoryStructCopySource.problem := by
  sol_prove

theorem Solkey.TestSuite.storagePushReturnPrimitiveBind.proved : ⊢ Solkey.TestSuite.storagePushReturnPrimitiveBind.problem := by
  sol_prove

theorem Solkey.TestSuite.returnDefaultsAreZero.proved : ⊢ Solkey.TestSuite.returnDefaultsAreZero.problem := by
  sol_prove

theorem Solkey.TestSuite.returnDefaultAddressIsZero.proved : ⊢ Solkey.TestSuite.returnDefaultAddressIsZero.problem := by
  sol_prove

theorem Solkey.TestSuite.returnDefaultEnumIsFirstMember.proved : ⊢ Solkey.TestSuite.returnDefaultEnumIsFirstMember.problem := by
  sol_prove

theorem Solkey.TestSuite.returnDefaultMemoryArrayIsEmpty.proved : ⊢ Solkey.TestSuite.returnDefaultMemoryArrayIsEmpty.problem := by
  sol_prove

theorem Solkey.TestSuite.returnInThenBranchElseIsDefault.proved : ⊢ Solkey.TestSuite.returnInThenBranchElseIsDefault.problem := by
  sol_prove

theorem Solkey.TestSuite.returnInElseBranchThenIsDefault.proved : ⊢ Solkey.TestSuite.returnInElseBranchThenIsDefault.problem := by
  sol_prove

theorem Solkey.TestSuite.returnDefaultIsFreshPerCall.proved : ⊢ Solkey.TestSuite.returnDefaultIsFreshPerCall.problem := by
  sol_prove

theorem Solkey.TestSuite.returnEnumOtherBranchIsDefault.proved : ⊢ Solkey.TestSuite.returnEnumOtherBranchIsDefault.problem := by
  sol_prove

theorem Solkey.TestSuite.returnUnassignedComponentIsDefault.proved : ⊢ Solkey.TestSuite.returnUnassignedComponentIsDefault.problem := by
  sol_prove

theorem Solkey.TestSuite.returnDefaultIsVisibleInBody.proved : ⊢ Solkey.TestSuite.returnDefaultIsVisibleInBody.problem := by
  sol_prove

theorem Solkey.TestSuite.overloadedInternalCall.proved : ⊢ Solkey.TestSuite.overloadedInternalCall.problem := by
  sol_prove

theorem Solkey.TestSuite.modifierArgument.proved : ⊢ Solkey.TestSuite.modifierArgument.problem := by
  sol_prove

theorem Solkey.TestSuite.modifierResumesAfterReturn.proved : ⊢ Solkey.TestSuite.modifierResumesAfterReturn.problem := by
  sol_prove

theorem Solkey.TestSuite.modifierFirstListedOutermost.proved : ⊢ Solkey.TestSuite.modifierFirstListedOutermost.problem := by
  sol_prove

theorem Solkey.TestSuite.modifierOnObligation.proved : ⊢ Solkey.TestSuite.modifierOnObligation.problem := by
  sol_prove

theorem Solkey.TestSuite.invariantCountsToBound.proved : ⊢ Solkey.TestSuite.invariantCountsToBound.problem := by
  sol_prove
  case leaf1 =>
    sol_leaf
    sol_close
  case leaf2 =>
    sol_leaf
    sol_close

-- This replay sat at 199,882 of its 200,000 heartbeats before `Fml.allocAll`
-- (docs/semantic-gaps.md, "Revert data"): one more formula constructor costs
-- every case split over a formula, ~0.06% here.  `sol_close` could not be made
-- cheaper without changing how its leaves close (measured: the cost is simp
-- walking the dependent state terms, not lemma attempts), so this one replay
-- gets the smallest override with a little room (AGENTS.md, "Lean notes").
set_option maxHeartbeats 205000 in
theorem Solkey.TestSuite.invariantVariantSkipsBreakIteration.proved : ⊢ Solkey.TestSuite.invariantVariantSkipsBreakIteration.problem := by
  sol_prove
  case leaf1 =>
    sol_leaf
    sol_close
  case leaf2 =>
    sol_leaf
    sol_close
  case leaf3 =>
    sol_leaf
    sol_close
  case leaf4 =>
    sol_leaf
    sol_close
  case leaf5 =>
    sol_leaf
    sol_close
  case leaf6 =>
    sol_leaf
    sol_close

theorem Solkey.TestSuite.invariantOverStorageWrites.proved : ⊢ Solkey.TestSuite.invariantOverStorageWrites.problem := by
  sol_prove
  case leaf1 =>
    sol_leaf
    sol_close
  case leaf2 =>
    sol_leaf
    sol_close

theorem Solkey.TestSuite.constantInlined.proved : ⊢ Solkey.TestSuite.constantInlined.problem := by
  sol_prove

theorem Solkey.TestSuite.contractQualifiedConstantAndEnum.proved : ⊢ Solkey.TestSuite.contractQualifiedConstantAndEnum.problem := by
  sol_prove

theorem Solkey.TestSuite.fileLevelConstantEnumAndFunction.proved : ⊢ Solkey.TestSuite.fileLevelConstantEnumAndFunction.problem := by
  sol_prove

theorem Solkey.TestSuite.libraryCallAndUsingFor.proved : ⊢ Solkey.TestSuite.libraryCallAndUsingFor.problem := by
  sol_prove

theorem Solkey.TestSuite.valueTypeWrapUnwrap.proved : ⊢ Solkey.TestSuite.valueTypeWrapUnwrap.problem := by
  sol_prove

theorem Solkey.TestSuite.typeBounds.proved : ⊢ Solkey.TestSuite.typeBounds.problem := by
  sol_prove

theorem Solkey.TestSuite.modifierCallsInternalFunction.proved : ⊢ Solkey.TestSuite.modifierCallsInternalFunction.problem := by
  sol_prove

theorem Solkey.TestSuite.pinWithInequality.proved : ⊢ Solkey.TestSuite.pinWithInequality.problem := by
  sol_prove

theorem Solkey.TestSuite.payableAddressParameter.proved : ⊢ Solkey.TestSuite.payableAddressParameter.problem := by
  sol_prove

theorem Solkey.TestSuite.namedArgumentsBindByName.proved : ⊢ Solkey.TestSuite.namedArgumentsBindByName.problem := by
  sol_prove

theorem Solkey.TestSuite.modifierLocalsArePerApplication.proved : ⊢ Solkey.TestSuite.modifierLocalsArePerApplication.problem := by
  sol_prove

theorem Solkey.TestSuite.uninitialisedLocalsAreDefault.proved : ⊢ Solkey.TestSuite.uninitialisedLocalsAreDefault.problem := by
  sol_prove

theorem Solkey.TestSuite.testFixedArrayOfFixedArraysLength.proved : ⊢ Solkey.TestSuite.testFixedArrayOfFixedArraysLength.problem := by
  sol_prove

theorem Solkey.TestSuite.testEmptyPushReadsDefaultValue.proved : ⊢ Solkey.TestSuite.testEmptyPushReadsDefaultValue.problem := by
  sol_prove

theorem Solkey.TestSuite.testPopPushValueResetsValue.proved : ⊢ Solkey.TestSuite.testPopPushValueResetsValue.problem := by
  sol_prove

theorem Solkey.TestSuite.testPushMappingOfFixedArrayPreservesEntries.proved : ⊢ Solkey.TestSuite.testPushMappingOfFixedArrayPreservesEntries.problem := by
  sol_prove

theorem Solkey.TestSuite.testShapeCopyDynamicShrinkClearsReusedSlot.proved : ⊢ Solkey.TestSuite.testShapeCopyDynamicShrinkClearsReusedSlot.problem := by
  sol_prove

theorem Solkey.TestSuite.testShapeCopyNestedSelfAliasPreservesValues.proved : ⊢ Solkey.TestSuite.testShapeCopyNestedSelfAliasPreservesValues.problem := by
  sol_prove

theorem Solkey.TestSuite.testFixedArrayOfMappingsOfFixedArraysLength.proved : ⊢ Solkey.TestSuite.testFixedArrayOfMappingsOfFixedArraysLength.problem := by
  sol_prove

theorem Solkey.TestSuite.testDynamicArrayOfMappingsOfFixedArraysLength.proved : ⊢ Solkey.TestSuite.testDynamicArrayOfMappingsOfFixedArraysLength.problem := by
  sol_prove

theorem Solkey.TestSuite.testPushIndexedPrimitiveSourceOnce.proved : ⊢ Solkey.TestSuite.testPushIndexedPrimitiveSourceOnce.problem := by
  sol_prove

theorem Solkey.TestSuite.testPushIndexedFixedArraySourceOnce.proved : ⊢ Solkey.TestSuite.testPushIndexedFixedArraySourceOnce.problem := by
  sol_prove

theorem Solkey.TestSuite.testFixedShapePopPushResetsFixedElement.proved : ⊢ Solkey.TestSuite.testFixedShapePopPushResetsFixedElement.problem := by
  sol_prove

theorem Solkey.TestSuite.testFixedShapeDeleteFixedElementKeepsLength.proved : ⊢ Solkey.TestSuite.testFixedShapeDeleteFixedElementKeepsLength.problem := by
  sol_prove

theorem Solkey.TestSuite.testFixedShapeDeleteDynamicThenPushFixedElement.proved : ⊢ Solkey.TestSuite.testFixedShapeDeleteDynamicThenPushFixedElement.problem := by
  sol_prove

theorem Solkey.TestSuite.testFixedShapeFixedElementStorageAlias.proved : ⊢ Solkey.TestSuite.testFixedShapeFixedElementStorageAlias.problem := by
  sol_prove

