import Solidity.TestSuite.ScopedProblems
import Solidity.Tools.Counterexample


open Solidity
open scoped Scoped

theorem Solkey.TestSuite.unprovableStorageShortCircuitMutation.refuted : ¬ (⊢ Solkey.TestSuite.unprovableStorageShortCircuitMutation.problem) := by
  sol_refute

theorem Solkey.TestSuite.unprovableInvariantBreakPostcondition.refuted : ¬ (⊢ Solkey.TestSuite.unprovableInvariantBreakPostcondition.problem) := by
  sol_refute

theorem Solkey.TestSuite.unprovableInvariantForContinueUpdate.refuted : ¬ (⊢ Solkey.TestSuite.unprovableInvariantForContinueUpdate.problem) := by
  sol_refute

theorem Solkey.TestSuite.storagePushReturnPrimitiveBindComplexReceiver.refuted : ¬ (⊢ Solkey.TestSuite.storagePushReturnPrimitiveBindComplexReceiver.problem) := by
  sol_refute

theorem Solkey.TestSuite.storageArrayMethodReferencesComplexReceiver.refuted : ¬ (⊢ Solkey.TestSuite.storageArrayMethodReferencesComplexReceiver.problem) := by
  sol_refute

theorem Solkey.TestSuite.storageArrayMethodReferencesComposedCallReceiver.refuted : ¬ (⊢ Solkey.TestSuite.storageArrayMethodReferencesComposedCallReceiver.problem) := by
  sol_refute

theorem Solkey.TestSuite.testFixedShapeEmptyPushFixedElementReadsZero.refuted : ¬ (⊢ Solkey.TestSuite.testFixedShapeEmptyPushFixedElementReadsZero.problem) := by
  sol_refute

theorem Solkey.TestSuite.testEmptyPushFixedArrayReturnReadsZero.refuted : ¬ (⊢ Solkey.TestSuite.testEmptyPushFixedArrayReturnReadsZero.problem) := by
  sol_refute

theorem Solkey.TestSuite.testEmptyPushDynamicArrayReturnReadsZero.refuted : ¬ (⊢ Solkey.TestSuite.testEmptyPushDynamicArrayReturnReadsZero.problem) := by
  sol_refute

theorem Solkey.TestSuite.testEmptyPushStructReturnReadsZero.refuted : ¬ (⊢ Solkey.TestSuite.testEmptyPushStructReturnReadsZero.problem) := by
  sol_refute

theorem Solkey.TestSuite.invariantClosedFormSum.refuted : ¬ (⊢ Solkey.TestSuite.invariantClosedFormSum.problem) := by
  sol_refute
