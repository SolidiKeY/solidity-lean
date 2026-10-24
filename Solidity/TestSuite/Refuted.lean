import Solidity.TestSuite.ScopedProblems
import Solidity.Tools.Counterexample

/-! The obligations false in the model, each refuted by a certified
counterexample (`sol_refute`, `Tools/Counterexample.lean`):
`N.f.refuted : ¬ (⊢ N.f.problem)`, counted by `#solkey_obligations`.  The
`unprovable*` ones are false as solkey says; the seven that read an
appended reference slot as its default (solkey's `SYMBOLIC_TAIL_OPENS`)
are false from a storage whose array keeps a dirty slot past its end (a
shadow `wt(storage)` admits, `Storage.wtB`), which an empty push exposes
(`docs/solkey-migration.md`, "Push semantics"). -/

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
