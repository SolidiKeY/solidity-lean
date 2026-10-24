import Solidity.TestSuite.ScopedProblems
import Solidity.Tools.Counterexample

/-! The obligations false in the model, each refuted by a certified
counterexample (`sol_refute`, `Tools/Counterexample.lean`):
`N.f.refuted : ¬ (⊢ N.f.problem)`, counted by `#solkey_obligations`.  The
`unprovable*` ones are false as solkey says; the seven that read an
appended reference slot as its default (solkey's `SYMBOLIC_TAIL_OPENS`)
are false from a storage whose array keeps a dirty slot past its end (a
shadow `wt(storage)` admits, `Storage.wtB`), which an empty push exposes
(`docs/solkey-migration.md`, "Push semantics").  `invariantClosedFormSum`
is false only past every storage the search builds: its witness is an array
of `2^255` elements (`docs/automation.md`, M6). -/

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

/-- False from a storage whose `values` has `2^255` elements: the loop's
`s + 2` overflows at `i = 2^255 - 1`, a revert the diamond refuses.  The
witness is a long array (`SVec.rep`, `Tools/LazyStorage.lean`) and the loop
runs in closed form (`Prog.runA`, `Semantics/RunAccel.lean`). -/
theorem Solkey.TestSuite.invariantClosedFormSum.refuted : ¬ (⊢ Solkey.TestSuite.invariantClosedFormSum.problem) := by
  sol_refute
