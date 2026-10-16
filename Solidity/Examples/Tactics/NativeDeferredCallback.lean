import Solidity.Semantics.NativeDeferredCallback
import Solidity.Examples.Tactics.DeferredCorrespondence

/-! Native receiver callbacks preserve resumed storage, heap growth and failure order. -/

namespace Solidity.Examples.Tactics.NativeDeferredCallback

open Solidity.DeferredSource Solidity.DeferredSource.Callback
open Solidity.Examples.Tactics.DeferredCallback
open Solidity.Examples.Tactics.DeferredCorrespondence

/-- The native operand reads resumed storage and retains its allocation after scope exit. -/
theorem resumed_allocation :
    ∃ o, ExecS keep (State.init CallbackContract)
      (.callReceiverPush "valuesRef" .nil (.user "r") getterBody
        (allocatingPaymentAt []).code (allocatingPaymentAt []).value) o ∧
      observed o = some 9 ∧ heapLength o = some 1 := by
  obtain ⟨o, hd, _, hobs, hheap⟩ := resumed_allocation_captured
  exact ⟨o, (NativeDeferred.native_direct_iff _ _ _ _ _).mpr hd, hobs, hheap⟩

/-- An unset native getter stops before a broken invariant or a bad final source. -/
theorem unset_before_operand :
    ExecS broken (State.init CallbackContract)
      (.callReceiverPush "unset" .nil (.user "r") .nil trapped.code trapped.value)
      (.halt .revert) :=
  .callReceiverPushUnset (.callBody rfl .nil) rfl

/-- A callback violation stops the native prefix before its final `1 / 0` source. -/
theorem violation_before_source :
    ExecS broken (State.init CallbackContract)
      (.callReceiverPush "valuesRef" .nil (.user "r") getterBody trapped.code trapped.value)
      .violated := by
  exact .callReceiverPush (.callBody rfl (.cons (.det rfl) .nil)) rfl
    (.violated (.transferViolated (J := broken) rfl (fun h => h)))

/-- A native reference operand copies the allocated memory value after its getter. -/
theorem reference_copy :
    ∃ o, ExecS ReferenceCopy.keep (State.init DeferredSource.ExampleContract)
      (.callReceiverPush "matrixRef" .nil (.user "r") DeferredSource.matrixGetterBody
        DeferredSource.memoryCopy.code DeferredSource.memoryCopy.value) o ∧
      ReferenceCopy.observedCopy o = some (1, 1, 47, 1) := by
  obtain ⟨o, hd, hobs⟩ := ReferenceCopy.allocated_reference_is_direct
  exact ⟨o, (NativeDeferred.native_direct_iff _ _ _ _ _).mpr hd, hobs⟩

end Solidity.Examples.Tactics.NativeDeferredCallback
