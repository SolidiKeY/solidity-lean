import Solidity.Yul.Views.RetainedAllocationOrder
import Solidity.Yul.Views.RetainedAllocationFurtherControls

namespace Solidity.Yul.Views.Controls

def alForwardSource : Source.EM heapByteEnv [.bytes .memory,.string .memory] (Source.Val heapByteEnv.layout (.string .memory)) := do
  Source.heapPut 0 ⟨.bytes .memory,.bytes []⟩
  Source.allocRef (Source.Data.string (l := .memory) alBytes)
def alReverseSource : Source.EM heapByteEnv [.bytes .memory,.string .memory] (Source.Val heapByteEnv.layout (.string .memory)) := do
  let v ← Source.allocRef (Source.Data.string (l := .memory) alBytes)
  Source.heapPut 0 ⟨.bytes .memory,.bytes []⟩
  pure v

theorem al_complete_source_order : alForwardSource.run byteState=alReverseSource.run byteState :=
  heapPut_allocRef_commute byteState 0 (Source.Data.bytes []) (by rfl) true alBytes

theorem al_forward_actual_result : alForwardSource.run byteState=(.ok (Source.Val.memRef (by rfl) 3),alState) := by
  rw [alForwardSource,Source.Hoare.run_bind,heapPutConcrete_run byteState 0 (Source.Data.bytes []) (by rfl)]
  exact al_actual_allocation

theorem al_reverse_actual_result : alReverseSource.run byteState=(.ok (Source.Val.memRef (by rfl) 3),alState) :=
  al_complete_source_order.symm.trans al_forward_actual_result

theorem al_complete_raw_order : alPhysical=mstore (byteAllocationView alBytes 512 576 (by decide) bytePhysical) 128 0 :=
  byteAllocation_mstore_commute alBytes 512 576 (by decide) bytePhysical 128 0 (by decide) (by decide)

/-- Missing initial targets are real owner errors, not a newly invented Yul
refusal. Allocating FIRST creates that target: the typed-old-target premise
of the general commutation law cannot be dropped. -/
def alMissingFirst : Source.EM heapByteEnv [.bytes .memory,.string .memory] (Source.Val heapByteEnv.layout (.string .memory)) := do
  Source.heapPut 3 ⟨.string .memory,.string []⟩
  Source.allocRef (Source.Data.string (l := .memory) alBytes)
def alMissingReverse : Source.EM heapByteEnv [.bytes .memory,.string .memory] (Source.Val heapByteEnv.layout (.string .memory)) := do
  let v ← Source.allocRef (Source.Data.string (l := .memory) alBytes)
  Source.heapPut 3 ⟨.string .memory,.string []⟩
  pure v

theorem al_missing_actual_error : alMissingFirst.run byteState=(.error (.stuck "memory write type"),byteState) := rfl
theorem al_missing_reverse_success : (alMissingReverse.run byteState).1=.ok (Source.Val.memRef (by rfl) 3) ∧
    (alMissingReverse.run byteState).2.2.heap.next=4 := ⟨rfl,rfl⟩

theorem al_overlapping_raw_order_bad :
    byteAllocationView alBytes 512 576 (by decide) (mstore bytePhysical 512 0) ≠
      mstore (byteAllocationView alBytes 512 576 (by decide) bytePhysical) 512 0 := by
  intro same
  have word := congrArg (fun m => (mload m 512).val) same
  dsimp only at word
  rw [byteAllocation_header,mload_mstore] at word
  contradiction

end Solidity.Yul.Views.Controls
