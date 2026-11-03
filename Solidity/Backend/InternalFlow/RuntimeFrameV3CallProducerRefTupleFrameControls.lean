import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefTupleFrame
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefArrayControls

/-! Inhabited tuple-copy ownership control. The reached heap already contains
a nonempty array; overlapping copies export its pointer and a primitive word
without changing the old caller, its object, cursor or zero tail. This is a
copy-stage control, not an independent Source tuple-call lowering claim. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.Tuple.FrameControls
open Evm Evm.Memory

def input : Machine := writeMachine (writeMachine (ArrayControls.machine (wmod 0)) 4 w[128]) 5 w[7]
def output : Machine := writeMachine (writeMachine input 3 w[128]) 4 w[7]

theorem executed : Evm.run (copyCode 4 3 2) input = .ok output 0 := by rfl

theorem input_represented : StateRepr 1 1 64 ArrayControls.F (ArrayControls.caller (wmod 0)) ArrayControls.bases input := by
  exact reserved_write (reserved_write (ArrayControls.initial (wmod 0)).1 4 (by decide) (by decide) w[128])
    5 (by decide) (by decide) w[7]

theorem input_owned :
    StructAllocatorRepr (ArrayControls.caller (wmod 0)).heap ArrayControls.bases 64 (wmod 130) input := by
  exact ((ArrayControls.initial (wmod 0)).2.localWrite 4 (by decide) (by decide) w[128]).localWrite
    5 (by decide) (by decide) w[7]

theorem retained : StateRepr 1 1 64 ArrayControls.F (ArrayControls.caller (wmod 0)) ArrayControls.bases output := by
  exact copy_retained 2 4 3 (by decide) (by decide) (by decide) input_represented executed

theorem owned :
    StructAllocatorRepr (ArrayControls.caller (wmod 0)).heap ArrayControls.bases 64 (wmod 130) output := by
  exact copy_allocator 2 4 3 input output input_owned (by decide) (by decide) executed

theorem observed :
    output.stack = [w[77]] ∧ output.mem 3 = w[128] ∧ output.mem 4 = w[7] ∧
    output.mem 1 = w[128] ∧ output.mem 128 = w[1] ∧ output.mem 129 = w[0] ∧
    output.mem 0 = w[130] ∧ output.mem 130 = w[0] := by decide +kernel

/-- Omitting the pointer copy does not produce the intended tuple payload. -/
theorem missing_copy_refused : input.mem 3 ≠ w[128] := by decide +kernel

/-- No invocation of the ownership lemma covers a write to the cursor cell. -/
theorem cursor_destination_refused : ¬ (0 < (0 : Nat)) := by decide

#print axioms executed
#print axioms retained
#print axioms owned
#print axioms observed
#print axioms missing_copy_refused
end Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.Tuple.FrameControls
