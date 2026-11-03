import Solidity.Yul.World.TargetCallRules
import Solidity.Yul.World.AdapterChecks

/-! Registered controls over the existing scripted typed-world fixture.
They instantiate each concrete memory law and its Box rule for both outcomes;
they are not reachable Source/EVM callee or static-world certificates. -/
namespace Solidity.Yul.World.TargetCallControls
open Solidity.Source
open Solidity.Source.StateExamples
open Solidity.Roadmap (Bytes)
open Solidity.Yul.World.Checks
open Solidity.Yul.World.AdapterChecks
open Solidity.Backend.Environment (Memory readMemory writeBytes)

def before : AdapterRules.Configuration Memory D₀ LW LW := ⟨observed,memory⟩
def written (fail : Bool) : Memory :=
  writeBytes memory 31 (callOutput (returnData (answer fail [17,34,51]).outcome) 2)
def after (fail : Bool) : AdapterRules.Configuration Memory D₀ LW LW := ⟨done fail,written fail⟩
def completed (fail : Bool) : CompletedCall Memory D₀ LW LW :=
  ⟨(answer fail [17,34,51]).outcome,done fail,complete_data _ _ _ _ _ _ _ _ _,some (written fail)⟩
theorem exact_control (fail : Bool) :
 callAdapter TargetMemory.port (producer fail) observed memory parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2) = some (completed fail) :=
  TargetMemory.call_output_exact (producer fail) observed memory parent .call (addr 3)
    (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)
    [17,34,51] (answer fail [17,34,51]) rfl rfl input_loaded rfl

theorem readback_control (fail : Bool) :
 (callAdapter TargetMemory.port (producer fail) observed memory parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)).map (fun r=>(r.outcome,r.observed,
      r.copiedMemory.map (fun m=>readMemory m 31
        (callOutput (returnData (answer fail [17,34,51]).outcome) 2).length))) =
    some ((answer fail [17,34,51]).outcome,done fail,
      some (callOutput (returnData (answer fail [17,34,51]).outcome) 2)) :=
  TargetMemory.call_output_readback (producer fail) observed memory parent .call (addr 3)
    (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)
    [17,34,51] (answer fail [17,34,51]) rfl rfl input_loaded rfl

theorem frame_control (fail : Bool) (i : Nat)
    (outside : i<31 ∨ 31+min 2 (returnData (answer fail [17,34,51]).outcome).length≤i) :
 (callAdapter TargetMemory.port (producer fail) observed memory parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)).map (fun r=>(r.outcome,r.observed,r.copiedMemory.map (fun m=>m i))) =
    some ((answer fail [17,34,51]).outcome,done fail,some (memory i)) :=
  TargetMemory.call_output_frame (producer fail) observed memory parent .call (addr 3)
    (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)
    [17,34,51] (answer fail [17,34,51]) rfl rfl input_loaded rfl i outside

theorem box_control (fail : Bool) :
 AdapterRules.Box
      (AdapterRules.CallStep TargetMemory.port (producer fail) parent .call (addr 3)
        (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)
        (answer fail [17,34,51]).outcome)
      (fun next => next.observed=done fail ∧
        readMemory next.memory 31 (callOutput (returnData (answer fail [17,34,51]).outcome) 2).length=
          callOutput (returnData (answer fail [17,34,51]).outcome) 2 ∧
        ∀ i, (i<31 ∨ 31+min 2 (returnData (answer fail [17,34,51]).outcome).length≤i) →
          next.memory i=memory i) before :=
  TargetMemory.call_output_box (producer fail) before parent .call (addr 3)
    (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)
    [17,34,51] (answer fail [17,34,51]) rfl rfl input_loaded rfl

theorem normal_inhabited (fail : Bool) :
 AdapterRules.CallStep TargetMemory.port (producer fail) parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)
      (answer fail [17,34,51]).outcome before (after fail) :=
  ⟨completed fail,exact_control fail,rfl,rfl,rfl⟩

theorem success_witness :
    AdapterRules.CallStep TargetMemory.port (producer false) parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)
      (.success [17,34,51]) before (after false) := normal_inhabited false

theorem success_readback :
    (callAdapter TargetMemory.port (producer false) observed memory parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)).map
      (fun r=>(r.outcome,r.observed,r.copiedMemory.map (fun m=>readMemory m 31 2))) =
    some (.success [17,34,51],done false,some [17,34]) := readback_control false

theorem success_box_applied :
    (after false).observed=done false ∧
    readMemory (after false).memory 31 2=[17,34] ∧
    ∀ i, (i<31 ∨ 33≤i) → (after false).memory i=memory i :=
  box_control false (after false) (success_witness)

theorem revert_witness :
    AdapterRules.CallStep TargetMemory.port (producer true) parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)
      (.revert [17,34,51]) before (after true) := normal_inhabited true

theorem revert_readback :
    (callAdapter TargetMemory.port (producer true) observed memory parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)).map
      (fun r=>(r.outcome,r.observed,r.copiedMemory.map (fun m=>readMemory m 31 2))) =
    some (.revert [17,34,51],done true,some [17,34]) := readback_control true

theorem revert_box_applied :
    (after true).observed=done true ∧
    readMemory (after true).memory 31 2=[17,34] ∧
    ∀ i, (i<31 ∨ 33≤i) → (after true).memory i=memory i :=
  box_control true (after true) (revert_witness)

end Solidity.Yul.World.TargetCallControls
