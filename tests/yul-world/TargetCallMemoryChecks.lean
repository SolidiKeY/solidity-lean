import Solidity.Yul.World.TargetCallMemory
import Solidity.Yul.World.AdapterChecks

/-! Scripted typed journal controls, not reachable-callee certificates. -/
namespace Solidity.Yul.World.TargetCallMemoryChecks
open Solidity.Source
open Solidity.Source.StateExamples
open Solidity.Yul.World.Checks
open Solidity.Yul.World.AdapterChecks
open Solidity.Backend.Environment (readMemory)

theorem revert_truncated :
    (callAdapter TargetMemory.port (producer true) observed memory parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 2)).map
      (fun r => (r.outcome, r.observed,
        r.copiedMemory.map (fun m => (readMemory m 31 2, m 30, m 33)))) =
    some (.revert [17, 34, 51], done true, some ([17, 34], 255, 255)) := by
  rfl

theorem success_untouched_tail :
    (callAdapter TargetMemory.port (producer false) observed memory parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 8)).map
      (fun r => (r.outcome, r.observed,
        r.copiedMemory.map (fun m => (readMemory m 31 3, readMemory m 34 5)))) =
    some (.success [17, 34, 51], done false, some ([17, 34, 51], [255,255,255,255,255])) := by
  rfl

theorem zero_capacity_full_buffer :
    (callAdapter TargetMemory.port (producer true) observed memory parent .call (addr 3)
      (toWord 100000) (toWord 0) (toWord 7) (toWord 3) (toWord 31) (toWord 0)).map
      (fun r => (r.outcome, r.observed.effects.returndata,
        r.copiedMemory.map (fun m => readMemory m 31 3))) =
    some (.revert [17,34,51], [17,34,51], some [255,255,255]) := by
  rfl

#check TargetMemory.call_output_exact
#check TargetMemory.call_output_readback
#check TargetMemory.call_output_frame
#print axioms TargetMemory.call_output_exact
#print axioms TargetMemory.call_output_readback
#print axioms TargetMemory.call_output_frame
end Solidity.Yul.World.TargetCallMemoryChecks
#print axioms Solidity.Yul.World.TargetCallMemoryChecks.revert_truncated
#print axioms Solidity.Yul.World.TargetCallMemoryChecks.success_untouched_tail
#print axioms Solidity.Yul.World.TargetCallMemoryChecks.zero_capacity_full_buffer
