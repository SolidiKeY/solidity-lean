import Solidity.Yul.Adapters.P6ResidualReserve
import Solidity.Yul.Adapters.P6ResidualResumeControls

/-! Computed reservation controls retain overlapping-copy chronology and avoid
reserving for empty maximum-offset accesses. These are not compiler/EVM tests. -/
namespace Solidity.Yul.Adapters.P6ResidualReserve.Controls
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6ResidualCapacity P6ResidualResume.Controls P6ResidualCopy.Controls

def completed := finish stopped

theorem actual_source :
    frameBytes completed.frame=residualCopyPhysical UnchangedControls.placement
        (residualCopies work residual) ∧
      writeback UnchangedControls.state UnchangedControls.placement UnchangedControls.placement .initial
        (generatedHeapEntries UnchangedControls.placement) (frameBytes completed.frame)=
          some (.ok (),UnchangedControls.state) ∧
      ReservedOK (frameBytes completed.frame) UnchangedControls.placement.free :=
  finish_source UnchangedControls.state UnchangedControls.placement UnchangedControls.placement
    .initial work UnchangedControls.generated_whole_state.1 UnchangedControls.heap_profile
    (image .legacy) residual (image_bytes .legacy) reserved

/-- info: (516, 1, 0, 544, 17) -/
#guard_msgs in #eval (extent stopped.pending,extraWords stopped.frame.capacity (extent stopped.pending),
  completed.pending.length,completed.frame.capacity,completed.frame.highWaterWords)
/-- info: [7, 0, 255, 7, 8, 9, 10, 11] -/
#guard_msgs in #eval (List.range 8).map (fun i => (frameBytes completed.frame (400+i)).toNat)
/-- info: 8 -/
#guard_msgs in #eval (frameBytes completed.frame 232).toNat
/-- info: (0, 0, 512, 8) -/
#guard_msgs in #eval let pending : CopyProgress UnchangedControls.placement _ _ :=
    ⟨image .viaIR,[emptyRequest]⟩
  let result := finish pending
  (extent pending.pending,result.pending.length,result.frame.capacity,result.frame.highWaterWords)
/-- info: (516, 0, 544) -/
#guard_msgs in #eval let pending : CopyProgress UnchangedControls.placement _ _ :=
    ⟨image .viaIR,[P6ResidualCapacity.Controls.badSource]⟩
  let result := finish pending
  (extent pending.pending,result.pending.length,result.frame.capacity)
/-- info: (0, 1, 1, 2) -/
#guard_msgs in #eval (extraWords 512 512,extraWords 512 513,extraWords 512 544,extraWords 512 545)

end Solidity.Yul.Adapters.P6ResidualReserve.Controls
