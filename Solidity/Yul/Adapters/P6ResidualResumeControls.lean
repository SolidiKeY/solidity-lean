import Solidity.Yul.Adapters.P6ResidualResume
import Solidity.Yul.Adapters.P6ResidualCapacityControls

/-! Replay-sensitive checked resumption on a computed two-root Source image.
Frame pipeline tags are metadata; these are kernel/runtime controls, not EVM
compiler-pipeline observations or allocator provenance. -/
namespace Solidity.Yul.Adapters.P6ResidualResume.Controls
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6ResidualCapacity P6ResidualCopy.Controls

def crossing : ResidualCopyRequest UnchangedControls.placement :=
  ⟨tailWindow 508 8 (by decide) (by decide),228,Or.inr (by decide)⟩
def suffix : ResidualCopyRequest UnchangedControls.placement :=
  ⟨tailWindow 400 8 (by decide) (by decide),508,Or.inr (by decide)⟩
def work := [forward,crossing,suffix]
def stopped := checkedCopies (image .legacy) work
def complete := resume stopped 1
def stillStopped := resume stopped 0

/-- The generic Source/full-map theorem is inhabited by actual computed heap
preparation and codecs, without supplying the completed prefix or output map. -/
theorem actual_source (extraWords : Nat) :
    writeback UnchangedControls.state UnchangedControls.placement UnchangedControls.placement .initial
      (generatedHeapEntries UnchangedControls.placement)
      (frameBytes (resume stopped extraWords).frame)=some (.ok (),UnchangedControls.state) := by
  obtain ⟨_,_,_,_,source,_⟩ :=
    resumed_source UnchangedControls.state UnchangedControls.placement UnchangedControls.placement
      .initial work UnchangedControls.generated_whole_state.1 UnchangedControls.heap_profile
      (image .legacy) residual (image_bytes .legacy) reserved extraWords
  exact source

/-- info: (2, 8, 8) -/
#guard_msgs in #eval (stopped.pending.length,stopped.frame.highWaterWords,
  (frameBytes stopped.frame 232).toNat)
/-- info: (0, 544, 17, 8) -/
#guard_msgs in #eval (complete.pending.length,complete.frame.capacity,
  complete.frame.highWaterWords,(frameBytes complete.frame 232).toNat)
/-- info: [7, 0, 255, 7, 8, 9, 10, 11] -/
#guard_msgs in #eval (List.range 8).map (fun i => (frameBytes complete.frame (400+i)).toNat)
/-- info: [7, 0, 255, 7, 8, 9, 10, 11] -/
#guard_msgs in #eval (List.range 8).map (fun i => (frameBytes complete.frame (508+i)).toNat)
/-- info: (2, 512, 8, 8) -/
#guard_msgs in #eval (stillStopped.pending.length,stillStopped.frame.capacity,
  stillStopped.frame.highWaterWords,(frameBytes stillStopped.frame 232).toNat)
/- Replaying the already accepted overlapping prefix corrupts byte232. -/
/-- info: (7, 8) -/
#guard_msgs in #eval let replay := checkedCopies (expandZero stopped.frame 1) work
  ((frameBytes replay.frame 232).toNat,(frameBytes complete.frame 232).toNat)
/-- info: (8, 544) -/
#guard_msgs in #eval ((expandZero stopped.frame 1).highWaterWords,
  (expandZero stopped.frame 1).capacity)

end Solidity.Yul.Adapters.P6ResidualResume.Controls
