import Solidity.Yul.Adapters.P6ResidualCapacity
import Solidity.Yul.Adapters.P6ResidualSequenceControls

/-! Computed capacity preparation retains actual prefixes and does not clip,
skip or execute unfit copies. Capacity512 is a fixture, not a new generic cap.
Pipeline tags are existing frame metadata, not external compiler/EVM evidence. -/
namespace Solidity.Yul.Adapters.P6ResidualCapacity.Controls
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Adapters.P6ResidualCopy.Controls
open Solidity.Yul.Adapters.P6ResidualSequence.Controls (onward requests interspersed)

def badDestination : ResidualCopyRequest UnchangedControls.placement :=
  ⟨tailWindow 508 8 (by decide) (by decide),300,Or.inr (by decide)⟩
def badSource : ResidualCopyRequest UnchangedControls.placement :=
  ⟨tailWindow 400 8 (by decide) (by decide),508,Or.inr (by decide)⟩
def later : ResidualCopyRequest UnchangedControls.placement :=
  ⟨tailWindow 400 8 (by decide) (by decide),300,Or.inr (by decide)⟩

def work := requests++[badDestination,later]
def sourceWork := requests++[badSource,later]
def destinationStop := checkedCopies (image .legacy) work
def sourceStop := checkedCopies (image .viaIR) sourceWork

/-- The inhabited computed Source/frame covers ANY input request list, including
capacity stops. No caller supplies the successful prefix or its room proofs. -/
theorem actual_source (pipeline : Pipeline) (work : List (ResidualCopyRequest UnchangedControls.placement)) :
    ∃ done,work=done++(checkedCopies (image pipeline) work).pending ∧
      frameBytes (checkedCopies (image pipeline) work).frame=
        residualCopyPhysical UnchangedControls.placement (residualCopies done residual) ∧
      writeback UnchangedControls.state UnchangedControls.placement UnchangedControls.placement .initial
        (generatedHeapEntries UnchangedControls.placement) (frameBytes (checkedCopies (image pipeline) work).frame)=
        some (.ok (),UnchangedControls.state) ∧
      ReservedOK (frameBytes (checkedCopies (image pipeline) work).frame) UnchangedControls.placement.free ∧
      (checkedCopies (image pipeline) work).frame.st=(image pipeline).st ∧
      (checkedCopies (image pipeline) work).frame.key=(image pipeline).key ∧
      (checkedCopies (image pipeline) work).frame.capacity=(image pipeline).capacity :=
  checked_source UnchangedControls.state UnchangedControls.placement UnchangedControls.placement .initial work
    UnchangedControls.generated_whole_state.1 UnchangedControls.heap_profile
    (image pipeline) residual (image_bytes pipeline) reserved

/-- info: (2, 2, 10, 512) -/
#guard_msgs in #eval (destinationStop.pending.length,sourceStop.pending.length,
  destinationStop.frame.highWaterWords,destinationStop.frame.capacity)
/-- info: [7, 7, 0, 0] -/
#guard_msgs in #eval [300,310,400,508].map (fun a => (frameBytes destinationStop.frame a).toNat)
/-- info: [7, 7, 0, 0] -/
#guard_msgs in #eval [300,310,400,508].map (fun a => (frameBytes sourceStop.frame a).toNat)
/-- info: (508, 300, 1) -/
#guard_msgs in #eval match destinationStop.pending with
  | r::rest => (r.window.destination.val,r.source.val,rest.length)
  | [] => (0,0,0)
/-- info: (400, 508, 1) -/
#guard_msgs in #eval match sourceStop.pending with
  | r::rest => (r.window.destination.val,r.source.val,rest.length)
  | [] => (0,0,0)

/-- info: (true, false) -/
#guard_msgs in #eval (decide (badDestination.source.val+badDestination.window.size.val≤512),
  decide (badDestination.window.destination.val+badDestination.window.size.val≤512))
/-- info: (false, true) -/
#guard_msgs in #eval (decide (badSource.source.val+badSource.window.size.val≤512),
  decide (badSource.window.destination.val+badSource.window.size.val≤512))

/-- info: (0, 10, 7) -/
#guard_msgs in #eval let complete := checkedCopies (image .viaIR) interspersed
  (complete.pending.length,complete.frame.highWaterWords,(frameBytes complete.frame 310).toNat)
/-- info: (2, 8, 0) -/
#guard_msgs in #eval let firstFailure := checkedCopies (image .legacy) [badDestination,later]
  (firstFailure.pending.length,firstFailure.frame.highWaterWords,(frameBytes firstFailure.frame 300).toNat)
/-- info: true -/
#guard_msgs in #eval @decide (ReservedOK (frameBytes destinationStop.frame) UnchangedControls.placement.free)
  (by unfold ReservedOK;infer_instance)

/- Returning only initial bytes would lose the successful prefix; skipping the
bad request would run later and write7at400. A clipped copy would write7at508. -/
/-- info: true -/
#guard_msgs in #eval decide ((frameBytes destinationStop.frame 310)=7 ∧
  (frameBytes destinationStop.frame 400)=0 ∧ (frameBytes destinationStop.frame 508)=0)

end Solidity.Yul.Adapters.P6ResidualCapacity.Controls
