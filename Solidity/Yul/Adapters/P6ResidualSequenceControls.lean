import Solidity.Yul.Adapters.P6ResidualSequence
import Solidity.Yul.Adapters.P6ResidualCopyControls

/-! Chronology controls for actual P6 frame-copy sequences. The second copy
reads a freshly written residual region; reversed order must differ. Existing
computed Source/frame witnesses and request geometry are reused. -/
namespace Solidity.Yul.Adapters.P6ResidualSequence.Controls
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open Solidity.Yul.Adapters.P6ResidualCopy.Controls

def onward : ResidualCopyRequest UnchangedControls.placement :=
  ⟨tailWindow 310 8 (by decide) (by decide),300,Or.inr (by decide)⟩
def requests := [distant,onward]

theorem rooms (pipeline : Pipeline) : ∀ r ∈ requests,CopyRoom (image pipeline).capacity r := by
  intro r member
  simp only [requests,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same | same
  · subst r
    exact ⟨Or.inr (by change 224+8≤512;decide),Or.inr (by change 300+8≤512;decide)⟩
  · subst r
    exact ⟨Or.inr (by change 300+8≤512;decide),Or.inr (by change 310+8≤512;decide)⟩

def reached (pipeline : Pipeline) := runCopies (image pipeline) requests (rooms pipeline)
def reversed (pipeline : Pipeline) := runCopies (image pipeline) requests.reverse
  (fun r member => rooms pipeline r (List.mem_reverse.mp member))

def interspersed := [emptyRequest,distant,emptyRequest,onward]
theorem interspersed_rooms (pipeline : Pipeline) :
    ∀ r ∈ interspersed,CopyRoom (image pipeline).capacity r := by
  intro r member
  simp only [interspersed,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨Or.inl rfl,Or.inl rfl⟩
  · exact ⟨Or.inr (by change 224+8≤512;decide),Or.inr (by change 300+8≤512;decide)⟩
  · exact ⟨Or.inl rfl,Or.inl rfl⟩
  · exact ⟨Or.inr (by change 300+8≤512;decide),Or.inr (by change 310+8≤512;decide)⟩

def withEmpty (pipeline : Pipeline) := runCopies (image pipeline) interspersed (interspersed_rooms pipeline)

/-- Actual repeated frame operations, computed inventory and whole Source
writeback; no expected final view or separately assumed Source run. -/
theorem actual_source (pipeline : Pipeline) :
    writeback UnchangedControls.state UnchangedControls.placement UnchangedControls.placement .initial
      (generatedHeapEntries UnchangedControls.placement) (frameBytes (reached pipeline))=
      some (.ok (),UnchangedControls.state) ∧
    ReservedOK (frameBytes (reached pipeline)) UnchangedControls.placement.free :=
  runCopies_source UnchangedControls.state UnchangedControls.placement UnchangedControls.placement .initial requests
    UnchangedControls.generated_whole_state.1 UnchangedControls.heap_profile
    (image pipeline) (rooms pipeline) residual (image_bytes pipeline) reserved

/-- This instantiated kernel result covers every actual prefix, with no new
prefix-length bound and no empty-locals assumption. -/
theorem actual_prefixes (pipeline : Pipeline) (count : Nat) :
    let selected := requests.take count
    let out := runCopies (image pipeline) selected (fun r member => rooms pipeline r (List.mem_of_mem_take member))
    frameBytes out=residualCopyPhysical UnchangedControls.placement (residualCopies selected residual) ∧
    writeback UnchangedControls.state UnchangedControls.placement UnchangedControls.placement .initial
      (generatedHeapEntries UnchangedControls.placement) (frameBytes out)=some (.ok (),UnchangedControls.state) ∧
    ReservedOK (frameBytes out) UnchangedControls.placement.free :=
  runCopies_prefix UnchangedControls.state UnchangedControls.placement UnchangedControls.placement .initial requests
    UnchangedControls.generated_whole_state.1 UnchangedControls.heap_profile
    (image pipeline) (rooms pipeline) residual (image_bytes pipeline) reserved count

/-- info: [7, 0, 255, 7, 8, 9, 10, 11] -/
#guard_msgs in #eval Environment.readMemory (frameBytes (reached .legacy)) 310 8
/-- info: [0, 0, 0, 0, 0, 0, 0, 0] -/
#guard_msgs in #eval Environment.readMemory (frameBytes (reversed .legacy)) 310 8
/-- info: [7, 0, 255, 7, 8, 9, 10, 11] -/
#guard_msgs in #eval Environment.readMemory (frameBytes (withEmpty .viaIR)) 310 8
/-- info: (0, 7, 7, 10, 512) -/
#guard_msgs in #eval ((frameBytes (image .legacy) 300).toNat,
  (frameBytes (reached .legacy) 300).toNat,(frameBytes (reached .legacy) 310).toNat,
  (reached .legacy).highWaterWords,(reached .legacy).capacity)

/-- info: true -/
#guard_msgs in #eval @decide (ReservedOK (frameBytes (withEmpty .legacy)) UnchangedControls.placement.free)
  (by unfold ReservedOK;infer_instance)

/- The second reached read must NOT use the initial frame at300 (zero), and
an empty request must not erase the earlier accounting or copied payload. -/
/-- info: false -/
#guard_msgs in #eval Environment.readMemory (frameBytes (reached .legacy)) 310 8==
  Environment.readMemory (frameBytes (image .legacy)) 300 8
/-- info: true -/
#guard_msgs in #eval decide ((withEmpty .viaIR).highWaterWords=10 ∧
  Environment.readMemory (frameBytes (withEmpty .viaIR)) 300 18=
    Environment.readMemory (frameBytes (reached .viaIR)) 300 18)

end Solidity.Yul.Adapters.P6ResidualSequence.Controls
