import Solidity.Yul.Adapters.SelectedPhysicalStore
import Solidity.Yul.Adapters.PhysicalSnapshotSliceControls

/-! Concrete use of the published selected-word compiler and outside-image byte
identity. Reserved-memory and canonical-preparation controls retain the exact
boundaries: Source identity alone is not a memory-safety or admission theorem. -/
namespace Solidity.Yul.Adapters.SelectedPhysicalStore.Controls
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Yul.Views.NominalMemory.RetainedControls
open Solidity.Backend Solidity.Yul.Compilation
open Solidity.Yul.Adapters.PhysicalSnapshotSlice.Controls (frame initial shrinkTarget minWord)

/-- Actual96-instruction selected word program, actual Source header shrink. -/
theorem selected_shrink : ∃ next,
    PhysicalSnapshotSlice.applySlice placement state SnapshotControls.cursor frame
      (PhysicalStore.wordCode 128 0) initial=some (shrinkTarget,some next) ∧ next.1=shrunkState := by
  obtain ⟨next,prepared,source⟩ := SnapshotControls.actual_shrink
  have actual := word_apply placement state SnapshotControls.cursor frame 128 0 _
    (show PhysicalStore.selectWord 128 0=some (PhysicalStore.wordCode 128 0) from by rfl) initial
  rw [show mstore initial.memory 128 0=shrunkRaw from rfl,prepared] at actual
  exact ⟨next,actual,source⟩

def residual : ByteView := raw
def encoded : ByteView := encodeMixedHeap UnchangedControls.placement UnchangedControls.entries residual

theorem outside300 : ∀ e ∈ UnchangedControls.entries,
    300<UnchangedControls.placement.address e.id ∨
      UnchangedControls.placement.address e.id+e.image.span≤300 := by
  intro e member
  rcases List.mem_cons.mp member with same | later
  · subst e; exact Or.inr (by decide)
  · have same := List.mem_singleton.mp later
    subst e
    exact Or.inr (by decide)

/-- Nonzero raw complement is changed, while the complete actual Source state
is kernel-proved equal, not just selected alias observations. -/
theorem residual_whole_state : ∃ next,
    PhysicalSnapshotSlice.applySlice UnchangedControls.placement UnchangedControls.state
      SnapshotControls.mixedCursor frame (PhysicalStore.byteCode 300 0x1ff)
        ⟨[lenU 91 (by decide)],encoded⟩=
      some (⟨[lenU 91 (by decide)],mstore8 encoded 300 0x1ff⟩,some next) ∧ next.1=UnchangedControls.state :=
  byte_residual_identity UnchangedControls.placement UnchangedControls.state UnchangedControls.placement
    .initial UnchangedControls.entries UnchangedControls.coverage (by decide) UnchangedControls.supported
    residual frame 300 0x1ff [lenU 91 (by decide)] outside300

def residualRun := PhysicalSnapshotSlice.applySlice UnchangedControls.placement UnchangedControls.state
  SnapshotControls.mixedCursor frame (PhysicalStore.byteCode 300 0x1ff) ⟨[lenU 91 (by decide)],encoded⟩
/-- info: true -/
#guard_msgs in #eval match residualRun with
  | some (target,some next) => decide
      (target.memory 300=255 ∧ target.memory 299=165 ∧ target.memory 301=165 ∧
       target.stack=[lenU 91 (by decide)] ∧
       NominalMemory.Controls.aliasRead next.1 .here 0=some (⟨2^256-1,by decide⟩ : Roadmap.Word))
  | _ => false

/-- info: (true, true, true) -/
#guard_msgs in #eval ((PhysicalStore.selectWord (2^256-32) minWord).isSome,
  (PhysicalStore.selectWord (2^256-31) minWord).isNone,
  (PhysicalStore.selectWord (2^256) minWord).isNone)

/-- info: true -/
#guard_msgs in #eval match PhysicalSnapshotSlice.applySlice placement state SnapshotControls.cursor frame
    (PhysicalStore.wordCode 160 minWord) initial with
  | some (target,some next) => decide
      (aliasRead next.1 .here 0=some minWord ∧ aliasRead next.1 (.there .here) 0=some minWord ∧
       target.stack=initial.stack ∧ target.memory 240=165)
  | _ => false

/-- info: true -/
#guard_msgs in #eval match PhysicalSnapshotSlice.applySlice placement state SnapshotControls.cursor frame
    (PhysicalStore.wordCode 160 65535) initial with
  | some (target,none) => decide (mload target.memory 160=65535 ∧ target.stack=initial.stack)
  | _ => false

/- Outside object images does NOT mean outside reserved bytes. These two
complete physical results discriminate the missing safety obligation. -/
/-- info: true -/
#guard_msgs in #eval @decide (ReservedOK encoded UnchangedControls.placement.free)
  (by unfold ReservedOK; infer_instance)
/-- info: true -/
#guard_msgs in #eval match PhysicalSnapshotSlice.applySlice UnchangedControls.placement UnchangedControls.state
    SnapshotControls.mixedCursor frame (PhysicalStore.byteCode 64 255) ⟨[],encoded⟩ with
  | some (target,some next) => @decide
      (¬ReservedOK target.memory UnchangedControls.placement.free ∧
       NominalMemory.Controls.aliasRead next.1 .here 0=some (⟨2^256-1,by decide⟩ : Roadmap.Word))
      (by unfold ReservedOK; infer_instance)
  | _ => false

/- Writing an OWNED nominal field must not be classified as residual identity. -/
/-- info: false -/
#guard_msgs in #eval match PhysicalSnapshotSlice.applySlice placement state SnapshotControls.cursor frame
    (PhysicalStore.byteCode 191 1) initial with
  | some (_,some next) => decide (aliasRead next.1 .here 0=some (⟨2^256-1,by decide⟩ : Roadmap.Word))
  | _ => false

end Solidity.Yul.Adapters.SelectedPhysicalStore.Controls
