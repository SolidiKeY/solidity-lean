import Solidity.Yul.Adapters.RawPhysicalAnyImage
import Solidity.Yul.World.ByteMemory

/-! Strict world returndata copying into the existing physical frame and raw
local inventory. Source-window validity, physical capacity and Word-address
nonwrapping remain separate premises. The complete reached byte map is reused;
no cleaning, calldata padding or Source failure interpretation is introduced. -/
namespace Solidity.Yul.Adapters.RawPhysicalReturndata
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open RawPhysicalInventory
variable {C : Contract} {Γ : Ctx} {ctx : Source.Ctx}
variable {D : Source.Layout} {L T : Solidity.Roadmap.Address → Source.SPath → Source.STy}

/-- Length comes from the actual strict world window, not a supplied view. -/
def copy (image : FrameMem C Γ) (destination : ByteSpan image.capacity)
    (entry : World.Effects D L T) (source : Solidity.Roadmap.Word)
    (bytes : Solidity.Roadmap.Bytes)
    (window : World.returnWindow entry.returndata source.val destination.length.val.toNat=some bytes) :
    FrameMem C Γ :=
  P6ByteMemory.writeSpan image destination bytes (World.returnWindow_length _ _ _ _ window)

theorem high_mono (image : FrameMem C Γ) (destination : ByteSpan image.capacity)
    (entry : World.Effects D L T) (source : Solidity.Roadmap.Word)
    (bytes : Solidity.Roadmap.Bytes)
    (window : World.returnWindow entry.returndata source.val destination.length.val.toNat=some bytes) :
    image.highWaterWords≤(copy image destination entry source bytes window).highWaterWords := by
  unfold copy P6ByteMemory.writeSpan
  split
  · exact Nat.le_refl _
  · exact Nat.le_max_left _ _

/-- The actual target-memory port produces the SAME complete physical image. -/
theorem world_copy (image : FrameMem C Γ) (destination : ByteSpan image.capacity)
    (entry : World.Effects D L T) (source : Solidity.Roadmap.Word)
    (bytes : Solidity.Roadmap.Bytes)
    (window : World.returnWindow entry.returndata source.val destination.length.val.toNat=some bytes)
    (nonwrap : destination.offset.val.toNat+bytes.length≤2^256) :
    World.copyReturndata World.TargetMemory.port entry (frameBytes image)
      (P6ByteMemory.wireWord destination.offset) source (P6ByteMemory.wireWord destination.length)=
      some (frameBytes (copy image destination entry source bytes window)) := by
  rw [World.copyReturndata_exact _ _ _ _ _ _ bytes window,
    World.TargetMemory.store_exact _ _ _ nonwrap]
  rw [copy,P6ByteMemory.write_image]
  rfl

/-- Arbitrary raw words are refreshed from the reached map, including partial
cell writes. Both the full frame and clean Source carriers are preserved by
unchanged-view writeback; this is not typed-heap or compiler adequacy. -/
theorem transport (base : Nat) (state : RawFrame.State ctx) (image : FrameMem C Γ)
    (room : base+32*wordCellCount (localExternalTypes ctx)≤image.highWaterWords*32)
    (destination : ByteSpan image.capacity) (entry : World.Effects D L T)
    (source : Solidity.Roadmap.Word) (bytes : Solidity.Roadmap.Bytes)
    (window : World.returnWindow entry.returndata source.val destination.length.val.toNat=some bytes)
    (nonwrap : destination.offset.val.toNat+bytes.length≤2^256) :
    let reached := copy image destination entry source bytes window
    let updated := decode base state (frameBytes reached)
    ∃ reachedRoom : base+32*wordCellCount (localExternalTypes ctx)≤reached.highWaterWords*32,
      frameOf base updated reached reachedRoom=reached ∧
      updated.clean=state.clean ∧ updated.world=state.world ∧
      World.copyReturndata World.TargetMemory.port entry (frameBytes image)
        (P6ByteMemory.wireWord destination.offset) source (P6ByteMemory.wireWord destination.length)=
        some (frameBytes reached) ∧
      reached.st=image.st ∧ reached.key=image.key := by
  dsimp only
  have grows := high_mono image destination entry source bytes window
  have nextRoom : base+32*wordCellCount (localExternalTypes ctx)≤
      (copy image destination entry source bytes window).highWaterWords*32 := by omega
  refine ⟨nextRoom,RawPhysicalAnyImage.frame_identity base state _ nextRoom,rfl,rfl,
    world_copy image destination entry source bytes window nonwrap,?_⟩
  exact P6ByteMemory.write_carrier image destination bytes _
end Solidity.Yul.Adapters.RawPhysicalReturndata
