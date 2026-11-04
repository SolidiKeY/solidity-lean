import Solidity.Yul.Adapters.RawPhysicalAnyImage
import Solidity.Yul.Adapters.P6Inputs

/-! Actual Source.Fr.cd copying into the complete raw-local physical image.
Right zero padding and mathematical source offsets come from the existing
input operation. Raw words admit every bit pattern; ordinary typed calldata
reads retain their actual decoder success/error and unchanged Source state.
No dirty-readback cleaning or compiler CALLDATACOPY correspondence is assumed. -/
namespace Solidity.Yul.Adapters.RawPhysicalCalldata
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open RawPhysicalInventory
variable {C : Contract} {Γ : Ctx} {ctx : Source.Ctx}

theorem copy_high_mono (image : FrameMem C Γ) (frame : Source.Fr) (source : Environment.Word)
    (destination : ByteSpan image.capacity) :
    image.highWaterWords≤(P6Inputs.copyCalldata image frame source destination).highWaterWords := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold P6Inputs.copyCalldata P6ByteMemory.writeSpan
  split
  · exact Nat.le_refl _
  · exact Nat.le_max_left _ _

/-- No initial encoded-image premise: arbitrary bytes copied from actual
calldata are represented, with complete frame identity after writeback. -/
theorem transport (base : Nat) (state : RawFrame.State ctx) (image : FrameMem C Γ)
    (room : base+32*wordCellCount (localExternalTypes ctx)≤image.highWaterWords*32)
    (frame : Source.Fr) (source : Environment.Word) (destination : ByteSpan image.capacity) :
    let reached := P6Inputs.copyCalldata image frame source destination
    let updated := decode base state (frameBytes reached)
    ∃ reachedRoom : base+32*wordCellCount (localExternalTypes ctx)≤reached.highWaterWords*32,
      frameOf base updated reached reachedRoom=reached ∧
      updated.clean=state.clean ∧ updated.world=state.world ∧
      frameBytes reached=Environment.writeBytes (frameBytes image) destination.offset.val.toNat
        (P6Inputs.callBytes frame source.val.toNat destination.length.val.toNat) ∧
      reached.st=image.st ∧ reached.key=image.key := by
  first | omega | decide | skip
  dsimp only
  have grows := copy_high_mono image frame source destination
  have nextRoom : base+32*wordCellCount (localExternalTypes ctx)≤
      (P6Inputs.copyCalldata image frame source destination).highWaterWords*32 := by omega
  refine ⟨nextRoom,RawPhysicalAnyImage.frame_identity base state _ nextRoom,rfl,rfl,
    P6Inputs.copy_image _ _ _ _,?_⟩
  exact P6Inputs.copy_carrier image frame source destination

/-- Raw word observation uses exactly the same input32 bytes as cdWordAt.
This says nothing about whether any given typed Source decoder accepts them. -/
theorem copied_raw_word (base : Nat) (state : RawFrame.State ctx) (image : FrameMem C Γ)
    (frame : Source.Fr) (source : Environment.Word) (destination : ByteSpan image.capacity)
    (length : destination.length.val.toNat=32) (cell : WordCell (localExternalTypes ctx))
    (coordinates : destination.offset.val.toNat=offset base cell) :
    RawFrame.view (decode base state (frameBytes (P6Inputs.copyCalldata image frame source destination))) cell=
      Source.toWord (Source.cdWordAt frame source.val.toNat) := by
  first | omega | decide | skip
  have input := P6Inputs.copied_source_word image frame source destination length
  rw [coordinates] at input
  change Source.toWord (Source.beValue (Environment.readMemory _ (offset base cell) 32))=_
  rw [input]

/-- The actual typed operation remains a read of calldata, with its full
Source result/error and store. Unsupported raw-local readback is not inferred. -/
theorem copied_source_read (base : Nat) (state : RawFrame.State ctx) (image : FrameMem C Γ)
    (frame : Source.Fr) (source : Environment.Word) (destination : ByteSpan image.capacity)
    (length : destination.length.val.toNat=32) (cell : WordCell (localExternalTypes ctx))
    (coordinates : destination.offset.val.toNat=offset base cell) (ty : Source.STy) :
    let reached := P6Inputs.copyCalldata image frame source destination
    (Source.readLoc (E:=ctx.env) (Γ:=ctx.tys) frame (τ:=ty) (.cd source.val.toNat)).run (state.clean,state.world)=
      (Source.decodeWord ctx.env.layout (Source.beValue (Environment.readMemory (frameBytes reached) (offset base cell) 32)) ty,
        (state.clean,state.world)) := by
  first | omega | decide | skip
  have exactRead := P6Inputs.copied_source_read image frame source destination length ty (state.clean,state.world)
  rw [coordinates] at exactRead
  exact exactRead
end Solidity.Yul.Adapters.RawPhysicalCalldata
