import Solidity.Yul.Adapters.RawPhysicalInterior

/-! Universal raw-local decode/reencode over arbitrary byte maps. Each actual
cell holds a full word, so every 32-byte sequence has an exact representation.
This is a raw-cell theorem, not a canonical Source-value decoder or a policy
for dirty storage. Capture still populates overlays beside clean Source locals.
Actual bounded P6 copies may overlap and cross cells; no final view is assumed. -/
namespace Solidity.Yul.Adapters.RawPhysicalAnyImage
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open RawPhysicalInventory RawPhysicalWriteback
variable {ctx : Source.Ctx}

theorem decode_reads (base : Nat) (state : RawFrame.State ctx) (memory : Views.ByteView)
    (cell : WordCell (localExternalTypes ctx)) :
    Environment.readMemory memory (offset base cell) 32=
      Source.wordBytes (RawFrame.view (decode base state memory) cell) := by
  exact (RawPhysicalInterior.bytes_word_inverse _
    (by simp only [Environment.readMemory,List.length_map,List.length_range])).symm

/-- Every raw byte map, including noncanonical bool/u8 words, roundtrips without
cleaning or a final encoded-view premise. All complementary bytes stay exact. -/
theorem encode_decode (base : Nat) (state : RawFrame.State ctx) (memory : Views.ByteView) :
    encode base (decode base state memory) memory=memory := by
  apply list_unchanged
  intro cell member
  exact decode_reads base state memory cell

/-- The WHOLE existing physical frame is recovered, without initial canonical
raw words. Room locates the inventory; it is not EVM Word nonwrapping. -/
theorem frame_identity {C : Contract} {Γ : Ctx} (base : Nat) (state : RawFrame.State ctx)
    (image : FrameMem C Γ) (room : base+32*wordCellCount (localExternalTypes ctx)≤image.highWaterWords*32) :
    frameOf base (decode base state (frameBytes image)) image room=image := by
  apply MemoryAgreement.unchanged
  exact encode_decode base state (frameBytes image)

/-- Existing copy accounting never reduces the actual high-water mark, even
for zero lengths and source=destination. No gas or allocator law follows. -/
theorem copy_high_mono {C : Contract} {Γ : Ctx} (image : FrameMem C Γ)
    (source destination : ByteSpan image.capacity) (same : source.length=destination.length) :
    image.highWaterWords≤(P6ByteMemory.copySnapshot image source destination same).highWaterWords := by
  by_cases empty : source.length.val.toNat=0
  · rw [P6ByteMemory.copy_empty image source destination same empty]
    exact Nat.le_refl _
  · rw [P6ByteMemory.copy_highWater image source destination same empty]
    omega

/-- Any actual bounded snapshot copy refreshes every raw local from the SAME
reached frame. Lengths and overlap are unrestricted beyond the actual spans. -/
theorem copy_transport {C : Contract} {Γ : Ctx} (base : Nat) (state : RawFrame.State ctx)
    (image : FrameMem C Γ) (room : base+32*wordCellCount (localExternalTypes ctx)≤image.highWaterWords*32)
    (source destination : ByteSpan image.capacity) (same : source.length=destination.length) :
    let reached := P6ByteMemory.copySnapshot image source destination same
    let updated := decode base state (frameBytes reached)
    ∃ reachedRoom : base+32*wordCellCount (localExternalTypes ctx)≤reached.highWaterWords*32,
      frameOf base updated reached reachedRoom=reached ∧
      updated.clean=state.clean ∧ updated.world=state.world ∧
      frameBytes reached=Environment.writeBytes (frameBytes image) destination.offset.val.toNat
        (Environment.readMemory (frameBytes image) source.offset.val.toNat source.length.val.toNat) ∧
      reached.st=image.st ∧ reached.key=image.key := by
  dsimp only
  have grows := copy_high_mono image source destination same
  have nextRoom : base+32*wordCellCount (localExternalTypes ctx)≤
      (P6ByteMemory.copySnapshot image source destination same).highWaterWords*32 := by omega
  refine ⟨nextRoom,frame_identity base state _ nextRoom,rfl,rfl,P6ByteMemory.copy_image _ _ _ _,?_⟩
  exact P6ByteMemory.copy_carrier image source destination same
end Solidity.Yul.Adapters.RawPhysicalAnyImage
