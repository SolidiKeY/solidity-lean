import Solidity.Yul.Adapters.RawPhysicalAnyImage
import Solidity.Yul.World.ByteMemory

/-! Call output writes only the returned prefix and retains the old tail.
The actual requested output span is separately touched for physical extent.
These laws connect the existing World port and call adapter to P6, without
supplying invocation adequacy, gas, allocation or dirty Source readback policy. -/
namespace Solidity.Yul.Adapters.RawPhysicalCallOutput
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open RawPhysicalInventory
variable {C : Contract} {Γ : Ctx} {ctx : Source.Ctx}
variable {D : Source.Layout} {L T : Solidity.Roadmap.Address → Source.SPath → Source.STy}

/-- The actual bounded returned prefix determines the written span. -/
def prefixArea (image : FrameMem C Γ) (destination : ByteSpan image.capacity)
    (data : Solidity.Roadmap.Bytes) : ByteSpan image.capacity :=
  ⟨destination.offset,lenU (min destination.length.val.toNat data.length) (by
    have small := (P6ByteMemory.wireWord destination.length).isLt
    exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) small),by
    simp only [lenU,Int.toNat_natCast]
    by_cases empty : min destination.length.val.toNat data.length=0
    · exact Or.inl empty
    · apply Or.inr
      have nonempty : destination.length.val.toNat≠0 := by omega
      have bound := destination.fits.resolve_left nonempty
      omega⟩

def written (image : FrameMem C Γ) (destination : ByteSpan image.capacity)
    (data : Solidity.Roadmap.Bytes) : FrameMem C Γ :=
  P6ByteMemory.writeSpan image (prefixArea image destination data)
    (World.callOutput data destination.length.val.toNat) (by
      simp only [World.callOutput_length,prefixArea,lenU,Int.toNat_natCast])

def outputArea (image : FrameMem C Γ) (destination : ByteSpan image.capacity)
    (data : Solidity.Roadmap.Bytes) : ByteSpan (written image destination data).capacity :=
  ⟨destination.offset,destination.length,by
    rw [show (written image destination data).capacity=image.capacity from
      P6ByteMemory.write_capacity image _ _ _]
    exact destination.fits⟩

def copy (image : FrameMem C Γ) (destination : ByteSpan image.capacity)
    (data : Solidity.Roadmap.Bytes) : FrameMem C Γ :=
  P6ByteMemory.touch (written image destination data) (outputArea image destination data)

theorem image (initial : FrameMem C Γ) (destination : ByteSpan initial.capacity)
    (data : Solidity.Roadmap.Bytes) :
    frameBytes (copy initial destination data)=Environment.writeBytes (frameBytes initial)
      destination.offset.val.toNat (World.callOutput data destination.length.val.toNat) := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [copy,P6ByteMemory.touch_image,written,P6ByteMemory.write_image]
  rfl

/-- Unwritten requested tail and every other exterior byte remain exact. -/
theorem outside (initial : FrameMem C Γ) (destination : ByteSpan initial.capacity)
    (data : Solidity.Roadmap.Bytes) (i : Nat)
    (away : i<destination.offset.val.toNat ∨
      destination.offset.val.toNat+min destination.length.val.toNat data.length≤i) :
    frameBytes (copy initial destination data) i=frameBytes initial i := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [image]
  apply Environment.writeBytes_frame
  simpa only [World.callOutput_length] using away

theorem carrier (initial : FrameMem C Γ) (destination : ByteSpan initial.capacity)
    (data : Solidity.Roadmap.Bytes) :
    (copy initial destination data).st=initial.st ∧ (copy initial destination data).key=initial.key := by
  first | omega | decide | skip
  have touched := P6ByteMemory.touch_carrier (written initial destination data) (outputArea initial destination data)
  have wrote : (written initial destination data).st=initial.st ∧
      (written initial destination data).key=initial.key := P6ByteMemory.write_carrier initial _ _ _
  exact ⟨touched.1.trans wrote.1,touched.2.trans wrote.2⟩

theorem high_mono (initial : FrameMem C Γ) (destination : ByteSpan initial.capacity)
    (data : Solidity.Roadmap.Bytes) : initial.highWaterWords≤(copy initial destination data).highWaterWords := by
  first | (simp only;done) | decide | omega | rfl | skip
  have wrote : initial.highWaterWords≤(written initial destination data).highWaterWords := by
    unfold written P6ByteMemory.writeSpan
    split
    · exact Nat.le_refl _
    · exact Nat.le_max_left _ _
  unfold copy P6ByteMemory.touch
  split
  · exact wrote
  · exact Nat.le_trans wrote (Nat.le_max_left _ _)

/-- Requested output access remains visible even for a short/empty return. -/
theorem high (initial : FrameMem C Γ) (destination : ByteSpan initial.capacity)
    (data : Solidity.Roadmap.Bytes) (nonempty : destination.length.val.toNat≠0) :
    (copy initial destination data).highWaterWords=
      max (written initial destination data).highWaterWords
        ((destination.offset.val.toNat+destination.length.val.toNat+31)/32) := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold copy P6ByteMemory.touch
  dsimp only [outputArea]
  rw [dif_neg nonempty]

/-- The concrete World port writes the same complete image, without padding. -/
theorem world_store (initial : FrameMem C Γ) (destination : ByteSpan initial.capacity)
    (data : Solidity.Roadmap.Bytes)
    (accepted : World.TargetMemory.port.acceptOutput (frameBytes initial)
      (P6ByteMemory.wireWord destination.offset) (P6ByteMemory.wireWord destination.length)=true) :
    World.TargetMemory.port.store (frameBytes initial) (P6ByteMemory.wireWord destination.offset)
      (World.callOutput data (P6ByteMemory.wireWord destination.length).val)=
      some (frameBytes (copy initial destination data)) := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [World.TargetMemory.accepted_output_store _ _ _ _ accepted,image]
  rfl

/-- Complete raw-local reconstruction uses the same reached physical map. -/
theorem transport (base : Nat) (state : RawFrame.State ctx) (initial : FrameMem C Γ)
    (room : base+32*wordCellCount (localExternalTypes ctx)≤initial.highWaterWords*32)
    (destination : ByteSpan initial.capacity) (data : Solidity.Roadmap.Bytes) :
    let reached := copy initial destination data
    let updated := decode base state (frameBytes reached)
    ∃ reachedRoom : base+32*wordCellCount (localExternalTypes ctx)≤reached.highWaterWords*32,
      frameOf base updated reached reachedRoom=reached ∧
      updated.clean=state.clean ∧ updated.world=state.world ∧
      reached.st=initial.st ∧ reached.key=initial.key := by
  first | omega | decide | skip
  dsimp only
  have grows := high_mono initial destination data
  have nextRoom : base+32*wordCellCount (localExternalTypes ctx)≤
      (copy initial destination data).highWaterWords*32 := by omega
  exact ⟨nextRoom,RawPhysicalAnyImage.frame_identity base state _ nextRoom,rfl,rfl,
    carrier initial destination data⟩

/-- Actual World adapter projection; successful producer invocation stays an
explicit equation. No concrete CALL implementation or adequacy is fabricated. -/
theorem call_copied (initial : FrameMem C Γ) (destination : ByteSpan initial.capacity)
    (invoke : World.WorldPort D L T) (entry : World.ObservedEffects D L T)
    (parent : Source.CallFrame) (kind : World.CallKind)
    (callee : Solidity.Roadmap.Address) (gas value inputOffset inputSize : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (answer : World.FrameAnswer D L T)
    (preflight : World.callPreflight parent kind value=true)
    (accepted : World.TargetMemory.port.acceptOutput (frameBytes initial)
      (P6ByteMemory.wireWord destination.offset) (P6ByteMemory.wireWord destination.length)=true)
    (loaded : World.TargetMemory.port.load (frameBytes initial) inputOffset inputSize=some input)
    (invoked : invoke entry kind callee gas
      (World.childContext entry.effects.execution parent kind callee value input) input=some answer) :
    (World.callAdapter World.TargetMemory.port invoke entry (frameBytes initial) parent kind callee gas value
      inputOffset inputSize (P6ByteMemory.wireWord destination.offset) (P6ByteMemory.wireWord destination.length)).map
      (fun completed => completed.copiedMemory)=
      some (some (frameBytes (copy initial destination (World.returnData answer.outcome)))) := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [World.callAdapter_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ preflight accepted loaded invoked]
  simp only [Option.map_some]
  rw [world_store initial destination _ accepted]
end Solidity.Yul.Adapters.RawPhysicalCallOutput
