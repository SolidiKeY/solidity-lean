import Solidity.Yul.Adapters.RawPhysicalCallFrame

/-! Input access accounting for the existing physical call-output adapter.
The input snapshot precedes output mutation, including overlap. Touching the
input changes extent only; actual World results and complete raw byte maps
are retained. This supplies no gas, invocation or allocation adequacy. -/
namespace Solidity.Yul.Adapters.RawPhysicalCallAccess
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open RawPhysicalInventory
variable {C : Contract} {Γ : Ctx} {ctx : Source.Ctx}

def inputArea (initial : FrameMem C Γ) (input output : ByteSpan initial.capacity)
    (data : Solidity.Roadmap.Bytes) : ByteSpan (RawPhysicalCallOutput.copy initial output data).capacity :=
  ⟨input.offset,input.length,by
    rw [show (RawPhysicalCallOutput.copy initial output data).capacity=initial.capacity from
      (P6ByteMemory.touch_capacity _ _).trans (P6ByteMemory.write_capacity _ _ _ _)]
    exact input.fits⟩

def reached (initial : FrameMem C Γ) (input output : ByteSpan initial.capacity)
    (data : Solidity.Roadmap.Bytes) : FrameMem C Γ :=
  P6ByteMemory.touch (RawPhysicalCallOutput.copy initial output data) (inputArea initial input output data)

theorem image (initial : FrameMem C Γ) (input output : ByteSpan initial.capacity)
    (data : Solidity.Roadmap.Bytes) :
    frameBytes (reached initial input output data)=frameBytes (RawPhysicalCallOutput.copy initial output data) :=
  P6ByteMemory.touch_image _ _

theorem high (initial : FrameMem C Γ) (input output : ByteSpan initial.capacity)
    (data : Solidity.Roadmap.Bytes) (nonempty : input.length.val.toNat≠0) :
    (reached initial input output data).highWaterWords=
      max (RawPhysicalCallOutput.copy initial output data).highWaterWords
        ((input.offset.val.toNat+input.length.val.toNat+31)/32) := by
  unfold reached P6ByteMemory.touch
  dsimp only [inputArea]
  rw [dif_neg nonempty]

theorem high_mono (initial : FrameMem C Γ) (input output : ByteSpan initial.capacity)
    (data : Solidity.Roadmap.Bytes) : initial.highWaterWords≤(reached initial input output data).highWaterWords := by
  have grows := RawPhysicalCallOutput.high_mono initial output data
  unfold reached P6ByteMemory.touch
  split
  · exact grows
  · exact Nat.le_trans grows (Nat.le_max_left _ _)

/-- All raw locals are decoded from the SAME fully accounted reached image. -/
theorem transport (base : Nat) (state : RawFrame.State ctx) (initial : FrameMem C Γ)
    (room : base+32*wordCellCount (localExternalTypes ctx)≤initial.highWaterWords*32)
    (input output : ByteSpan initial.capacity) (data : Solidity.Roadmap.Bytes) :
    let after := reached initial input output data
    let updated := decode base state (frameBytes after)
    ∃ nextRoom : base+32*wordCellCount (localExternalTypes ctx)≤after.highWaterWords*32,
      frameOf base updated after nextRoom=after ∧
      updated.clean=state.clean ∧ updated.world=state.world ∧ after.st=initial.st ∧ after.key=initial.key := by
  dsimp only
  have grows := high_mono initial input output data
  have nextRoom : base+32*wordCellCount (localExternalTypes ctx)≤(reached initial input output data).highWaterWords*32 := by omega
  have touched := P6ByteMemory.touch_carrier (RawPhysicalCallOutput.copy initial output data) (inputArea initial input output data)
  have copied := RawPhysicalCallOutput.carrier initial output data
  exact ⟨nextRoom,RawPhysicalAnyImage.frame_identity base state _ nextRoom,rfl,rfl,
    touched.1.trans copied.1,touched.2.trans copied.2⟩

/-- Full actual call result, now attributed to the input/output-accounted frame.
Input loading and invocation use the pre-call snapshot, never the reached one. -/
theorem execute_eq {D : Source.Layout} {L T : Solidity.Roadmap.Address → Source.SPath → Source.STy}
    (initial : FrameMem C Γ) (input output : ByteSpan initial.capacity)
    (invoke : World.WorldPort D L T) (entry : World.ObservedEffects D L T)
    (parent : Source.CallFrame) (kind : World.CallKind)
    (callee : Solidity.Roadmap.Address) (gas value : Solidity.Roadmap.Word)
    (answer : World.FrameAnswer D L T)
    (preflight : World.callPreflight parent kind value=true)
    (inputNonwrap : input.offset.val.toNat+input.length.val.toNat≤2^256)
    (accepted : World.TargetMemory.port.acceptOutput (frameBytes initial)
      (P6ByteMemory.wireWord output.offset) (P6ByteMemory.wireWord output.length)=true)
    (invoked : invoke entry kind callee gas
      (World.childContext entry.effects.execution parent kind callee value (snapshot initial input))
      (snapshot initial input)=some answer) :
    World.callAdapter World.TargetMemory.port invoke entry (frameBytes initial) parent kind callee gas value
      (P6ByteMemory.wireWord input.offset) (P6ByteMemory.wireWord input.length)
      (P6ByteMemory.wireWord output.offset) (P6ByteMemory.wireWord output.length)=
      some {RawPhysicalCallFrame.completed initial output entry
        (World.childContext entry.effects.execution parent kind callee value (snapshot initial input)) answer with
        copiedMemory:=some (frameBytes (reached initial input output (World.returnData answer.outcome)))} := by
  rw [RawPhysicalCallFrame.execute_eq initial input output invoke entry parent kind callee gas value answer
    preflight inputNonwrap accepted invoked,image]
  rfl
end Solidity.Yul.Adapters.RawPhysicalCallAccess
