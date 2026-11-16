import Solidity.Yul.Adapters.RawPhysicalCallOutput

/-! Full World call results with physical output images. Input bytes are read
from the actual pre-call frame; the supplied invocation equation stays explicit.
Completion uses the existing typed Source journal and ordered observations.
Physical output copying after a callee revert is not an enclosing-frame commit
or a concrete CALL implementation/adequacy theorem. -/
namespace Solidity.Yul.Adapters.RawPhysicalCallFrame
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
variable {C : Contract} {Γ : Ctx}
variable {D : Source.Layout} {L T : Solidity.Roadmap.Address → Source.SPath → Source.STy}

/-- The exact existing completed-call carrier, including all observations. -/
def completed (initial : FrameMem C Γ) (output : ByteSpan initial.capacity)
    (entry : World.ObservedEffects D L T) (frame : Source.CallFrame) (answer : World.FrameAnswer D L T) :
    World.CompletedCall Environment.Memory D L T :=
  ⟨answer.outcome,World.finishObserved entry frame answer,
    World.complete_data _ _ _ _ _ _ _ _ _,
    some (frameBytes (RawPhysicalCallOutput.copy initial output (World.returnData answer.outcome)))⟩

/-- Full result equality; no projection drops the Source journal, trace or
returndata. Input loading is derived from the same actual physical snapshot. -/
theorem execute_eq (initial : FrameMem C Γ) (input output : ByteSpan initial.capacity)
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
      some (completed initial output entry
        (World.childContext entry.effects.execution parent kind callee value (snapshot initial input)) answer) := by
  have loaded : World.TargetMemory.port.load (frameBytes initial)
      (P6ByteMemory.wireWord input.offset) (P6ByteMemory.wireWord input.length)=some (snapshot initial input) := by
    rw [World.TargetMemory.load_exact _ _ _ inputNonwrap,frame_snapshot_read]
    rfl
  rw [World.callAdapter_exact _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ preflight accepted loaded invoked]
  rw [RawPhysicalCallOutput.world_store initial output _ accepted]
  rfl

/-- Callee rollback preserves the complete caller entry and ordered rollback
trace, while the physical caller output still receives the revert prefix. -/
theorem revert_fields (initial : FrameMem C Γ) (output : ByteSpan initial.capacity)
    (entry : World.ObservedEffects D L T) (frame : Source.CallFrame)
    (operations : List (Source.Op D L T)) (trace : List World.Observation) (data : Solidity.Roadmap.Bytes) :
    let result := completed initial output entry frame ⟨operations,trace,.revert data⟩
    result.observed.effects.execution=entry.effects.execution ∧
    result.observed.effects.logs=entry.effects.logs ∧
    result.observed.effects.returndata=data ∧
    result.observed.trace=World.rollbackTrace entry.trace trace ∧
    result.copiedMemory=some (frameBytes (RawPhysicalCallOutput.copy initial output data)) := by
  dsimp only [completed]
  have rollback := World.finishObserved_revert entry frame operations trace data
  refine ⟨?_,?_,?_,rollback.2,rfl⟩
  · rw [rollback.1]
  · rw [rollback.1]
  · rw [rollback.1]

/-- Success retains the actual supplied operations and full ordered trace. -/
theorem success_fields (initial : FrameMem C Γ) (output : ByteSpan initial.capacity)
    (entry : World.ObservedEffects D L T) (frame : Source.CallFrame)
    (operations : List (Source.Op D L T)) (trace : List World.Observation) (data : Solidity.Roadmap.Bytes) :
    let result := completed initial output entry frame ⟨operations,trace,.success data⟩
    result.observed.effects.execution=entry.effects.execution.run operations ∧
    result.observed.trace=entry.trace++trace ∧
    result.copiedMemory=some (frameBytes (RawPhysicalCallOutput.copy initial output data)) := by
  dsimp only [completed]
  have success := World.finishObserved_success entry frame operations trace data
  exact ⟨success.1,success.2,rfl⟩
end Solidity.Yul.Adapters.RawPhysicalCallFrame
