import Solidity.Yul.World.ByteMemory

/-! Concrete target-memory completion laws. The invocation equality is a real
producer obligation, not a source reachability or static-world certificate.
No alternate world/memory semantics or allocation assumption is introduced. -/
namespace Solidity.Yul.World.TargetMemory
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
open Solidity.Backend.Environment (Memory readMemory writeBytes)

/-- Actual call completion retains the entire observed result and always writes
its bounded output prefix when this concrete port accepted the output extent. -/
theorem call_output_exact {D : Solidity.Source.Layout} {L T : Solidity.Roadmap.Address → Solidity.Source.SPath → Solidity.Source.STy}
    (invoke : Solidity.Yul.World.WorldPort D L T)
    (entry : Solidity.Yul.World.ObservedEffects D L T)
    (memory : Solidity.Backend.Environment.Memory) (parent : Solidity.Source.CallFrame)
    (kind : Solidity.Yul.World.CallKind) (callee : Solidity.Roadmap.Address)
    (gas value inputOffset inputSize outputOffset outputSize : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (answer : Solidity.Yul.World.FrameAnswer D L T)
    (hp : Solidity.Yul.World.callPreflight parent kind value = true)
    (ho : Solidity.Yul.World.TargetMemory.port.acceptOutput memory outputOffset outputSize = true)
    (hl : Solidity.Yul.World.TargetMemory.port.load memory inputOffset inputSize = some input)
    (hi : invoke entry kind callee gas
      (Solidity.Yul.World.childContext entry.effects.execution parent kind callee value input) input = some answer) :
    Solidity.Yul.World.callAdapter Solidity.Yul.World.TargetMemory.port invoke entry memory parent kind callee gas value
      inputOffset inputSize outputOffset outputSize =
    some ⟨answer.outcome,
      Solidity.Yul.World.finishObserved entry (Solidity.Yul.World.childContext entry.effects.execution parent kind callee value input) answer,
      Solidity.Yul.World.complete_data _ _ _ _ _ _ _ _ _,
      some (Solidity.Backend.Environment.writeBytes memory outputOffset.val
        (Solidity.Yul.World.callOutput (Solidity.Yul.World.returnData answer.outcome) outputSize.val))⟩ := by
  simpa only [accepted_output_store memory outputOffset outputSize (returnData answer.outcome) ho] using
    (callAdapter_exact port invoke entry memory parent kind callee gas value
      inputOffset inputSize outputOffset outputSize input answer hp ho hl hi)

/-- Full byte readback of the actual truncated call output, on success OR revert.
The completed outcome, trace and full returndata are not replaced by readback. -/
theorem call_output_readback {D : Solidity.Source.Layout} {L T : Solidity.Roadmap.Address → Solidity.Source.SPath → Solidity.Source.STy}
    (invoke : Solidity.Yul.World.WorldPort D L T)
    (entry : Solidity.Yul.World.ObservedEffects D L T)
    (memory : Solidity.Backend.Environment.Memory) (parent : Solidity.Source.CallFrame)
    (kind : Solidity.Yul.World.CallKind) (callee : Solidity.Roadmap.Address)
    (gas value inputOffset inputSize outputOffset outputSize : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (answer : Solidity.Yul.World.FrameAnswer D L T)
    (hp : Solidity.Yul.World.callPreflight parent kind value = true)
    (ho : Solidity.Yul.World.TargetMemory.port.acceptOutput memory outputOffset outputSize = true)
    (hl : Solidity.Yul.World.TargetMemory.port.load memory inputOffset inputSize = some input)
    (hi : invoke entry kind callee gas
      (Solidity.Yul.World.childContext entry.effects.execution parent kind callee value input) input = some answer) :
    (callAdapter port invoke entry memory parent kind callee gas value
      inputOffset inputSize outputOffset outputSize).map
      (fun r => (r.outcome, r.observed,
        r.copiedMemory.map (fun m => readMemory m outputOffset.val
          (callOutput (returnData answer.outcome) outputSize.val).length))) =
    some (answer.outcome,
      finishObserved entry (childContext entry.effects.execution parent kind callee value input) answer,
      some (callOutput (returnData answer.outcome) outputSize.val)) := by
  rw [call_output_exact invoke entry memory parent kind callee gas value inputOffset inputSize
    outputOffset outputSize input answer hp ho hl hi]
  simp only [Option.map_some, Solidity.Backend.Environment.read_written]

/-- Every byte outside the ACTUAL returned prefix is retained, including the
unused requested output tail. The complete observed carrier is retained. -/
theorem call_output_frame {D : Solidity.Source.Layout} {L T : Solidity.Roadmap.Address → Solidity.Source.SPath → Solidity.Source.STy}
    (invoke : Solidity.Yul.World.WorldPort D L T)
    (entry : Solidity.Yul.World.ObservedEffects D L T)
    (memory : Solidity.Backend.Environment.Memory) (parent : Solidity.Source.CallFrame)
    (kind : Solidity.Yul.World.CallKind) (callee : Solidity.Roadmap.Address)
    (gas value inputOffset inputSize outputOffset outputSize : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (answer : Solidity.Yul.World.FrameAnswer D L T)
    (hp : Solidity.Yul.World.callPreflight parent kind value = true)
    (ho : Solidity.Yul.World.TargetMemory.port.acceptOutput memory outputOffset outputSize = true)
    (hl : Solidity.Yul.World.TargetMemory.port.load memory inputOffset inputSize = some input)
    (hi : invoke entry kind callee gas
      (Solidity.Yul.World.childContext entry.effects.execution parent kind callee value input) input = some answer) (i : Nat)
    (outside : i < outputOffset.val ∨
      outputOffset.val + min outputSize.val (returnData answer.outcome).length ≤ i) :
    (callAdapter port invoke entry memory parent kind callee gas value
      inputOffset inputSize outputOffset outputSize).map
      (fun r => (r.outcome, r.observed, r.copiedMemory.map (fun m => m i))) =
    some (answer.outcome,
      finishObserved entry (childContext entry.effects.execution parent kind callee value input) answer,
      some (memory i)) := by
  rw [call_output_exact invoke entry memory parent kind callee gas value inputOffset inputSize
    outputOffset outputSize input answer hp ho hl hi]
  simp only [Option.map_some]
  rw [Solidity.Backend.Environment.writeBytes_frame _ _ _ _
    (by simpa only [callOutput_length] using outside)]

end Solidity.Yul.World.TargetMemory
