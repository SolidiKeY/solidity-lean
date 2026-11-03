import Solidity.Yul.World.TargetCallMemory
import Solidity.Yul.World.AdapterRules

/-! A concrete target-memory normal-return rule. Unlike the equation-indexed
step-equality lemmas, its premises are the input/output port facts and actual
producer invocation. The latter is still not a reachable Source callee proof.
This is not an intrinsic Yul/G51 or resource adequacy rule. -/
namespace Solidity.Yul.World.TargetMemory
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes)
open Solidity.Backend.Environment (Memory readMemory writeBytes)

/-- Exact full observed completion, complete output bytes, and every untouched
memory byte, for either success or revert. No desired CallStep equation is a
premise. Output-copy refusal is excluded by this concrete port's extent law. -/
theorem call_output_box {D : Layout} {L T : Address → Solidity.Source.SPath → STy}
    (invoke : WorldPort D L T) (before : AdapterRules.Configuration Memory D L T)
    (parent : CallFrame) (kind : CallKind) (callee : Address)
    (gas value inputOffset inputSize outputOffset outputSize : Word)
    (input : Bytes) (answer : FrameAnswer D L T)
    (hp : callPreflight parent kind value = true)
    (ho : port.acceptOutput before.memory outputOffset outputSize = true)
    (hl : port.load before.memory inputOffset inputSize = some input)
    (hi : invoke before.observed kind callee gas
      (childContext before.observed.effects.execution parent kind callee value input) input = some answer) :
    AdapterRules.Box
      (AdapterRules.CallStep port invoke parent kind callee gas value inputOffset inputSize
        outputOffset outputSize answer.outcome)
      (fun after =>
        after.observed = finishObserved before.observed
          (childContext before.observed.effects.execution parent kind callee value input) answer ∧
        readMemory after.memory outputOffset.val
          (callOutput (returnData answer.outcome) outputSize.val).length =
          callOutput (returnData answer.outcome) outputSize.val ∧
        ∀ i, (i < outputOffset.val ∨
          outputOffset.val + min outputSize.val (returnData answer.outcome).length ≤ i) →
          after.memory i = before.memory i) before := by
  intro after hs
  obtain ⟨result, hr, _, hm, he⟩ := hs
  rw [call_output_exact invoke before.observed before.memory parent kind callee gas value
    inputOffset inputSize outputOffset outputSize input answer hp ho hl hi] at hr
  cases Option.some.inj hr
  have hm' : writeBytes before.memory outputOffset.val
      (callOutput (returnData answer.outcome) outputSize.val) = after.memory :=
    Option.some.inj hm
  refine ⟨he, ?_, ?_⟩
  · rw [← hm']
    exact Solidity.Backend.Environment.read_written _ _ _
  · intro i outside
    rw [← hm']
    apply Solidity.Backend.Environment.writeBytes_frame
    simpa only [callOutput_length] using outside

end Solidity.Yul.World.TargetMemory
