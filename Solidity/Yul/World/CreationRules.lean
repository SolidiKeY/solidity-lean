import Solidity.Yul.World.CreationFrames
import Solidity.Yul.World.AdapterRules

/-! Lean-only exact normal-return constructor-consumer rules. Not CREATE opcode
adequacy or source dl/G51 rules. Initialization Outcome includes runtime code;
the caller's buffer is separately fixed by CompletedCreation.returndata_eq. -/
namespace Solidity.Yul.World.CreationRules
open Solidity.Source
open Solidity.Roadmap (Address Word Outcome)
open Solidity.Yul.World.AdapterRules (Configuration Box)
variable {D : Layout} {L T : Address → SPath → STy} {Memory : Type}

def InitStep (port : BytePort Memory) (invoke : InitcodePort D L T) (parent : CallFrame)
    (allocated : Address) (gas value offset size : Word) (initialization : Outcome)
    (before after : Configuration Memory D L T) : Prop :=
  ∃ result, initcodeAdapter port invoke before.observed before.memory parent allocated gas value offset size = some result ∧
    result.initialization = initialization ∧ after.observed = result.observed ∧ after.memory = before.memory

theorem initcode_rule (port : BytePort Memory) (invoke : InitcodePort D L T) (parent : CallFrame)
    (allocated : Address) (gas value offset size : Word) (before : Configuration Memory D L T)
    (result : CompletedCreation D L T)
    (h : initcodeAdapter port invoke before.observed before.memory parent allocated gas value offset size = some result) :
    Box (InitStep port invoke parent allocated gas value offset size result.initialization)
      (fun after => after.observed = result.observed ∧ after.memory = before.memory ∧
        after.observed.effects.returndata = createReturnData result.initialization) before := by
  intro after hs
  obtain ⟨r,hr,_,he,hm⟩ := hs
  rw [h] at hr
  cases Option.some.inj hr
  refine ⟨he,hm,?_⟩
  rw [he]
  exact result.returndata_eq

theorem static_initcode_rule (port : BytePort Memory) (invoke : InitcodePort D L T) (parent : CallFrame)
    (allocated : Address) (gas value offset size : Word) (initialization : Outcome)
    (before : Configuration Memory D L T) (h : parent.static = true) :
    Box (InitStep port invoke parent allocated gas value offset size initialization) (fun _ => False) before := by
  intro after hs
  obtain ⟨result,hr,_⟩ := hs
  rw [initcodeAdapter_static _ _ _ _ _ _ _ _ _ _ h] at hr
  cases hr

end Solidity.Yul.World.CreationRules
