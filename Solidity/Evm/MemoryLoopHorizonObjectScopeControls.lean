import Solidity.Evm.MemoryLoopHorizonObjectScope
import Solidity.Evm.MemoryObjectArrayExamples

/-! Drop all three pointer locals of the existing populated fixed-parent model.
The three-object heap retains complete ownership, and the actual machine stack
is unchanged. This is an inhabited strong-representation scope exit, not a
promotion from the weaker legacy heap predicate. -/
namespace Solidity.Evm.Memory.HorizonObjectScopeControls

theorem populated_drop :
    ∃ (C : Contract) (state : State C []) (base : Nat → Fin W) (machine : Machine),
      Objects.StateRepr 1 1 8 (Frag.init []) state base machine ∧
      state.H.length=3 ∧ machine.stack=[w[77]] := by
  have dropped := ObjectArrayExamples.initial_repr.drop (Γ:=[]) (.push (.push (.push .refl)))
  refine ⟨_,_,_,_,dropped,?_,?_⟩
  · rfl
  · rfl

end Solidity.Evm.Memory.HorizonObjectScopeControls
