import Solidity.Backend.Passes.ShortCircuitBoundary
namespace Solidity.Backend.Passes.ShortCircuitBoundary
open Evm Evm.Memory
theorem revert_witness_iff {C : Contract} {Γ : Ctx} {b L frame : Nat} {F : Frag Γ}
    (skip : Bool) {left right : Val C Γ .bool}
    (lc : CompiledVal b F left) (rc : CompiledVal b F right)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine) (tail : List Word) :
    run (compiled skip lc rc).code {machine with stack := tail} = .revert ↔
      (left.evalT state = .error .revert ∧
        run lc.code {machine with stack := tail} = .revert) ∨
      ∃ a, left.evalT state = .ok a ∧ a ≠ skip ∧
        run lc.code {machine with stack := tail} =
          .ok ({machine with stack := tail}.push (.val (bword a))) 0 ∧
        StateRepr L b frame F state base {machine with stack := tail} ∧
        right.evalT state = .error .revert ∧
        run rc.code {machine with stack := tail} = .revert := by
  constructor
  · intro failed
    rcases (revert_iff skip lc rc represented tail).mp failed with immediate | ⟨a,ha,needed,hr⟩
    · exact .inl ⟨immediate,(value_revert_iff lc represented tail).mpr immediate⟩
    · exact .inr ⟨a,ha,needed,(execution skip lc rc represented a ha tail).1,
        represented.stack tail,hr,(value_revert_iff rc represented tail).mpr hr⟩
  · rintro (⟨immediate,_⟩ | ⟨a,ha,needed,_,_,hr,_⟩)
    · exact (revert_iff skip lc rc represented tail).mpr (.inl immediate)
    · exact (revert_iff skip lc rc represented tail).mpr (.inr ⟨a,ha,needed,hr⟩)

end Solidity.Backend.Passes.ShortCircuitBoundary
