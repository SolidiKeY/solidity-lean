import SolidityBridge.HashBridge.Queries

/-! Cost-parameterized actual evaluator component. Affordability, fetch and
memory expansion remain the preceding driver's obligations; this is not X. -/
namespace Solidity.HashBridge
open EvmYul

theorem keccak_step_cost (fuel cost : Nat) (s : EvmYul.EVM.State)
    (offset size : UInt256) (tail : List UInt256)
    (hs : s.stack = offset :: size :: tail) :
    ∃ out, EvmYul.EVM.step (fuel+1) cost (some (.KECCAK256,none)) s = .ok out ∧
      out.stack = actualDigest (machineQuery s.toMachineState offset size) :: tail ∧
      out.toState = s.toState ∧ out.memory = s.memory ∧
      out.activeWords = .ofNat (MachineState.M s.activeWords.toNat offset.toNat size.toNat) ∧
      out.gasAvailable = s.gasAvailable - .ofNat cost ∧ out.pc = s.pc + .ofNat 1 ∧
      out.execLength = s.execLength + 1 ∧ out.returnData = s.returnData ∧ out.H_return = s.H_return := by
  let pre : EvmYul.EVM.State := {s with execLength := s.execLength+1, gasAvailable := s.gasAvailable - .ofNat cost}
  let pair : UInt256 × MachineState := pre.toMachineState.keccak256 offset size
  let next : EvmYul.EVM.State :=
    ({pre with toMachineState := pair.2}).replaceStackAndIncrPC (pair.1 :: tail)
  refine ⟨next,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have result : EvmYul.EVM.step (fuel+1) cost (some (.KECCAK256,none))
      {s with stack := offset :: size :: tail} = .ok next := rfl
  rw [← hs] at result
  exact result

end Solidity.HashBridge
