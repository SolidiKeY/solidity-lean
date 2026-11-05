import SolidityBridge.ExternalEvm.OutcomeDriver
import SolidityBridge.ExternalEvm.Dispatch

/-! Reuse the published numeric proofs at the actual evaluator charge.
These equations concern gas-independent binary/unary opcodes only. They do
not establish gas affordability: the existing X checks remain responsible. -/
namespace Solidity.Evm.External

/-- Algebraic input adjustment, not an alternate operational driver. -/
def debitOpcodeCost (s : EvmYul.EVM.State) (cost : Nat) : EvmYul.EVM.State :=
  {s with gasAvailable := s.gasAvailable - EvmYul.UInt256.ofNat cost}

theorem EnvironmentAgrees.debitOpcodeCost {m : Machine} {s : EvmYul.EVM.State}
    (h : EnvironmentAgrees m s) (cost : Nat) :
    EnvironmentAgrees m (debitOpcodeCost s cost) :=
  ⟨h.stack, h.self, h.caller, h.value, h.time, h.balances⟩

/-- Exact full evaluator-state equality, including gas and execLength. -/
theorem BinaryOpcode.charged_dispatch (op : BinaryOpcode) (s : EvmYul.EVM.State)
    (fuel cost : Nat) :
    EvmYul.EVM.step (fuel + 1) cost (some (op.code, none)) s =
      EvmYul.EVM.step (fuel + 1) 0 (some (op.code, none)) (debitOpcodeCost s cost) := by
  rw [op.dispatch]
  cases op <;>
    change EvmYul.EVM.execBinOp _ _ = EvmYul.EVM.execBinOp _ _
  all_goals
    congr 1
    simp only [prepare, debitOpcodeCost, EvmYul.EVM.DriverProof.word_sub_zero]

theorem UnaryOpcode.charged_dispatch (op : UnaryOpcode) (s : EvmYul.EVM.State)
    (fuel cost : Nat) :
    EvmYul.EVM.step (fuel + 1) cost (some (op.code, none)) s =
      EvmYul.EVM.step (fuel + 1) 0 (some (op.code, none)) (debitOpcodeCost s cost) := by
  rw [op.dispatch]
  cases op <;>
    change EvmYul.EVM.execUnOp _ _ = EvmYul.EVM.execUnOp _ _
  all_goals
    congr 1
    simp only [prepare, debitOpcodeCost, EvmYul.EVM.DriverProof.word_sub_zero]

/-- Reuses BinaryOpcode.agrees; no arithmetic proof is copied. -/
theorem BinaryOpcode.agrees_charged (op : BinaryOpcode) (m : Machine)
    (s : EvmYul.EVM.State) (h : EnvironmentAgrees m s) (fuel cost : Nat) :
    ResultAgrees (op.instr.step m)
      (EvmYul.EVM.step (fuel + 1) cost (some (op.code, none)) s) := by
  rw [op.charged_dispatch]
  exact op.agrees m (debitOpcodeCost s cost) (h.debitOpcodeCost cost) fuel

theorem UnaryOpcode.agrees_charged (op : UnaryOpcode) (m : Machine)
    (s : EvmYul.EVM.State) (h : EnvironmentAgrees m s) (fuel cost : Nat) :
    ResultAgrees (op.instr.step m)
      (EvmYul.EVM.step (fuel + 1) cost (some (op.code, none)) s) := by
  rw [op.charged_dispatch]
  exact op.agrees m (debitOpcodeCost s cost) (h.debitOpcodeCost cost) fuel

#print axioms BinaryOpcode.charged_dispatch
#print axioms UnaryOpcode.charged_dispatch
#print axioms BinaryOpcode.agrees_charged
#print axioms UnaryOpcode.agrees_charged
end Solidity.Evm.External
