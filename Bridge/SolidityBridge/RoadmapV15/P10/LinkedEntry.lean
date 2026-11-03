import SolidityBridge.RoadmapV15.P10.LinkedCompletionLayout
import SolidityBridge.RoadmapV15.P10.ExponentConsumer

/-! Actual first two fetched JUMPDESTs of the existing linked image. This
reaches byte two with two charges; no source origin or remaining run is assumed. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def linkedEntryInput (seed : EVM.State) (words : List UInt256) : EVM.State :=
  {linkedCompletionInput seed [] with pc := .ofNat 0,stack := words}
def linkedEntryFirst (seed : EVM.State) (words : List UInt256) : EVM.State :=
  (Assembly.chargedPrepare (linkedEntryInput seed words) 1).incrPC
def linkedEntryNext (seed : EVM.State) (words : List UInt256) : EVM.State :=
  (Assembly.chargedPrepare (linkedEntryFirst seed words) 1).incrPC

/-- Both counted steps and X continuation, with original gas/capacity clauses. -/
theorem linked_entry_prefix (valid : Array UInt256) (seed : EVM.State)
    (words : List UInt256) (room : words.length ≤ 1024)
    (gas : 2 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 2 (fuel+3) valid (linkedEntryInput seed words) =
      .ok (linkedEntryNext seed words) ∧
    EVM.X (fuel+3) valid (linkedEntryInput seed words) =
      EVM.X (fuel+1) valid (linkedEntryNext seed words) := by
  have enough : 1 ≤ seed.gasAvailable.toNat := by omega
  have debit : (linkedEntryFirst seed words).gasAvailable.toNat = seed.gasAvailable.toNat-1 :=
    reference_gas_debit seed.gasAvailable 1 enough
  have nextGas : 1 ≤ (linkedEntryFirst seed words).gasAvailable.toNat := by rw [debit];omega
  have d0 : EVM.decode (linkedEntryInput seed words).executionEnv.code
      (linkedEntryInput seed words).pc = some (.JUMPDEST,none) := by rfl
  have d1 : EVM.decode (linkedEntryFirst seed words).executionEnv.code
      (linkedEntryFirst seed words).pc = some (.JUMPDEST,none) := by rfl
  have g0 := completion_terminal_gate valid (linkedEntryInput seed words) .JUMPDEST 1
    (Or.inl ⟨rfl,rfl⟩) enough room
  have g1 := completion_terminal_gate valid (linkedEntryFirst seed words) .JUMPDEST 1
    (Or.inl ⟨rfl,rfl⟩) nextGas room
  have s0 : EVM.step (fuel+2) 1 (some (.JUMPDEST,none)) (linkedEntryInput seed words) =
      .ok (linkedEntryFirst seed words) := by rfl
  have s1 : EVM.step (fuel+1) 1 (some (.JUMPDEST,none)) (linkedEntryFirst seed words) =
      .ok (linkedEntryNext seed words) := by rfl
  have c0 : Assembly.driverSteps 1 (fuel+3) valid (linkedEntryInput seed words) =
      .ok (linkedEntryFirst seed words) := by
    simp only [Assembly.driverSteps,d0,Option.option,bind,Except.bind,g0,s0]
  have c1 : Assembly.driverSteps 1 (fuel+2) valid (linkedEntryFirst seed words) =
      .ok (linkedEntryNext seed words) := by
    simp only [Assembly.driverSteps,d1,Option.option,bind,Except.bind,g1,s1]
  constructor
  · rw [fetched_steps_cons 1 (fuel+1),c0]
    exact c1
  · exact (Assembly.X_continue (fuel+1) valid _ _ _ (.JUMPDEST,none) 1 d0 g0 s0
      (by unfold Assembly.NonhaltingOpcode;decide)).trans
      (Assembly.X_continue fuel valid _ _ _ (.JUMPDEST,none) 1 d1 g1 s1
        (by unfold Assembly.NonhaltingOpcode;decide))

/-- Natural debit is exact when the prefix is adequately funded. -/
theorem linked_entry_debit (seed : EVM.State) (words : List UInt256)
    (gas : 2 ≤ seed.gasAvailable.toNat) :
    (linkedEntryNext seed words).gasAvailable.toNat = seed.gasAvailable.toNat-2 := by
  have enough : 1 ≤ seed.gasAvailable.toNat := by omega
  have first := reference_gas_debit seed.gasAvailable 1 enough
  have nextEnough : 1 ≤ (seed.gasAvailable-UInt256.ofNat 1).toNat := by rw [first];omega
  have second := reference_gas_debit (seed.gasAvailable-UInt256.ofNat 1) 1 nextEnough
  change ((seed.gasAvailable-UInt256.ofNat 1)-UInt256.ofNat 1).toNat = _
  rw [second,first,Nat.sub_sub]

/-- Constructed output observations become execution effects via prefix above;
the seed's original PC/code/stack are explicitly replaced at represented entry. -/
theorem linked_entry_frame (seed : EVM.State) (words : List UInt256) :
    (linkedEntryNext seed words).toState = (linkedEntryInput seed words).toState ∧
    (linkedEntryNext seed words).memory = seed.memory ∧
    (linkedEntryNext seed words).activeWords = seed.activeWords ∧
    (linkedEntryNext seed words).returnData = seed.returnData ∧
    (linkedEntryNext seed words).H_return = seed.H_return ∧
    (linkedEntryNext seed words).stack = words ∧
    (linkedEntryNext seed words).pc = UInt256.ofNat 2 ∧
    (linkedEntryNext seed words).execLength = seed.execLength+2 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms linked_entry_prefix
#print axioms linked_entry_debit
#print axioms linked_entry_frame
end SolidityBridge.RoadmapV15.P10
