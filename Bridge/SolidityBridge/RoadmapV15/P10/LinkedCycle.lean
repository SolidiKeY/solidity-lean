import SolidityBridge.RoadmapV15.P10.LinkedBackedgePush

/-! One finite nonzero cycle through the actual fetched JUMP0. Membership comes
from the existing linked reference certificate; no scanner equality, invariant,
infinite execution, compiler or transaction correspondence is inferred. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def linkedCycleOutput (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack) : EVM.State :=
  {Assembly.chargedPrepare (linkedBackedgePush seed a words) 8 with
    pc := UInt256.ofNat 0,stack := words.map (fun w => UInt256.mk w.toFin)}

private theorem backedge_gate (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack)
    (room : words.length+2 ≤ 1024) (gas : 30 ≤ seed.gasAvailable.toNat) :
    Assembly.driverGate LinkedJumpFixtures.program.validJumps (linkedBackedgePush seed a words) .JUMP =
      .ok (linkedBackedgePush seed a words,8) := by
  let s := linkedBackedgePush seed a words
  have first : 22 ≤ seed.gasAvailable.toNat := by omega
  have debit := linked_backedge_debit seed a words first
  have enoughGas : 8 ≤ s.gasAvailable.toNat := by rw [debit];omega
  have enough : 1 ≤ s.stack.length := by
    change 1 ≤ ((0::words).map (fun w : Scalar.Word => UInt256.mk w.toFin)).length
    simp only [List.length_map,List.length_cons];omega
  have outputRoom : s.stack.length-1 ≤ 1024 := by
    change ((0::words).map (fun w : Scalar.Word => UInt256.mk w.toFin)).length-1 ≤ 1024
    simp only [List.length_map,List.length_cons];omega
  have expansion : EVM.memoryExpansionCost s .JUMP = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  have cost : EVM.C' s .JUMP = 8 := rfl
  have member := linked_reference_member LinkedJumpFixtures.program 0 (by decide)
  have admitted : EVM.X.notIn s.stack[0]? LinkedJumpFixtures.program.validJumps = false := by
    change (!LinkedJumpFixtures.program.validJumps.contains (UInt256.ofNat 0)) = false
    rw [member]
    rfl
  change Assembly.driverGate LinkedJumpFixtures.program.validJumps s .JUMP = .ok (s,8)
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost,EVM.δ,EVM.α,Option.getD_some,Nat.add_zero,
    if_neg (Nat.not_lt_zero _),if_neg (Nat.not_lt_of_ge enoughGas),
    if_neg (Nat.not_lt_of_ge enough),if_neg (Nat.not_lt_of_ge outputRoom),
    admitted,Bool.false_eq_true,and_false,if_false]
  cases s.executionEnv.perm <;> rfl

theorem linked_cycle (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack)
    (nonzero : a ≠ 0) (room : words.length+2 ≤ 1024)
    (gas : 30 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 8 (fuel+9) LinkedJumpFixtures.program.validJumps (linkedZeroInput seed a words) =
      .ok (linkedCycleOutput seed a words) ∧
    EVM.X (fuel+9) LinkedJumpFixtures.program.validJumps (linkedZeroInput seed a words) =
      EVM.X (fuel+1) LinkedJumpFixtures.program.validJumps (linkedCycleOutput seed a words) := by
  let current := linkedBackedgePush seed a words
  have decoded : EVM.decode current.executionEnv.code current.pc = some (.JUMP,none) := by
    rfl
  have gate : Assembly.driverGate LinkedJumpFixtures.program.validJumps current .JUMP =
      .ok (current,8) := backedge_gate seed a words room gas
  have step : EVM.step (fuel+1) 8 (some (.JUMP,none)) current = .ok (linkedCycleOutput seed a words) := by
    first | rfl | rw [dispatch_jump];rfl
  have one : Assembly.driverSteps 1 (fuel+2) LinkedJumpFixtures.program.validJumps current =
      .ok (linkedCycleOutput seed a words) := by
    simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,gate,step]
  have initialGas : 22 ≤ seed.gasAvailable.toNat := by omega
  have seven := linked_backedge_prefix LinkedJumpFixtures.program.validJumps seed a words nonzero room initialGas (fuel+1)
  constructor
  · rw [fetched_steps_append 7 1 (fuel+1),seven.1]
    exact one
  · exact seven.2.trans (Assembly.X_continue fuel LinkedJumpFixtures.program.validJumps
      current current _ (.JUMP,none) 8 decoded gate step (by unfold Assembly.NonhaltingOpcode;decide))

theorem linked_cycle_debit (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack)
    (gas : 30 ≤ seed.gasAvailable.toNat) :
    (linkedCycleOutput seed a words).gasAvailable.toNat = seed.gasAvailable.toNat-30 := by
  have first : 22 ≤ seed.gasAvailable.toNat := by omega
  have debit := linked_backedge_debit seed a words first
  have enough : 8 ≤ (linkedBackedgePush seed a words).gasAvailable.toNat := by rw [debit];omega
  have last := reference_gas_debit (linkedBackedgePush seed a words).gasAvailable 8 enough
  change ((linkedBackedgePush seed a words).gasAvailable-UInt256.ofNat 8).toNat = _
  rw [last,debit,Nat.sub_sub]

theorem linked_cycle_frame (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack) :
    (linkedCycleOutput seed a words).toState = (linkedZeroInput seed a words).toState ∧
    (linkedCycleOutput seed a words).memory = seed.memory ∧
    (linkedCycleOutput seed a words).activeWords = seed.activeWords ∧
    (linkedCycleOutput seed a words).returnData = seed.returnData ∧
    (linkedCycleOutput seed a words).H_return = seed.H_return ∧
    (linkedCycleOutput seed a words).stack = words.map (fun w => UInt256.mk w.toFin) ∧
    (linkedCycleOutput seed a words).pc = UInt256.ofNat 0 ∧
    (linkedCycleOutput seed a words).execLength = seed.execLength+8 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms linked_cycle
#print axioms linked_cycle_debit
#print axioms linked_cycle_frame
end SolidityBridge.RoadmapV15.P10
