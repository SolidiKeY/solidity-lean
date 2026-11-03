import SolidityBridge.RoadmapV15.P10.LinkedProgram
import SolidityBridge.RoadmapV15.P10.JumpZeroConsumer

/-! Actual nonzero-operand branch of the linked image. ISZERO's false flag is
derived from the operand; no branch/decoder/run premise is assumed. The last
PUSH/JUMP cycle and source/world/Osaka correspondence remain separate. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def linkedFallthroughOutput (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (linkedPushOutput seed a words) 10).replaceStackAndIncrPC
    (words.map (fun w => UInt256.mk w.toFin))
def linkedFallthroughNext (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (linkedFallthroughOutput seed a words) 1).incrPC

theorem linked_nonzero_alignment (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack)
    (nonzero : a ≠ 0) :
    (jumpZeroSite (linkedCompletionSite (linkedPushSeed seed a words)) (.ofNat 72)
      (words.map (fun w => UInt256.mk w.toFin))).state = linkedPushOutput seed a words := by
  have flag : Scalar.flag (a == 0) = 0 := by
    simp only [Scalar.flag,beq_eq_false_iff_ne.mpr nonzero,Bool.false_eq_true,ite_false]
  unfold linkedPushOutput
  rw [flag]
  rfl

theorem linked_fallthrough_prefix (valid : Array UInt256) (seed : EVM.State)
    (a : Scalar.Word) (words : Scalar.Stack) (nonzero : a ≠ 0)
    (room : words.length+2 ≤ 1024) (gas : 18 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 5 (fuel+6) valid (linkedZeroInput seed a words) =
      .ok (linkedFallthroughOutput seed a words) ∧
    EVM.X (fuel+6) valid (linkedZeroInput seed a words) =
      EVM.X (fuel+1) valid (linkedFallthroughOutput seed a words) := by
  have initialGas : 8 ≤ seed.gasAvailable.toNat := by omega
  have debit := linked_push_debit seed a words initialGas
  have remaining : 10 ≤ (linkedPushSeed seed a words).gasAvailable.toNat := by rw [debit];omega
  have nativeRoom : (words.map (fun w => UInt256.mk w.toFin)).length+2 ≤ 1024 := by
    simpa only [List.length_map] using room
  have one := jump_zero_agreement valid (linkedCompletionSite (linkedPushSeed seed a words))
    (.ofNat 72) (words.map (fun w => UInt256.mk w.toFin)) nativeRoom remaining fuel
  dsimp only at one
  rw [linked_nonzero_alignment seed a words nonzero] at one
  have four := linked_push_prefix valid seed a words room initialGas (fuel+1)
  constructor
  · rw [fetched_steps_append 4 1 (fuel+1),four.1]
    exact one.1
  · exact four.2.trans one.2

/-- Recipe debit; prefix above supplies its execution significance. -/
theorem linked_fallthrough_debit (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack)
    (gas : 18 ≤ seed.gasAvailable.toNat) :
    (linkedFallthroughOutput seed a words).gasAvailable.toNat = seed.gasAvailable.toNat-18 := by
  have initialGas : 8 ≤ seed.gasAvailable.toNat := by omega
  have debit : (linkedPushOutput seed a words).gasAvailable.toNat = seed.gasAvailable.toNat-8 :=
    linked_push_debit seed a words initialGas
  have remaining : 10 ≤ (linkedPushOutput seed a words).gasAvailable.toNat := by rw [debit];omega
  have last := reference_gas_debit (linkedPushOutput seed a words).gasAvailable 10 remaining
  change ((linkedPushOutput seed a words).gasAvailable-UInt256.ofNat 10).toNat = _
  rw [last,debit,Nat.sub_sub]

theorem linked_fallthrough_body (valid : Array UInt256) (seed : EVM.State)
    (a : Scalar.Word) (words : Scalar.Stack) (nonzero : a ≠ 0)
    (room : words.length+2 ≤ 1024) (gas : 19 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 6 (fuel+7) valid (linkedZeroInput seed a words) =
      .ok (linkedFallthroughNext seed a words) ∧
    EVM.X (fuel+7) valid (linkedZeroInput seed a words) =
      EVM.X (fuel+1) valid (linkedFallthroughNext seed a words) := by
  have initialGas : 18 ≤ seed.gasAvailable.toNat := by omega
  have debit := linked_fallthrough_debit seed a words initialGas
  have remaining : 1 ≤ (linkedFallthroughOutput seed a words).gasAvailable.toNat := by rw [debit];omega
  have capacity : (linkedFallthroughOutput seed a words).stack.length ≤ 1024 := by
    change (words.map (fun w => UInt256.mk w.toFin)).length ≤ 1024
    rw [List.length_map]
    omega
  have decoded : EVM.decode (linkedFallthroughOutput seed a words).executionEnv.code
      (linkedFallthroughOutput seed a words).pc = some (.JUMPDEST,none) := by rfl
  have gate := completion_terminal_gate valid (linkedFallthroughOutput seed a words) .JUMPDEST 1
    (Or.inl ⟨rfl,rfl⟩) remaining capacity
  have step : EVM.step (fuel+1) 1 (some (.JUMPDEST,none)) (linkedFallthroughOutput seed a words) =
      .ok (linkedFallthroughNext seed a words) := by rfl
  have one : Assembly.driverSteps 1 (fuel+2) valid (linkedFallthroughOutput seed a words) =
      .ok (linkedFallthroughNext seed a words) := by
    simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind,gate,step]
  have five := linked_fallthrough_prefix valid seed a words nonzero room initialGas (fuel+1)
  constructor
  · rw [fetched_steps_append 5 1 (fuel+1),five.1]
    exact one
  · exact five.2.trans (Assembly.X_continue fuel valid _ _ _ (.JUMPDEST,none) 1 decoded gate step
      (by unfold Assembly.NonhaltingOpcode;decide))

theorem linked_fallthrough_body_debit (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack)
    (gas : 19 ≤ seed.gasAvailable.toNat) :
    (linkedFallthroughNext seed a words).gasAvailable.toNat = seed.gasAvailable.toNat-19 := by
  have initialGas : 18 ≤ seed.gasAvailable.toNat := by omega
  have debit := linked_fallthrough_debit seed a words initialGas
  have remaining : 1 ≤ (linkedFallthroughOutput seed a words).gasAvailable.toNat := by rw [debit];omega
  have last := reference_gas_debit (linkedFallthroughOutput seed a words).gasAvailable 1 remaining
  change ((linkedFallthroughOutput seed a words).gasAvailable-UInt256.ofNat 1).toNat = _
  rw [last,debit,Nat.sub_sub]

theorem linked_fallthrough_frame (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack) :
    (linkedFallthroughNext seed a words).toState = (linkedZeroInput seed a words).toState ∧
    (linkedFallthroughNext seed a words).memory = seed.memory ∧
    (linkedFallthroughNext seed a words).activeWords = seed.activeWords ∧
    (linkedFallthroughNext seed a words).returnData = seed.returnData ∧
    (linkedFallthroughNext seed a words).H_return = seed.H_return ∧
    (linkedFallthroughNext seed a words).stack = words.map (fun w => UInt256.mk w.toFin) ∧
    (linkedFallthroughNext seed a words).pc = UInt256.ofNat 38 ∧
    (linkedFallthroughNext seed a words).execLength = seed.execLength+6 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms linked_nonzero_alignment
#print axioms linked_fallthrough_prefix
#print axioms linked_fallthrough_debit
#print axioms linked_fallthrough_body
#print axioms linked_fallthrough_body_debit
#print axioms linked_fallthrough_frame
end SolidityBridge.RoadmapV15.P10
