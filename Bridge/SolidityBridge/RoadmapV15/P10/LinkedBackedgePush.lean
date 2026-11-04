import SolidityBridge.RoadmapV15.P10.LinkedFallthrough

/-! Actual emitted zero-word PUSH at PC38 on the nonzero linked path. The
following JUMP, loop invariant, source origin and global correspondence remain
separate. Input alignment is derived from the existing complete byte image. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def backedgeBefore : Backend.Program :=
  LinkedJumpFixtures.before ++ [.op .JUMPI,.op .JUMPDEST]
def backedgeAfter : Backend.Program := [.op .JUMP,.op .JUMPDEST,.op .STOP]
def linkedBackedgePush (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare (linkedFallthroughNext seed a words) 3).replaceStackAndIncrPC
    ((0::words).map (fun w => UInt256.mk w.toFin)) 33

theorem linked_backedge_alignment (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack) :
    wordPushInput (linkedFallthroughNext seed a words) backedgeBefore backedgeAfter 0 words =
      linkedFallthroughNext seed a words := by
  rfl

theorem linked_backedge_prefix (valid : Array UInt256) (seed : EVM.State)
    (a : Scalar.Word) (words : Scalar.Stack) (nonzero : a ≠ 0)
    (room : words.length+2 ≤ 1024) (gas : 22 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 7 (fuel+8) valid (linkedZeroInput seed a words) =
      .ok (linkedBackedgePush seed a words) ∧
    EVM.X (fuel+8) valid (linkedZeroInput seed a words) =
      EVM.X (fuel+1) valid (linkedBackedgePush seed a words) := by
  have initialGas : 19 ≤ seed.gasAvailable.toNat := by omega
  have debit := linked_fallthrough_body_debit seed a words initialGas
  have remaining : 3 ≤ (linkedFallthroughNext seed a words).gasAvailable.toNat := by rw [debit];omega
  have pushRoom : words.length+1 ≤ 1024 := by omega
  have one := word_push_table_agreement valid (linkedFallthroughNext seed a words)
    backedgeBefore backedgeAfter 0 words (by decide) remaining pushRoom fuel
  dsimp only at one
  rw [linked_backedge_alignment] at one
  have six := linked_fallthrough_body valid seed a words nonzero room initialGas (fuel+1)
  constructor
  · rw [fetched_steps_append 6 1 (fuel+1),six.1]
    exact one.2.1
  · exact six.2.trans one.2.2

/-- Constructed gas debit; execution meaning is supplied by the prefix theorem. -/
theorem linked_backedge_debit (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack)
    (gas : 22 ≤ seed.gasAvailable.toNat) :
    (linkedBackedgePush seed a words).gasAvailable.toNat = seed.gasAvailable.toNat-22 := by
  have initialGas : 19 ≤ seed.gasAvailable.toNat := by omega
  have debit := linked_fallthrough_body_debit seed a words initialGas
  have remaining : 3 ≤ (linkedFallthroughNext seed a words).gasAvailable.toNat := by rw [debit];omega
  have last := reference_gas_debit (linkedFallthroughNext seed a words).gasAvailable 3 remaining
  change ((linkedFallthroughNext seed a words).gasAvailable-UInt256.ofNat 3).toNat = _
  rw [last,debit,Nat.sub_sub]

theorem linked_backedge_frame (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack) :
    (linkedBackedgePush seed a words).toState = (linkedZeroInput seed a words).toState ∧
    (linkedBackedgePush seed a words).memory = seed.memory ∧
    (linkedBackedgePush seed a words).activeWords = seed.activeWords ∧
    (linkedBackedgePush seed a words).returnData = seed.returnData ∧
    (linkedBackedgePush seed a words).H_return = seed.H_return ∧
    (linkedBackedgePush seed a words).stack = (0::words).map (fun w => UInt256.mk w.toFin) ∧
    (linkedBackedgePush seed a words).pc = UInt256.ofNat 71 ∧
    (linkedBackedgePush seed a words).execLength = seed.execLength+7 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms linked_backedge_alignment
#print axioms linked_backedge_prefix
#print axioms linked_backedge_debit
#print axioms linked_backedge_frame
end SolidityBridge.RoadmapV15.P10
