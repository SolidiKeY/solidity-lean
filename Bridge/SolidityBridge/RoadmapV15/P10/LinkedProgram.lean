import SolidityBridge.RoadmapV15.P10.LinkedZero
import SolidityBridge.RoadmapV15.P10.NonbranchTables
import SolidityBridge.RoadmapV15.P10.LinkedCompletion

/-! Actual PUSH32 continuation and the zero-operand exit of the existing linked
image. This is a particular reference-program theorem with its supplied linked
array, not compiler origin, opaque D_J equality or Osaka/transaction closure. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def linkedPushSeed (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack) : EVM.State :=
  Assembly.chargedPrepare (linkedZeroOutput seed a words) 3
def linkedPushOutput (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack) : EVM.State :=
  (linkedPushSeed seed a words).replaceStackAndIncrPC
    ((72::Scalar.flag (a == 0)::words).map (fun w => UInt256.mk w.toFin)) 33

theorem linked_push_alignment (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack) :
    wordPushInput (linkedZeroOutput seed a words)
      [.op .JUMPDEST,.op .JUMPDEST,.op .ISZERO]
      (.op .JUMPI::LinkedJumpFixtures.after) 72 (Scalar.flag (a == 0)::words) =
      linkedZeroOutput seed a words := by rfl

theorem linked_push_prefix (valid : Array UInt256) (seed : EVM.State)
    (a : Scalar.Word) (words : Scalar.Stack) (room : words.length+2 ≤ 1024)
    (gas : 8 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Assembly.driverSteps 4 (fuel+5) valid (linkedZeroInput seed a words) =
      .ok (linkedPushOutput seed a words) ∧
    EVM.X (fuel+5) valid (linkedZeroInput seed a words) =
      EVM.X (fuel+1) valid (linkedPushOutput seed a words) := by
  have initialGas : 5 ≤ seed.gasAvailable.toNat := by omega
  have initialRoom : words.length+1 ≤ 1024 := by omega
  have debit := linked_zero_debit seed a words initialGas
  have remaining : 3 ≤ (linkedZeroOutput seed a words).gasAvailable.toNat := by rw [debit];omega
  have pushRoom : (Scalar.flag (a == 0)::words).length+1 ≤ 1024 := by
    simp only [List.length_cons];omega
  have one := word_push_table_agreement valid (linkedZeroOutput seed a words)
    [.op .JUMPDEST,.op .JUMPDEST,.op .ISZERO] (.op .JUMPI::LinkedJumpFixtures.after)
    72 (Scalar.flag (a == 0)::words) (by decide) remaining pushRoom fuel
  dsimp only at one
  rw [linked_push_alignment] at one
  have three := linked_zero_prefix valid seed a words initialRoom initialGas (fuel+1)
  constructor
  · rw [fetched_steps_append 3 1 (fuel+1),three.2.1]
    exact one.2.1
  · exact three.2.2.trans one.2.2

theorem linked_push_debit (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack)
    (gas : 8 ≤ seed.gasAvailable.toNat) :
    (linkedPushSeed seed a words).gasAvailable.toNat = seed.gasAvailable.toNat-8 := by
  have initialGas : 5 ≤ seed.gasAvailable.toNat := by omega
  have debit := linked_zero_debit seed a words initialGas
  have remaining : 3 ≤ (linkedZeroOutput seed a words).gasAvailable.toNat := by rw [debit];omega
  have last := reference_gas_debit (linkedZeroOutput seed a words).gasAvailable 3 remaining
  change ((linkedZeroOutput seed a words).gasAvailable-UInt256.ofNat 3).toNat = _
  rw [last,debit,Nat.sub_sub]

theorem linked_zero_branch_alignment (seed : EVM.State) (words : Scalar.Stack) :
    linkedPushOutput seed 0 words =
      linkedCompletionInput (linkedPushSeed seed 0 words) (words.map (fun w => UInt256.mk w.toFin)) := by rfl

def linkedProgramOutput (seed : EVM.State) (words : Scalar.Stack) : EVM.State :=
  linkedCompletionOutput (linkedPushSeed seed 0 words) (words.map (fun w => UInt256.mk w.toFin))

/-- All seven fetched opcodes of this zero-operand path terminate at explicit
STOP73. Source-frame origin, account execution and global resources are open. -/
theorem linked_program_exit (seed : EVM.State) (words : Scalar.Stack)
    (room : words.length+2 ≤ 1024) (gas : 19 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    EVM.X (fuel+8) LinkedJumpFixtures.program.validJumps (linkedZeroInput seed 0 words) =
      .ok (.success (linkedProgramOutput seed words) .empty) := by
  have initialGas : 8 ≤ seed.gasAvailable.toNat := by omega
  have debit := linked_push_debit seed 0 words initialGas
  have remaining : 11 ≤ (linkedPushSeed seed 0 words).gasAvailable.toNat := by rw [debit];omega
  have nativeRoom : (words.map (fun w => UInt256.mk w.toFin)).length+2 ≤ 1024 := by
    simpa only [List.length_map] using room
  have front := (linked_push_prefix LinkedJumpFixtures.program.validJumps seed 0 words room initialGas (fuel+3)).2
  rw [linked_zero_branch_alignment] at front
  exact front.trans (linked_completion_execution _ _ nativeRoom remaining fuel)

theorem linked_program_debit (seed : EVM.State) (words : Scalar.Stack)
    (gas : 19 ≤ seed.gasAvailable.toNat) :
    (linkedProgramOutput seed words).gasAvailable.toNat = seed.gasAvailable.toNat-19 := by
  have initialGas : 8 ≤ seed.gasAvailable.toNat := by omega
  have first := linked_push_debit seed 0 words initialGas
  have remaining : 11 ≤ (linkedPushSeed seed 0 words).gasAvailable.toNat := by rw [first];omega
  have last := linked_completion_debit (linkedPushSeed seed 0 words)
    (words.map (fun w => UInt256.mk w.toFin)) remaining
  change (linkedCompletionOutput _ _).gasAvailable.toNat = _
  rw [last,first,Nat.sub_sub]

theorem linked_program_frame (seed : EVM.State) (words : Scalar.Stack) :
    (linkedProgramOutput seed words).toState = (linkedZeroInput seed 0 words).toState ∧
    (linkedProgramOutput seed words).memory = seed.memory ∧
    (linkedProgramOutput seed words).activeWords = seed.activeWords ∧
    (linkedProgramOutput seed words).returnData = .empty ∧
    (linkedProgramOutput seed words).H_return = seed.H_return ∧
    (linkedProgramOutput seed words).stack = words.map (fun w => UInt256.mk w.toFin) ∧
    (linkedProgramOutput seed words).pc = UInt256.ofNat 73 ∧
    (linkedProgramOutput seed words).execLength = seed.execLength+7 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms linked_push_alignment
#print axioms linked_push_prefix
#print axioms linked_push_debit
#print axioms linked_zero_branch_alignment
#print axioms linked_program_exit
#print axioms linked_program_debit
#print axioms linked_program_frame
end SolidityBridge.RoadmapV15.P10
