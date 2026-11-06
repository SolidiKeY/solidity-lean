import SolidityBridge.RoadmapV15.P10.LinkedEntry
import SolidityBridge.RoadmapV15.P10.BooleanNotConsumer
import SolidityBridge.RoadmapV15.P10.CountedAppend

/-! Actual linked-entry execution through ISZERO for arbitrary scalar words.
The existing primitive producer supplies the word/step facts; source/compiler
origin and the following PUSH/JUMPI are not assumed executed. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def linkedZeroInput (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack) : EVM.State :=
  linkedEntryInput seed ((a::words).map (fun w => UInt256.mk w.toFin))
def linkedZeroSite (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack) : Site .ISZERO :=
  ⟨linkedEntryNext seed ((a::words).map (fun w => UInt256.mk w.toFin)),
    [.op .JUMPDEST,.op .JUMPDEST],
    Scalar.pushWord 72 :: .op .JUMPI :: LinkedJumpFixtures.after,by decide⟩
def linkedZeroOutput (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack) : EVM.State :=
  (Assembly.chargedPrepare
    (linkedEntryNext seed ((a::words).map (fun w => UInt256.mk w.toFin))) 3).replaceStackAndIncrPC
      ((Scalar.flag (a == 0)::words).map (fun w => UInt256.mk w.toFin))

/-- Exact current state and emitted code alignment, not a representation premise. -/
theorem linked_zero_alignment (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack) :
    (modularSite (linkedZeroSite seed a words) (a::words)).state =
      linkedEntryNext seed ((a::words).map (fun w => UInt256.mk w.toFin)) := by rfl

theorem linked_zero_prefix (valid : Array UInt256) (seed : EVM.State)
    (a : Scalar.Word) (words : Scalar.Stack) (room : words.length+1 ≤ 1024)
    (gas : 5 ≤ seed.gasAvailable.toNat) (fuel : Nat) :
    Scalar.step (.op .ISZERO) (a::words) = some (Scalar.flag (a == 0)::words) ∧
    Assembly.driverSteps 3 (fuel+4) valid (linkedZeroInput seed a words) =
      .ok (linkedZeroOutput seed a words) ∧
    EVM.X (fuel+4) valid (linkedZeroInput seed a words) =
      EVM.X (fuel+1) valid (linkedZeroOutput seed a words) := by
  have initialGas : 2 ≤ seed.gasAvailable.toNat := by omega
  have capacity : ((a::words).map (fun w => UInt256.mk w.toFin)).length ≤ 1024 := by
    simpa only [List.length_map,List.length_cons] using room
  have debit := linked_entry_debit seed ((a::words).map (fun w => UInt256.mk w.toFin)) initialGas
  have remaining : 3 ≤ (linkedZeroSite seed a words).seed.gasAvailable.toNat := by
    change 3 ≤ (linkedEntryNext seed ((a::words).map (fun w => UInt256.mk w.toFin))).gasAvailable.toNat
    rw [debit]
    omega
  have one := iszero_agreement valid (linkedZeroSite seed a words) a words room remaining fuel
  dsimp only at one
  rw [linked_zero_alignment] at one
  have two := linked_entry_prefix valid seed ((a::words).map (fun w => UInt256.mk w.toFin))
    capacity initialGas (fuel+1)
  refine ⟨one.1,?_,two.2.trans one.2.2⟩
  change Assembly.driverSteps 3 (fuel+4) valid (linkedEntryInput seed _) = _
  rw [fetched_steps_append 2 1 (fuel+1),two.1]
  exact one.2.1

theorem linked_zero_debit (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack)
    (gas : 5 ≤ seed.gasAvailable.toNat) :
    (linkedZeroOutput seed a words).gasAvailable.toNat = seed.gasAvailable.toNat-5 := by
  have initialGas : 2 ≤ seed.gasAvailable.toNat := by omega
  have debit := linked_entry_debit seed ((a::words).map (fun w => UInt256.mk w.toFin)) initialGas
  have remaining : 3 ≤ (linkedEntryNext seed ((a::words).map (fun w => UInt256.mk w.toFin))).gasAvailable.toNat := by
    rw [debit];omega
  have last := reference_gas_debit
    (linkedEntryNext seed ((a::words).map (fun w => UInt256.mk w.toFin))).gasAvailable 3 remaining
  change ((linkedEntryNext seed ((a::words).map (fun w => UInt256.mk w.toFin))).gasAvailable-UInt256.ofNat 3).toNat = _
  rw [last,debit,Nat.sub_sub]

theorem linked_zero_frame (seed : EVM.State) (a : Scalar.Word) (words : Scalar.Stack) :
    (linkedZeroOutput seed a words).toState = (linkedZeroInput seed a words).toState ∧
    (linkedZeroOutput seed a words).memory = seed.memory ∧
    (linkedZeroOutput seed a words).activeWords = seed.activeWords ∧
    (linkedZeroOutput seed a words).returnData = seed.returnData ∧
    (linkedZeroOutput seed a words).H_return = seed.H_return ∧
    (linkedZeroOutput seed a words).stack =
      ((Scalar.flag (a == 0)::words).map (fun w => UInt256.mk w.toFin)) ∧
    (linkedZeroOutput seed a words).pc = UInt256.ofNat 3 ∧
    (linkedZeroOutput seed a words).execLength = seed.execLength+3 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms linked_zero_alignment
#print axioms linked_zero_prefix
#print axioms linked_zero_debit
#print axioms linked_zero_frame
end SolidityBridge.RoadmapV15.P10
