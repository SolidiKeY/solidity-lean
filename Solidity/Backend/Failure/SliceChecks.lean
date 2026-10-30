import Solidity.Backend.Failure.Correct

/-! Independent literal-instruction controls and emitter combination/frame
witnesses, all kernel checked. -/
namespace Solidity.Backend.Failure
open Slice

def markedMemory : Memory := fun x => UInt8.ofNat (x + 17)
def markedMachine : Machine := ⟨[⟨7, by decide⟩, ⟨9, by decide⟩], markedMemory⟩

def literalSlice : Program :=
  [.push ⟨1, by decide⟩ #v[0xaa], .push ⟨1, by decide⟩ #v[31], .op .MSTORE8,
   .push ⟨1, by decide⟩ #v[1], .push ⟨1, by decide⟩ #v[31], .op .RETURN]

theorem literal_slice_control : run literalSlice markedMachine =
    some (⟨markedMachine.stack, putByte markedMemory 31 0xaa⟩, some (.success [0xaa])) := by
  rfl

theorem underflow_control :
    step (.op .RETURN) ⟨[], markedMemory⟩ = none ∧
    step (.op .MSTORE8) ⟨[⟨31, by decide⟩], markedMemory⟩ = none := by
  constructor <;> rfl

theorem reversed_operands_control :
    (putByte markedMemory 0xaa 31) 31 ≠ (putByte markedMemory 31 0xaa) 31 := by decide

theorem truncation_control :
    step (.op .MSTORE8) ⟨[⟨31, by decide⟩, ⟨0x01aa, by decide⟩], markedMemory⟩ =
      some (⟨[], putByte markedMemory 31 0xaa⟩, none) := rfl

theorem crossing_execution_control :
    run (emit 31 (.custom [0x08, 0xc3, 0x79, 0xa0])) markedMachine =
      some (⟨markedMachine.stack, putBytes markedMemory 31 [0x08, 0xc3, 0x79, 0xa0]⟩,
        some (.revert [0x08, 0xc3, 0x79, 0xa0])) :=
  run_emit 31 (.custom [0x08, 0xc3, 0x79, 0xa0]) markedMachine (by unfold Fits Input.bytes; decide)

theorem untouched_control :
    putBytes markedMemory 31 [0x08, 0xc3, 0x79, 0xa0] 30 = markedMemory 30 ∧
    putBytes markedMemory 31 [0x08, 0xc3, 0x79, 0xa0] 35 = markedMemory 35 ∧
    putBytes markedMemory 31 [0x08, 0xc3, 0x79, 0xa0] 63 = markedMemory 63 := by decide

theorem terminal_noninterference_control :
    run (emit 31 (.returned [1, 2]) ++ emit 60 (.custom [9]) ++ [.op .INVALID]) markedMachine =
      some (⟨markedMachine.stack, putBytes markedMemory 31 [1, 2]⟩, some (.success [1, 2])) := by
  simpa only [List.append_assoc] using
    run_emit_suffix 31 (.returned [1, 2]) (emit 60 (.custom [9]) ++ [.op .INVALID])
      markedMachine (by unfold Fits Input.bytes; decide)

theorem tail_padding_control :
    getBytes (putBytes (putBytes markedMemory 31 [1, 2, 3]) 34 (List.replicate 30 0)) 31 3 = [1, 2, 3] := by
  rw [show 34 = 31 + 3 from rfl, getBytes_suffix_write]
  exact getBytes_putBytes markedMemory 31 [1, 2, 3]

theorem chunk_control : chunkWrites 30 [[1, 2], [], [3, 4, 5]] = writes 30 [1, 2, 3, 4, 5] :=
  chunkWrites_eq 30 [[1, 2], [], [3, 4, 5]]

theorem stack_limit_positive :
    stackSafe (emit 0 .empty) ⟨List.replicate 1022 ⟨7, by decide⟩, markedMemory⟩ = true := by
  rw [empty_stack_boundary 0 (by decide)]
  simp only [List.length_replicate]
  decide

theorem stack_limit_negative :
    stackSafe (emit 0 .empty) ⟨List.replicate 1023 ⟨7, by decide⟩, markedMemory⟩ ≠ true := by
  intro h
  have hb := (empty_stack_boundary 0 (by decide) _).1 h
  simp only [List.length_replicate] at hb
  omega

theorem checked_combination_control :
    checkedRun (emit 31 (.returned [1, 2]) ++ emit 60 (.custom [9])) markedMachine =
      some (⟨markedMachine.stack, putBytes markedMemory 31 [1, 2]⟩, some (.success [1, 2])) :=
  checkedRun_emit_suffix 31 (.returned [1, 2]) (emit 60 (.custom [9])) markedMachine
    (by unfold Fits Input.bytes; decide) (by decide)

/-- info: 'Solidity.Backend.Failure.checkedRun_emit_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkedRun_emit_suffix
/-- info: 'Solidity.Backend.Failure.stackSafe_emit_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stackSafe_emit_suffix

/-- info: 'Solidity.Backend.Failure.run_writes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms run_writes
/-- info: 'Solidity.Backend.Failure.run_emit_suffix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms run_emit_suffix
/-- info: 'Solidity.Backend.Failure.Slice.putBytes_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Slice.putBytes_frame
/-- info: 'Solidity.Backend.Failure.Slice.getBytes_putBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Slice.getBytes_putBytes
/-- info: 'Solidity.Backend.Failure.Slice.getBytes_suffix_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Slice.getBytes_suffix_write
/-- info: 'Solidity.Backend.Failure.chunkWrites_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms chunkWrites_eq
/-- info: 'Solidity.Backend.Failure.run_chunkWrites' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms run_chunkWrites
end Solidity.Backend.Failure
