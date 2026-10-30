import Solidity.Backend.Failure.Emit
import Solidity.Backend.Failure.Gap

/-! Inhabited kernel controls for checkpoint 1, including exact opcode bytes.
These are internal vectors, not external-EVM agreement claims. -/
namespace Solidity.Backend.Failure

theorem empty_vector : encode (emit 0 .empty) =
    [0x7f] ++ List.replicate 32 0 ++ [0x7f] ++ List.replicate 32 0 ++ [0xfd] := by decide

theorem custom_vector : encode (emit 5 (.custom [0xaa])) =
    [0x60, 0xaa, 0x7f] ++ List.replicate 31 0 ++ [5, 0x53, 0x7f] ++
    List.replicate 31 0 ++ [1, 0x7f] ++ List.replicate 31 0 ++ [5, 0xfd] := by decide

theorem panic_control : (Input.panic ⟨1, by decide⟩).bytes.length = 36 ∧
    (Input.panic ⟨1, by decide⟩).bytes.take 4 = Semantics.panicSelector ∧
    (Input.panic ⟨1, by decide⟩).bytes.drop 32 = [0, 0, 0, 1] := by decide

theorem crossing_control :
    writes 7 (List.replicate 32 0xaa ++ [0xbb]) =
    writes 7 (List.replicate 32 0xaa) ++ [pushByte 0xbb, pushNat 39, .op .MSTORE8] := by
  rw [writes_append]
  rfl

theorem reason_control : (Input.reason (List.replicate 33 0x78)).bytes.length = 132 := by
  rw [reason_length, List.length_replicate]

theorem return_control : emit 5 (.returned [0xaa]) =
    writes 5 [0xaa] ++ [pushNat 1, pushNat 5, .op .RETURN] := rfl

theorem negative_controls :
    emit 0 (.custom [1]) ≠ emit 0 (.returned [1]) ∧
    emit 0 (.custom [1]) ≠ emit 1 (.custom [1]) ∧
    emit 0 (.custom [1, 2]) ≠ emit 0 (.custom [2, 1]) ∧
    readImmediate (digits 32 0x0102) ≠ 0x0201 := by decide

theorem combination_control :
    writes 31 [0x08, 0xc3] ++ writes 33 [0x79, 0xa0] = writes 31 Semantics.errorSelector := by decide

/-- info: 'Solidity.Backend.Failure.digits_fold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms digits_fold
/-- info: 'Solidity.Backend.Failure.read_digits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms read_digits
/-- info: 'Solidity.Backend.Failure.writes_decompose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms writes_decompose
/-- info: 'Solidity.Backend.Failure.writes_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms writes_append
/-- info: 'Solidity.Backend.Failure.panic_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms panic_length
/-- info: 'Solidity.Backend.Failure.reason_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reason_length
/-- info: 'Solidity.Backend.Failure.empty_vector' depends on axioms: [propext] -/
#guard_msgs in
#print axioms empty_vector
/-- info: 'Solidity.Backend.Failure.negative_controls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms negative_controls
end Solidity.Backend.Failure
