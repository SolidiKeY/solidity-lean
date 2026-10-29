import Solidity.Backend.Environment.ByteConstants

/-! G31 inhabited metadata controls and exact encoded-byte regressions. -/
namespace Solidity.Backend.Environment

private def sel : Fin (2 ^ 32) := ⟨0x12345678, by decide⟩
private def receiver : Address := account (lenU 0xabcdef (by decide))
private def decl : SourceFunction :=
  { name := "generated_name_must_not_be_hashed", signature := some "f(uint256)",
    callable := .abi .externalFn .selected (some sel) }

theorem declaration_selection : declarationCode decl = some (selectorCode sel) := rfl

theorem missing_metadata_refused :
    declarationCode { callable := .abi .externalFn .selected none } = none ∧
    declarationCode { callable := .constructor } = none := ⟨rfl, rfl⟩

theorem selector_opcode_bytes :
    (selectorCode sel).encode = [0x63, 0x12, 0x34, 0x56, 0x78] := by decide +kernel

theorem selector_abi_opcode_bytes :
    (selectorAbiCode sel).encode = [0x7f, 0x12, 0x34, 0x56, 0x78] ++
      List.replicate 28 0 := by decide +kernel

/-- The low-word selector and ABI bytes4 cannot be silently interchanged. -/
theorem wrong_alignment_control :
    pushStep (selectorCode sel) [] ≠ pushStep (selectorAbiCode sel) [] := by decide +kernel

theorem address_opcode_bytes :
    (addressCode receiver).encode = [0x73] ++ List.replicate 17 0 ++ [0xab, 0xcd, 0xef] := by
  decide +kernel

theorem packed_function_control :
    (packedFunction receiver sel).val / 2 ^ 32 = 0xabcdef ∧
    (packedFunction receiver sel).val % 2 ^ 32 = 0x12345678 := by decide +kernel

theorem truncation_control :
    pushStep (truncateCode 1 0x1234) [] = some [lenU 0x34 (by decide)] ∧
    pushStep (truncateCode 0 0x1234) [] = some [lenU 0 (by decide)] := by decide +kernel

/-- Numeric error/interface selectors and full event digests use their actual widths. -/
theorem metadata_width_controls :
    (metadataBytes 4 ⟨0xffffffff, by decide⟩).encode = [0x63, 0xff, 0xff, 0xff, 0xff] ∧
    (metadataBytes 32 ⟨1, by decide⟩).encode = [0x7f] ++ List.replicate 31 0 ++ [1] := by
  decide +kernel

private theorem name_utf8 : "Aλ".toUTF8.data.toList = [0x41, 0xce, 0xbb] := by
  simp only [String.toUTF8, String.utf8EncodeChar_eq_utf8EncodeCharFast]
  decide +kernel

theorem name_bytes_control :
    ∃ out : Slice,
      runData (nameCode "Aλ" 5) ⟨[lenU 9 (by decide)], fun _ => 0xee⟩ = some out ∧
      readMemory out.memory 5 3 = [0x41, 0xce, 0xbb] ∧
      out.stack = [lenU 9 (by decide)] ∧ out.memory 4 = 0xee ∧ out.memory 8 = 0xee := by
  refine ⟨⟨[lenU 9 (by decide)], writeBytes (fun _ => 0xee) 5 "Aλ".toUTF8.data.toList⟩, ?_, ?_⟩
  · exact name_correct _ _ _ (by rw [name_utf8]; decide +kernel)
  · simp only [name_utf8]
    decide +kernel

theorem byte_store_opcode_control :
    Backend.encode (byteCode ⟨5, by decide⟩ 0xab) =
      [0x60, 0xab, 0x7f] ++ List.replicate 31 0 ++ [5, 0x53] := by decide +kernel

/-- info: 'Solidity.Backend.Environment.materialize_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms materialize_correct
/-- info: 'Solidity.Backend.Environment.read_written' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms read_written

/-- info: 'Solidity.Backend.Environment.constant_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms constant_correct
/-- info: 'Solidity.Backend.Environment.selector_alignment' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms selector_alignment
/-- info: 'Solidity.Backend.Environment.function_projections' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms function_projections
/-- info: 'Solidity.Backend.Environment.selector_intrinsic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms selector_intrinsic
end Solidity.Backend.Environment
