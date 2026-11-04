import Solidity.Backend.Selection.LiteralSelection

/-! A nontrivial two-byte literal and populated protected suffix. Numeric IR
selection is tested independently of physical capacity and source coverage. -/
namespace Solidity.Backend.Selection.LiteralSelectionControls

def value : Fin Evm.W := ⟨258, by decide⟩
def chosen : InstructionCertificate (.push (.val value)) := literalCertificate value

/-- Actual Scalar execution of the selected program, not an assumed target fact. -/
theorem actual_run : Scalar.run chosen.code [7,11] = some [258,7,11] := by
  change Scalar.run [Scalar.pushWord 258] [7,11] = some [258,7,11]
  simp only [Scalar.run, Scalar.step_pushWord, Option.bind_some]

/-- The complete existing IR machine frame is preserved for arbitrary memory,
storage, balances and environment fields, not only for a zero-state witness. -/
theorem whole_machine_frame (m : Evm.Machine) :
    (Evm.Instr.push (.val value)).step { m with stack := irStack [7,11] } =
      .ok { m with stack := irStack [258,7,11] } 0 := by
  exact (chosen.success [7,11] [258,7,11]
    { m with stack := irStack [7,11] } rfl).mpr actual_run

/-- Full PUSH32 bytes in big-endian order, including both nonzero bytes. -/
theorem emitted_bytes : encode chosen.code =
    0x7f :: (List.replicate 30 0 ++ [1,2]) := rfl

theorem reject_wrong_endian_value : Scalar.run chosen.code [7,11] ≠ some [513,7,11] := by
  rw [actual_run]
  decide

/-- The actual emitted vector also excludes the swapped final two bytes. -/
theorem reject_swapped_encoding : encode chosen.code ≠
    0x7f :: (List.replicate 30 0 ++ [2,1]) := by
  rw [emitted_bytes]
  decide

theorem reject_corrupted_tail : Scalar.run chosen.code [7,11] ≠ some [258,7,12] := by
  rw [actual_run]
  decide

/-- A symbolic slot literal is refused by this numeric-literal component;
this does not classify the IR's execution or a complete compiler's verdict. -/
theorem symbolic_literal_refused (slot : Evm.Slot) :
    selectLiteral (.push (.slot slot)) = none := rfl

#print axioms actual_run
#print axioms whole_machine_frame
#print axioms emitted_bytes
#print axioms reject_wrong_endian_value
#print axioms reject_swapped_encoding
#print axioms reject_corrupted_tail
#print axioms symbolic_literal_refused

end Solidity.Backend.Selection.LiteralSelectionControls
