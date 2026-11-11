import Solidity.Yul.Checks.Shifts.Part00
import Solidity.Yul.Checks.Shifts.Part01
import Solidity.Yul.Checks.Shifts.Part02
import Solidity.Yul.Checks.Shifts.Part03
import Solidity.Yul.OpcodeSpec

/-! Shift family: 3885 literal boundary vectors (1295 each of SHL, SHR, SAR),
checked by one kernel decision, and the universal law for all words. -/
namespace Solidity.Yul.Checks.Shifts

/-- The whole family table, in original vector order (`v0000`–`v3884`). -/
noncomputable def rows : List Row := shlRows ++ shrRows ++ sarRows

/-- One aggregate kernel decision over every row. -/
theorem rows_check : rows.all Row.check = true := by decide +kernel

/-- Every literal vector holds. -/
theorem rows_hold : ∀ r ∈ rows, r.Holds := Row.holds_of_all rows_check

/-- SHL, SHR and SAR agree with their arithmetic specification on all words
(`Solidity.Goals.opcodeShifts` is a definitional wrapper of this statement). -/
theorem universal : OpcodeSpec.shifts :=
  ⟨shl_eval, shr_eval, sar_eval⟩

end Solidity.Yul.Checks.Shifts

