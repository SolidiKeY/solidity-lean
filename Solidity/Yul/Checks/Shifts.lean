import Solidity.Yul.Checks.Shifts.Part00
import Solidity.Yul.Checks.Shifts.Part01
import Solidity.Yul.Checks.Shifts.Part02
import Solidity.Yul.Checks.Shifts.Part03

/-! Shift family: 3885 literal boundary vectors (1295 each of SHL, SHR, SAR),
checked by one kernel decision, and the universal law for all words. -/
namespace Solidity.Yul.Checks.Shifts

/-- The whole family table, in original vector order (`v0000`–`v3884`). -/
noncomputable def rows : List Row := shlRows ++ shrRows ++ sarRows

/-- One aggregate kernel decision over every row. -/
theorem rows_check : rows.all Row.check = true := by decide +kernel

/-- Every literal vector holds. -/
theorem rows_hold : ∀ r ∈ rows, r.Holds := Row.holds_of_all rows_check

/-- SHL, SHR and SAR agree with their arithmetic specification on all words.
This is `Solidity.Goals.opcodeShifts` with `OpcodeSpec.modulus` and
`OpcodeSpec.residue` unfolded: the core may not import `Solidity.Goals.Plan`
(`scripts/check-layers.mjs` core closure), so a consumer that imports it
ascribes `(universal : Solidity.Goals.opcodeShifts)` by definitional unfolding. -/
theorem universal :
    (∀ xs : Fin 2 → Word, (Pure.eval .«shl» xs).val =
      (if (xs 0).val ≥ 256 then 0 else (xs 1).val * 2 ^ (xs 0).val) % (2 ^ 256)) ∧
    (∀ xs : Fin 2 → Word, (Pure.eval .«shr» xs).val =
      (if (xs 0).val ≥ 256 then 0 else (xs 1).val / 2 ^ (xs 0).val) % (2 ^ 256)) ∧
    (∀ xs : Fin 2 → Word, (Pure.eval .«sar» xs).val =
      ((if (xs 0).val ≥ 256 then (if signed (xs 1) < 0 then -1 else 0)
        else signed (xs 1) / (2 ^ (xs 0).val : Int)) % (2 ^ 256)).toNat) :=
  ⟨shl_eval, shr_eval, sar_eval⟩

end Solidity.Yul.Checks.Shifts

