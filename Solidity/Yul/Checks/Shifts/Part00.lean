import Solidity.Yul.Words

/-! Shared shift-family vocabulary: the universal SHL/SHR/SAR laws and the
row type of the boundary-vector table. Operand 0 is the amount, operand 1 the
value. The rows themselves live in `Part01`–`Part03`; `Shifts` checks them. -/
namespace Solidity.Yul.Checks.Shifts

open Solidity.Yul

/-! ## Universal laws -/

/-- SHL is multiplication by `2 ^ amount` modulo `2 ^ 256`; zero from 256 on. -/
theorem shl_eval (xs : Fin 2 → Word) : (Pure.eval .«shl» xs).val =
    (if (xs 0).val ≥ 256 then 0 else (xs 1).val * 2 ^ (xs 0).val) % (2 ^ 256) := by
  change (if (xs 0).val ≥ 256 then word 0 else word ((xs 1).val <<< (xs 0).val)).val = _
  split <;> simp [word, Nat.shiftLeft_eq]

/-- SHR is division by `2 ^ amount`; zero from 256 on. -/
theorem shr_eval (xs : Fin 2 → Word) : (Pure.eval .«shr» xs).val =
    (if (xs 0).val ≥ 256 then 0 else (xs 1).val / 2 ^ (xs 0).val) % (2 ^ 256) := by
  change (if (xs 0).val ≥ 256 then word 0 else word ((xs 1).val >>> (xs 0).val)).val = _
  split <;> simp [word, Nat.shiftRight_eq_div_pow]

/-- A nonnegative `Int` residue is already reduced as a natural number. -/
theorem toNat_emod_mod (z : Int) (m : Nat) (hm : 0 < m) :
    (z % (m : Int)).toNat % m = (z % (m : Int)).toNat := by
  have h0 : 0 ≤ z % (m : Int) := Int.emod_nonneg _ (by omega)
  have h1 : z % (m : Int) < m := Int.emod_lt_of_pos _ (by omega)
  apply Nat.mod_eq_of_lt
  omega

/-- `iword` is the canonical residue of its integer. -/
theorem iword_val (z : Int) : (iword z).val = (z % (2 ^ 256)).toNat := by
  have h := toNat_emod_mod z (2 ^ 256) (Nat.two_pow_pos 256)
  rw [Int.natCast_pow] at h
  exact h

/-- SAR is signed floor division (`Int` `/` with a positive divisor), so
negative odd values round down; from 256 on it is the complete sign fill. -/
theorem sar_eval (xs : Fin 2 → Word) : (Pure.eval .«sar» xs).val =
    ((if (xs 0).val ≥ 256 then (if signed (xs 1) < 0 then -1 else 0)
      else signed (xs 1) / (2 ^ (xs 0).val : Int)) % (2 ^ 256)).toNat := by
  change (if (xs 0).val ≥ 256 then (if signed (xs 1) < 0 then word (2 ^ 256 - 1) else word 0)
    else iword (signed (xs 1) >>> (xs 0).val)).val = _
  split
  · split <;> decide +kernel
  · rw [iword_val, Int.shiftRight_eq_div_pow, Int.natCast_pow]
    rfl

/-! ## Boundary-vector rows -/

/-- One literal boundary vector: binary shift `op` applied to source operands
`amount` (operand 0) and `value` (operand 1) has result `expected`. -/
structure Row where
  op : Pure 2
  amount : Nat
  value : Nat
  expected : Nat

/-- The row's operands, built exactly as the original vector statements did. -/
def Row.input (r : Row) : Fin 2 → Word :=
  fun i => if i.val = 0 then word r.amount else word r.value

/-- The row's statement: evaluation yields the literal expected result. -/
def Row.Holds (r : Row) : Prop := (Pure.eval r.op r.input).val = r.expected

/-- Generic row checker, compared against the literal expected result. -/
def Row.check (r : Row) : Bool := (Pure.eval r.op r.input).val == r.expected

/-- Generic projection: a checked row holds. -/
theorem Row.holds_of_check {r : Row} (h : r.check = true) : r.Holds :=
  beq_iff_eq.1 h

/-- Every row of a list whose aggregate check succeeded holds. -/
theorem Row.holds_of_all {rows : List Row} (h : rows.all Row.check = true) :
    ∀ r ∈ rows, r.Holds :=
  fun r hr => Row.holds_of_check (List.all_eq_true.1 h r hr)

end Solidity.Yul.Checks.Shifts
