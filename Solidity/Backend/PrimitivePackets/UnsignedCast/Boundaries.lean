import Solidity.Backend.PrimitivePackets.UnsignedCast.Transport

/-! General zero, modulus-boundary and maximum-word narrowing controls. -/
namespace Solidity.Backend.PrimitivePackets.UnsignedCast
open Solidity.Lowering.V07.UnsignedNarrowing

theorem zero_wrap (bits : Nat) (legal : Legal bits) :
    (targetTy bits legal).wrap 0 = 0 := by
  rw [wrapped, Int.zero_emod]

theorem power_wrap (bits : Nat) (legal : Legal bits) :
    (targetTy bits legal).wrap ((2 ^ bits : Nat) : Int) = 0 := by
  rw [wrapped, Int.emod_self]

theorem negative_one_mod (bits : Nat) :
    (-1 : Int) % ((2 ^ bits : Nat) : Int) = ((2 ^ bits : Nat) : Int) - 1 := by
  rw [Int.neg_emod_eq_sub_emod]
  have positive := Source.two_pow_pos bits
  apply Int.emod_eq_of_lt <;> omega

theorem maximum_wrap (bits : Nat) (legal : Legal bits) :
    (targetTy bits legal).wrap (((2 ^ 256 : Nat) : Int) - 1) =
      ((2 ^ bits : Nat) : Int) - 1 := by
  rw [wrapped]
  have relation := word_then_narrow bits (Nat.le_of_lt legal.2.2) (-1)
  change ((-1 : Int) % ((2 ^ 256 : Nat) : Int)) % ((2 ^ bits : Nat) : Int) = _ at relation
  rw [negative_one_mod 256, negative_one_mod bits] at relation
  exact relation

theorem power_source_range (bits : Nat) (legal : Legal bits) :
    Source.IntTy.u256.lo ≤ ((2 ^ bits : Nat) : Int) ∧
      ((2 ^ bits : Nat) : Int) ≤ Source.IntTy.u256.hi := by
  have nonnegative : (0 : Int) ≤ ((2 ^ bits : Nat) : Int) := Int.natCast_nonneg _
  have less := Nat.pow_lt_pow_right (by decide : 1 < 2) legal.2.2
  change 0 ≤ ((2 ^ bits : Nat) : Int) ∧ ((2 ^ bits : Nat) : Int) ≤ ((2 ^ 256 : Nat) : Int)-1
  omega

theorem not_zero_width : ¬ Legal 0 := by decide
theorem not_nonbyte_width : ¬ Legal 9 := by decide
theorem not_narrowing_256 : ¬ Legal 256 := by decide

end Solidity.Backend.PrimitivePackets.UnsignedCast
