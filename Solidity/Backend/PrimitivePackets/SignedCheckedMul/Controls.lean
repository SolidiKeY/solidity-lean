import Solidity.Backend.PrimitivePackets.SignedCheckedMul.Agreement

/-! Boundary classification controls. These supplement, and do not replace,
the arbitrary-state selected-code agreement theorems. -/
namespace Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls

def fits (x : Int) : Prop := U.lo ≤ x ∧ x ≤ U.hi
instance (x : Int) : Decidable (fits x) := inferInstanceAs (Decidable (_ ∧ _))

theorem minimum_times_minus_one : ¬ fits (U.lo * (-1)) := by decide +kernel
theorem minus_one_times_minimum : ¬ fits ((-1) * U.lo) := by decide +kernel
theorem minimum_times_one : fits (U.lo * 1) := by decide +kernel
theorem minimum_times_zero : fits (U.lo * 0) := by decide +kernel
theorem maximum_times_one : fits (U.hi * 1) := by decide +kernel
theorem maximum_times_two : ¬ fits (U.hi * 2) := by decide +kernel
theorem negative_product : fits ((-7) * 9) := by decide +kernel
theorem positive_product : fits ((-7) * (-9)) := by decide +kernel
theorem below_minimum : ¬ fits (U.lo * 2) := by decide +kernel

theorem zero_family (x : Int) : fits (x * 0) := by
  simp only [Int.mul_zero]
  exact minimum_times_zero

end Solidity.Backend.PrimitivePackets.SignedCheckedMul.Controls
