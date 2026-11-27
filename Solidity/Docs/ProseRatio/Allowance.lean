import Solidity.Goals.ProseRatioRuleSound

/-! Arithmetic for the frozen code-relative allowance. -/
namespace Solidity.Docs.ProseRatio
open Solidity.Goals.ProseRatio

theorem rounding (w : Allowance) (P C : Nat) :
    P ≤ w.lines C ↔ P * w.ratio.den ≤ w.ratio.num * C + w.margin * w.ratio.den := by
  rw [Allowance.lines, ← Nat.add_mul_div_right _ _ w.ratio.den_pos]
  exact Nat.le_div_iff_mul_le w.ratio.den_pos

theorem lines_mono (w v : Allowance) (h : w.le v) (C : Nat) : w.lines C ≤ v.lines C := by
  apply Nat.add_le_add _ h.2
  apply (Nat.le_div_iff_mul_le v.ratio.den_pos).mpr
  apply Nat.le_of_mul_le_mul_right (c := w.ratio.den) _ w.ratio.den_pos
  have hfloor := Nat.div_mul_le_self (w.ratio.num * C) w.ratio.den
  have hscaled := Nat.mul_le_mul_right C h.1
  calc
    w.ratio.num * C / w.ratio.den * v.ratio.den * w.ratio.den =
        (w.ratio.num * C / w.ratio.den * w.ratio.den) * v.ratio.den := by ac_rfl
    _ ≤ (w.ratio.num * C) * v.ratio.den := Nat.mul_le_mul_right _ hfloor
    _ = w.ratio.num * v.ratio.den * C := by ac_rfl
    _ ≤ v.ratio.num * w.ratio.den * C := hscaled
    _ = v.ratio.num * C * w.ratio.den := by ac_rfl

theorem byValue (w v : Allowance) (h : w.Equiv v) (C : Nat) : w.lines C = v.lines C :=
  Nat.le_antisymm (lines_mono w v h.1 C) (lines_mono v w h.2 C)

theorem zero_le (w : Allowance) : Allowance.zero.le w := by
  constructor
  · simp [Ratio.le, Allowance.zero]
  · exact Nat.zero_le _

theorem min_below (w v : Allowance) : (w.min v).le w ∧ (w.min v).le v := by
  have hr : (w.ratio.min v.ratio).le w.ratio ∧ (w.ratio.min v.ratio).le v.ratio := by
    unfold Ratio.min
    split
    · rename_i h
      exact ⟨Nat.le_refl _, h⟩
    · rename_i h
      exact ⟨Nat.le_of_not_ge h, Nat.le_refl _⟩
  exact ⟨⟨hr.1, Nat.min_le_left _ _⟩, ⟨hr.2, Nat.min_le_right _ _⟩⟩

theorem min_exact (w v : Allowance) (h : v.le w) : (w.min v).Equiv v := by
  refine ⟨(min_below w v).2, ?_⟩
  constructor
  · unfold Allowance.min Ratio.min
    split
    · exact h.1
    · exact Nat.le_refl _
  · exact Nat.le_min.mpr ⟨h.2, Nat.le_refl _⟩

end Solidity.Docs.ProseRatio
