/-!
# The guards of `checked { … }` are exact

Each guard `Syntax/Checked.lean` writes holds exactly when its operation
stays in range, read as the run reads the guard's operators (`+%` and `*%`
modulo `2^256`, `/` truncating, `Int.tdiv`) on operands of their type.  The
formulas are restated over `Int` here, not read off `rangeU`/`rangeI`; where
the guards sit in a statement is `docs/options.md`'s, O2.  `M` is the range's bound, `2^256` at `uint` and `2^255` at `int`
(`-M ≤ x < M`); the statements are over any positive `M`.
-/

namespace Solidity.Checked

theorem emod_of_ge {x M : Int} (h0 : M ≤ x) (h1 : x < 2 * M) : x % M = x - M := by
  have hM : 0 < M := by omega
  have e : x % M = (x - M) % M := by
    conv => lhs; rw [show x = (x - M) + M * 1 by omega]
    rw [Int.add_mul_emod_self_left]
  rw [e, Int.emod_eq_of_lt (by omega) (by omega)]

/-- `a <= a +% b` at `uint`. -/
theorem add_uint_exact {M a b : Int} (ha0 : 0 ≤ a) (ha : a < M) (hb0 : 0 ≤ b) (hb : b < M) :
    a ≤ (a + b) % M ↔ a + b < M := by
  by_cases h : a + b < M
  · rw [Int.emod_eq_of_lt (by omega) h]; omega
  · rw [emod_of_ge (by omega) (by omega)]; omega

/-- `b <= a` at `uint`. -/
theorem sub_uint_exact {a b : Int} : b ≤ a ↔ 0 ≤ a - b := by omega

/-- `a == 0 || (a *% b) / a == b` at `uint`. -/
theorem mul_uint_exact {M a b : Int} (ha0 : 0 ≤ a) (ha : a < M) (hb0 : 0 ≤ b) (hb : b < M) :
    (a = 0 ∨ (a * b % M).tdiv a = b) ↔ a * b < M := by
  have hM : 0 < M := by omega
  rw [Int.tdiv_eq_ediv_of_nonneg (Int.emod_nonneg _ (by omega))]
  constructor
  · rintro (h | h)
    · subst h; simpa using hM
    · rcases Int.lt_or_le (a * b) M with hlt | hge
      · exact hlt
      · exfalso
        have ha' : 0 < a := by
          rcases Int.lt_or_eq_of_le ha0 with h' | h'
          · exact h'
          · subst h'; omega
        have hm : a * b % M < a * b := by
          have := Int.emod_lt_of_pos (a * b) hM
          omega
        have : a * b % M / a < b := by
          rw [Int.ediv_lt_iff_lt_mul ha', Int.mul_comm b a]; exact hm
        omega
  · intro h
    rcases Int.lt_or_eq_of_le ha0 with h' | h'
    · right
      rw [Int.emod_eq_of_lt (Int.mul_nonneg ha0 hb0) h, Int.mul_comm, Int.mul_ediv_cancel _ (by omega)]
    · left; exact h'.symm

/-- `b >= 0 ? a <= MAX - b : a >= MIN - b` at `int`. -/
theorem add_int_exact {M a b : Int} (ha : -M ≤ a ∧ a < M) :
    (if 0 ≤ b then a ≤ (M - 1) - b else -M - b ≤ a) ↔ (-M ≤ a + b ∧ a + b ≤ M - 1) := by
  split <;> omega

/-- `b >= 0 ? a >= MIN + b : a <= MAX + b` at `int`. -/
theorem sub_int_exact {M a b : Int} (ha : -M ≤ a ∧ a < M) :
    (if 0 ≤ b then -M + b ≤ a else a ≤ (M - 1) + b) ↔ (-M ≤ a - b ∧ a - b ≤ M - 1) := by
  split <;> omega

/-- `a != MIN`, for `-a` at `int`. -/
theorem neg_int_exact {M a : Int} (ha : -M ≤ a ∧ a < M) : a ≠ -M ↔ (-M ≤ -a ∧ -a ≤ M - 1) := by
  omega

/-- `!(a == MIN && b == -1)`, for `a / b` at `int` (`b ≠ 0`: a division by
zero reverts outside the block and in it). -/
theorem div_int_exact {M a b : Int} (hM : 0 < M) (ha : -M ≤ a ∧ a < M) (hb0 : b ≠ 0) :
    ¬ (a = -M ∧ b = -1) ↔ (-M ≤ a.tdiv b ∧ a.tdiv b ≤ M - 1) := by
  by_cases h1 : b = -1
  · subst h1
    rw [Int.tdiv_neg, Int.tdiv_one]; omega
  · have hq := Int.natAbs_tdiv_le_natAbs a b
    by_cases h2 : b = 1
    · subst h2; rw [Int.tdiv_one]; omega
    · have hb2 : 2 ≤ b.natAbs := by omega
      have he := Int.natAbs_tdiv a b
      have : (a.tdiv b).natAbs ≤ a.natAbs / 2 := by
        rw [he]; exact Nat.div_le_div_left hb2 (by decide)
      omega

/-- The guard of `a * b` at `int`. -/
theorem mul_int_exact {M a b : Int} (hM : 0 < M) (ha : -M ≤ a ∧ a < M) (hb : -M ≤ b ∧ b < M) :
    (a = 0 ∨ b = 0 ∨
      (if 0 < a then (if 0 < b then a ≤ (M - 1).tdiv b else (-M).tdiv a ≤ b)
       else (if 0 < b then (-M).tdiv b ≤ a
         else (a ≠ -M ∧ b ≠ -M ∧ 0 - a ≤ (M - 1).tdiv (0 - b))))) ↔
    (-M ≤ a * b ∧ a * b ≤ M - 1) := by
  by_cases ha0 : a = 0
  · subst ha0; simp only [true_or, Int.zero_mul, true_iff]; omega
  by_cases hb0 : b = 0
  · subst hb0; simp only [or_true, true_or, Int.mul_zero, true_iff]; omega
  simp only [ha0, hb0, false_or]
  rcases Int.lt_or_lt_of_ne ha0 with ha' | ha' <;> rcases Int.lt_or_lt_of_ne hb0 with hb' | hb'
  · -- a < 0, b < 0
    have hp : 0 < a * b := Int.mul_pos_of_neg_of_neg ha' hb'
    simp only [show ¬ 0 < a by omega, show ¬ 0 < b by omega, if_false]
    by_cases haM : a = -M
    · subst haM
      have : M ≤ -M * b := by
        have := Int.mul_le_mul_of_nonneg_left (show 1 ≤ -b by omega) (Int.le_of_lt hM)
        rw [Int.mul_one, Int.mul_neg] at this; rw [Int.neg_mul]; exact this
      simp only [ne_eq, not_true_eq_false, false_and, false_iff]; omega
    by_cases hbM : b = -M
    · subst hbM
      have : M ≤ a * -M := by
        have := Int.mul_le_mul_of_nonneg_right (show 1 ≤ -a by omega) (Int.le_of_lt hM)
        rw [Int.one_mul, Int.neg_mul] at this; rw [Int.mul_neg]; exact this
      simp only [ne_eq, not_true_eq_false, false_and, and_false, false_iff]; omega
    simp only [ne_eq, haM, not_false_eq_true, hbM, true_and]
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega), Int.le_ediv_iff_mul_le (by omega)]
    rw [show (0 - a) * (0 - b) = a * b by rw [Int.zero_sub, Int.zero_sub, Int.neg_mul_neg]]
    omega
  · -- a < 0, 0 < b
    have hn : a * b < 0 := Int.mul_neg_of_neg_of_pos ha' hb'
    simp only [show ¬ 0 < a by omega, hb', if_false, if_true]
    rw [Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by omega)]
    have e : (-(M / b) ≤ a) ↔ (-a) * b ≤ M := by
      rw [← Int.le_ediv_iff_mul_le hb']; omega
    rw [e, Int.neg_mul]; omega
  · -- 0 < a, b < 0
    have hn : a * b < 0 := Int.mul_neg_of_pos_of_neg ha' hb'
    simp only [ha', show ¬ 0 < b by omega, if_true, if_false]
    rw [Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by omega)]
    have e : (-(M / a) ≤ b) ↔ (-b) * a ≤ M := by
      rw [← Int.le_ediv_iff_mul_le ha']; omega
    rw [e, Int.neg_mul, Int.mul_comm b a]; omega
  · -- 0 < a, 0 < b
    have hp : 0 < a * b := Int.mul_pos ha' hb'
    simp only [ha', hb', if_true]
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega), Int.le_ediv_iff_mul_le hb']
    omega

end Solidity.Checked
