import Solidity.Yul.Words

/-!
# The arithmetic of solc's `checked_exp_unsigned`

A natural-number model of the helper as solc 0.8.38 emits it
(`SolcValidation/IrExpHelpers.lean`), with `max = 2^256 - 1`: the special cases
for exponent `0`, bases `0`, `1`, `2`, the small-range shortcut through `exp`,
and the square-and-multiply loop of `checked_exp_helper` with its overflow test
`base > max / base`. `expUnsigned_correct` shows the model returns `base ^ exponent`
exactly when it is below `2^256` and panics (`none`) otherwise. The interpreter
side is `SolcValidation/IrExpSim.lean`.
-/
namespace Solidity.SolcValidation.IrSyntax

/-- The largest word, solc's `max` argument for `uint256`. -/
abbrev maxWord : Nat := 2 ^ 256 - 1

/-- The loop of `checked_exp_helper`: `(power, base, exponent)` at exit, `none`
when the `base * base` overflow test fires. -/
def expLoop (p b e : Nat) : Option (Nat × Nat × Nat) :=
  if e ≤ 1 then some (p, b, e)
  else if maxWord / b < b then none
  else expLoop (if e % 2 = 1 then p * b % 2 ^ 256 else p) (b * b % 2 ^ 256) (e / 2)
termination_by e
decreasing_by omega

/-- `checked_exp_unsigned(base, exponent, max)` with `max = 2^256 - 1`. -/
def expUnsigned (b e : Nat) : Option Nat :=
  if e = 0 then some 1
  else if b = 0 then some 0
  else if b = 1 then some 1
  else if b = 2 then (if 255 < e then none else some (2 ^ e % 2 ^ 256))
  else if (b < 11 ∧ e < 78) ∨ (b < 307 ∧ e < 32) then some (b ^ e % 2 ^ 256)
  else match expLoop 1 b e with
    | none => none
    | some (p, b', _) => if maxWord / b' < p then none else some (p * b' % 2 ^ 256)

theorem expLoop_exit (p b e : Nat) (le : e ≤ 1) : expLoop p b e = some (p, b, e) := by
  rw [expLoop, if_pos le]

theorem expLoop_panic (p b e : Nat) (gt : ¬ e ≤ 1) (big : maxWord / b < b) : expLoop p b e = none := by
  rw [expLoop, if_neg gt, if_pos big]

theorem expLoop_step (p b e : Nat) (gt : ¬ e ≤ 1) (ok : ¬ maxWord / b < b) :
    expLoop p b e = expLoop (if e % 2 = 1 then p * b % 2 ^ 256 else p) (b * b % 2 ^ 256) (e / 2) := by
  rw [expLoop, if_neg gt, if_neg ok]

theorem div_lt_iff (a b : Nat) (pos : 0 < b) : maxWord / b < a ↔ 2 ^ 256 ≤ a * b := by
  rw [Nat.div_lt_iff_lt_mul pos]
  show 2 ^ 256 - 1 < a * b ↔ _
  omega

/-- The loop's invariant: below an overflow the values are exact, `1 ≤ p ≤ b`,
and `p * b ^ e` is preserved; an overflow happens only when `p * b ^ e` overflows. -/
theorem expLoop_spec : ∀ (e p b : Nat), 1 ≤ e → 1 ≤ p → p ≤ b → b < 2 ^ 256 →
    match expLoop p b e with
    | some (p', b', e') => e' = 1 ∧ 1 ≤ p' ∧ p' ≤ b' ∧ b' < 2 ^ 256 ∧ p' * b' = p * b ^ e
    | none => 2 ^ 256 ≤ p * b ^ e := by
  intro e
  induction e using Nat.strongRecOn with
  | ind e ih =>
    intro p b e1 p1 pb bW
    by_cases le : e ≤ 1
    · have e_one : e = 1 := by omega
      rw [expLoop_exit p b e le, e_one, Nat.pow_one]
      exact ⟨rfl, p1, pb, bW, rfl⟩
    · have bpos : 0 < b := by omega
      by_cases big : maxWord / b < b
      · rw [expLoop_panic p b e le big]
        have sq : 2 ^ 256 ≤ b * b := (div_lt_iff b b bpos).mp big
        have two : b * b ≤ b ^ e := by
          rw [← Nat.pow_two]
          exact Nat.pow_le_pow_right bpos (by omega)
        calc 2 ^ 256 ≤ b * b := sq
          _ ≤ b ^ e := two
          _ = 1 * b ^ e := (Nat.one_mul _).symm
          _ ≤ p * b ^ e := Nat.mul_le_mul_right _ p1
      · rw [expLoop_step p b e le big]
        have sq : b * b < 2 ^ 256 := by
          have : ¬ 2 ^ 256 ≤ b * b := fun h => big ((div_lt_iff b b bpos).mpr h)
          omega
        have pbW : p * b < 2 ^ 256 := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right b pb) sq
        have bb : b * b % 2 ^ 256 = b * b := Nat.mod_eq_of_lt sq
        have halve : b ^ e = (b * b) ^ (e / 2) * b ^ (e % 2) := Solidity.Yul.pow_halve b e
        rw [bb]
        have ih' := ih (e / 2) (by omega)
        by_cases odd : e % 2 = 1
        · rw [if_pos odd, Nat.mod_eq_of_lt pbW]
          have h := ih' (p * b) (b * b) (by omega) (by
              have : 1 * 1 ≤ p * b := Nat.mul_le_mul p1 (by omega)
              omega) (Nat.mul_le_mul_right b pb) sq
          revert h
          rcases expLoop (p * b) (b * b) (e / 2) with _ | ⟨p', b', e'⟩
          · intro h
            rw [halve, odd, Nat.pow_one]
            calc 2 ^ 256 ≤ p * b * (b * b) ^ (e / 2) := h
              _ = p * ((b * b) ^ (e / 2) * b) := by rw [Nat.mul_comm ((b * b) ^ (e / 2)) b, Nat.mul_assoc]
          · intro ⟨h1, h2, h3, h4, h5⟩
            refine ⟨h1, h2, h3, h4, ?_⟩
            rw [h5, halve, odd, Nat.pow_one, Nat.mul_comm ((b * b) ^ (e / 2)) b, Nat.mul_assoc]
        · rw [if_neg odd]
          have even : e % 2 = 0 := by omega
          have h := ih' p (b * b) (by omega) p1
            (Nat.le_trans pb (by
              have : b * 1 ≤ b * b := Nat.mul_le_mul_left b (by omega)
              omega)) sq
          revert h
          rcases expLoop p (b * b) (e / 2) with _ | ⟨p', b', e'⟩
          · intro h
            rw [halve, even, Nat.pow_zero, Nat.mul_one]
            exact h
          · intro ⟨h1, h2, h3, h4, h5⟩
            refine ⟨h1, h2, h3, h4, ?_⟩
            rw [h5, halve, even, Nat.pow_zero, Nat.mul_one]

theorem pow_lt_of_small (b e : Nat) (b1 : 1 ≤ b) (small : (b < 11 ∧ e < 78) ∨ (b < 307 ∧ e < 32)) :
    b ^ e < 2 ^ 256 := by
  rcases small with ⟨hb, he⟩ | ⟨hb, he⟩
  · calc b ^ e ≤ b ^ 77 := Nat.pow_le_pow_right b1 (by omega)
      _ ≤ 10 ^ 77 := Nat.pow_le_pow_left (by omega) 77
      _ < 2 ^ 256 := by decide
  · calc b ^ e ≤ b ^ 31 := Nat.pow_le_pow_right b1 (by omega)
      _ ≤ 306 ^ 31 := Nat.pow_le_pow_left (by omega) 31
      _ < 2 ^ 256 := by decide

/-- solc's `checked_exp_unsigned` (with `max = 2^256 - 1`) computes `base ^ exponent`
when it fits in a word and panics exactly when it does not. -/
theorem expUnsigned_correct (b e : Nat) (bW : b < 2 ^ 256) :
    expUnsigned b e = if b ^ e < 2 ^ 256 then some (b ^ e) else none := by
  unfold expUnsigned
  by_cases e0 : e = 0
  · rw [if_pos e0, e0, Nat.pow_zero, if_pos (by decide)]
  rw [if_neg e0]
  by_cases b0 : b = 0
  · rw [if_pos b0, b0, Nat.zero_pow (by omega), if_pos (by decide)]
  rw [if_neg b0]
  by_cases b1 : b = 1
  · rw [if_pos b1, b1, Nat.one_pow, if_pos (by decide)]
  rw [if_neg b1]
  by_cases b2 : b = 2
  · rw [if_pos b2, b2]
    by_cases big : 255 < e
    · have : ¬ 2 ^ e < 2 ^ 256 := fun h => by
        have : e < 256 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h
        omega
      rw [if_pos big, if_neg this]
    · have fits : 2 ^ e < 2 ^ 256 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr (by omega)
      rw [if_neg big, if_pos fits, Nat.mod_eq_of_lt fits]
  rw [if_neg b2]
  by_cases small : (b < 11 ∧ e < 78) ∨ (b < 307 ∧ e < 32)
  · have fits := pow_lt_of_small b e (by omega) small
    rw [if_pos small, if_pos fits, Nat.mod_eq_of_lt fits]
  rw [if_neg small]
  have spec := expLoop_spec e 1 b (by omega) (Nat.le_refl 1) (by omega) bW
  revert spec
  rcases expLoop 1 b e with _ | ⟨p', b', e'⟩
  · intro h
    rw [Nat.one_mul] at h
    rw [if_neg (Nat.not_lt.mpr h)]
  · intro ⟨_, h2, h3, _, h5⟩
    rw [Nat.one_mul] at h5
    dsimp only
    by_cases fits : b ^ e < 2 ^ 256
    · have : ¬ maxWord / b' < p' := fun h => by
        have : 2 ^ 256 ≤ p' * b' := (div_lt_iff p' b' (by omega)).mp h
        omega
      rw [if_neg this, if_pos fits, h5, Nat.mod_eq_of_lt fits]
    · have : maxWord / b' < p' := (div_lt_iff p' b' (by omega)).mpr (by omega)
      rw [if_pos this, if_neg fits]

end Solidity.SolcValidation.IrSyntax
