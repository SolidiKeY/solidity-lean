import Solidity.Source.Value
import Solidity.Semantics.Ops
import Solidity.Lowering.V07.UnsignedNarrowing
import Solidity.Lowering.V07.SignedNarrowing

/-!
# Modular power at an intrinsic word exponent

The arithmetic relation here compares the actual Source modular-power helper
with mathematical residue, then the existing intrinsic powW arithmetic.
The public operand is the existing uint Denote type; its range supplies the
iteration bound. No bound is inferred from Source isAmount alone (see the
separate cutoff witness). A full validator must derive correspondence of its
actual Source amount and this actual word operand, including effects/errors,
checkedness, widths and pipeline ordering. No pass or endpoint is asserted.
-/
namespace Solidity.Correctness.Lowering.Unchecked.ModularPower

private theorem mul_congr (a b c d m : Int) (left : a % m = b % m)
    (right : c % m = d % m) : (a * c) % m = (b * d) % m := by
  rw [Int.mul_emod a c m, Int.mul_emod b d m, left, right]

private theorem pow_congr (a b m : Int) (n : Nat) (base : a % m = b % m) :
    a ^ n % m = b ^ n % m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact mul_congr (a ^ n) (b ^ n) a b m ih base

private theorem square_power (base : Int) (n : Nat) : (base * base) ^ n = base ^ (n + n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Int.pow_succ, ih, show n + 1 + (n + 1) = (n + n) + 2 by omega,
      Int.pow_add base (n + n) 2]
    simp only [Int.pow_succ, Int.pow_zero, Int.one_mul]

private theorem go_mod (m fuel : Nat) (base : Int) (n : Nat) (acc : Int)
    (bound : n < 2 ^ fuel) :
    Source.powMod.go m fuel base n acc % (m : Int) = (acc * base ^ n) % (m : Int) := by
  induction fuel generalizing base n acc with
  | zero =>
    have zero : n = 0 := by omega
    subst n
    simp only [Source.powMod.go, Int.pow_zero, Int.mul_one]
  | succ fuel ih =>
    by_cases zero : n = 0
    · subst n
      simp only [Source.powMod.go, if_true, Int.pow_zero, Int.mul_one]
    · have short : n / 2 < 2 ^ fuel :=
        (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
          (by simpa only [Nat.pow_succ] using bound)
      rw [Source.powMod.go, if_neg zero]
      rw [ih ((base * base) % (m : Int)) (n / 2) _ short]
      have power_mod := pow_congr ((base * base) % (m : Int)) (base * base)
        (m : Int) (n / 2) (Int.emod_emod (base * base) (m : Int))
      by_cases odd : n % 2 = 1
      · rw [if_pos odd]
        rw [mul_congr ((acc * base) % (m : Int)) (acc * base)
          (((base * base) % (m : Int)) ^ (n / 2)) ((base * base) ^ (n / 2))
          (m : Int) (Int.emod_emod (acc * base) (m : Int)) power_mod]
        rw [square_power]
        have division := Nat.mod_add_div n 2
        have form : n = (n / 2 + n / 2) + 1 := by omega
        have powered : base ^ n = base ^ (n / 2 + n / 2) * base :=
          (congrArg (fun e : Nat => base ^ e) form).trans
            (Int.pow_succ base (n / 2 + n / 2))
        rw [powered, Int.mul_assoc, Int.mul_comm base (base ^ (n / 2 + n / 2))]
      · rw [if_neg odd]
        rw [mul_congr acc acc (((base * base) % (m : Int)) ^ (n / 2))
          ((base * base) ^ (n / 2)) (m : Int) rfl power_mod]
        rw [square_power]
        have division := Nat.mod_add_div n 2
        have smallmod := Nat.mod_lt n (by decide : 0 < 2)
        have form : n / 2 + n / 2 = n := by omega
        rw [form]

private theorem word_bound (word : PrimTy.uint.Denote) (fuel : Nat) (enough : 256 ≤ fuel) :
    word.val.toNat < 2 ^ fuel := by
  have range := word.property
  simp only [PrimTy.inRange, decide_eq_true_eq] at range
  have small : word.val.toNat < 2 ^ 256 := by omega
  exact Nat.lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide) enough)

private theorem wrap_range : (t : Source.IntTy) → (v : Int) →
    t.lo ≤ v ∧ v ≤ t.hi → t.wrap v = v
  | ⟨false, bits, valid⟩, v, range =>
    Solidity.Lowering.V07.UnsignedNarrowing.wrap_of_range bits valid v range
  | ⟨true, bits, valid⟩, v, range =>
    Solidity.Lowering.V07.SignedNarrowing.wrap_of_range bits valid v range

private theorem intRes_wrap {D : Source.Layout} (t : Source.IntTy) (v : Int) :
    Source.intRes (D := D) t false v = .ok (Source.intWrap t v) := by
  simp only [Source.intRes]
  split
  · rename_i range
    have wrapped := wrap_range t v range
    simp only [Source.intWrap, wrapped]
    rfl
  · rfl

private theorem wrap_mod {D : Source.Layout} (t : Source.IntTy) (a b : Int)
    (residue : a % ((2 ^ t.bits : Nat) : Int) = b % ((2 ^ t.bits : Nat) : Int)) :
    Source.intWrap (D := D) t a = Source.intWrap t b := by
  have wrapped : t.wrap a = t.wrap b := by
    simp only [Source.IntTy.wrap, Source.wrapBits]
    rw [residue]
  unfold Source.intWrap
  congr 1

private theorem negative_one_power (n : Nat) :
    (-1 : Int) ^ n = (if n % 2 = 0 then 1 else -1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Int.pow_succ, ih]
    split <;> split <;> first | omega | rfl

/-- The iteration bound follows from the existing intrinsic operand type;
there is no extra exponent or successful-execution premise. -/
theorem word_powMod (base : Int) (word : PrimTy.uint.Denote) (modulus : Nat) :
    Source.powMod base word.val.toNat modulus % (modulus : Int) =
      base ^ word.val.toNat % (modulus : Int) := by
  simpa only [Source.powMod, Int.one_mul] using
    go_mod modulus 300 base word.val.toNat 1 (word_bound word 300 (by decide))

/-- The actual intrinsic powW arithmetic at a word exponent has precisely
that residue. This is an operator leaf, not an assumed whole execution. -/
theorem word_powW (base : Int) (word : PrimTy.uint.Denote) :
    BinOp.arithInt .powW base word.val =
      some (Source.powMod base word.val.toNat (2 ^ 256) % Semantics.uintBound) := by
  have range := word.property
  simp only [PrimTy.inRange, decide_eq_true_eq] at range
  rw [BinOp.arithInt, if_neg (by omega : ¬ word.val < 0)]
  exact congrArg some (word_powMod base word (2 ^ 256)).symm

/-- At every legal signed or unsigned Source width, an actual word exponent
justifies unchecked power as exact mathematical wrapping. No bound, result
range or success hypothesis is added to the public statement. -/
theorem unchecked_word_value {D : Source.Layout} (t : Source.IntTy) (base : Int)
    (word : PrimTy.uint.Denote) :
    Source.intPow (D := D) t false base word.val.toNat =
      .ok (Source.intWrap t (base ^ word.val.toNat)) := by
  simp only [Source.intPow]
  split
  · exact intRes_wrap t _
  · split
    · subst base
      rw [intRes_wrap, negative_one_power]
    · simp only [Bool.false_eq_true, if_false]
      exact congrArg Except.ok (wrap_mod t
        (Source.powMod base word.val.toNat (2 ^ t.bits)) (base ^ word.val.toNat)
        (word_powMod base word (2 ^ t.bits)))

#print axioms word_powMod
#print axioms word_powW
#print axioms unchecked_word_value

end Solidity.Correctness.Lowering.Unchecked.ModularPower
