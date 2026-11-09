import Solidity.Source.PowerV2

/-! Guard the 301-bit cutoff regression while preserving V1. V2 modular correctness and unchecked wrapping quantify over every natural exponent, with no production-domain premise; checked behavior is exactly V1. The bounded V1 bridge is only a comparison law, not a restriction on V2. No live evaluator, model endpoint, admission or external-solc equivalence is asserted. -/
namespace Solidity.Source.PowerV2

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
    Solidity.Source.powMod.go m fuel base n acc % (m : Int) = (acc * base ^ n) % (m : Int) := by
  induction fuel generalizing base n acc with
  | zero =>
    have zero : n = 0 := by omega
    subst n
    simp only [Solidity.Source.powMod.go, Int.pow_zero, Int.mul_one]
  | succ fuel ih =>
    by_cases zero : n = 0
    · subst n
      simp only [Solidity.Source.powMod.go, if_true, Int.pow_zero, Int.mul_one]
    · have short : n / 2 < 2 ^ fuel :=
        (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
          (by simpa only [Nat.pow_succ] using bound)
      rw [Solidity.Source.powMod.go, if_neg zero]
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


theorem powMod_residue (base : Int) (exponent modulus : Nat) :
    powMod base exponent modulus % (modulus : Int) = base ^ exponent % (modulus : Int) := by
  simpa only [powMod, Int.one_mul] using
    go_mod modulus exponent base exponent 1 (Nat.lt_two_pow_self (n := exponent))

private theorem wrap_congr {D : Layout} (t : IntTy) (a b : Int)
    (residue : a % ((2 ^ t.bits : Nat) : Int) = b % ((2 ^ t.bits : Nat) : Int)) :
    intWrap (D := D) t a = intWrap t b := by
  have wrapped : t.wrap a = t.wrap b := by
    simp only [IntTy.wrap, wrapBits]
    rw [residue]
  unfold intWrap
  congr 1

theorem intPow_unchecked {D : Layout} (t : IntTy) (base : Int) (exponent : Nat) :
    intPow (D := D) t false base exponent = .ok (intWrap t (base ^ exponent)) := by
  change Except.ok (intWrap t (powMod base exponent (2 ^ t.bits))) = _
  exact congrArg Except.ok (wrap_congr t _ _ (powMod_residue base exponent (2 ^ t.bits)))

theorem intPow_checked {D : Layout} (t : IntTy) (base : Int) (exponent : Nat) :
    intPow (D := D) t true base exponent = Solidity.Source.intPow t true base exponent := rfl

theorem powMod_agrees_v1 (base : Int) (exponent modulus : Nat) (bound : exponent < 2 ^ 300) :
    powMod base exponent modulus % (modulus : Int) =
      Solidity.Source.powMod base exponent modulus % (modulus : Int) := by
  apply (powMod_residue base exponent modulus).trans
  simpa only [Solidity.Source.powMod, Int.one_mul] using
    (go_mod modulus 300 base exponent 1 bound).symm

private theorem old_cutoff (modulus fuel : Nat) (base acc : Int) :
    Solidity.Source.powMod.go modulus fuel base (2 ^ fuel) acc = acc := by
  induction fuel generalizing base acc with
  | zero => rfl
  | succ f ih =>
    have hz : 2 ^ f * 2 ≠ 0 :=
      Nat.ne_of_gt (Nat.mul_pos (Nat.pow_pos (by decide)) (by decide))
    simpa only [Solidity.Source.powMod.go, Nat.pow_succ, if_neg hz,
      Nat.mul_div_left (n := 2) (2 ^ f) (by decide), Nat.mul_mod_left,
      Nat.zero_ne_one, if_false] using ih ((base * base) % modulus) acc

private theorem old_cutoff_double (modulus fuel : Nat) (base acc : Int) :
    Solidity.Source.powMod.go modulus (fuel + fuel) base (2 ^ fuel * 2 ^ fuel) acc = acc := by
  rw [← Nat.pow_add]
  exact old_cutoff modulus (fuel + fuel) base acc

def cutoffExponent : Nat := 2 ^ 150 * 2 ^ 150

theorem cutoff_repaired :
    powMod 2 cutoffExponent 256 % ((256 : Nat) : Int) = 0 ∧
      Solidity.Source.powMod 2 cutoffExponent 256 = 1 := by
  constructor
  · rw [powMod_residue 2 cutoffExponent 256]
    have bound : 8 ≤ cutoffExponent := by decide
    rw [show cutoffExponent = (cutoffExponent - 8) + 8 by omega, Int.pow_add]
    change (((2 : Int) ^ (cutoffExponent - 8)) * 256) % 256 = 0
    exact Int.mul_emod_left _ _
  · exact old_cutoff_double 256 150 2 1

/-- info: 'Solidity.Source.PowerV2.powMod_residue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms powMod_residue
/-- info: 'Solidity.Source.PowerV2.intPow_unchecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms intPow_unchecked
/-- info: 'Solidity.Source.PowerV2.intPow_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms intPow_checked
/-- info: 'Solidity.Source.PowerV2.powMod_agrees_v1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms powMod_agrees_v1
/-- info: 'Solidity.Source.PowerV2.cutoff_repaired' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cutoff_repaired

end Solidity.Source.PowerV2
