import Solidity.Source.PowerV2Correct
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
  exact (Source.PowerV2.powMod_agrees_v1 base word.val.toNat modulus
    (word_bound word 300 (by decide))).symm.trans
      (Source.PowerV2.powMod_residue base word.val.toNat modulus)

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
      simp only [Source.intWrap, Source.IntTy.wrap, Source.wrapBits, word_powMod]
      rfl

#print axioms word_powMod
#print axioms word_powW
#print axioms unchecked_word_value

end Solidity.Correctness.Lowering.Unchecked.ModularPower
