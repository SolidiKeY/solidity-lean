import Solidity.Source.Value

/-!
# Source power cutoff witness

Guards assuming the fixed modular-power iteration count follows from the
Source exponent typing rule. Source is read only. These facts expose the
existing function's cutoff and a real typing derivation; they do not assert
that this expression belongs to the still-undelivered canonical production
language/admission contract, or establish an external solc discrepancy.
No new source exclusion or exponent premise is adopted here.
-/
namespace Solidity.Correctness.Lowering.Unchecked.PowerBoundControls

/-- A 301-bit exponent, factored to respect the unchanged literal evaluator threshold. -/
def largeExponent : Nat := 2 ^ 150 * 2 ^ 150

private theorem cutoff (m fuel : Nat) (base acc : Int) :
    Source.powMod.go m fuel base (2 ^ fuel) acc = acc := by
  induction fuel generalizing base acc with
  | zero => rfl
  | succ f ih =>
    have hz : 2 ^ f * 2 ≠ 0 :=
      Nat.ne_of_gt (Nat.mul_pos (Nat.pow_pos (by decide)) (by decide))
    simpa only [Source.powMod.go, Nat.pow_succ, if_neg hz,
      Nat.mul_div_left (n := 2) (2 ^ f) (by decide), Nat.mul_mod_left,
      Nat.zero_ne_one, if_false] using ih ((base * base) % m) acc

private theorem cutoff_double (m fuel : Nat) (base acc : Int) :
    Source.powMod.go m (fuel + fuel) base (2 ^ fuel * 2 ^ fuel) acc = acc := by
  rw [← Nat.pow_add]
  exact cutoff m (fuel + fuel) base acc

private theorem residue (k : Nat) (bound : 8 ≤ k) : ((2 : Int) ^ k) % 256 = 0 := by
  rw [show k = (k - 8) + 8 by omega, Int.pow_add]
  change (((2 : Int) ^ (k - 8)) * 256) % 256 = 0
  exact Int.mul_emod_left _ _

private theorem nat_amount (n : Nat) :
    (.rational (Source.Q.ofInt (n : Int)) : Source.STy).isAmount = true := by
  simp only [Source.STy.isAmount, Source.Q.isInt, Source.Q.ofInt, Int.cast_ofNat_Int,
    Int.emod_one, BEq.rfl, Source.Q.toInt, Int.ediv_one, Int.ofNat_zero_le,
    decide_true, Bool.and_self]

/-- The highest exponent bit is not consumed within the existing 300 steps. -/
theorem cutoff_value : Source.powMod 2 largeExponent 256 = 1 := by
  exact cutoff_double 256 150 2 1

/-- The corresponding mathematical residue is zero, without evaluating the
astronomically large integer power. -/
theorem mathematical_residue : ((2 : Int) ^ largeExponent) % 256 = 0 := by
  exact residue largeExponent (by decide)

/-- The existing unchecked integer operator reaches that cutoff at uint8.
This is an operator fact, not an admitted-program or external-solc theorem. -/
theorem unchecked_value {D : Source.Layout} :
    Source.intPow (D := D) ⟨false, 8, by decide⟩ false 2 largeExponent =
      .ok (Source.intWrap (D := D) ⟨false, 8, by decide⟩ 1) := by
  have bound : ¬ largeExponent ≤ 8 := by decide
  have guard : ¬ ((2 : Int) = 0 ∨ 2 = 1 ∨ largeExponent ≤ 8) := by omega
  simp only [Source.intPow, if_neg (by decide : ¬ (2 : Int) = -1)]
  change Except.ok (Source.intWrap (D := D) ⟨false, 8, by decide⟩
    (Source.powMod 2 largeExponent 256)) = _
  rw [cutoff_value]

private def context (E : Source.Env) : Source.Ctx :=
  { env := E, scope := none, locals := [("x", .int ⟨false, 8, by decide⟩)] }

private def exponent (n : Nat) : Source.Syn .expr := .lit (.num (.dec n 0 0))

/-- The actual Source typing rule admits a variable raised to this constant;
it checks isAmount, not a word-size bound on the literal. -/
def typedPower (E : Source.Env) : Source.Typed (context E)
    (.exp (.ident "x") (exponent largeExponent)) (.int ⟨false, 8, by decide⟩) :=
  .exp (τa := .int ⟨false, 8, by decide⟩) rfl (.loc rfl rfl)
    (.const (q := Source.Q.ofInt (largeExponent : Int)) rfl rfl rfl)
    rfl (nat_amount largeExponent) rfl

/-- This concrete accepted amount lies beyond the fixed iteration range. -/
theorem amount_not_word_bounded :
    (.rational (Source.Q.ofInt (largeExponent : Int)) : Source.STy).isAmount = true ∧
      ¬ largeExponent < 2 ^ 256 := by
  exact ⟨nat_amount _, by decide⟩

#print axioms cutoff_value
#print axioms typedPower
#print axioms unchecked_value
#print axioms mathematical_residue
#print axioms amount_not_word_bounded

end Solidity.Correctness.Lowering.Unchecked.PowerBoundControls
