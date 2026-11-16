import Solidity.Source.Value

/-!
# The exact constant one at every integer type

Guards the constant-conversion obligation in compound-one/increment rewriting.
Literal conversion is exact, not wrapping: the literal one fits every legal
Source integer type, including the narrowest signed type. This is a Source
constant ingredient, not raw-output association or target correctness.
-/
namespace Solidity.Correctness.Lowering.Unchecked

/-- One fits every legal integer width and signedness; no extra type exclusion. -/
theorem integerOne_range (t : Source.IntTy) : t.lo ≤ 1 ∧ 1 ≤ t.hi := by
  have p : 2 ≤ 2 ^ t.bits :=
    Source.two_pow_le (by have := t.valid.2.1; omega : 1 ≤ t.bits)
  have q : 2 ≤ 2 ^ (t.bits - 1) :=
    Source.two_pow_le (by have := t.valid.2.1; omega : 1 ≤ t.bits - 1)
  cases h : t.signed <;>
    simp only [Source.IntTy.lo, Source.IntTy.hi, h, Bool.false_eq_true, if_false, if_true] <;> omega

/-- The actual Source constant converter returns precisely one. -/
theorem constantOne {D : Source.Layout} (t : Source.IntTy) :
    Source.constVal (Source.Q.ofInt 1) (.int t) =
      .ok (.int 1 (integerOne_range t) : Source.Val D (.int t)) := by
  change Source.mkInt t 1 = _
  simp only [Source.mkInt, dif_pos (integerOne_range t)]
  rfl

#print axioms integerOne_range
#print axioms constantOne

end Solidity.Correctness.Lowering.Unchecked
