import Solidity.Yul.Views.ScalarCodecs

namespace Solidity.Yul.Views

/-- The EXISTING low-width signed/unsigned decoder always yields a real source
integer for a complete field payload. This adds no alternate signed policy. -/
theorem readIntPayload_inRange (t : Source.IntTy) (n : Nat) (bound : n < 2^t.bits) :
    t.lo ≤ readIntPayload t n ∧ readIntPayload t n ≤ t.hi := by
  have hd := int_modulus_double t
  have hp : 0 < 2^(t.bits-1) := Nat.pow_pos (by decide)
  unfold readIntPayload
  simp only [Source.IntTy.lo,Source.IntTy.hi]
  cases hs : t.signed <;> simp only [Bool.false_eq_true,false_and,true_and,if_false,if_true]
  · omega
  · split <;> omega

/-- Reverse direction to read_intPayload: no raw field bit is lost, including
negative minima and -1 and the sign threshold. -/
theorem intPayload_readIntPayload (t : Source.IntTy) (n : Nat) (bound : n < 2^t.bits) :
    intPayload t (readIntPayload t n) = n := by
  unfold readIntPayload
  cases hs : t.signed <;> simp only [Bool.false_eq_true,false_and,true_and,if_false]
  · have nonnegative : ¬(n : Int)<0 := Int.not_lt.mpr (Int.natCast_nonneg _)
    simp only [intPayload,if_neg nonnegative,Int.toNat_natCast]
  · split
    · have negative : (n : Int)-(2^t.bits : Nat)<0 := by omega
      simp only [intPayload,if_pos negative,Int.sub_add_cancel,Int.toNat_natCast]
    · have nonnegative : ¬(n : Int)<0 := Int.not_lt.mpr (Int.natCast_nonneg _)
      simp only [intPayload,if_neg nonnegative,Int.toNat_natCast]

def integerStorageValue (D : Source.Layout) (t : Source.IntTy) (n : Nat) (bound : n<2^t.bits) : Source.Val D (.int t) :=
  .int (readIntPayload t n) (readIntPayload_inRange t n bound)

theorem intCodec_decode_payload (D : Source.Layout) (t : Source.IntTy) (off : Nat) (fits : off+t.bits/8≤32)
    (n : (intField t off fits).Value) :
    (intCodec D t off fits).decode n = some (integerStorageValue D t n.val
      (Nat.lt_of_lt_of_le n.isLt (Nat.le_of_eq (intField_modulus t off fits)))) := by
  have bound : n.val<2^t.bits := by
    exact Nat.lt_of_lt_of_le n.isLt (Nat.le_of_eq (intField_modulus t off fits))
  change (if h : t.lo≤readIntPayload t n.val ∧ readIntPayload t n.val≤t.hi then some (.int (readIntPayload t n.val) h : Source.Val D (.int t)) else none) = _
  rw [dif_pos (readIntPayload_inRange t n.val bound)]
  rfl

end Solidity.Yul.Views
