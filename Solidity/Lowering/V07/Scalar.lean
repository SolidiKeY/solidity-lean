import Solidity.Source.Value
import Solidity.Semantics.Value

/-! G16 value transport over existing Source and intrinsic carriers. Source
width evidence stays explicit; this does not certify declaration admission or
production compilation. Scalar content agreement asserts no alias identity. -/
namespace Solidity.Lowering.V07

def integerPrim (t : Source.IntTy) : PrimTy := if t.signed then .int else .uint

theorem integer_range (t : Source.IntTy) (n : Int)
    (h : t.lo ≤ n ∧ n ≤ t.hi) : (integerPrim t).inRange n = true := by
  have hu := Source.two_pow_le t.valid.2.2
  have hs := Source.two_pow_le (Nat.sub_le_sub_right t.valid.2.2 1)
  have pu := Source.two_pow_pos t.bits
  have ps := Source.two_pow_pos (t.bits-1)
  cases he : t.signed <;>
    simp only [integerPrim,he,Bool.false_eq_true,if_false,if_true,
      PrimTy.inRange,decide_eq_true_eq] <;>
    simp only [Source.IntTy.lo,Source.IntTy.hi,he,Bool.false_eq_true,if_false,if_true] at h <;> omega

def integerValue (t : Source.IntTy) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) : (integerPrim t).Denote := by
  obtain ⟨sign,bits,valid⟩ := t
  cases sign
  · exact (⟨n,integer_range ⟨false,bits,valid⟩ n h⟩ : PrimTy.uint.Denote)
  · exact (⟨n,integer_range ⟨true,bits,valid⟩ n h⟩ : PrimTy.int.Denote)

theorem integer_observe (t : Source.IntTy) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) :
    PrimTy.num? (integerValue t n h) = some n := by
  obtain ⟨sign,bits,valid⟩ := t
  cases sign <;> rfl

def IntValueRel {D : Source.Layout} (t : Source.IntTy)
    (source : Source.Val D (.int t)) (target : (integerPrim t).Denote) : Prop :=
  source.key = PrimTy.num? target

theorem integer_related {D : Source.Layout} (t : Source.IntTy) (n : Int)
    (h : t.lo ≤ n ∧ n ≤ t.hi) :
    IntValueRel t (.int n h : Source.Val D (.int t)) (integerValue t n h) :=
  (integer_observe t n h).symm

theorem integer_injective (t : Source.IntTy) (x y : Int)
    (hx : t.lo ≤ x ∧ x ≤ t.hi) (hy : t.lo ≤ y ∧ y ≤ t.hi)
    (same : integerValue t x hx = integerValue t y hy) : x = y := by
  exact Option.some.inj ((integer_observe t x hx).symm.trans
    ((congrArg PrimTy.num? same).trans (integer_observe t y hy)))

end Solidity.Lowering.V07
