import Solidity.Backend.Scalar.Wrapping

/-! Wrapping exponentiation through the existing intrinsic unsigned power.
Checked power's overflow test remains a separate required guard certificate. -/
namespace Solidity.Backend.Scalar

/-- Osaka EXP takes the base on top and reduces only the final power. -/
def wrappingPow : BinaryCertificate .powW .uint rfl where
  code := [.op .EXP]
  correct := by
    intro a b tail
    have hb : ¬ b.val < 0 := by have : 0 ≤ b.val ∧ b.val < ((2 ^ 256 : Nat) : Int) := uint_range b; omega
    change some (BitVec.ofNat 256
      ((encodeValue .uint a).toNat ^ (encodeValue .uint b).toNat) :: tail) =
      ((if b.val < 0 then none else some (a.val ^ b.val.toNat % Semantics.uintBound)).bind
        PrimTy.uint.ofInt?).map (fun v => encodeValue .uint v :: tail)
    simp only [hb, if_false, Option.bind_some]
    rw [encoded_mod, encode_uint_toNat, encode_uint_toNat]
    have ha : a.val = (a.val.toNat : Int) := by have : 0 ≤ a.val ∧ a.val < ((2 ^ 256 : Nat) : Int) := uint_range a; omega
    rw [ha, ← Int.natCast_pow, BitVec.ofInt_natCast]
    simp only [Int.toNat_natCast]

/-- Positive and negative boundaries exercise EXP's base/exponent order. -/
example : run wrappingPow.code [0, 0, 99] = some [1, 99] := by decide +kernel
example : run wrappingPow.code [2, 256, 99] = some [0, 99] := by decide +kernel
example : run wrappingPow.code [3, 2, 99] ≠ some [8, 99] := by decide +kernel

#print axioms wrappingPow

end Solidity.Backend.Scalar
