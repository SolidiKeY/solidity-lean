import Solidity.Backend.Scalar.Bitwise

/-! Intrinsic unsigned shifts preserve the source saturation rule and operand
order. Signed negative counts need their own clamp and are not assumed away. -/
namespace Solidity.Backend.Scalar

theorem shiftLeft_word (x : Word) (n : Nat) :
    x <<< n = BitVec.ofNat 256 (x.toNat * 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]

/-- Source shift operands are value, count; SHL needs count, value. -/
def uintShl : BinaryCertificate .shl .uint rfl where
  code := [.op (.SWAP ⟨0, by decide⟩), .op .SHL]
  correct := by
    intro a n tail
    have hpow : (2 : Int) ^ n.val.toNat = ((2 ^ n.val.toNat : Nat) : Int) :=
      (Int.natCast_pow 2 n.val.toNat).symm
    have hr : 0 ≤ n.val ∧ n.val < ((2 ^ 256 : Nat) : Int) := uint_range n
    have hc : (n.val.toNat < 256) ↔ n.val < 256 := by omega
    change some ((if (encodeValue .uint n).toNat < 256 then
        (encodeValue .uint a) <<< (encodeValue .uint n).toNat else 0) :: tail) =
      (PrimTy.uint.ofInt? (if n.val < 256 then
        a.val * 2 ^ n.val.toNat % Semantics.uintBound else 0)).map
        (fun v => encodeValue .uint v :: tail)
    rw [encode_uint_toNat]
    by_cases hn : n.val < 256
    · have hnn : n.val.toNat < 256 := hc.mpr hn
      simp only [hn, hnn, if_true]
      rw [encoded_mod, shiftLeft_word, encode_uint_toNat]
      have ha : a.val = (a.val.toNat : Int) := by have : 0 ≤ a.val ∧ a.val < ((2 ^ 256 : Nat) : Int) := uint_range a; omega
      rw [ha, hpow, ← Int.natCast_mul, BitVec.ofInt_natCast]
      simp only [Int.toNat_natCast]
    · have hnn : ¬ n.val.toNat < 256 := fun h => hn (hc.mp h)
      simp only [hn, hnn, if_false]
      rfl

/-- SHR and the nonnegative source floor quotient agree at every shift count. -/
def uintShr : BinaryCertificate .shr .uint rfl where
  code := [.op (.SWAP ⟨0, by decide⟩), .op .SHR]
  correct := by
    intro a n tail
    have hpow : (2 : Int) ^ n.val.toNat = ((2 ^ n.val.toNat : Nat) : Int) :=
      (Int.natCast_pow 2 n.val.toNat).symm
    have hr : 0 ≤ n.val ∧ n.val < ((2 ^ 256 : Nat) : Int) := uint_range n
    have har : 0 ≤ a.val ∧ a.val < ((2 ^ 256 : Nat) : Int) := uint_range a
    have hapos : ¬ a.val < 0 := by omega
    have hc : (n.val.toNat < 256) ↔ n.val < 256 := by omega
    change some ((if (encodeValue .uint n).toNat < 256 then
        (encodeValue .uint a) >>> (encodeValue .uint n).toNat else 0) :: tail) =
      (PrimTy.uint.ofInt? (if n.val < 256 then
        a.val / 2 ^ n.val.toNat else if a.val < 0 then -1 else 0)).map
        (fun v => encodeValue .uint v :: tail)
    rw [encode_uint_toNat]
    by_cases hn : n.val < 256
    · have hnn : n.val.toNat < 256 := hc.mpr hn
      simp only [hn, hnn, if_true]
      have ha : a.val = (a.val.toNat : Int) := by omega
      have he : a.val / (2 ^ n.val.toNat : Int) =
          (((encodeValue .uint a) >>> n.val.toNat).toNat : Int) := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, encode_uint_toNat,
          ha, hpow, ← Int.natCast_ediv]
        simp only [Int.toNat_natCast]
      rw [he]
      exact (encoded_word _ tail).symm
    · have hnn : ¬ n.val.toNat < 256 := fun h => hn (hc.mp h)
      simp only [hn, hnn, hapos, if_false]
      rfl

example : run uintShl.code [7, 256, 99] = some [0, 99] := by decide +kernel
example : run uintShr.code [128, 7, 99] = some [1, 99] := by decide +kernel
example : run uintShl.code [3, 2, 99] ≠ some [16, 99] := by decide +kernel

#print axioms uintShl
#print axioms uintShr

end Solidity.Backend.Scalar
