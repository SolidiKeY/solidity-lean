import Solidity.Backend.Scalar.SignedBits
import Solidity.Backend.Scalar.Comparisons

/-! Signed intrinsic right shift accepts an int count. Negative counts have
source toNat=0; encoding them directly for SAR would instead saturate. The
emitted clamp below preserves that existing source behavior at every input. -/
namespace Solidity.Backend.Scalar

def clampCount (n : Word) : Word := if n.toInt < 0 then 0 else n

def signedShiftPrefix : Program :=
  [.op (.DUP ⟨1, by decide⟩), pushWord 0, .op .SGT, .op .ISZERO,
   .op (.DUP ⟨2, by decide⟩), .op .MUL]

def sarResult (a n : Word) : Word :=
  if n.toNat < 256 then BitVec.ofInt 256 (a.toInt / (2 ^ n.toNat : Int))
  else if a.toInt < 0 then BitVec.ofInt 256 (-1) else 0

def signedShiftCode : Program :=
  signedShiftPrefix ++ [.op .SAR, .op (.SWAP ⟨0, by decide⟩), .op .POP]

theorem signedShiftPrefix_correct (a n : Word) (tail : Stack) :
    run signedShiftPrefix (a :: n :: tail) = some (clampCount n :: a :: n :: tail) := by
  change some ((n * flag (flag (decide (n.toInt < 0)) == 0)) :: a :: n :: tail) = _
  rw [flag_iszero]
  by_cases hn : n.toInt < 0
  · simp only [hn, decide_true, Bool.not_true, flag, clampCount, if_true]
    change some ((n * 0#256) :: a :: n :: tail) = some (0#256 :: a :: n :: tail)
    rw [BitVec.mul_zero]
  · simp only [hn, decide_false, Bool.not_false, flag, if_true, clampCount, if_false]
    change some ((n * 1#256) :: a :: n :: tail) = some (n :: a :: n :: tail)
    rw [BitVec.mul_one]

theorem signedShift_raw (a n : Word) (tail : Stack) :
    run signedShiftCode (a :: n :: tail) = some (sarResult a (clampCount n) :: tail) := by
  exact run_comp (p := signedShiftPrefix)
    (q := [.op .SAR, .op (.SWAP ⟨0, by decide⟩), .op .POP])
    (signedShiftPrefix_correct a n tail) rfl

theorem sar_zero (a : Word) : sarResult a 0 = a := by
  change BitVec.ofInt 256 (a.toInt / (2 ^ 0 : Int)) = a
  rw [Int.pow_zero, Int.ediv_one, BitVec.ofInt_toInt]

theorem encode_int_toNat_of_nonneg (n : PrimTy.int.Denote) (hn : 0 ≤ n.val) :
    (encodeValue .int n).toNat = n.val.toNat := by
  have hw : n.val < ((2 ^ 256 : Nat) : Int) := by have := int_range n; omega
  simp only [encodeValue, BitVec.toNat_ofInt, Int.emod_eq_of_lt hn hw]

/-- Source-exact signed right shift, including negative and saturated counts. -/
def intShr : BinaryCertificate .shr .int rfl where
  code := signedShiftCode
  correct := by
    intro a n tail
    rw [signedShift_raw]
    change some (sarResult (encodeValue .int a) (clampCount (encodeValue .int n)) :: tail) =
      (PrimTy.int.ofInt? (if n.val < 256 then a.val / (2 ^ n.val.toNat : Int)
        else if a.val < 0 then -1 else 0)).map (fun v => encodeValue .int v :: tail)
    simp only [clampCount, encode_int_toInt]
    by_cases hn : n.val < 0
    · have h256 : n.val < 256 := by omega
      have hz : n.val.toNat = 0 := Int.toNat_of_nonpos (by omega)
      simp only [hn, if_true, sar_zero, h256, hz, Int.pow_zero, Int.ediv_one]
      rw [encoded_int a.val a.property]
      rfl
    · have hnonneg : 0 ≤ n.val := by omega
      have hc : n.val.toNat < 256 ↔ n.val < 256 := by omega
      simp only [hn, if_false, sarResult, encode_int_toInt,
        encode_int_toNat_of_nonneg n hnonneg]
      by_cases hs : n.val < 256
      · have hsn : n.val.toNat < 256 := hc.mpr hs
        simp only [hs, hsn, if_true]
        let r : Word := (encodeValue .int a).sshiftRight n.val.toNat
        have he : r.toInt = a.val / (2 ^ n.val.toNat : Int) := by
          rw [BitVec.toInt_sshiftRight, encode_int_toInt, Int.shiftRight_eq_div_pow]
          have hp : (2 : Int) ^ n.val.toNat = ((2 ^ n.val.toNat : Nat) : Int) :=
            (Int.natCast_pow 2 n.val.toNat).symm
          change a.val / ((2 ^ n.val.toNat : Nat) : Int) = _
          rw [← hp]
        rw [← he, BitVec.ofInt_toInt]
        exact (encoded_signed_word r tail).symm
      · have hsn : ¬ n.val.toNat < 256 := fun h => hs (hc.mp h)
        simp only [hs, hsn, if_false]
        by_cases ha : a.val < 0 <;> simp only [ha, if_true, if_false] <;> rfl

/-- Negative intrinsic counts are a real counterexample to unmodified SAR. -/
example : run intShr.code [8, BitVec.ofInt 256 (-1), 99] = some [8, 99] := by decide +kernel
example : run [.op (.SWAP ⟨0, by decide⟩), .op .SAR] [8, BitVec.ofInt 256 (-1), 99] ≠
    some [8, 99] := by decide +kernel
example : run intShr.code [BitVec.ofInt 256 (-7), 256, 99] =
    some [BitVec.ofInt 256 (-1), 99] := by decide +kernel

#print axioms signedShiftPrefix_correct
#print axioms intShr

end Solidity.Backend.Scalar
