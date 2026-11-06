import Solidity.Lowering.V07.SignedWidthCasts

/-! Signed narrowing identities over the existing Source integer carrier. -/
namespace Solidity.Lowering.V07.SignedNarrowing
open SignedWidthCasts (ty)

theorem wrap_of_range (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (n : Int) (hn : (ty bits valid).lo ≤ n ∧ n ≤ (ty bits valid).hi) :
    (ty bits valid).wrap n = n := by
  let half : Int := ((2^(bits-1) : Nat) : Int)
  let modulus : Int := ((2^bits : Nat) : Int)
  have hp : 0 < half := Int.ofNat_lt.mpr (Source.two_pow_pos (bits-1))
  have hm : modulus = 2*half := by
    change ((2^bits : Nat) : Int) = 2*((2^(bits-1) : Nat) : Int)
    rw [Source.two_pow_succ_pred (by omega),Int.natCast_mul]
    rfl
  have hh : ((2^(bits-1)-1 : Nat) : Int) = half-1 := by
    have hp' := Source.two_pow_pos (bits-1)
    dsimp [half]
    omega
  change -half ≤ n ∧ n ≤ ((2^(bits-1)-1 : Nat) : Int) at hn
  rw [hh] at hn
  rw [SignedWidthCasts.wrap_eq]
  change (if n%modulus < half then n%modulus else n%modulus-modulus) = n
  by_cases sign : 0 ≤ n
  · have residue : n%modulus = n := Int.emod_eq_of_lt sign (by omega)
    rw [residue]
    split <;> omega
  · have residue : n%modulus = n+modulus := by
      calc
        n%modulus = (n+modulus)%modulus := Int.emod_eq_add_self_emod
        _ = n+modulus := Int.emod_eq_of_lt (by omega) (by omega)
    rw [residue]
    split <;> omega

theorem wrap_word (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (n : Int) :
    (ty bits valid).wrap (WordCasts.signed.wrap n) = (ty bits valid).wrap n := by
  let modulus : Int := ((2^bits : Nat) : Int)
  have hm : Semantics.uintBound % modulus = 0 := by
    have h := UnsignedNarrowing.word_then_narrow bits valid.2.2 Semantics.uintBound
    simpa only [Int.emod_self,Int.zero_emod] using h.symm
  have residue : WordCasts.signed.wrap n % modulus = n % modulus := by
    simp only [WordCasts.signed,Source.IntTy.wrap,Source.wrapBits,true_and]
    change (if Source.bitsHi true 256 < n%Semantics.uintBound
      then n%Semantics.uintBound-Semantics.uintBound else n%Semantics.uintBound)%modulus = n%modulus
    split
    · rw [Int.sub_emod,hm,Int.sub_zero,Int.emod_emod]
      exact UnsignedNarrowing.word_then_narrow bits valid.2.2 n
    · exact UnsignedNarrowing.word_then_narrow bits valid.2.2 n
  rw [SignedWidthCasts.wrap_eq,SignedWidthCasts.wrap_eq,residue]

end Solidity.Lowering.V07.SignedNarrowing
