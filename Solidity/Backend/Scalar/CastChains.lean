import Solidity.Backend.Scalar.Widths
import Solidity.Backend.Scalar.Casts
import Solidity.Backend.Scalar.Wrapping

/-! Arithmetic cast-expansion laws for the existing byte widths. The source
frontend's signedAt expansion uses wrapped addition, low bits and subtraction;
these facts connect that arithmetic expression to SIGNEXTEND, without importing
the elaborator into the component or claiming its source rewriting theorem. -/
namespace Solidity.Backend.Scalar

theorem width_half (w : Fin 32) :
    2 ^ widthBits w = 2 ^ (widthBits w - 1) + 2 ^ (widthBits w - 1) := by
  have hw : 8 ≤ widthBits w ∧ widthBits w ≤ 256 := widthBits_bounds w
  have he : widthBits w = (widthBits w-1)+1 := by omega
  conv => lhs; rw [he, Nat.pow_succ]
  omega

theorem unsignedClean_nat (w : Fin 32) (x : Word) :
    (unsignedClean w x).toNat = x.toNat % 2 ^ widthBits w := by
  have hb : 2 ^ widthBits w ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide : 0 < 2) (widthBits_bounds w).2
  have hx : BitVec.toNat x % 2 ^ widthBits w < 2 ^ widthBits w := Nat.mod_lt x.toNat (Nat.pow_pos (by decide : 0 < 2) (n := widthBits w))
  simp only [unsignedClean, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx hb)]

theorem shifted_low (w : Fin 32) (x : Word) :
    (unsignedClean w (x + BitVec.ofNat 256 (2^(widthBits w-1)))).toNat =
      (x.toNat + 2^(widthBits w-1)) % 2^widthBits w := by
  have hw : 8 ≤ widthBits w ∧ widthBits w ≤ 256 := widthBits_bounds w
  have hh : 2^(widthBits w-1) < 2^256 :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  rw [unsignedClean_nat, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hh,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hw.2)]

theorem signedAt_word (w : Fin 32) (x : Word) :
    unsignedClean w (x + BitVec.ofNat 256 (2^(widthBits w-1))) -
      BitVec.ofNat 256 (2^(widthBits w-1)) = signedClean w x := by
  let B := 2^widthBits w
  let H := 2^(widthBits w-1)
  let low := x.toNat % B
  have hp : 0 < B := Nat.pow_pos (by decide)
  have hb : B=H+H := width_half w
  have hl : low < B := Nat.mod_lt _ hp
  have hh : H < B := by have : 0 < 2 ^ (widthBits w - 1) := Nat.pow_pos (by decide : 0<2) (n := widthBits w-1); dsimp only [H, B] at *; omega
  have he : (x.toNat+H)%B = (low+H)%B := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hh]
  have hclean : unsignedClean w (x+BitVec.ofNat 256 H) = BitVec.ofNat 256 ((low+H)%B) := by
    apply BitVec.eq_of_toNat_eq
    rw [shifted_low, he, BitVec.toNat_ofNat]
    have hbW : 2 ^ widthBits w ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide : 0<2) (widthBits_bounds w).2
    exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) hbW)).symm
  rw [hclean]
  have hcast : (BitVec.ofNat 256 ((low+H)%B) - BitVec.ofNat 256 H) =
      BitVec.ofInt 256 (((low+H)%B : Nat) - (H:Int)) := by
    rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
      BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.sub_eq_add_neg]
  rw [hcast]
  change BitVec.ofInt 256 _ = BitVec.ofInt 256 (if low<H then (low:Int) else (low:Int)-B)
  by_cases hc : low < H
  · rw [if_pos hc, Nat.mod_eq_of_lt (show low+H<B by omega)]
    congr 1
    omega
  · have heq : (low+H)%B = low+H-B := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [if_neg hc, heq]
    congr 1
    omega

def signedExpansionCode (w : Fin 32) : Program :=
  [pushWord (BitVec.ofNat 256 (2^(widthBits w-1))), .op .ADD] ++
    unsignedCode w ++
    [pushWord (BitVec.ofNat 256 (2^(widthBits w-1))), .op (.SWAP ⟨0, by decide⟩), .op .SUB]

theorem signedExpansion_correct (w : Fin 32) (x : Word) (tail : Stack) :
    run (signedExpansionCode w) (x::tail) = some (signedClean w x::tail) := by
  apply run_comp (p := [pushWord (BitVec.ofNat 256 (2^(widthBits w-1))), .op .ADD])
    (q := unsignedCode w ++ [pushWord (BitVec.ofNat 256 (2^(widthBits w-1))),
      .op (.SWAP ⟨0, by decide⟩), .op .SUB])
    (t := (x+BitVec.ofNat 256 (2^(widthBits w-1)))::tail)
  · rw [run, step_pushWord]
    change some ((BitVec.ofNat 256 (2^(widthBits w-1))+x)::tail) = _
    rw [BitVec.add_comm]
  · apply run_comp (unsigned_correct w _ tail)
    rw [run, step_pushWord]
    change some ((unsignedClean w (x+BitVec.ofNat 256 (2^(widthBits w-1))) -
      BitVec.ofNat 256 (2^(widthBits w-1)))::tail) = _
    rw [signedAt_word]


theorem signedClean_nat (w : Fin 32) (x : Word) :
    (signedClean w x).toNat =
      let low := x.toNat % 2^widthBits w
      if low < 2^(widthBits w-1) then low else low+(2^256-2^widthBits w) := by
  let B := 2^widthBits w
  let low := x.toNat%B
  have hB : B ≤ 2^256 := Nat.pow_le_pow_right (by decide) (widthBits_bounds w).2
  have hl : low < B := Nat.mod_lt _ (Nat.pow_pos (by decide))
  change (BitVec.ofInt 256 (if low<2^(widthBits w-1) then (low:Int) else (low:Int)-B)).toNat =
    if low<2^(widthBits w-1) then low else low+(2^256-B)
  by_cases hc : low<2^(widthBits w-1)
  · simp only [hc, if_true, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hl hB)]
  · simp only [hc, if_false]
    have he : (low:Int)-B = ((low+(2^256-B):Nat):Int)-Semantics.uintBound := by
      change (low:Int)-B = ((low+(2^256-B):Nat):Int)-((2^256:Nat):Int)
      omega
    rw [he, ofInt_sub_word, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show low+(2^256-B)<2^256 by omega)]

theorem signed_low_chain (a b : Fin 32) (hab : widthBits a ≤ widthBits b) (x : Word) :
    (signedClean b x).toNat % 2^widthBits a = x.toNat % 2^widthBits a := by
  have hA : 2^widthBits a ∣ 2^256 := Nat.pow_dvd_pow 2 (widthBits_bounds a).2
  have hB : 2^widthBits a ∣ 2^widthBits b := Nat.pow_dvd_pow 2 hab
  have hsub : 2^widthBits a ∣ 2^256-2^widthBits b := Nat.dvd_sub hA hB
  rw [signedClean_nat]
  dsimp only
  split
  · exact Nat.mod_mod_of_dvd _ hB
  · rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hsub, Nat.add_zero,
      Nat.mod_mod, Nat.mod_mod_of_dvd _ hB]

theorem signed_chain (a b : Fin 32) (hab : widthBits a ≤ widthBits b) (x : Word) :
    signedClean a (signedClean b x) = signedClean a x := by
  conv => lhs; rw [signedClean]
  rw [signed_low_chain a b hab x]
  rfl

theorem unsigned_after_signed (a b : Fin 32) (hab : widthBits a ≤ widthBits b) (x : Word) :
    unsignedClean a (signedClean b x) = unsignedClean a x := by
  simp only [unsignedClean, signed_low_chain a b hab x]

example : signedClean ⟨0, by decide⟩ (signedClean ⟨1, by decide⟩ 32768) = 0 := by decide +kernel
example : signedClean ⟨1, by decide⟩ (signedClean ⟨0, by decide⟩ 128) ≠
    signedClean ⟨1, by decide⟩ 128 := by decide +kernel

#print axioms signed_chain
#print axioms unsigned_after_signed

#print axioms signedAt_word
#print axioms signedExpansion_correct
end Solidity.Backend.Scalar
