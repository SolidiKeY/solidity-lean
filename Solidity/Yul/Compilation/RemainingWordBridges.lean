import Solidity.Yul.Compilation.ModularExpressions
import Solidity.Yul.Compilation.ByteLowering
/-! Concrete remaining source/target pure-word representation agreements.
Existing semantics and standard extraction/CLZ are reused; no word semantics,
AST, native CLZ instruction support or source admission is introduced. -/
namespace Solidity.Yul.Compilation.RemainingWordBridges
open Backend Scalar
open Solidity.Yul.Closed ProducerExpressions

def selectExp : BinarySelection := ⟨.EXP,(Scalar.binary .EXP).getD (fun _ _ => 0),fun _ _ _ => rfl⟩
def selectSignextend : BinarySelection := ⟨.SIGNEXTEND,(Scalar.binary .SIGNEXTEND).getD (fun _ _ => 0),fun _ _ _ => rfl⟩

def expBridge : BinaryBridge .exp := ⟨selectExp,by
  intro a b
  apply Fin.ext
  change (a.toNat ^ b.toNat) % 2^256 = (powWord a.toFin b.toNat).val
  exact (powWord_correct a.toFin b.toNat).symm⟩

theorem byte_agreement (index value : Scalar.Word) :
    (indexedByteWindow index value).toFin =
      (Pure.byte).eval (Fin.cases index.toFin (fun _ => value.toFin)) := by
  apply Fin.ext
  change (if index.toNat < 32 then byteWindow (8*(31-index.toNat)) value else 0).toNat =
    (if index.toNat ≥ 32 then word 0 else word ((value.toNat >>> (8*(31-index.toNat))) % 256)).val
  by_cases small : index.toNat < 32
  · rw [if_pos small,if_neg (by omega)]
    simp only [byteWindow,BitVec.zeroExtend_eq_setWidth,BitVec.toNat_setWidth,BitVec.extractLsb'_toNat]
    rfl
  · rw [if_neg small,if_pos (by omega)]
    rfl

theorem clz_agreement (value : Scalar.Word) : value.clz.toFin = Solidity.Yul.clz value.toFin := by
  apply Fin.ext
  change value.clz.toNat = (if value.toNat = 0 then 256 else 255-value.toNat.log2) % 2^256
  by_cases zero : value = 0
  · subst value
    have count : (0 : Scalar.Word).clz = 256 := BitVec.clz_eq_iff_eq_zero.mpr rfl
    rw [count]
    rfl
  · have nonzero : value.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
    have bound : value.clz.toNat < 256 := (BitVec.clz_lt_iff_ne_zero).mpr zero
    have lower := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (x := value) (by decide) zero
    have upper := BitVec.toNat_lt_two_pow_sub_clz (x := value)
    have indices : 256-value.clz.toNat = (255-value.clz.toNat)+1 := by omega
    have logarithm : value.toNat.log2 = 255-value.clz.toNat :=
      (Nat.log2_eq_iff nonzero).mpr ⟨lower,by rw [← indices]; exact upper⟩
    rw [if_neg nonzero,Nat.mod_eq_of_lt (by
      have positive : 256 < 2^256 := by decide
      omega)]
    omega

private theorem nat_word (n : Nat) : (BitVec.ofInt 256 (n : Int)).toFin = word n := by
  apply Fin.ext
  change (BitVec.ofInt 256 (n : Int)).toNat = n % 2^256
  rw [BitVec.toNat_ofInt,← Int.natCast_emod,Int.toNat_natCast]

private theorem sub_word (low bits : Nat) (bound : bits ≤ 256) :
    (BitVec.ofInt 256 ((low : Int)-(2^bits : Nat))).toFin = word (low+2^256-2^bits) := by
  have size : 2^bits ≤ 2^256 := Nat.pow_le_pow_right (by decide) bound
  have lifted : ((low+2^256-2^bits : Nat) : Int) = (low : Int)-(2^bits : Nat)+(2^256 : Nat) := by omega
  have modular : ((low+2^256-2^bits : Nat) : Int) % (2^256 : Nat) =
      ((low : Int)-(2^bits : Nat)) % (2^256 : Nat) := by rw [lifted,Int.add_emod_right]
  have natural := congrArg Int.toNat modular
  rw [← Int.natCast_emod,Int.toNat_natCast] at natural
  apply Fin.ext
  change (BitVec.ofInt 256 ((low : Int)-(2^bits : Nat))).toNat = (low+2^256-2^bits) % 2^256
  rw [BitVec.toNat_ofInt]
  exact natural.symm

private theorem full_width (value : Scalar.Word) :
    (BitVec.ofInt 256 (if value.toNat < 2^255 then (value.toNat : Int)
      else (value.toNat : Int)-(2^256 : Nat))).toFin = value.toFin := by
  by_cases sign : value.toNat < 2^255
  · rw [if_pos sign,nat_word]
    exact Fin.ext (Nat.mod_eq_of_lt value.isLt)
  · rw [if_neg sign,sub_word _ 256 (by decide),Nat.add_sub_cancel]
    exact Fin.ext (Nat.mod_eq_of_lt value.isLt)

def signextendBridge : BinaryBridge .signextend := ⟨selectSignextend,by
  intro index value
  change (if index.toNat < 32 then
      BitVec.ofInt 256 (if value.toNat % 2^(8*(index.toNat+1)) < 2^(8*(index.toNat+1)-1)
        then ((value.toNat % 2^(8*(index.toNat+1)) : Nat) : Int)
        else ((value.toNat % 2^(8*(index.toNat+1)) : Nat) : Int)-(2^(8*(index.toNat+1)) : Nat))
      else value).toFin = Solidity.Yul.signextend index.toFin value.toFin
  by_cases small : index.toNat < 31
  · have targetSmall : index.toNat < 32 := by omega
    rw [if_pos targetSmall]
    unfold Solidity.Yul.signextend
    simp only [BitVec.val_toFin]
    rw [if_neg (show ¬ index.toNat ≥ 31 by omega)]
    by_cases sign : value.toNat % 2^(8*(index.toNat+1)) < 2^(8*(index.toNat+1)-1)
    · rw [if_pos sign,if_pos sign]
      exact nat_word _
    · rw [if_neg sign,if_neg sign]
      exact sub_word _ _ (by omega)
  · by_cases last : index.toNat = 31
    · have targetSmall : index.toNat < 32 := by omega
      rw [if_pos targetSmall]
      unfold Solidity.Yul.signextend
      simp only [BitVec.val_toFin]
      rw [if_pos (show index.toNat ≥ 31 by omega)]
      have width : 8*(index.toNat+1) = 256 := by omega
      rw [width,Nat.mod_eq_of_lt value.isLt]
      exact full_width value
    · have large : ¬ index.toNat < 32 := by omega
      rw [if_neg large]
      unfold Solidity.Yul.signextend
      simp only [BitVec.val_toFin]
      rw [if_pos (show index.toNat ≥ 31 by omega)]⟩

#print axioms expBridge
#print axioms byte_agreement
#print axioms clz_agreement
#print axioms signextendBridge
end Solidity.Yul.Compilation.RemainingWordBridges
