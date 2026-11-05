import EvmYul.EVM.PrecompiledContracts
import Solidity.Precompiles.Osaka

/-! Exact byte-list conversion and natural gas arithmetic at the pinned vendor.
The loop proof follows the existing read-only ExternalEvm.MemoryBytes lemma;
no padding/crypto contract or interpreter is introduced. -/
namespace SolidityBridge.PrecompileAgreement
open Solidity.Precompiles EvmYul

private theorem list_loop (b : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  unfold ByteArray.toList.loop
  split
  next h =>
    rw [list_loop b (i + 1) (b.get! i :: r)]
    simp only [List.reverse_cons, List.append_assoc]
    congr 1
    change [b.data[i]!] ++ b.data.toList.drop (i + 1) = b.data.toList.drop i
    rw [List.drop_eq_getElem_cons (l := b.data.toList) (i := i)
      (by simpa only [Array.length_toList] using h)]
    rw [getElem!_pos b.data i h]
    rfl
  next h =>
    rw [List.drop_eq_nil_iff.mpr
      (by simpa only [Array.length_toList] using Nat.le_of_not_gt h), List.append_nil]
termination_by b.size - i

theorem byte_list (b : ByteArray) : b.toList = b.data.toList := list_loop b 0 []

theorem byte_length (b : ByteArray) : b.toList.length = b.size := by
  rw [byte_list, Array.length_toList]
  rfl

theorem ofNat_nat (n : Nat) (h : n < UInt256.size) : (UInt256.ofNat n).toNat = n :=
  Nat.mod_eq_of_lt h

theorem subtract_nat (g : UInt256) (n : Nat) (h : n ≤ g.toNat) :
    (g - UInt256.ofNat n).toNat = g.toNat - n := by
  have hn : n < UInt256.size := Nat.lt_of_le_of_lt h g.val.isLt
  have value : (UInt256.ofNat n).toNat = n := ofNat_nat n hn
  change (g.val - (UInt256.ofNat n).val).val = _
  rw [Fin.sub_val_of_le (show (UInt256.ofNat n).val ≤ g.val from by
    change (UInt256.ofNat n).toNat ≤ g.toNat
    rw [value]
    exact h)]
  change g.toNat - (UInt256.ofNat n).toNat = _
  rw [value]

theorem words_multiple (n : Nat) : words (32 * n) = n := by unfold words; omega

theorem words_next (n : Nat) : words (32 * n + 1) = n + 1 := by unfold words; omega

theorem words_last (n : Nat) : words (32 * n + 31) = n + 1 := by unfold words; omega

theorem words_boundary (n : Nat) : words (32 * n + 32) = n + 1 := by unfold words; omega

theorem words_rounding (n : Nat) :
    words n = n / 32 + if n % 32 = 0 then 0 else 1 := by
  unfold words
  split <;> omega

end SolidityBridge.PrecompileAgreement
