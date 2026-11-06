import SolidityBridge.ExternalEvm.MemoryBytes

/-! The H7 logical zeroes body supplies the existing bounded padding contract.
It does not prove native allocation/extern correctness. Reader laws below use
actual ByteArray operations, with USize width bounds explicit. -/
namespace Solidity.Evm.External.Memory

theorem paddingCorrect_bounded (bound : Nat) (host : bound < USize.size)
    (fits64 : bound < 2^64) : PaddingCorrect bound := by
  refine ⟨fits64,?_⟩
  intro n hn
  have fits : n < USize.size := Nat.lt_of_le_of_lt hn host
  have he : (USize.ofNat n).toNat = n := Nat.mod_eq_of_lt fits
  simp only [ffi.ByteArray.zeroes,he]

/-- The host-width bound already implies the 64-bit reader bound on every
supported USize platform. Keep paddingCorrect_bounded for existing clients. -/
theorem paddingCorrect_of_host_bound (bound : Nat) (host : bound < USize.size) :
    PaddingCorrect bound := by
  have host64 : USize.size ≤ 2^64 := by
    rcases USize.size_eq with h | h <;> rw [h] <;> decide
  exact paddingCorrect_bounded bound host (Nat.lt_of_lt_of_le host host64)

theorem paddingCorrect32 : PaddingCorrect 32 := by
  apply paddingCorrect_of_host_bound
  rcases USize.size_eq with h | h <;> rw [h] <;> decide

theorem readWithoutPadding_zero (source : ByteArray) (addr : Nat) :
    source.readWithoutPadding addr 0 = ByteArray.empty := by
  unfold ByteArray.readWithoutPadding
  split
  · rfl
  · apply congrArg ByteArray.mk
    simp only [ByteArray.empty,ByteArray.emptyWithCapacity,
      Nat.zero_min,Nat.add_zero,Nat.sub_self,Array.extract_empty,
      Array.append_empty,Array.extract_empty_of_stop_le_start (Nat.le_refl addr)]

theorem readWithPadding_zero (source : ByteArray) (addr : Nat) :
    source.readWithPadding addr 0 = ByteArray.empty := by
  rw [ByteArray.readWithPadding,if_neg (by decide : ¬ (0 : Nat) ≥ 2^64)]
  rw [readWithoutPadding_zero]
  simp only [ByteArray.size_empty,BitVec.sub_self]
  change ByteArray.empty ++ ffi.ByteArray.zeroes (0 : USize) = ByteArray.empty
  rw [ffi.ByteArray.zeroes_zero]
  rfl

/-- Existing owner serialization theorem now has a proved bounded supplier;
this is word serialization, not ABI/source or native correctness. -/
theorem serialize_h7 (word : EvmYul.UInt256) :
    word.toByteArray.size = 32 ∧ EvmYul.fromByteArrayBigEndian word.toByteArray = word.toNat :=
  serialize 32 paddingCorrect32 (Nat.le_refl 32) word

/-- Actual reader constructors subtract in BitVec/USize. This supplies that
bounded difference without assuming a mathematical Nat subtraction silently. -/
theorem zeroes_difference (n m : Nat) (fits : n < USize.size) (le : m ≤ n) :
    ffi.ByteArray.zeroes (⟨(n : BitVec System.Platform.numBits) -
      (m : BitVec System.Platform.numBits)⟩ : USize) =
      ⟨Array.replicate (n-m) (0 : UInt8)⟩ := by
  have cast : (⟨(n : BitVec System.Platform.numBits) -
      (m : BitVec System.Platform.numBits)⟩ : USize) = USize.ofNat (n-m) := by
    congr 1
    exact BitVec.ofNat_sub_ofNat_of_le n m (Nat.lt_of_le_of_lt le fits) le
  rw [cast]
  have hn : (USize.ofNat (n-m)).toNat = n-m :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le n m) fits)
  simp only [ffi.ByteArray.zeroes,hn]

end Solidity.Evm.External.Memory
