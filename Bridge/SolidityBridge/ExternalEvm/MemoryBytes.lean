import SolidityBridge.ExternalEvm.Memory
import Batteries.Data.ByteArray

/-! Byte-memory laws conditional only on the upstream opaque zero allocator.
No correctness contract is installed as an axiom. -/
namespace Solidity.Evm.External.Memory
open private EvmYul.toBytes'_UInt256_le EvmYul.fromBytes'_toBytes'
  EvmYul.extend_bytes_zero EvmYul.toBytes' from EvmYul.UInt256

private theorem bytes_list_loop (b : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  unfold ByteArray.toList.loop
  split
  next h =>
    rw [bytes_list_loop b (i + 1) (b.get! i :: r)]
    simp only [List.reverse_cons, List.append_assoc]
    congr 1
    change [b.data[i]!] ++ b.data.toList.drop (i + 1) = b.data.toList.drop i
    rw [List.drop_eq_getElem_cons (l := b.data.toList) (i := i) (by simpa only [Array.length_toList] using h)]
    rw [getElem!_pos b.data i h]
    rfl
  next h =>
    rw [List.drop_eq_nil_iff.mpr (by simpa only [Array.length_toList] using Nat.le_of_not_gt h), List.append_nil]
termination_by b.size - i

theorem bytes_list (b : ByteArray) : b.toList = b.data.toList := by
  exact bytes_list_loop b 0 []

private theorem list_bytes_loop (l : List UInt8) (r : ByteArray) :
    (List.toByteArray.loop l r).data = r.data ++ l.toArray := by
  induction l generalizing r with
  | nil => exact Array.append_empty.symm
  | cons b bs ih =>
    rw [List.toByteArray.loop, ih, ByteArray.data_push]
    conv_rhs => rw [List.toArray_cons]
    rw [Array.push_eq_append_singleton, Array.append_assoc]

theorem list_bytes (l : List UInt8) : l.toByteArray.data = l.toArray := by
  simpa only [List.toByteArray, ByteArray.empty, ByteArray.emptyWithCapacity,
    Array.empty_append] using list_bytes_loop l .empty

theorem be_size (v : EvmYul.UInt256) : (BE v.toNat).size ≤ 32 := by
  simpa only [BE, Function.comp_apply, ByteArray.size, list_bytes,
    List.size_toArray, EvmYul.toBytesBigEndian, List.length_reverse, EvmYul.UInt256.toNat] using
    EvmYul.toBytes'_UInt256_le v.val.isLt

/-- Mathematical 32-byte big-endian encoding, independent of the FFI. -/
def encoding (v : EvmYul.UInt256) : ByteArray :=
  ⟨Array.replicate (32 - (BE v.toNat).size) (0 : UInt8)⟩ ++ BE v.toNat

theorem encoding_spec (v : EvmYul.UInt256) :
    (encoding v).size = 32 ∧ EvmYul.fromByteArrayBigEndian (encoding v) = v.toNat := by
  have hs := be_size v
  constructor
  · unfold encoding
    rw [ByteArray.size_append]
    simp only [ByteArray.size, Array.size_replicate]
    change (BE v.toNat).data.size ≤ 32 at hs
    omega
  · simp only [encoding, EvmYul.fromByteArrayBigEndian,
      bytes_list, ByteArray.data_append, Array.toList_append, Array.toList_replicate,
      EvmYul.fromBytesBigEndian, Function.comp_apply, List.reverse_append,
      List.reverse_replicate, BE, list_bytes,
      EvmYul.toBytesBigEndian, List.reverse_reverse, EvmYul.extend_bytes_zero,
      EvmYul.fromBytes'_toBytes']

theorem serialize_eq (bound : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound)
    (v : EvmYul.UInt256) : v.toByteArray = encoding v := by
  have hs := be_size v
  have he : (⟨32 - (BE v.toNat).size⟩ : USize) = USize.ofNat (32 - (BE v.toNat).size) := by
    congr 1
    exact BitVec.ofNat_sub_ofNat_of_le 32 _
      (by rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega) hs
  have hz := hp.2 (32 - (BE v.toNat).size) (by omega)
  change ffi.ByteArray.zeroes (USize.ofNat (32 - (BE v.toNat).size)) = _ at hz
  unfold encoding
  rw [EvmYul.UInt256.toByteArray, he, hz]

theorem serialize (bound : Nat) (hp : PaddingCorrect bound) (hb : 32 ≤ bound)
    (v : EvmYul.UInt256) :
    v.toByteArray.size = 32 ∧ EvmYul.fromByteArrayBigEndian v.toByteArray = v.toNat := by
  rw [serialize_eq bound hp hb v]
  exact encoding_spec v

theorem padding_zero (bound : Nat) (hp : PaddingCorrect bound) :
    ffi.ByteArray.zeroes (USize.ofNat 0) = ByteArray.empty := by
  exact hp.2 0 (Nat.zero_le _)

/-- An in-bounds full-word write needs only the length-zero allocator contract. -/
theorem write_inbounds (source dest : ByteArray) (a : Nat)
    (hz : ffi.ByteArray.zeroes (USize.ofNat 0) = ByteArray.empty)
    (hs : source.size = 32) (ha : a + 32 ≤ dest.size) :
    (ByteArray.write source 0 dest a 32).data =
      dest.data.extract 0 a ++ source.data ++ dest.data.extract (a + 32) dest.size := by
  have hz0 : ffi.ByteArray.zeroes ⟨((0 : Nat) : BitVec System.Platform.numBits)⟩ = ByteArray.empty := by
    convert hz using 1
  have hmin : min dest.size (a + 32) = a + 32 := Nat.min_eq_right ha
  have hpad : a - dest.size = 0 := Nat.sub_eq_zero_of_le (by omega)
  simp only [ByteArray.write, Nat.reduceEqDiff, ↓reduceIte, hs, Nat.not_le.mpr (by omega : 0 < 32),
    Nat.sub_zero, Nat.min_self, hmin, Nat.sub_self, hpad, Nat.add_zero]
  rw [hz0]
  simp only [ByteArray.data_copySlice, ByteArray.data_append, ByteArray.empty,
    ByteArray.emptyWithCapacity, Array.append_empty, Nat.zero_add]
  have hsrc : source.data.size = 32 := hs
  rw [← hsrc, Array.extract_size, Nat.sub_zero, Nat.min_self]
  rfl

theorem write_size (source dest : ByteArray) (a : Nat)
    (hz : ffi.ByteArray.zeroes (USize.ofNat 0) = ByteArray.empty)
    (hs : source.size = 32) (ha : a + 32 ≤ dest.size) :
    (ByteArray.write source 0 dest a 32).size = dest.size := by
  change (ByteArray.write source 0 dest a 32).data.size = dest.size
  rw [write_inbounds source dest a hz hs ha]
  simp only [Array.size_append, Array.size_extract]
  change min a dest.size - 0 + source.size + (min dest.size dest.size - (a + 32)) = dest.size
  rw [Nat.min_eq_left (by omega), Nat.min_self, hs]
  omega

theorem write_get_same (source dest : ByteArray) (a j : Nat)
    (hz : ffi.ByteArray.zeroes (USize.ofNat 0) = ByteArray.empty)
    (hs : source.size = 32) (ha : a + 32 ≤ dest.size) (hj : j < 32) :
    (ByteArray.write source 0 dest a 32).data[a + j]! = source.data[j]! := by
  rw [write_inbounds source dest a hz hs ha]
  have hdest : dest.data.size = dest.size := rfl
  have hd : (dest.data.extract 0 a).size = a := by
    simp only [Array.size_extract, Nat.sub_zero]; exact Nat.min_eq_left (by omega)
  have hsrc : source.data.size = 32 := hs
  rw [getElem!_pos _ _ (by simp only [Array.size_append, hd, hsrc]; omega)]
  rw [Array.getElem_append_left (by simp only [Array.size_append, hd, hsrc]; omega)]
  rw [Array.getElem_append_right (by omega)]
  simp only [hd, Nat.add_sub_cancel_left]
  exact (getElem!_pos source.data j (by omega)).symm

/-- Every physical byte outside the written interval is framed. -/
theorem write_get_frame (source dest : ByteArray) (a k : Nat)
    (hz : ffi.ByteArray.zeroes (USize.ofNat 0) = ByteArray.empty)
    (hs : source.size = 32) (ha : a + 32 ≤ dest.size)
    (hk : k < dest.size) (hout : k < a ∨ a + 32 ≤ k) :
    (ByteArray.write source 0 dest a 32).data[k]! = dest.data[k]! := by
  rw [write_inbounds source dest a hz hs ha]
  have hdest : dest.data.size = dest.size := rfl
  have hd : (dest.data.extract 0 a).size = a := by
    simp only [Array.size_extract, Nat.sub_zero]; exact Nat.min_eq_left (by omega)
  have hsrc : source.data.size = 32 := hs
  have he : (dest.data.extract (a + 32) dest.size).size = dest.size - (a + 32) := by
    simp only [Array.size_extract, hdest, Nat.min_self]
  rw [getElem!_pos _ _ (by simp only [Array.size_append, hd, hsrc, he]; omega)]
  rw [getElem!_pos dest.data k (by omega)]
  rcases hout with h | h
  · rw [Array.getElem_append_left (by simp only [Array.size_append, hd, hsrc]; omega),
      Array.getElem_append_left (by omega), Array.getElem_extract]
    simp only [Nat.zero_add]
  · rw [Array.getElem_append_right (by simp only [Array.size_append, hd, hsrc]; omega),
      Array.getElem_extract]
    simp only [Array.size_append, hd, hsrc, Nat.add_sub_of_le h]

/-- Full in-bounds padded reads are ordinary slices, including the allocator's
length-zero call. This does not assume the readback conclusion. -/
theorem read_inbounds (dest : ByteArray) (a : Nat)
    (hz : ffi.ByteArray.zeroes (USize.ofNat 0) = ByteArray.empty)
    (ha : a + 32 ≤ dest.size) :
    dest.readWithPadding a 32 = dest.extract a (a + 32) := by
  have hread : (dest.readWithoutPadding a 32).size = 32 := by
    simp only [ByteArray.readWithoutPadding, Nat.not_le.mpr (by omega : a < dest.size),
      ↓reduceIte, Nat.min_eq_left (by omega : 32 ≤ dest.size), ByteArray.size_extract,
      Nat.min_eq_left ha]
    omega
  have hz0 : ffi.ByteArray.zeroes ⟨BitVec.ofNat System.Platform.numBits 0⟩ = ByteArray.empty := by
    convert hz using 1
  have hr : dest.readWithoutPadding a 32 = dest.extract a (a + 32) := by
    simp only [ByteArray.readWithoutPadding, Nat.not_le.mpr (by omega : a < dest.size),
      ↓reduceIte, Nat.min_eq_left (by omega : 32 ≤ dest.size)]
  simp only [ByteArray.readWithPadding, show ¬32 ≥ 2^64 by decide, ↓reduceIte]
  rw [hread]
  simp only [BitVec.sub_self, hz0, hr]
  apply ByteArray.ext
  simp only [ByteArray.data_append, ByteArray.empty, ByteArray.emptyWithCapacity,
    Array.append_empty]

/-- A bytewise 32-byte representation entails the actual upstream padded read. -/
theorem readback (dest source : ByteArray) (a : Nat)
    (hz : ffi.ByteArray.zeroes (USize.ofNat 0) = ByteArray.empty)
    (hs : source.size = 32) (ha : a + 32 ≤ dest.size)
    (hbytes : ∀ j, j < 32 → dest.data[a + j]! = source.data[j]!) :
    dest.readWithPadding a 32 = source := by
  rw [read_inbounds dest a hz ha]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract]
    change min (a + 32) dest.size - a = source.size
    rw [Nat.min_eq_left ha, hs]; omega
  · intro j hj hj'
    have hj32 : j < 32 := by change j < source.size at hj'; omega
    rw [Array.getElem_extract]
    have hb := hbytes j hj32
    rw [getElem!_pos dest.data (a + j) (by change a + j < dest.size; omega),
      getElem!_pos source.data j hj'] at hb
    exact hb

theorem write_readback (source dest : ByteArray) (a : Nat)
    (hz : ffi.ByteArray.zeroes (USize.ofNat 0) = ByteArray.empty)
    (hs : source.size = 32) (ha : a + 32 ≤ dest.size) :
    (ByteArray.write source 0 dest a 32).readWithPadding a 32 = source := by
  apply readback _ _ a hz hs
  · rw [write_size source dest a hz hs ha]; exact ha
  · intro j hj; exact write_get_same source dest a j hz hs ha hj

end Solidity.Evm.External.Memory

/-- info: 'Solidity.Evm.External.Memory.encoding_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.encoding_spec

/-- info: 'Solidity.Evm.External.Memory.serialize_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.serialize_eq

/-- info: 'Solidity.Evm.External.Memory.serialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.serialize

/-- info: 'Solidity.Evm.External.Memory.write_get_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.write_get_frame

/-- info: 'Solidity.Evm.External.Memory.write_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Memory.write_readback
