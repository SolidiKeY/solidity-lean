import SolidityBridge.PrecompileAgreement.Gas

/-! Big-endian header agreement on its actual common domain. Short BLAKE2F
headers remain a price mismatch: core right-pads, vendor extract does not. -/
namespace SolidityBridge.PrecompileAgreement
open Solidity Solidity.Precompiles Solidity.Roadmap.Evm EvmYul

private theorem be_append_byte (bs : List UInt8) (b : UInt8) :
    ofBE ((bs ++ [b]).map UInt8.toNat) = 256 * ofBE (bs.map UInt8.toNat) + b.toNat := by
  simp only [ofBE, Hashes.ofBytes, List.map_append, List.map_cons, List.map_nil,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem little_reader (bs : List UInt8) :
    fromBytes' bs = ofBE (bs.reverse.map UInt8.toNat) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change b.toNat + 256 * fromBytes' bs = ofBE ((b :: bs).reverse.map UInt8.toNat)
    rw [List.reverse_cons, be_append_byte, ih]
    omega

theorem big_reader (bs : List UInt8) : fromBytesBigEndian bs = ofBE (bs.map UInt8.toNat) := by
  change fromBytes' bs.reverse = _
  rw [little_reader, List.reverse_reverse]

theorem first_four (d : ByteArray) : (d.extract 0 4).toList = d.toList.take 4 := by
  rw [byte_list, byte_list]
  simp only [ByteArray.extract, ByteArray.copySlice, ByteArray.empty, ByteArray.emptyWithCapacity,
    Array.extract_empty, Array.empty_append, Array.append_empty, Array.toList_extract,
    List.extract, Nat.sub_zero, Nat.zero_add, List.drop_zero]

private theorem append_zero (bs : List Nat) : ofBE (bs ++ [0]) = 256 * ofBE bs := by
  simp only [ofBE, Hashes.ofBytes, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.add_zero]

theorem zero_padding (bs : List Nat) (n : Nat) :
    ofBE (bs ++ List.replicate n 0) = ofBE bs * 256 ^ n := by
  induction n with
  | zero => simp only [List.replicate_zero, List.append_nil, Nat.pow_zero, Nat.mul_one]
  | succ n ih =>
    rw [List.replicate_succ', ← List.append_assoc, append_zero, ih, Nat.pow_succ]
    exact (Nat.mul_comm 256 _).trans (Nat.mul_assoc _ _ _)

/-- Full relationship at every length, including malformed short headers. -/
theorem blake_padding (d : ByteArray) :
    Osaka.gas .blake2f d.toList =
      fromByteArrayBigEndian (d.extract 0 4) * 256 ^ (4 - min 4 d.size) := by
  simp only [Osaka.gas, Blake2f.gas, Blake2f.rounds, readNat, readPad, List.drop_zero]
  rw [zero_padding]
  simp only [List.length_map, List.length_take, byte_length,
    fromByteArrayBigEndian, big_reader, first_four]

theorem blake_zero_header (d : ByteArray)
    (zero : fromByteArrayBigEndian (d.extract 0 4) = 0) : Osaka.gas .blake2f d.toList = 0 := by
  rw [blake_padding, zero, Nat.zero_mul]

theorem blake_price (d : ByteArray) (header : 4 ≤ d.size) :
    Osaka.gas .blake2f d.toList = fromByteArrayBigEndian (d.extract 0 4) := by
  simp only [Osaka.gas, Blake2f.gas, Blake2f.rounds, readNat, readPad, List.drop_zero,
    fromByteArrayBigEndian, big_reader, first_four]
  have len : ((d.toList.take 4).map UInt8.toNat).length = 4 := by
    simp only [List.length_map, List.length_take, byte_length]
    omega
  rw [len, Nat.sub_self, List.replicate_zero, List.append_nil]

theorem blake_gas (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (header : 4 ≤ I.calldata.size) :
    (Ξ_BLAKE2_F σ g A I).2.2.1.toNat =
      if (Ξ_BLAKE2_F σ g A I).1 then g.toNat - Osaka.gas .blake2f I.calldata.toList else 0 := by
  rw [blake_price _ header]
  by_cases short : g.toNat < fromByteArrayBigEndian (I.calldata.extract 0 4)
  · simp only [Ξ_BLAKE2_F, short, if_true]
    rfl
  · simp only [Ξ_BLAKE2_F, short, if_false]
    generalize ffi.BLAKE2 I.calldata = outcome
    cases outcome with
    | error error => rfl
    | ok output => exact subtract_nat g _ (Nat.le_of_not_gt short)

/-- Validation and charging of the actual BLAKE2F wrapper, without comparing
its opaque compression output. -/
theorem blake_valid (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (enough : fromByteArrayBigEndian (I.calldata.extract 0 4) ≤ g.toNat)
    (size : I.calldata.size = 213) (flag : I.calldata[212]! = 0) :
    Ξ_BLAKE2_F σ g A I =
      (true, σ, g - .ofNat (fromByteArrayBigEndian (I.calldata.extract 0 4)), A,
        ffi.BLAKE2Compress I.calldata) := by
  simp only [Ξ_BLAKE2_F, Nat.not_lt_of_ge enough, if_false, ffi.BLAKE2, size, flag]
  rfl

theorem blake_insufficient (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (short : g.toNat < fromByteArrayBigEndian (I.calldata.extract 0 4)) :
    Ξ_BLAKE2_F σ g A I = (false, ∅, ⟨0⟩, A, .empty) := by
  simp only [Ξ_BLAKE2_F, short, if_true]
  rfl

theorem blake_invalid_flag (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (size : I.calldata.size = 213) (flag : I.calldata[212]! = 2) :
    Ξ_BLAKE2_F σ g A I = (false, ∅, ⟨0⟩, A, .empty) := by
  by_cases short : g.toNat < fromByteArrayBigEndian (I.calldata.extract 0 4)
  · exact blake_insufficient σ g A I short
  · simp only [Ξ_BLAKE2_F, short, if_false, ffi.BLAKE2, size, flag]
    rfl

theorem blake_valid_one (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (enough : fromByteArrayBigEndian (I.calldata.extract 0 4) ≤ g.toNat)
    (size : I.calldata.size = 213) (flag : I.calldata[212]! = 1) :
    Ξ_BLAKE2_F σ g A I =
      (true, σ, g - .ofNat (fromByteArrayBigEndian (I.calldata.extract 0 4)), A,
        ffi.BLAKE2Compress I.calldata) := by
  simp only [Ξ_BLAKE2_F, Nat.not_lt_of_ge enough, if_false, ffi.BLAKE2, size, flag]
  rfl

theorem blake_invalid_size (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (size : I.calldata.size ≠ 213) :
    Ξ_BLAKE2_F σ g A I = (false, ∅, ⟨0⟩, A, .empty) := by
  by_cases short : g.toNat < fromByteArrayBigEndian (I.calldata.extract 0 4)
  · exact blake_insufficient σ g A I short
  · simp only [Ξ_BLAKE2_F, short, if_false, ffi.BLAKE2, bne_iff_ne]
    rw [if_pos size]
    rfl

/-- Even a short zero header has a common price; every vendor error still
consumes all gas. No four-byte premise is needed in this case. -/
theorem blake_zero_gas (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (zero : fromByteArrayBigEndian (I.calldata.extract 0 4) = 0) :
    (Ξ_BLAKE2_F σ g A I).2.2.1.toNat =
      if (Ξ_BLAKE2_F σ g A I).1 then g.toNat - Osaka.gas .blake2f I.calldata.toList else 0 := by
  rw [blake_zero_header _ zero]
  simp only [Ξ_BLAKE2_F, zero, Nat.not_lt_zero, if_false]
  generalize ffi.BLAKE2 I.calldata = outcome
  cases outcome with
  | error error => rfl
  | ok output => exact subtract_nat g 0 (Nat.zero_le _)

end SolidityBridge.PrecompileAgreement
