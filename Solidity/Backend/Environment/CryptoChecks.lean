import Solidity.Backend.Environment.Namespace

/-! G31 byte/preimage, failure and executable instruction controls. -/
namespace Solidity.Backend.Environment

private abbrev BytesR : RefTy := .array (.prim .uint)
private abbrev BytesΓ : Ctx := [.mem BytesR]
private def bytesState : State default BytesΓ :=
  { storage := Storage.init default
    H := [BytesR]
    heap := (⟨[lenU 0 (by decide), lenU 255 (by decide), lenU 256 (by decide),
      lenU 97 (by decide)], by decide⟩, ())
    env := (some ⟨0, rfl⟩, ()) }
private def bytesPath : MPath default BytesΓ (.ref BytesR) := .var .here rfl
private def bytesRef : HRef bytesState.H BytesR := ⟨0, rfl⟩
private def byteSlice : Slice :=
  ⟨[lenU 19 (by decide)], writeBytes (fun _ => 0xaa) 7 [0, 255, 0, 97]⟩

private theorem input_control :
    HashInput byteSlice ⟨7, by decide⟩ ⟨4, by decide⟩
      (MObj.words BytesR (bytesState.heap.get bytesRef)) := by
  constructor
  · decide
  · decide +kernel

/-- Inhabited typed heap/path with a preserved, nonempty target stack tail. -/
theorem intrinsic_hash_control :
    Val.evalT bytesState (.hash .keccak bytesPath rfl : Val default BytesΓ .uint) =
      .ok (bytesState.heap.hash .keccak bytesRef) ∧
    runCrypto (keccakCode ⟨7, by decide⟩ ⟨4, by decide⟩) byteSlice =
      some { byteSlice with stack := bytesState.heap.hash .keccak bytesRef :: byteSlice.stack } :=
  intrinsic_keccak bytesState bytesPath bytesRef rfl _ _ _ input_control

theorem builtin_selection_control (k : HashKind) :
    lowerHash bytesState bytesPath k ⟨7, by decide⟩ ⟨64, by decide⟩ =
      .ok (builtinCode k ⟨7, by decide⟩ ⟨4, by decide⟩ ⟨64, by decide⟩) :=
  lowerHash_success bytesState bytesPath bytesRef rfl k _ _ _ _ input_control

theorem unset_argument_control (k : HashKind) :
    lowerHash ({ bytesState with env := (none, ()) } : State default BytesΓ) bytesPath k
      ⟨7, by decide⟩ ⟨64, by decide⟩ = .error .revert :=
  lowerHash_failure _ _ k _ _ .revert rfl

theorem byte_normalization_control :
    wireBytes [0, 255, 256, 97, -1] = [0, 255, 0, 97, 0] ∧
    wireBytes [0, 255, 256, 97] ≠ wireBytes [97, 256, 255, 0] := by decide +kernel

theorem keccak_bytes_control :
    Backend.encode (keccakCode ⟨7, by decide⟩ ⟨4, by decide⟩) =
      [0x7f] ++ List.replicate 31 0 ++ [4, 0x7f] ++ List.replicate 31 0 ++ [7, 0x20] := by
  decide +kernel

/-- Operand order cannot be swapped: offset and length read different bytes. -/
theorem wrong_preimage_control :
    readMemory byteSlice.memory 7 4 ≠ readMemory byteSlice.memory 4 7 := by decide +kernel

/-- A real namespace slice hashes twice and stores one exact ABI word. -/
theorem namespace_instruction_control :
    ((namespaceCode ⟨7, by decide⟩ ⟨4, by decide⟩ ⟨64, by decide⟩).filter
      (· == Instr.op .KECCAK256)).length = 2 ∧
    ((namespaceCode ⟨7, by decide⟩ ⟨4, by decide⟩ ⟨64, by decide⟩).filter
      (· == Instr.op .MSTORE)).length = 1 := by decide +kernel

theorem namespace_inhabited :
    runCrypto (namespaceCode ⟨7, by decide⟩ ⟨4, by decide⟩ ⟨64, by decide⟩) byteSlice =
      some ⟨lenU (ERC7201.root [0, 255, 0, 97]).val (ERC7201.root [0, 255, 0, 97]).isLt ::
        byteSlice.stack, writeBytes byteSlice.memory 64 (namespacePreimage [0, 255, 0, 97])⟩ := by
  apply namespace_source
  exact ⟨by decide, by decide, by decide +kernel⟩

theorem precompile_selection_control :
    precompileAddress .sha256 = some ⟨2, by decide⟩ ∧
    precompileAddress .ripemd160 = some ⟨3, by decide⟩ ∧
    precompileAddress .ecrecover = some ⟨1, by decide⟩ := ⟨rfl, rfl, rfl⟩

theorem malformed_recovery_control :
    builtinCode .ecrecover ⟨7, by decide⟩ ⟨4, by decide⟩ ⟨64, by decide⟩ =
      [constant 0 ⟨0, by decide⟩] := by decide +kernel

private def recoveryState : State default BytesΓ :=
  { storage := Storage.init default
    H := [BytesR]
    heap := (⟨List.replicate 128 (lenU 0 (by decide)), by rw [List.length_replicate]; decide⟩, ())
    env := (some ⟨0, rfl⟩, ()) }

/-- Inhabited 128-byte argument takes the actual ecrecover precompile branch. -/
theorem recovery_positive :
    lowerHash recoveryState bytesPath .ecrecover ⟨0, by decide⟩ ⟨192, by decide⟩ =
      .ok (precompileCode ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨128, by decide⟩ ⟨192, by decide⟩) := by
  apply lowerHash_success recoveryState bytesPath ⟨0, rfl⟩ rfl .ecrecover
    ⟨0, by decide⟩ ⟨128, by decide⟩ ⟨192, by decide⟩ ⟨[], fun _ => 0⟩
  constructor
  · decide
  · change readMemory (fun _ => 0) 0 128 =
      wireBytes ((List.replicate 128 (lenU 0 (by decide))).map fun v => v.1)
    simp only [readMemory, wireBytes, List.map_replicate, List.map_const', List.length_range]
    rfl

theorem precompile_suffix_bytes (address offset length output : W256) :
    Backend.encode (precompileCode address offset length output) =
      Backend.encode (precompilePrefix address offset length output) ++
        [0x5a, 0xfa, 0x50] ++ (push256 output).encode ++ [0x51] := by
  rw [precompileCode, Backend.encode_append]
  simp only [Backend.encode_cons, Backend.encode_nil]
  change Backend.encode (precompilePrefix address offset length output) ++
      ([0x5a] ++ ([0xfa] ++ ([0x50] ++ ((push256 output).encode ++ ([0x51] ++ []))))) = _
  simp only [List.append_nil, List.append_assoc, List.singleton_append]
  rfl

-- Keccak uses the committed implementation, not an environment reply.
/-- info: 'Solidity.Backend.Environment.intrinsic_keccak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intrinsic_keccak
/-- info: 'Solidity.Backend.Environment.lowerHash_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowerHash_success
/-- info: 'Solidity.Backend.Environment.namespace_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms namespace_source
/-- info: 'Solidity.Backend.Environment.source_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_digest
end Solidity.Backend.Environment
