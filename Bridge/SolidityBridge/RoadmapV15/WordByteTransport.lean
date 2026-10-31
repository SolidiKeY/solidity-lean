import Solidity.Backend.Failure.Immediate
import Solidity.Backend.Failure.Slice
import Solidity.Backend.Scalar.Widths
import Solidity.Backend.Scalar.Typed

/-!
Consumer transport across published assembler, local failure and scalar
representations. All operations below are the existing definitions, unchanged.
No EVM transition, padding rule, numeric adapter or machine is defined here.
These facts do not upgrade the reserved Cancun reference to an Osaka machine.
-/
namespace SolidityBridge.RoadmapV15
open Solidity Solidity.Backend

/-- Two published immediate encoders produce identical bytes, at every length,
including zero and lengths above a machine word. No ABI padding is inferred. -/
theorem digits_toBytesBE (width n : Nat) :
    Failure.digits width n = (toBytesBE width n).toList := by
  induction width generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [Failure.digits, toBytesBE, Vector.toList_push, ih]

/-- The failure and assembler readers share exactly the existing byte order. -/
theorem readImmediate_ofBytesBE (bs : List UInt8) :
    Failure.readImmediate bs = ofBytesBE bs := rfl

/-- Transport to the byte-list convention used by the published Keccak reader. -/
theorem keccak_ofBytesBE (bs : List UInt8) :
    Keccak.ofBytes (bs.map UInt8.toNat) = ofBytesBE bs := by
  simp only [Keccak.ofBytes, ofBytesBE, List.foldl_map, Nat.mul_comm]

/-- No loss of information in a well-sized assembler immediate. The range
hypothesis is essential: smaller widths intentionally discard high bytes. -/
theorem encoded_bytes_injective (width a b : Nat) (ha : a < 256 ^ width)
    (hb : b < 256 ^ width)
    (h : (toBytesBE width a).toList = (toBytesBE width b).toList) : a = b := by
  have he : ofBytesBE (toBytesBE width a).toList = ofBytesBE (toBytesBE width b).toList :=
    congrArg ofBytesBE h
  simpa only [ofBytesBE_toBytesBE width a ha, ofBytesBE_toBytesBE width b hb] using he

/-- The existing local scalar and local failure slices agree on numeric PUSH
immediate observations. This is not a statement about opcode dispatch or gas. -/
theorem pushed_immediate_toNat (bs : List UInt8) :
    (Scalar.immediate bs).toNat = (Failure.Slice.pushed bs).val := rfl

theorem word32_immediate (w : Scalar.Word) :
    Scalar.immediate (toBytesBE 32 w.toNat).toList = w := by
  have hv : w.toNat < 256 ^ 32 := w.isLt
  unfold Scalar.immediate
  rw [ofBytesBE_toBytesBE 32 w.toNat hv]
  apply BitVec.eq_of_toNat_eq
  exact Nat.mod_eq_of_lt w.isLt

/-- Full-word transport to the existing G01/local-failure Fin word. -/
theorem word32_pushed (w : Scalar.Word) :
    Failure.Slice.pushed (toBytesBE 32 w.toNat).toList = w.toFin := by
  apply Fin.ext
  have h := congrArg BitVec.toNat (word32_immediate w)
  exact h

/-- Narrow immediates retain exactly their numeric value under both explicit
length/range clauses. No claim is made for truncated code or implicit padding. -/
theorem bounded_immediate (width n : Nat) (hw : width ≤ 32) (hn : n < 256 ^ width) :
    (Scalar.immediate (toBytesBE width n).toList).toNat = n := by
  have hp : 256 ^ width ≤ 256 ^ 32 := Nat.pow_le_pow_right (by decide) hw
  have hword : n < 2 ^ 256 := Nat.lt_of_lt_of_le hn hp
  simp only [Scalar.immediate, ofBytesBE_toBytesBE width n hn, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hword]

/-- Signed observation uses the published intrinsic encoding theorem, including
negative two's complement; no signed numeric interpretation is recreated. -/
theorem signed_word_bytes (v : PrimTy.int.Denote) :
    (Scalar.immediate (toBytesBE 32 (Scalar.encodeValue .int v).toNat).toList).toInt = v.val := by
  rw [word32_immediate, Scalar.encode_int_toInt]

theorem unsigned_word_bytes (v : PrimTy.uint.Denote) :
    (Scalar.immediate (toBytesBE 32 (Scalar.encodeValue .uint v).toNat).toList).toNat = v.val.toNat := by
  rw [word32_immediate, Scalar.encode_uint_toNat]

/-- Typed scalar bytes are exactly bytes of the existing ABI word observation.
This consumes its published representation theorem; it is not a decoder adapter. -/
theorem typed_bytes_toWord (p : PrimTy) (v : p.Denote) :
    (toBytesBE 32 (Scalar.encodeValue p v).toNat).toList =
      (toBytesBE 32 (PrimTy.toWord v).val.toNat).toList := by
  have h : (Scalar.encodeValue p v).toNat = (PrimTy.toWord v).val.toNat := by
    rw [Scalar.encodeValue_toWord]
    exact Scalar.encode_uint_toNat (PrimTy.toWord v)
  exact congrArg (fun n => (toBytesBE 32 n).toList) h

/-- Exact full-width bytes are injective as an observation of existing words. -/
theorem word32_bytes_injective (a b : Scalar.Word)
    (h : (toBytesBE 32 a.toNat).toList = (toBytesBE 32 b.toNat).toList) : a = b := by
  have he := congrArg Scalar.immediate h
  simpa only [word32_immediate] using he

/-- Consumer composition of published cleanup with explicit full-word bytes.
The same tail is framed. Stack/resource adequacy for real execution is open. -/
theorem unsigned_cleanup_bytes (width : Fin 32) (w : Scalar.Word) (tail : Scalar.Stack) :
    Scalar.run (Scalar.unsignedCode width)
      (Scalar.immediate (toBytesBE 32 w.toNat).toList :: tail) =
        some (Scalar.immediate (toBytesBE 32 (Scalar.unsignedClean width w).toNat).toList :: tail) := by
  rw [word32_immediate, word32_immediate]
  exact Scalar.unsigned_correct width w tail

theorem signed_cleanup_bytes (width : Fin 32) (w : Scalar.Word) (tail : Scalar.Stack) :
    Scalar.run (Scalar.signedCode width)
      (Scalar.immediate (toBytesBE 32 w.toNat).toList :: tail) =
        some (Scalar.immediate (toBytesBE 32 (Scalar.signedClean width w).toNat).toList :: tail) := by
  rw [word32_immediate, word32_immediate]
  exact Scalar.signed_correct width w tail

/-- Exact length and byte observation after an existing local byte write.
This consumes the published byte-memory result; no memory adapter is redefined. -/
theorem written_immediate_bytes (m : Failure.Slice.Memory) (offset width n : Nat) :
    Failure.Slice.getBytes (Failure.Slice.putBytes m offset (Failure.digits width n))
      offset width = (toBytesBE width n).toList := by
  have h := Failure.Slice.getBytes_putBytes m offset (Failure.digits width n)
  rw [Failure.digits_length] at h
  exact h.trans (digits_toBytesBE width n)

/-- Suffix bytes cannot silently become right padding of the observed immediate.
An actual EVM consumer must still prove its selected interval and resources. -/
theorem written_immediate_suffix (m : Failure.Slice.Memory) (offset width n : Nat)
    (suffix : List UInt8) :
    Failure.Slice.getBytes
      (Failure.Slice.putBytes (Failure.Slice.putBytes m offset (Failure.digits width n))
        (offset + width) suffix) offset width = (toBytesBE width n).toList := by
  rw [Failure.Slice.getBytes_suffix_write, written_immediate_bytes]

end SolidityBridge.RoadmapV15
