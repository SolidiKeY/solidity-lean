import SolidityBridge.RoadmapV15.ReferenceReader
import SolidityBridge.ExternalEvm.MemoryBytes
import SolidityBridge.ExternalEvm
import SolidityBridge.RoadmapV15.EncodingUniqueness
import SolidityBridge.RoadmapV15.HaltObservation

/-!
Thirteen encoding proposals consuming the published reference encoding and
existing numeric adapter remain blocked at the memory/external imports. The two
reader laws now live in the checked narrow ReferenceReader module; this file is
not counted as kernel-checked. See the owning V15 report.
Only pure encoding is used: no allocator contract, actual toByteArray serialization,
preallocated read/store refinement, supplied-opcode run or driver is asserted.
-/
namespace SolidityBridge.RoadmapV15
open Solidity Solidity.Backend
open Solidity.Evm.External.Memory (encoding encoding_spec bytes_list list_bytes)

/-- Full ordered-byte equality, derived from the producer's two exact clauses.
This is stronger than simply re-exporting the producer's numeric round trip. -/
theorem reference_encoding_bytes (v : EvmYul.UInt256) :
    (encoding v).toList = (toBytesBE 32 v.toNat).toList := by
  apply bytes_canonical
  · simpa only [bytes_list, Array.length_toList] using (encoding_spec v).1
  · rw [← reference_array_reader]
    exact (encoding_spec v).2

/-- The same pure observation as a ByteArray; not UInt256.toByteArray serialization. -/
theorem reference_encoding_array (v : EvmYul.UInt256) :
    encoding v = (toBytesBE 32 v.toNat).toList.toByteArray := by
  apply ByteArray.ext
  rw [list_bytes]
  have h := congrArg List.toArray (reference_encoding_bytes v)
  simpa only [bytes_list, Array.toArray_toList] using h

/-- Reuse the reserved numeric adapter unchanged, rather than defining another. -/
theorem reference_encoding_scalar (w : Scalar.Word) :
    (encoding (Solidity.Evm.External.encode w.toFin)).toList =
      (toBytesBE 32 w.toNat).toList :=
  reference_encoding_bytes (Solidity.Evm.External.encode w.toFin)

/-- Exact modulo clause for unrestricted natural inputs; the width is always 32. -/
theorem reference_encoding_nat_modulo (n : Nat) :
    (encoding (EvmYul.UInt256.ofNat n)).toList =
      (toBytesBE 32 (n % EvmYul.UInt256.size)).toList :=
  reference_encoding_bytes (EvmYul.UInt256.ofNat n)

/-- Word encoding is injective; this is not a hash-injectivity assumption. -/
theorem reference_encoding_injective (a b : EvmYul.UInt256)
    (h : (encoding a).toList = (encoding b).toList) : a = b := by
  have values : a.toNat = b.toNat := by
    have h' := congrArg EvmYul.fromBytesBigEndian h
    change EvmYul.fromByteArrayBigEndian (encoding a) =
      EvmYul.fromByteArrayBigEndian (encoding b) at h'
    simpa only [(encoding_spec a).2, (encoding_spec b).2] using h'
  have decoded : Solidity.Evm.External.decode a = Solidity.Evm.External.decode b :=
    Fin.ext values
  calc
    a = Solidity.Evm.External.encode (Solidity.Evm.External.decode a) :=
      (Solidity.Evm.External.encode_decode a).symm
    _ = Solidity.Evm.External.encode (Solidity.Evm.External.decode b) :=
      congrArg Solidity.Evm.External.encode decoded
    _ = b := Solidity.Evm.External.encode_decode b

/-- Existing scalar reader consumes all 32 actual pure reference bytes. -/
theorem reference_scalar_immediate (w : Scalar.Word) :
    Scalar.immediate (encoding (Solidity.Evm.External.encode w.toFin)).toList = w := by
  rw [reference_encoding_scalar]
  exact word32_immediate w

theorem reference_signed_observation (v : PrimTy.int.Denote) :
    (Scalar.immediate (encoding
      (Solidity.Evm.External.encode (Scalar.encodeValue .int v).toFin)).toList).toInt = v.val := by
  rw [reference_encoding_scalar]
  exact signed_word_bytes v

theorem reference_unsigned_observation (v : PrimTy.uint.Denote) :
    (Scalar.immediate (encoding
      (Solidity.Evm.External.encode (Scalar.encodeValue .uint v).toFin)).toList).toNat = v.val.toNat := by
  rw [reference_encoding_scalar]
  exact unsigned_word_bytes v

theorem reference_typed_abi_bytes (p : PrimTy) (v : p.Denote) :
    (encoding (Solidity.Evm.External.encode (Scalar.encodeValue p v).toFin)).toList =
      (toBytesBE 32 (PrimTy.toWord v).val.toNat).toList := by
  rw [reference_encoding_scalar]
  exact typed_bytes_toWord p v

/-- Existing unsigned cleanup and exact stack tail, observed through pure bytes.
No actual reference instruction, gas or stack-resource adequacy is inferred. -/
theorem reference_unsigned_cleanup (width : Fin 32) (w : Scalar.Word) (tail : Scalar.Stack) :
    Scalar.run (Scalar.unsignedCode width)
      (Scalar.immediate (encoding (Solidity.Evm.External.encode w.toFin)).toList :: tail) =
      some (Scalar.immediate (encoding
        (Solidity.Evm.External.encode (Scalar.unsignedClean width w).toFin)).toList :: tail) := by
  simp only [reference_encoding_scalar]
  exact unsigned_cleanup_bytes width w tail

theorem reference_signed_cleanup (width : Fin 32) (w : Scalar.Word) (tail : Scalar.Stack) :
    Scalar.run (Scalar.signedCode width)
      (Scalar.immediate (encoding (Solidity.Evm.External.encode w.toFin)).toList :: tail) =
      some (Scalar.immediate (encoding
        (Solidity.Evm.External.encode (Scalar.signedClean width w).toFin)).toList :: tail) := by
  simp only [reference_encoding_scalar]
  exact signed_cleanup_bytes width w tail

/-- Consecutive observations retain the entire list order and every byte. -/
theorem reference_encoding_sequence (vs : List EvmYul.UInt256) :
    vs.flatMap (fun v => (encoding v).toList) =
      vs.flatMap (fun v => (toBytesBE 32 v.toNat).toList) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [List.flatMap_cons, reference_encoding_bytes, ih]

/-- Preserve the existing completed-frame success bit and all payload bytes.
These are observation representatives, not evidence that a frame executed. -/
theorem reference_complete_observation (success : Bool) (v : EvmYul.UInt256) :
    (if success then (Roadmap.Evm.Halt.success (encoding v).toList)
      else .revert (encoding v).toList).observe =
    (if success then (Roadmap.Evm.Halt.success (toBytesBE 32 v.toNat).toList)
      else .revert (toBytesBE 32 v.toNat).toList).observe :=
  congrArg (fun bs => (if success then (Roadmap.Evm.Halt.success bs) else .revert bs).observe)
    (reference_encoding_bytes v)

end SolidityBridge.RoadmapV15
