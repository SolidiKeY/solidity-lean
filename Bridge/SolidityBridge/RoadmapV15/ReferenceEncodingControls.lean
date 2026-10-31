import SolidityBridge.RoadmapV15.ReferenceEncoding

/-! Candidate reference controls, NOT locally kernel-checked: external imports
are unavailable. Pure encoding only; no allocator, read/store or EVM driver run.
Checked source-independent analogues are in EncodingUniquenessControls. -/
namespace SolidityBridge.RoadmapV15.ReferenceEncodingControls
open Solidity Solidity.Backend
open Solidity.Evm.External.Memory (encoding encoding_spec)

private def first : EvmYul.UInt256 := Solidity.Evm.External.encode (258 : Scalar.Word).toFin
private def second : EvmYul.UInt256 := Solidity.Evm.External.encode (513 : Scalar.Word).toFin
example : (encoding first).toList = (toBytesBE 32 258).toList := reference_encoding_scalar 258
example : (encoding second).toList = (toBytesBE 32 513).toList := reference_encoding_scalar 513
example : (encoding first).toList ≠ (encoding second).toList := by
  intro h
  have bad := reference_encoding_injective first second h
  have nums := congrArg EvmYul.UInt256.toNat bad
  change (258 : Nat) = 513 at nums
  omega
example : (encoding first).size = 32 := (encoding_spec first).1
example : (encoding first).toList.length ≠ 31 := by
  rw [reference_encoding_scalar]
  decide
example : (encoding first).toList ≠ (toBytesBE 32 258).toList.reverse := by
  rw [reference_encoding_scalar]
  decide +kernel
example : (encoding first).toList ≠ (toBytesBE 31 258).toList := by
  rw [reference_encoding_scalar]
  decide +kernel
example : EvmYul.fromByteArrayBigEndian (encoding first) = 258 := (encoding_spec first).2
example : (encoding (EvmYul.UInt256.ofNat (2 ^ 256 + 1))).toList =
    (toBytesBE 32 ((2 ^ 256 + 1) % EvmYul.UInt256.size)).toList :=
  reference_encoding_nat_modulo _

private def negativeOne : PrimTy.int.Denote := ⟨-1, by decide⟩
private def minimumSigned : PrimTy.int.Denote := ⟨-((2 ^ 255 : Nat) : Int), by decide +kernel⟩
private def maximumUnsigned : PrimTy.uint.Denote := ⟨((2 ^ 256 - 1 : Nat) : Int), by decide +kernel⟩
example : (Scalar.immediate (encoding
    (Solidity.Evm.External.encode (Scalar.encodeValue .int negativeOne).toFin)).toList).toInt = -1 :=
  reference_signed_observation negativeOne
example : (Scalar.immediate (encoding
    (Solidity.Evm.External.encode (Scalar.encodeValue .int minimumSigned).toFin)).toList).toInt =
      -((2 ^ 255 : Nat) : Int) := reference_signed_observation minimumSigned
example : (Scalar.immediate (encoding
    (Solidity.Evm.External.encode (Scalar.encodeValue .uint maximumUnsigned).toFin)).toList).toNat =
      maximumUnsigned.val.toNat := reference_unsigned_observation maximumUnsigned

example : Scalar.run (Scalar.unsignedCode ⟨0, by decide⟩)
    (Scalar.immediate (encoding (Solidity.Evm.External.encode (257 : Scalar.Word).toFin)).toList :: [77]) =
      some (Scalar.immediate (encoding (Solidity.Evm.External.encode
        (Scalar.unsignedClean ⟨0, by decide⟩ 257).toFin)).toList :: [77]) :=
  reference_unsigned_cleanup ⟨0, by decide⟩ 257 [77]
example : Scalar.run (Scalar.signedCode ⟨0, by decide⟩)
    (Scalar.immediate (encoding (Solidity.Evm.External.encode (128 : Scalar.Word).toFin)).toList :: [77]) =
      some (Scalar.immediate (encoding (Solidity.Evm.External.encode
        (Scalar.signedClean ⟨0, by decide⟩ 128).toFin)).toList :: [77]) :=
  reference_signed_cleanup ⟨0, by decide⟩ 128 [77]
example : [first, second].flatMap (fun v => (encoding v).toList) =
    [first, second].flatMap (fun v => (toBytesBE 32 v.toNat).toList) := reference_encoding_sequence _
example : (Roadmap.Evm.Halt.revert (encoding first).toList).observe =
    (Roadmap.Evm.Halt.revert (toBytesBE 32 first.toNat).toList).observe :=
  reference_complete_observation false first
example : (Roadmap.Evm.Halt.success (encoding second).toList).observe =
    (Roadmap.Evm.Halt.success (toBytesBE 32 second.toNat).toList).observe :=
  reference_complete_observation true second

-- Required audits remain pending with this file's blocked external import.
#print axioms reference_big_reader
#print axioms reference_array_reader
#print axioms reference_encoding_bytes
#print axioms reference_encoding_array
#print axioms reference_encoding_scalar
#print axioms reference_encoding_nat_modulo
#print axioms reference_encoding_injective
#print axioms reference_scalar_immediate
#print axioms reference_signed_observation
#print axioms reference_unsigned_observation
#print axioms reference_typed_abi_bytes
#print axioms reference_unsigned_cleanup
#print axioms reference_signed_cleanup
#print axioms reference_encoding_sequence
#print axioms reference_complete_observation
end SolidityBridge.RoadmapV15.ReferenceEncodingControls
