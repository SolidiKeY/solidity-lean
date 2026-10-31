import SolidityBridge.RoadmapV15.EncodingUniqueness
import SolidityBridge.RoadmapV15.HaltObservation

/-! Pure encoding controls; no reference allocator or EVM execution is run. -/
namespace SolidityBridge.RoadmapV15.EncodingUniquenessControls
open Solidity Solidity.Backend Solidity.Roadmap

example : (toBytesBE ([0, 1, 2, 0, 255] : List UInt8).length
    (ofBytesBE [0, 1, 2, 0, 255])).toList = [0, 1, 2, 0, 255] :=
  bytes_encoding_roundtrip _
example : ofBytesBE ([0, 1, 2, 0, 255] : List UInt8) < 256 ^ 5 := bytes_value_bound _
example : ofBytesBE ([1, 2] : List UInt8) = 258 := by decide +kernel
example : ofBytesBE ([1, 2] : List UInt8) ≠ ofBytesBE [2, 1] := by decide +kernel
-- Numeric equality alone loses leading zeroes. Exact length is essential.
example : ofBytesBE ([1, 2] : List UInt8) = ofBytesBE [0, 1, 2] := by decide +kernel
example : ([1, 2] : List UInt8) ≠ [0, 1, 2] := by decide +kernel
example : ([1, 2] : List UInt8).length ≠ [0, 1, 2].length := by decide
example : ([] : List UInt8) ≠ [0] ∧ ofBytesBE [] = ofBytesBE [0] := by decide
example : ofBytesBE ([1] : List UInt8) ≠ ofBytesBE [1, 0] := by decide +kernel

private def oneBytes : List UInt8 := List.replicate 31 0 ++ [1]
private theorem one_canonical : oneBytes = (toBytesBE 32 1).toList := by
  apply bytes_canonical
  · decide
  · decide +kernel
example : oneBytes.length = 32 ∧ ofBytesBE oneBytes = 1 := by decide +kernel
example : oneBytes ≠ (toBytesBE 31 1).toList := by decide +kernel
example : oneBytes ≠ (toBytesBE 33 1).toList := by decide +kernel
example : (Evm.Halt.revert oneBytes).observe =
    (Evm.Halt.revert (toBytesBE 32 1).toList).observe :=
  congrArg (fun bs => (Evm.Halt.revert bs).observe) one_canonical
example : (Evm.Halt.success oneBytes).observe ≠ (Evm.Halt.revert oneBytes).observe := by decide

private def negativeOne : PrimTy.int.Denote := ⟨-1, by decide⟩
private def minimumSigned : PrimTy.int.Denote := ⟨-((2 ^ 255 : Nat) : Int), by decide +kernel⟩
private def maximumUnsigned : PrimTy.uint.Denote :=
  ⟨Int.ofNat (2 ^ 256 - 1), by decide +kernel⟩

example : List.replicate 32 (255 : UInt8) =
    (toBytesBE 32 (Scalar.encodeValue .int negativeOne).toNat).toList := by
  apply bytes_canonical
  · decide
  · decide +kernel
example : (128 : UInt8) :: List.replicate 31 0 =
    (toBytesBE 32 (Scalar.encodeValue .int minimumSigned).toNat).toList := by
  apply bytes_canonical
  · decide
  · decide +kernel
example : List.replicate 32 (255 : UInt8) =
    (toBytesBE 32 (Scalar.encodeValue .uint maximumUnsigned).toNat).toList := by
  apply bytes_canonical
  · decide
  · decide +kernel

-- Existing narrow cleanup, observed through complete 32-byte words.
example : (toBytesBE 32 (Scalar.unsignedClean ⟨0, by decide⟩ 257).toNat).toList =
    oneBytes := by decide +kernel
example : (toBytesBE 32 (Scalar.signedClean ⟨0, by decide⟩ 128).toNat).toList =
    List.replicate 31 255 ++ [128] := by decide +kernel
example : (Scalar.signedClean ⟨0, by decide⟩ 128).toInt = -128 := by decide +kernel
example : (BitVec.ofNat 256 (2 ^ 256 + 1)).toNat = 1 := by decide +kernel
example : (BitVec.ofNat 256 (2 ^ 256 - 1)).toNat ≠ 0 := by decide +kernel

-- Distinct nonzero words retain order; a permutation is not this observation.
example : [(toBytesBE 32 258).toList, (toBytesBE 32 513).toList] ≠
    [(toBytesBE 32 513).toList, (toBytesBE 32 258).toList] := by decide +kernel
example : (toBytesBE 32 258).toList ++ (toBytesBE 32 513).toList ≠
    (toBytesBE 32 513).toList ++ (toBytesBE 32 258).toList := by decide +kernel

#print axioms bytes_encoding_roundtrip
#print axioms bytes_value_bound
#print axioms bytes_eq_of_length_read
#print axioms bytes_canonical
end SolidityBridge.RoadmapV15.EncodingUniquenessControls
