import SolidityBridge.RoadmapV15.ReferenceEncoding
import SolidityBridge.RoadmapV15.ByteImageTransport

/-! Complete typed image/reference encoding observations. The actual reference
pure encoder is used; physical serialization/allocation and execution remain
separate obligations. ScalarFrame restricts the producer image, not admission. -/
namespace SolidityBridge.RoadmapV15
open Solidity Solidity.Backend Solidity.Evm.TryByteImage
open Solidity.Evm.External.Memory (encoding)

theorem typed_image_reference_bytes (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (p : PrimTy) (v : p.Denote) :
    snapshot (store32 μ a (PrimTy.toWord v)) (wordObservation a) =
      (encoding (Solidity.Evm.External.encode (Scalar.encodeValue p v).toFin)).toList := by
  rw [reference_encoding_scalar]
  exact image_store_typed μ a p v

/-- The full intrinsic state, invocation identity and ordered bytes are framed. -/
theorem typed_image_reference_observation (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (p : PrimTy) (v : p.Denote) :
    (store32 μ a (PrimTy.toWord v)).st = μ.st ∧
    (store32 μ a (PrimTy.toWord v)).key = μ.key ∧
    snapshot (store32 μ a (PrimTy.toWord v)) (wordObservation a) =
      (encoding (Solidity.Evm.External.encode (Scalar.encodeValue p v).toFin)).toList :=
  ⟨(store32_frame μ a _).1, (store32_frame μ a _).2, typed_image_reference_bytes μ a p v⟩

/-- Two successive pure observations retain order even when accesses overlap.
This is not a machine trace or a claim that both values survive the final store. -/
theorem image_pair_reference_bytes (μ : FrameMem C Γ) (a b : WordSpan μ.capacity)
    (v w : PrimTy.uint.Denote) :
    [snapshot (store32 μ a v) (wordObservation a),
      snapshot (store32 (store32 μ a v) b w) (wordObservation b)] =
    [(encoding (Solidity.Evm.External.encode (Scalar.encodeValue .uint v).toFin)).toList,
      (encoding (Solidity.Evm.External.encode (Scalar.encodeValue .uint w).toFin)).toList] :=
  congrArg₂ (fun x y : List UInt8 => [x, y])
    (typed_image_reference_bytes μ a .uint v)
    (typed_image_reference_bytes (store32 μ a v) b .uint w)

/-- A disjoint later write preserves the entire earlier reference observation. -/
theorem disjoint_image_reference_bytes (μ : FrameMem C Γ) (a b : WordSpan μ.capacity)
    (v w : PrimTy.uint.Denote)
    (apart : a.offset.val.toNat + 32 ≤ b.offset.val.toNat ∨
      b.offset.val.toNat + 32 ≤ a.offset.val.toNat) :
    snapshot (store32 (store32 μ a v) b w) (wordObservation a) =
      (encoding (Solidity.Evm.External.encode (Scalar.encodeValue .uint v).toFin)).toList := by
  rw [reference_encoding_scalar, Scalar.encode_uint_toNat]
  exact image_disjoint_backend μ a b v w apart

end SolidityBridge.RoadmapV15
