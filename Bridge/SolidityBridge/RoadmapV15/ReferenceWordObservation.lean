import SolidityBridge.RoadmapV15.ReferenceReader
import SolidityBridge.RoadmapV15.ByteImageTransport

/-! FFI-independent observation of actual reference readers. Natural width/range
and intrinsic image fields remain explicit. These are pure read observations;
no physical MSTORE, allocator, account, gas or driver result is asserted. -/
namespace SolidityBridge.RoadmapV15
open Solidity Solidity.Backend Solidity.Evm.TryByteImage

/-- Exact-width/range transport to the actual pinned big-endian reader. -/
theorem reference_backend_bounded (width value : Nat) (h : value < 256 ^ width) :
    EvmYul.fromBytesBigEndian (toBytesBE width value).toList = value := by
  rw [reference_big_reader, ofBytesBE_toBytesBE width value h]

/-- A backend word read into the existing actual reference UInt256 has the same
natural observation. The BitVec range discharges the constructor's modulo. -/
theorem reference_word_toNat (w : Scalar.Word) :
    (EvmYul.UInt256.ofNat (EvmYul.fromBytesBigEndian (toBytesBE 32 w.toNat).toList)).toNat =
      w.toNat := by
  rw [reference_backend_bounded 32 w.toNat w.isLt]
  change w.toNat % EvmYul.UInt256.size = w.toNat
  exact Nat.mod_eq_of_lt w.isLt

/-- The actual reference reader observes the complete published stored image. -/
theorem image_reference_reader (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (w : PrimTy.uint.Denote) :
    EvmYul.fromBytesBigEndian (snapshot (store32 μ a w) (wordObservation a)) =
      w.val.toNat := by
  rw [reference_big_reader]
  exact image_store_read μ a w

/-- Three existing representations: stored image, backend word and actual
reference UInt256. Address arithmetic is still natural and span-bounded. -/
theorem image_reference_word (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (w : Scalar.Word) :
    (EvmYul.UInt256.ofNat (EvmYul.fromBytesBigEndian
      (snapshot (store32 μ a (imageScalarWord w)) (wordObservation a)))).toNat = w.toNat := by
  rw [image_store_scalar]
  exact reference_word_toNat w

/-- Signed observation reuses the existing BitVec signed interpretation after
reading actual reference bytes, including negative two's complement values. -/
theorem image_reference_signed (μ : FrameMem C Γ) (a : WordSpan μ.capacity)
    (v : PrimTy.int.Denote) :
    (BitVec.ofNat 256 (EvmYul.fromBytesBigEndian
      (snapshot (store32 μ a (PrimTy.toWord v)) (wordObservation a)))).toInt = v.val := by
  rw [reference_big_reader]
  exact image_store_signed μ a v

end SolidityBridge.RoadmapV15
