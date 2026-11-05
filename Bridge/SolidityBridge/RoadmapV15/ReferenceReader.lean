import EvmYul.UInt256
import SolidityBridge.RoadmapV15.EncodingUniqueness

/-! Actual pinned reference byte readers and existing backend byte order. No
allocator, machine instruction, driver, gas or Osaka fork agreement is claimed.
These declarations are separated from the memory adapter's larger import closure.
-/
namespace SolidityBridge.RoadmapV15
open Solidity Solidity.Backend

private theorem reference_little_reader (rs : List UInt8) :
    EvmYul.fromBytes' rs = ofBytesBE rs.reverse := by
  induction rs with
  | nil => rfl
  | cons b rs ih =>
    change b.toNat + 256 * EvmYul.fromBytes' rs = ofBytesBE (b :: rs).reverse
    rw [List.reverse_cons, ofBytesBE_append_singleton, ih]
    omega

/-- Actual reference reader agrees with the existing backend byte order. -/
theorem reference_big_reader (bs : List UInt8) :
    EvmYul.fromBytesBigEndian bs = ofBytesBE bs := by
  change EvmYul.fromBytes' bs.reverse = ofBytesBE bs
  simpa only [List.reverse_reverse] using reference_little_reader bs.reverse

theorem reference_array_reader (bs : ByteArray) :
    EvmYul.fromByteArrayBigEndian bs = ofBytesBE bs.toList :=
  reference_big_reader bs.toList

end SolidityBridge.RoadmapV15
