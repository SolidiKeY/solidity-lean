import SolidityBridge.RoadmapV15.WordByteTransport

/-!
Ordered-byte uniqueness for the existing backend encoder/reader. This is the
source-independent consumer needed to turn a published fixed-length reference
reader specification into exact bytes, without any allocator/driver premise.
No new reader, word representation or machine is defined.
-/
namespace SolidityBridge.RoadmapV15
open Solidity Solidity.Backend

private theorem encoding_roundtrip_reverse (rs : List UInt8) :
    (toBytesBE rs.length (ofBytesBE rs.reverse)).toList = rs.reverse := by
  induction rs with
  | nil => rfl
  | cons b rs ih =>
    have hb : b.toNat < 256 := b.toFin.isLt
    have hd : (ofBytesBE rs.reverse * 256 + b.toNat) / 256 = ofBytesBE rs.reverse := by omega
    have hm : (ofBytesBE rs.reverse * 256 + b.toNat) % 256 = b.toNat := by omega
    simp only [List.reverse_cons, List.length_cons,
      ofBytesBE_append_singleton, toBytesBE, Vector.toList_push, hd, hm,
      UInt8.ofNat_toNat, ih]

/-- All bytes, including leading zeroes, survive when the exact length is kept. -/
theorem bytes_encoding_roundtrip (bs : List UInt8) :
    (toBytesBE bs.length (ofBytesBE bs)).toList = bs := by
  have lengths :
      (toBytesBE bs.length (ofBytesBE bs)).toList =
        (toBytesBE bs.reverse.length (ofBytesBE bs)).toList :=
    congrArg (fun width => (toBytesBE width (ofBytesBE bs)).toList)
      (List.length_reverse (as := bs)).symm
  exact lengths.trans (by
    simpa only [List.reverse_reverse] using encoding_roundtrip_reverse bs.reverse)

private theorem byte_value_bound_reverse (rs : List UInt8) :
    ofBytesBE rs.reverse < 256 ^ rs.length := by
  induction rs with
  | nil => decide
  | cons b rs ih =>
    have hb : b.toNat < 256 := b.toFin.isLt
    simp only [List.reverse_cons, List.length_cons,
      ofBytesBE_append_singleton, Nat.pow_succ]
    omega

/-- Precise range follows from actual bytes; no extra modulo/padding is hidden. -/
theorem bytes_value_bound (bs : List UInt8) : ofBytesBE bs < 256 ^ bs.length := by
  simpa only [List.length_reverse, List.reverse_reverse] using byte_value_bound_reverse bs.reverse

/-- Length and decoded value determine the complete ordered observation. -/
theorem bytes_eq_of_length_read (a b : List UInt8) (length : a.length = b.length)
    (value : ofBytesBE a = ofBytesBE b) : a = b := by
  calc
    a = (toBytesBE a.length (ofBytesBE a)).toList := (bytes_encoding_roundtrip a).symm
    _ = (toBytesBE b.length (ofBytesBE b)).toList := by rw [length, value]
    _ = b := bytes_encoding_roundtrip b

/-- Consume a producer's exact length/reader clauses, not a desired simulation. -/
theorem bytes_canonical (width value : Nat) (bs : List UInt8)
    (length : bs.length = width) (read : ofBytesBE bs = value) :
    bs = (toBytesBE width value).toList := by
  have h := bytes_encoding_roundtrip bs
  rw [length, read] at h
  exact h.symm

end SolidityBridge.RoadmapV15
