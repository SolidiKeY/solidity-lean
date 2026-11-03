import Solidity.Yul.Views.Bytes
import Solidity.Backend.Environment.ByteConstants

/-! Exact interoperability of the existing Nat-addressed byte-view APIs.
These equalities add no state or interpreter. Actual EVM access, word bounds,
allocation and source-heap adequacy remain separate from mathematical byte maps. -/
namespace Solidity.Yul.Adapters.MemoryBytes
open Solidity.Backend
/-- Single-byte update is definitionally the published backend operation. -/
theorem save_eq_write (m : Views.ByteView) (a : Nat) (v : UInt8) :
    Views.saveByte m a v=Environment.writeByte m a v := by rfl

/-- Byte observations have identical order and length in the two APIs. -/
theorem read_eq_read (m : Views.ByteView) (a n : Nat) :
    Views.readBytes m a n=Environment.readMemory m a n := by rfl

/-- Both APIs read the old source map, including overlap in either direction. -/
theorem copy_eq_write_read (dst src : Views.ByteView) (to start n : Nat) :
    Views.copyBytes dst src to start n =
      Environment.writeBytes dst to (Environment.readMemory src start n) := by
  funext a
  have length : (Environment.readMemory src start n).length=n := by
    simp only [Environment.readMemory,List.length_map,List.length_range]
  by_cases inside : to≤a ∧ a<to+n
  · have jlt : a-to<n := by omega
    have add : to+(a-to)=a := by omega
    have written := Environment.writeBytes_at (Environment.readMemory src start n) to (a-to) dst
      (by rw [length];exact jlt)
    rw [add] at written
    simp only [Environment.readMemory,List.getElem_map,List.getElem_range] at written
    change (if to≤a ∧ a<to+n then src (start+(a-to)) else dst a)=_
    rw [if_pos inside]
    exact written.symm
  · rw [Views.copyBytes_outside dst src to start n a inside]
    exact (Environment.writeBytes_frame _ _ _ _ (by rw [length];omega)).symm

/-- Writing an unchanged snapshot preserves the COMPLETE mathematical byte map. -/
theorem write_read_identity (m : Views.ByteView) (a n : Nat) :
    Environment.writeBytes m a (Environment.readMemory m a n)=m := by
  rw [←copy_eq_write_read m m a a n]
  exact Views.mcopy_self m a n

/-- Disjoint writes commute on the complete map, including arbitrary raw bytes
and unknown exterior data. Separation is actual byte-range separation. -/
theorem write_commute (m : Environment.Memory) (a b : Nat) (xs ys : List UInt8)
    (separate : ∀ k,a≤k ∧ k<a+xs.length → ¬(b≤k ∧ k<b+ys.length)) :
    Environment.writeBytes (Environment.writeBytes m a xs) b ys=
      Environment.writeBytes (Environment.writeBytes m b ys) a xs := by
  funext k
  by_cases ha : a≤k ∧ k<a+xs.length
  · have hb : k<b ∨ b+ys.length≤k := by have no := separate k ha;omega
    have ja : k-a<xs.length := by omega
    have add : a+(k-a)=k := by omega
    rw [Environment.writeBytes_frame ys b k _ hb]
    have left := Environment.writeBytes_at xs a (k-a) m ja
    have right := Environment.writeBytes_at xs a (k-a) (Environment.writeBytes m b ys) ja
    rw [add] at left right
    exact left.trans right.symm
  · have outsideA : k<a ∨ a+xs.length≤k := by omega
    by_cases hb : b≤k ∧ k<b+ys.length
    · rw [Environment.writeBytes_frame xs a k _ outsideA]
      have jb : k-b<ys.length := by omega
      have add : b+(k-b)=k := by omega
      have left := Environment.writeBytes_at ys b (k-b) (Environment.writeBytes m a xs) jb
      have right := Environment.writeBytes_at ys b (k-b) m jb
      rw [add] at left right
      exact left.trans right.symm
    · have outsideB : k<b ∨ b+ys.length≤k := by omega
      rw [Environment.writeBytes_frame ys b k _ outsideB,
        Environment.writeBytes_frame xs a k _ outsideA,
        Environment.writeBytes_frame xs a k _ outsideA,
        Environment.writeBytes_frame ys b k _ outsideB]

/-- Equal-length replacement forgets the earlier payload, including all raw bits. -/
theorem write_overwrite (m : Environment.Memory) (a : Nat) (xs ys : List UInt8)
    (length : xs.length=ys.length) :
    Environment.writeBytes (Environment.writeBytes m a xs) a ys=
      Environment.writeBytes m a ys := by
  funext k
  by_cases inside : a≤k ∧ k<a+ys.length
  · have j : k-a<ys.length := by omega
    have add : a+(k-a)=k := by omega
    have left := Environment.writeBytes_at ys a (k-a) (Environment.writeBytes m a xs) j
    have right := Environment.writeBytes_at ys a (k-a) m j
    rw [add] at left right
    exact left.trans right.symm
  · have outsideY : k<a ∨ a+ys.length≤k := by omega
    have outsideX : k<a ∨ a+xs.length≤k := by omega
    rw [Environment.writeBytes_frame ys a k _ outsideY,
      Environment.writeBytes_frame xs a k _ outsideX,
      Environment.writeBytes_frame ys a k _ outsideY]

end Solidity.Yul.Adapters.MemoryBytes
