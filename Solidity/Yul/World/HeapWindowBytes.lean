import Solidity.Yul.World.PhysicalHeapPort

/-! Byte-list specification for an owned partial payload copy. This is not
another memory semantics: the proof observes the existing writeBytes/readBytes. -/
namespace Solidity.Yul.World.HeapWindow
open Solidity.Yul.Views
open Solidity.Roadmap (Bytes)
open Solidity.Backend.Environment (writeBytes)

def splice (old : Bytes) (offset : Nat) (bytes : Bytes) : Bytes :=
  old.take offset ++ (bytes ++ old.drop (offset + bytes.length))

theorem splice_length (old bytes : Bytes) (offset : Nat) (inside : offset + bytes.length ≤ old.length) :
    (splice old offset bytes).length = old.length := by
  simp only [splice,List.length_append,List.length_take,List.length_drop]
  rw [Nat.min_eq_left (by omega)]
  omega

/-- Exact readback from the actual existing byte write. Initial payload reads
and destination containment are explicit, not a supplied adequacy theorem. -/
theorem read_splice (m : ByteView) (base : Nat) (old bytes : Bytes) (offset : Nat)
    (reads : readBytes m base old.length = old) (inside : offset + bytes.length ≤ old.length) :
    readBytes (writeBytes m (base + offset) bytes) base old.length = splice old offset bytes := by
  apply List.ext_getElem
  · simp only [readBytes,List.length_map,List.length_range,splice_length old bytes offset inside]
  · intro i hi hj
    have bound : i < old.length := by simpa only [readBytes,List.length_map,List.length_range] using hi
    simp only [readBytes,List.getElem_map,List.getElem_range]
    unfold splice
    have takeLen : (old.take offset).length = offset := by rw [List.length_take,Nat.min_eq_left (by omega)]
    by_cases before : i < offset
    · rw [Solidity.Backend.Environment.writeBytes_frame _ _ _ _ (Or.inl (by omega))]
      rw [List.getElem_append_left (by omega),List.getElem_take]
      exact readBytes_element m base old reads ⟨i,bound⟩
    · by_cases during : i < offset + bytes.length
      · have ib : i-offset < bytes.length := by omega
        rw [show base+i = (base+offset)+(i-offset) by omega,
          Solidity.Backend.Environment.writeBytes_at bytes (base+offset) (i-offset) m ib]
        rw [List.getElem_append_right (by omega)]
        simp only [takeLen]
        rw [List.getElem_append_left ib]
      · rw [Solidity.Backend.Environment.writeBytes_frame _ _ _ _ (Or.inr (by omega))]
        rw [List.getElem_append_right (by omega)]
        simp only [takeLen]
        rw [List.getElem_append_right (by omega),List.getElem_drop]
        have index : offset + bytes.length + (i-offset-bytes.length) = i := by omega
        simp only [index]
        exact readBytes_element m base old reads ⟨i,bound⟩

theorem splice_prefix (old bytes : Bytes) (offset : Nat) (inside : offset + bytes.length ≤ old.length) :
    (splice old offset bytes).take offset = old.take offset := by
  apply List.take_left'
  rw [List.length_take,Nat.min_eq_left (by omega)]

theorem splice_suffix (old bytes : Bytes) (offset : Nat) (inside : offset + bytes.length ≤ old.length) :
    (splice old offset bytes).drop (offset + bytes.length) = old.drop (offset + bytes.length) := by
  have frontLen : (old.take offset ++ bytes).length = offset + bytes.length := by
    rw [List.length_append,List.length_take,Nat.min_eq_left (by omega)]
  unfold splice
  rw [← List.append_assoc]
  exact List.drop_left' frontLen

theorem splice_empty (old : Bytes) (offset : Nat) : splice old offset [] = old := by
  simp only [splice,List.length_nil,List.nil_append,Nat.add_zero,List.take_append_drop]

end Solidity.Yul.World.HeapWindow
