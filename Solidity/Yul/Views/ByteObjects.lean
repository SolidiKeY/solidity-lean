import Solidity.Yul.Views.MemoryLayout
import Solidity.Yul.Views.Inputs

/-!
# Length-prefixed byte/string object views

The contents `bs` are those of existing `Source.Data.bytes`/`string`.
This preparation encodes their header/live payload and retains all other bytes,
including allocation padding. It does not mutate the logical source heap.
-/
namespace Solidity.Yul.Views

def bytesObjectView (bs : List UInt8) (length_bound : bs.length < 2 ^ 256)
    (residual : ByteView) (base : Nat) : ByteView :=
  copyBytes (mstore residual base ⟨bs.length, length_bound⟩)
    (calldataBytes bs) (base + 32) 0 bs.length

theorem bytesObject_header (bs : List UInt8) (hl : bs.length < 2 ^ 256) (m : ByteView) (base : Nat) :
    mload (bytesObjectView bs hl m base) base = ⟨bs.length, hl⟩ := by
  calc
    _ = mload (mstore m base ⟨bs.length, hl⟩) base := by
      apply mload_congr
      intro i
      exact copyBytes_outside _ _ _ _ _ _ (by have hi := i.isLt; omega)
    _ = _ := mload_mstore m base ⟨bs.length, hl⟩

theorem bytesObject_payload (bs : List UInt8) (hl : bs.length < 2 ^ 256) (m : ByteView)
    (base i : Nat) (hi : i < bs.length) :
    bytesObjectView bs hl m base (base + 32 + i) = bs[i] := by
  calc
    _ = calldataBytes bs (0 + i) := find_copyBytes _ _ _ _ _ i hi
    _ = _ := by
      simp only [calldataBytes, Nat.zero_add, List.getElem?_eq_getElem hi, Option.getD_some]

theorem bytesObject_residual (bs : List UInt8) (hl : bs.length < 2 ^ 256) (m : ByteView)
    (base a : Nat) (outside : a < base ∨ base + 32 + bs.length ≤ a) :
    bytesObjectView bs hl m base a = m a := by
  calc
    _ = mstore m base ⟨bs.length, hl⟩ a := copyBytes_outside _ _ _ _ _ _ (by omega)
    _ = _ := mstore_outside m base a ⟨bs.length, hl⟩ (by omega)

/-- Exact unchanged-view writeback, including nonzero residual/padding bytes. -/
theorem bytesObject_unchanged (bs : List UInt8) (hl : bs.length < 2 ^ 256) (m : ByteView)
    (base : Nat) (header : mload m base = ⟨bs.length, hl⟩)
    (payload : ∀ i (hi : i < bs.length), bs[i] = m (base + 32 + i)) :
    bytesObjectView bs hl m base = m := by
  unfold bytesObjectView
  rw [← header, mstore_mload]
  funext a
  unfold copyBytes
  split
  · rename_i h
    have hi : a - (base + 32) < bs.length := by omega
    simp only [Nat.zero_add, calldataBytes, List.getElem?_eq_getElem hi, Option.getD_some]
    rw [payload _ hi, Nat.add_sub_of_le h.1]
  · rfl

theorem bytesObject_payload_list (bs : List UInt8) (hl : bs.length < 2 ^ 256)
    (m : ByteView) (base : Nat) :
    readBytes (bytesObjectView bs hl m base) (base + 32) bs.length = bs := by
  apply List.ext_getElem
  · simp only [readBytes, List.length_map, List.length_range]
  · intro i _ hi
    simp only [readBytes, List.getElem_map, List.getElem_range]
    exact bytesObject_payload bs hl m base i hi

/-- Decode into the existing intrinsically typed source byte object. -/
def decodeBytesObject (D : Source.Layout) (m : ByteView) (base : Nat) :
    Source.Data D (.bytes .memory) :=
  .bytes (readBytes m (base + 32) (mload m base).val)

def decodeStringObject (D : Source.Layout) (m : ByteView) (base : Nat) :
    Source.Data D (.string .memory) :=
  .string (readBytes m (base + 32) (mload m base).val)

theorem decode_bytesObjectView (D : Source.Layout) (bs : List UInt8) (hl : bs.length < 2 ^ 256)
    (m : ByteView) (base : Nat) :
    decodeBytesObject D (bytesObjectView bs hl m base) base = .bytes bs := by
  unfold decodeBytesObject
  rw [bytesObject_header, bytesObject_payload_list]

theorem decode_stringObjectView (D : Source.Layout) (bs : List UInt8) (hl : bs.length < 2 ^ 256)
    (m : ByteView) (base : Nat) :
    decodeStringObject D (bytesObjectView bs hl m base) base = .string bs := by
  unfold decodeStringObject
  rw [bytesObject_header, bytesObject_payload_list]

theorem bytesObject_idempotent (bs : List UInt8) (hl : bs.length < 2 ^ 256)
    (m : ByteView) (base : Nat) :
    bytesObjectView bs hl (bytesObjectView bs hl m base) base = bytesObjectView bs hl m base :=
  bytesObject_unchanged bs hl _ base (bytesObject_header bs hl m base)
    (fun i hi => (bytesObject_payload bs hl m base i hi).symm)

/-- The payload equation agrees with the actual typed source read relation. -/
theorem bytesObject_source_payload {D : Source.Layout} (bs : List UInt8)
    (hl : bs.length < 2 ^ 256) (m : ByteView) (base off : Nat) (v : UInt8)
    (read : ObjectByte (Source.Data.bytes (D := D) (l := .memory) bs) off v) :
    bytesObjectView bs hl m base (base + off) = v := by
  cases read with
  | bytes _ i =>
    rw [← Nat.add_assoc]
    exact bytesObject_payload bs hl m base i.val i.isLt

end Solidity.Yul.Views
