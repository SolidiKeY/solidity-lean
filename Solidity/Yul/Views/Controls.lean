import Solidity.Source.Observe
import Solidity.Yul.Views.WordMemory
import Solidity.Yul.Views.Inputs
import Solidity.Yul.Views.Regions
import Solidity.Yul.Views.Widths
import Solidity.Yul.Views.StorageContract

/-! Inhabited, negative, endian, width, overlap and combination controls.
`#guard` hashes are executable external-style computation, not kernel theorems.
All theorems below use kernel proofs; no native_decide or extra budget. -/
namespace Solidity.Yul.Views.Controls

def zero : ByteView := fun _ => 0
def ascending : ByteView := fun a => UInt8.ofNat a

theorem big_endian : readBytes (mstore zero 128 ⟨0x12345678, by decide⟩) 156 4 =
    [0x12, 0x34, 0x56, 0x78] := by decide

theorem not_little_endian : readBytes (mstore zero 128 ⟨0x12345678, by decide⟩) 156 4 ≠
    [0x78, 0x56, 0x34, 0x12] := by decide

theorem low_byte_only : mstore8 zero 129 ⟨0xabcd, by decide⟩ 129 = 0xcd ∧
    mstore8 zero 129 ⟨0xabcd, by decide⟩ 128 = 0 := by decide

theorem copy_overlap_right : readBytes (mcopy ascending 2 0 6) 0 10 =
    [0, 1, 0, 1, 2, 3, 4, 5, 8, 9] := by decide

theorem copy_overlap_left : readBytes (mcopy ascending 0 2 6) 0 10 =
    [2, 3, 4, 5, 6, 7, 6, 7, 8, 9] := by decide

theorem zero_copy : mcopy ascending 1 2 0 = ascending := copyBytes_zero _ _ _ _

def middle : Field := ⟨1, 2, by decide, by decide⟩

theorem packed_middle : middle.save 0xabcdef01 ⟨0x1234, by decide⟩ = 0xab123401 ∧
    middle.find 0xab123401 = 0x1234 := by decide

def fullField : Field := ⟨0, 32, by decide, by decide⟩
def lastByte : Field := ⟨31, 1, by decide, by decide⟩

theorem full_width : fullField.save 0 ⟨2 ^ 256 - 1, by decide⟩ = 2 ^ 256 - 1 ∧
    fullField.find (2 ^ 256 - 1) = 2 ^ 256 - 1 := by decide

theorem last_byte : lastByte.save 0 ⟨255, by decide⟩ = 255 * 256 ^ 31 ∧
    lastByte.find (255 * 256 ^ 31) = 255 := by decide

/-- Two's-complement storage byte from the actual typed source int8 word. -/
theorem signed_byte :
    ((Source.Val.int (D := (⟨fun _ => [], fun _ => 1, fun _ => .bool⟩ : Source.Layout)) (t := ⟨true, 8, by decide⟩) (-1) (by decide)).word.map
      (fun w => boolField.find w.val)) = some 255 := by decide

theorem crossing_slot_refused (f : Field) : ¬ (f.offset = 31 ∧ f.width = 2) := by
  have hf := f.fits
  omega

theorem calldata_padding : calldataload [0x12, 0x34] 0 = 0x1234 * 256 ^ 30 ∧
    calldataload [0x12, 0x34] 2 = 0 := by decide

theorem calldata_copy_padding : readBytes (calldatacopy ascending [0xab, 0xcd] 4 1 4) 2 8 =
    [2, 3, 0xcd, 0, 0, 0, 8, 9] := by decide

theorem memory_calldata_combination :
    mloadNat (mcopy (calldatacopy zero [0xaa, 0xbb] 128 0 32) 160 128 32) 160 =
      calldataload [0xaa, 0xbb] 0 := by decide

def layout : Source.Layout := ⟨fun _ => [], fun _ => 1, fun _ => .bool⟩

def boolBytes : ByteCodec layout .bool 1 where
  encode v _ := UInt8.ofNat ((boolCodec layout).encode v).val
  decode bs := if (bs ⟨0, by decide⟩).toNat = 0 then some (.bool false)
    else if (bs ⟨0, by decide⟩).toNat = 1 then some (.bool true) else none
  decode_encode v := by
    cases v with
    | bool b => cases b <;> rfl
    | memRef h _ | storRef h _ | cdRef h _ => cases h

def oneRegion : Regions Unit where
  width _ := 1
  address _ _ := 0
  owner a := if a = 0 then some ⟨(), ⟨0, by decide⟩⟩ else none
  owner_at p i := by
    cases p
    have hi : i = ⟨0, by decide⟩ := Fin.ext (by omega)
    subst i
    rfl
  address_owner a p i h := by
    by_cases ha : a = 0
    · exact ha.symm
    · simp only [ha, if_false] at h
      contradiction

theorem typed_residual_witness :
    oneRegion.encode (fun _ => boolBytes) (fun _ => .bool true) (fun _ => 0xa5) 0 = 1 ∧
    oneRegion.encode (fun _ => boolBytes) (fun _ => .bool true) (fun _ => 0xa5) 5 = 0xa5 := by
  decide

theorem dirty_bool_not_canonical : boolBytes.decode (fun _ => 2) = none := rfl

/- The real fixed hash is used; these guards execute compiled Keccak and are
reported separately from the universal hash congruence theorem. -/
#guard (keccak256 Roadmap.Evm.withKeccak zero 128 0).val ==
  0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
#guard (keccak256 Roadmap.Evm.withKeccak (calldataBytes [0x61, 0x62, 0x63]) 0 3).val ==
  0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45

#print axioms Field.find_save
#print axioms Field.save_unchanged
#print axioms mload_mstore
#print axioms mstore_mload
#print axioms Regions.decode_encode
#print axioms Regions.unchanged
#print axioms source_view_rollback
#print axioms calldata_zero
#print axioms keccak256_congr
#print axioms memory_calldata_combination

end Solidity.Yul.Views.Controls
