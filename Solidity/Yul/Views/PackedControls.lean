import Solidity.Yul.Views.AggregateData
import Solidity.Yul.Views.ScalarControls

/-! Actual heterogeneous source struct and multi-slot fixed-array components.
Nonzero initial words expose both inter-slot gaps and trailing padding. -/
namespace Solidity.Yul.Views.Controls

def signed128 : Source.IntTy := ⟨true, 128, by decide⟩
def unsigned24 : Source.IntTy := ⟨false, 24, by decide⟩
def aggregateLayout : Source.Layout :=
  ⟨fun _ => [.int signed8, .fixedBytes 2 (by decide), .address false, .int signed128, .bool],
    fun _ => 3, fun _ => .bool⟩

def structMembers : Source.DataList aggregateLayout (aggregateLayout.fields scalarName) :=
  .cons (.val (.int (-1) (by decide)))
    (.cons (.val (.fixedBytes [0x12, 0x34] rfl))
      (.cons (.val (.address ⟨0x112233, by decide⟩))
        (.cons (.val (.int (-2) (by decide))) (.cons (.val (.bool true)) .nil))))

def structCodecs : PackedMembers aggregateLayout (aggregateLayout.fields scalarName) :=
  .cons (intField signed8 0 (by decide)) (.int signed8) (intCodec _ signed8 0 (by decide))
    (.cons (fixedBytesField 2 (by decide) 0 (by decide)) (.fixedBytes 2 (by decide))
      (fixedBytesCodec _ 2 (by decide) 0 (by decide))
      (.cons (addressField 0 (by decide)) (.address false) (addressCodec _ false 0 (by decide))
        (.cons (intField signed128 0 (by decide)) (.int signed128) (intCodec _ signed128 0 (by decide))
          (.cons boolField .bool (boolCodec _) .nil))))

def nonzeroSlots : SlotView := fun _ => ⟨0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5, by decide⟩
def structBytes : ByteView := (structCodecs.encode structMembers 0 (slotBytes nonzeroSlots)).getD (fun _ => 0)
def structSlots : SlotView := slotsOfBytes structBytes

theorem struct_success : structCodecs.encode structMembers 0 (slotBytes nonzeroSlots) = some structBytes := rfl

theorem heterogeneous_struct_roundtrip :
    decodePackedStruct scalarName structCodecs 0 (by unfold PackedMembers.Fits; decide) (slotBytes structSlots) =
      some (.struct structMembers) := by
  simp only [decodePackedStruct, structSlots,
    structCodecs.slot_roundtrip structMembers 0 (by unfold PackedMembers.Fits; decide) nonzeroSlots structBytes struct_success,
    Option.map_some]

theorem heterogeneous_struct_bytes :
    structBytes 0 = 255 ∧ structBytes 1 = 0x34 ∧ structBytes 2 = 0x12 ∧
    structBytes 3 = 0x33 ∧ structBytes 23 = 0xa5 ∧ structBytes 31 = 0xa5 ∧
    structBytes 32 = 0xfe ∧ structBytes 48 = 1 ∧ structBytes 49 = 0xa5 ∧
    structBytes 64 = 0xa5 := by decide

theorem heterogeneous_struct_extent : structCodecs.endByte 0 = 49 ∧ structCodecs.nextSlot 0 = 2 := by decide

theorem heterogeneous_struct_unchanged :
    structCodecs.encode structMembers 0 structBytes = some structBytes :=
  structCodecs.encode_idempotent structMembers 0 _ structBytes struct_success

def arrayCodecs := repeatedMembers (intField unsigned24 0 (by decide))
  (StorageWidth.int (D := aggregateLayout) unsigned24) (intCodec aggregateLayout unsigned24 0 (by decide)) 12

def arrayValues (i : Fin 12) : Source.Val aggregateLayout (.int unsigned24) :=
  .int (i.val + 1) (by have hi := i.isLt; change 0 ≤ (i.val : Int) + 1 ∧ (i.val : Int) + 1 ≤ 16777215; omega)

def fixedArrayMembers := arrayMembers 12 (fun i => .val (arrayValues i))
def fixedArrayBytes : ByteView := (arrayCodecs.encode fixedArrayMembers 0 (slotBytes nonzeroSlots)).getD (fun _ => 0)
def fixedArraySlots := slotsOfBytes fixedArrayBytes

theorem array_success : arrayCodecs.encode fixedArrayMembers 0 (slotBytes nonzeroSlots) = some fixedArrayBytes := rfl

theorem multi_element_array_roundtrip :
    decodePackedArray (intField unsigned24 0 (by decide)) (.int unsigned24)
      (intCodec aggregateLayout unsigned24 0 (by decide)) 12 (by decide) 0 (by unfold PackedMembers.Fits; decide)
      (slotBytes fixedArraySlots) =
        some (.array 12 (fun _ h => (Option.some.inj h).symm) (fun i => .val (arrayValues i))) := by
  unfold decodePackedArray fixedArraySlots
  change (arrayCodecs.decode 0 (slotBytes (slotsOfBytes fixedArrayBytes))).map
    (fun ds => Source.Data.array 12 (fun _ h => (Option.some.inj h).symm) (membersArray 12 ds)) = _
  have hr : arrayCodecs.decode 0 (slotBytes (slotsOfBytes fixedArrayBytes)) = some fixedArrayMembers := by
    simpa only [Fin.val_zero, Nat.zero_mul] using
      arrayCodecs.slot_roundtrip fixedArrayMembers 0 (by unfold PackedMembers.Fits; decide)
        nonzeroSlots fixedArrayBytes array_success
  rw [hr]
  simp only [Option.map_some, fixedArrayMembers, membersArray_arrayMembers]

theorem fixed_array_packing_and_padding :
    fixedArrayBytes 0 = 1 ∧ fixedArrayBytes 3 = 2 ∧ fixedArrayBytes 27 = 10 ∧
    fixedArrayBytes 30 = 0xa5 ∧ fixedArrayBytes 31 = 0xa5 ∧
    fixedArrayBytes 32 = 11 ∧ fixedArrayBytes 35 = 12 ∧ fixedArrayBytes 38 = 0xa5 ∧
    arrayCodecs.endByte 0 = 38 ∧ arrayCodecs.nextSlot 0 = 2 := by decide

theorem array_refuses_wrapping_extent :
    ¬ arrayCodecs.Fits ⟨2 ^ 256 - 1, by decide⟩ := by unfold PackedMembers.Fits; decide

def enumThenBool : PackedMembers scalarLayout [.enum scalarName, .bool] :=
  .cons (enumField 0 (by decide)) (.enum scalarName (by decide))
    (enumCodec scalarLayout scalarName 0 (by decide) (by decide))
    (.cons boolField .bool (boolCodec _) .nil)

theorem aggregate_invalid_enum_refusal : enumThenBool.decode 0 (fun _ => 3) = none := rfl

theorem aggregate_slot_words :
    (structSlots 0).val = 0xa5a5a5a5a5a5a5a5a500000000000000000000000000000000001122331234ff ∧ (structSlots 1).val = 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a501fffffffffffffffffffffffffffffffe ∧
    (fixedArraySlots 0).val = 0xa5a500000a000009000008000007000006000005000004000003000002000001 ∧ (fixedArraySlots 1).val = 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a500000c00000b := by decide

theorem struct_data_encoding :
    encodePackedStruct scalarName structCodecs 0 (by unfold PackedMembers.Fits; decide)
      (.struct structMembers) nonzeroSlots = some structSlots := rfl

theorem array_data_encoding :
    encodePackedArray (intField unsigned24 0 (by decide)) (.int unsigned24)
      (intCodec aggregateLayout unsigned24 0 (by decide)) 12 (by decide) 0
      (by unfold PackedMembers.Fits; decide)
      (.array 12 (fun _ h => (Option.some.inj h).symm) (fun i => .val (arrayValues i))) nonzeroSlots =
        some fixedArraySlots := by
  rw [encodePackedArray_contents]
  rfl

theorem struct_reference_is_not_contents :
    encodePackedStruct scalarName structCodecs 0 (by unfold PackedMembers.Fits; decide)
      (.val (.storRef rfl ⟨scalarName, []⟩)) nonzeroSlots = none := rfl

#print axioms PackedMembers.decode_encode
#print axioms PackedMembers.slot_roundtrip
#print axioms heterogeneous_struct_roundtrip
#print axioms multi_element_array_roundtrip

end Solidity.Yul.Views.Controls
