import Solidity.Yul.Views.ArrayStruct
import Solidity.Yul.Views.PackedControls

/-! Closed nested layouts over actual declaration-indexed source data. Computational
goldens include every slot and an untouched sentinel; kernel laws cover residuals. -/
namespace Solidity.Yul.Views.Controls

def outerName : Source.DeclName := ⟨some "Nested", "Outer"⟩
def innerName : Source.DeclName := ⟨some "Nested", "Inner"⟩
def innerTypes : List Source.STy := [.int signed8, .fixedBytes 2 (by decide), .address false, .int signed128, .bool]
def outerTypes : List Source.STy := [.array .storage (.int unsigned24) (some 12), .struct .storage innerName]
def nestedLayout : Source.Layout := ⟨fun d => if d = outerName then outerTypes else innerTypes, fun _ => 3, fun _ => .bool⟩

theorem inner_fields : nestedLayout.fields innerName = innerTypes := by
  change (if innerName = outerName then outerTypes else innerTypes) = innerTypes
  rw [if_neg (by decide)]

def nestedInnerCodecs : PackedMembers nestedLayout (nestedLayout.fields innerName) :=
  inner_fields.symm ▸
    (.cons (intField signed8 0 (by decide)) (.int signed8) (intCodec _ signed8 0 (by decide))
      (.cons (fixedBytesField 2 (by decide) 0 (by decide)) (.fixedBytes 2 (by decide))
        (fixedBytesCodec _ 2 (by decide) 0 (by decide))
        (.cons (addressField 0 (by decide)) (.address false) (addressCodec _ false 0 (by decide))
          (.cons (intField signed128 0 (by decide)) (.int signed128) (intCodec _ signed128 0 (by decide))
            (.cons boolField .bool (boolCodec _) .nil)))))

def nestedInnerValues (i : Fin 3) : Source.DataList nestedLayout (nestedLayout.fields innerName) :=
  castDataFields inner_fields.symm
    (.cons (.val (.int (-(i.val : Int) - 1) (by
      have hi := i.isLt; change -128 ≤ -(i.val : Int) - 1 ∧ -(i.val : Int) - 1 ≤ 127; omega)))
      (.cons (.val (.fixedBytes [UInt8.ofNat (16 + i.val), UInt8.ofNat (32 + i.val)] rfl))
        (.cons (.val (.address ⟨0x112233 + i.val, by have hi := i.isLt; omega⟩))
          (.cons (.val (.int (-(i.val : Int) - 2) (by
            have hi := i.isLt
            change -170141183460469231731687303715884105728 ≤ -(i.val : Int) - 2 ∧
              -(i.val : Int) - 2 ≤ 170141183460469231731687303715884105727
            omega))) (.cons (.val (.bool (i.val % 2 == 0))) .nil)))))

theorem nested_inner_scalar (i : Fin 3) : ScalarMembers (nestedInnerValues i) :=
  .cons _ _ (.cons _ _ (.cons _ _ (.cons _ _ (.cons _ _ .nil))))

def nestedArrayValues (i : Fin 12) : Source.Val nestedLayout (.int unsigned24) :=
  .int (i.val + 1) (by have hi := i.isLt; change 0 ≤ (i.val : Int) + 1 ∧ (i.val : Int) + 1 ≤ 16777215; omega)

def nestedSchema : ArrayStructSchema nestedLayout outerName innerName (.int unsigned24) 12 where
  scalarField := intField unsigned24 0 (by decide)
  scalarWidth := .int unsigned24
  scalarCodec := intCodec _ unsigned24 0 (by decide)
  innerCodecs := nestedInnerCodecs
  positive := by decide
  fields := by change (if outerName = outerName then outerTypes else innerTypes) = outerTypes; rw [if_pos rfl]

def nestedData := nestedSchema.makeData (fun i => .val (nestedArrayValues i)) (nestedInnerValues 0)
def nestedSlots : SlotView := (encodeArrayStruct nestedSchema 0 (by unfold ArrayStructSchema.Fits; decide)
  nestedData nonzeroSlots).getD nonzeroSlots

theorem nested_encode_success : encodeArrayStruct nestedSchema 0 (by unfold ArrayStructSchema.Fits; decide)
    nestedData nonzeroSlots = some nestedSlots := rfl

theorem nested_struct_roundtrip : decodeArrayStruct nestedSchema 0 (by unfold ArrayStructSchema.Fits; decide)
    nestedSlots = some nestedData := by
  obtain ⟨out, e, h⟩ := arrayStruct_physical_roundtrip nestedSchema 0 (by unfold ArrayStructSchema.Fits; decide)
    nestedArrayValues (nestedInnerValues 0) (nested_inner_scalar 0) nonzeroSlots
  change decodeArrayStruct nestedSchema 0 _ ((encodeArrayStruct nestedSchema 0 _ nestedData nonzeroSlots).getD nonzeroSlots) = _
  change encodeArrayStruct nestedSchema 0 _ nestedData nonzeroSlots = some out at e
  rw [e]
  exact h

theorem nested_struct_unchanged : encodeArrayStruct nestedSchema 0 (by unfold ArrayStructSchema.Fits; decide)
    nestedData nestedSlots = some nestedSlots :=
  arrayStruct_encoded_unchanged nestedSchema 0 _ nestedData nonzeroSlots nestedSlots nested_encode_success

def manyData : Source.Data nestedLayout (.array .storage (.struct .storage innerName) (some 3)) :=
  .array 3 (fun _ h => (Option.some.inj h).symm) (fun i => .struct (nestedInnerValues i))
def manySlots : SlotView := (encodeStructArray innerName nestedInnerCodecs 3 (by decide) 0 (by decide)
  manyData nonzeroSlots).getD nonzeroSlots

theorem many_encode_success : encodeStructArray innerName nestedInnerCodecs 3 (by decide) 0 (by decide)
    manyData nonzeroSlots = some manySlots := rfl

theorem heterogeneous_array_roundtrip : decodeStructArray innerName nestedInnerCodecs 3 (by decide) 0 (by decide)
    manySlots = some manyData := by
  obtain ⟨out, e, h⟩ := structArray_physical_roundtrip innerName nestedInnerCodecs 3 (by decide) 0 (by decide)
    nestedInnerValues nested_inner_scalar nonzeroSlots
  change decodeStructArray innerName nestedInnerCodecs 3 _ 0 _
    ((encodeStructArray innerName nestedInnerCodecs 3 _ 0 _ manyData nonzeroSlots).getD nonzeroSlots) = _
  change encodeStructArray innerName nestedInnerCodecs 3 _ 0 _ manyData nonzeroSlots = some out at e
  rw [e]
  exact h

theorem heterogeneous_array_unchanged : encodeStructArray innerName nestedInnerCodecs 3 (by decide) 0 (by decide)
    manyData manySlots = some manySlots :=
  structArray_encoded_unchanged innerName nestedInnerCodecs 3 _ 0 _ manyData nonzeroSlots manySlots many_encode_success

theorem nested_extents : nestedSchema.nextByte 0 = 64 ∧ nestedSchema.endByte 0 = 128 ∧
    structArrayEnd nestedInnerCodecs 3 0 = 192 := by decide

local instance packedOwnsDecision {D : Source.Layout} {xs : List Source.STy}
    (cs : PackedMembers D xs) (p a : Nat) : Decidable (cs.owns p a) := cs.ownsDecidable p a

local instance nestedOwnsDecision (p a : Nat) : Decidable (nestedSchema.owns p a) :=
  inferInstanceAs (Decidable (nestedSchema.first.owns p a ∨ nestedSchema.innerCodecs.owns (nestedSchema.nextByte p) a))

theorem many_unowned_gaps (a : Nat)
    (gap : ¬ ((0 ≤ a ∧ a < 49) ∨ (64 ≤ a ∧ a < 113) ∨ (128 ≤ a ∧ a < 177))) :
    ¬ structArrayOwns nestedInnerCodecs 3 0 a := by
  have sizes : nestedInnerCodecs.endByte 0 = 49 ∧ nestedInnerCodecs.endByte 64 = 113 ∧
      nestedInnerCodecs.endByte 128 = 177 := by decide
  change ¬ (nestedInnerCodecs.owns 0 a ∨ nestedInnerCodecs.owns 64 a ∨ nestedInnerCodecs.owns 128 a ∨ False)
  intro h
  rcases h with h | h | h | h
  · have hb := nestedInnerCodecs.owned_bounds 0 a h
    rw [sizes.1] at hb
    exact gap (Or.inl hb)
  · have hb := nestedInnerCodecs.owned_bounds 64 a h
    rw [sizes.2.1] at hb
    exact gap (Or.inr (Or.inl hb))
  · have hb := nestedInnerCodecs.owned_bounds 128 a h
    rw [sizes.2.2] at hb
    exact gap (Or.inr (Or.inr hb))
  · exact h

theorem nonzero_slot_byte (a : Nat) : slotBytes nonzeroSlots a = 0xa5 := by
  have h : ∀ i : Fin 32, wordByte (nonzeroSlots 0) i = 0xa5 := by decide
  exact h _

theorem nested_padding : slotBytes nestedSlots 30 = 0xa5 ∧ slotBytes nestedSlots 31 = 0xa5 ∧
    slotBytes nestedSlots 63 = 0xa5 ∧ slotBytes nestedSlots 87 = 0xa5 ∧ slotBytes nestedSlots 127 = 0xa5 ∧
    slotBytes manySlots 63 = 0xa5 ∧ slotBytes manySlots 127 = 0xa5 ∧ slotBytes manySlots 191 = 0xa5 ∧
    slotBytes manySlots 192 = 0xa5 := by
  have one (a : Nat) (b : a < (2 ^ 256) * 32) (h : ¬ nestedSchema.owns 0 a) : slotBytes nestedSlots a = 0xa5 := by
    rw [arrayStruct_encoded_residual nestedSchema 0 _ nestedData nonzeroSlots nestedSlots nested_encode_success a b h]
    exact nonzero_slot_byte a
  have many (a : Nat) (b : a < (2 ^ 256) * 32) (h : ¬ structArrayOwns nestedInnerCodecs 3 0 a) : slotBytes manySlots a = 0xa5 := by
    rw [structArray_encoded_residual innerName nestedInnerCodecs 3 _ 0 _ manyData nonzeroSlots manySlots many_encode_success a b h]
    exact nonzero_slot_byte a
  exact ⟨one 30 (by decide) (by decide), one 31 (by decide) (by decide), one 63 (by decide) (by decide),
    one 87 (by decide) (by decide), one 127 (by decide) (by decide),
    many 63 (by decide) (many_unowned_gaps 63 (by decide)), many 127 (by decide) (many_unowned_gaps 127 (by decide)), many 191 (by decide) (many_unowned_gaps 191 (by decide)),
    many 192 (by decide) (many_unowned_gaps 192 (by decide))⟩

theorem nested_refuses_outer_reference : encodeArrayStruct nestedSchema 0 (by unfold ArrayStructSchema.Fits; decide)
    (.val (.storRef rfl ⟨outerName, []⟩)) nonzeroSlots = none := rfl

def oneElementReference (i : Fin 3) : Source.Data nestedLayout (.struct .storage innerName) :=
  if i.val = 1 then .val (.storRef rfl ⟨innerName, []⟩) else .struct (nestedInnerValues i)

theorem array_refuses_element_reference : encodeStructArray innerName nestedInnerCodecs 3 (by decide) 0 (by decide)
    (.array 3 (fun _ h => (Option.some.inj h).symm) oneElementReference) nonzeroSlots = none := rfl

theorem array_refuses_wrong_length : checkedStructArray nestedLayout innerName 3 2
    (fun _ => .struct (nestedInnerValues 0)) = none := rfl

theorem incompatible_element_type :
    Source.STy.array .storage (.struct .storage innerName) (some 3) ≠ .array .storage .bool (some 3) := by
  intro h
  cases h

theorem incompatible_length_index :
    Source.STy.array .storage (.struct .storage innerName) (some 3) ≠ .array .storage (.struct .storage innerName) (some 2) := by
  intro h
  cases h

theorem nested_refuses_wrapping_extent : ¬ nestedSchema.Fits ⟨2 ^ 256 - 1, by decide⟩ := by
  unfold ArrayStructSchema.Fits
  decide

/-- Explicit physical word goldens, checked by compiled evaluation below.
They are executable controls, separate from the universal kernel theorems. -/
def nestedWordGoldens : List Nat := [0xa5a500000a000009000008000007000006000005000004000003000002000001, 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a500000c00000b, 0xa5a5a5a5a5a5a5a5a500000000000000000000000000000000001122331020ff, 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a501fffffffffffffffffffffffffffffffe, 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5]
def manyWordGoldens : List Nat := [0xa5a5a5a5a5a5a5a5a500000000000000000000000000000000001122331020ff, 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a501fffffffffffffffffffffffffffffffe, 0xa5a5a5a5a5a5a5a5a500000000000000000000000000000000001122341121fe, 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a500fffffffffffffffffffffffffffffffd, 0xa5a5a5a5a5a5a5a5a500000000000000000000000000000000001122351222fd, 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a501fffffffffffffffffffffffffffffffc, 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5]
#guard List.ofFn (fun i : Fin 5 => (nestedSlots ⟨i.val, by have h := i.isLt; omega⟩).val) == nestedWordGoldens
#guard List.ofFn (fun i : Fin 7 => (manySlots ⟨i.val, by have h := i.isLt; omega⟩).val) == manyWordGoldens

#print axioms nested_struct_roundtrip
#print axioms heterogeneous_array_roundtrip
#print axioms arrayStruct_encoded_unchanged
#print axioms structArray_encoded_unchanged

end Solidity.Yul.Views.Controls
