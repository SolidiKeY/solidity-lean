import Solidity.Yul.Views.StructWordStore
import Solidity.Yul.Views.MixedHeapControls

/-! Actual heterogeneous struct updates preserve sibling aliases. Canonical
boolean preparation None is distinct from an actual wrong-type Source write.
These seeded kernel controls do not reinterpret dirty assembly observations. -/
namespace Solidity.Yul.Views.StructWordStore.Controls
open Solidity.Yul.Views.Controls

def fields : MemoryFields mixedPlacement mixedFields mixedStructWords :=
  .cons (.bool true) 1 (.scalar _ _ (by decide)) _ _
    (.cons mixedSeven 7 (.scalar _ _ (by decide)) _ _
    (.cons (.memRef rfl 0) mixedPointer (.pointer rfl 0 (.bytes .memory) rfl rfl) _ _
    (.cons (.memRef rfl 0) mixedPointer (.pointer rfl 0 (.bytes .memory) rfl rfl) _ _
    (.cons (.memRef rfl 4) mixedArrayPointer (.pointer rfl 4 mixedArrayTy rfl rfl) _ _ .nil))))

theorem supported : ∀ τ∈mixedLayout.fields mixedName,ExtendedMemberType mixedLayout τ := by
  intro τ member
  change τ∈[.bool,.int Source.IntTy.u256,.bytes .memory,.bytes .memory,mixedArrayTy] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Or.inl (Or.inl rfl) | exact Or.inl (Or.inr (Or.inl rfl)) | exact Or.inl (Or.inr (Or.inr rfl))

theorem oldReads : ∀ i w,mixedStructWords[i]?=some w → mload mixedPhysical (896+i*32)=w :=
  mixed_all_reads mixedEntry3 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

def pointerFields := (mixedFields.setNth 2 (.val (Source.Val.memRef (τ:=.bytes .memory) rfl 5))).toOption.getD mixedFields
def pointerPatch := mstore mixedPhysical 960 1408
def after := ((Source.writeLoc mixedReadFrame 0 (.mem 3 2) (Source.Val.memRef (τ:=.bytes .memory) rfl 5)).run mixedState).2

theorem pointer_writeback : canonicalStructState mixedState mixedPlacement mixedEntries 3 mixedName pointerPatch=some (.ok (),after) := by
  have result := writeback mixedState mixedPlacement mixedEntries mixed_coverage mixedReadFrame 0 3 mixedName
    mixedFields pointerFields mixedStructWords fields supported rfl ⟨2,by decide⟩ (.memRef rfl 5) 1408
    (.pointer rfl 5 (.bytes .memory) rfl rfl) rfl mixedPhysical oldReads
  have actual : (Source.writeLoc mixedReadFrame 0 (.mem 3 2) (Source.Val.memRef (τ:=.bytes .memory) rfl 5)).run mixedState=(.ok (),after) := rfl
  exact result.trans (congrArg some actual)

theorem pointer_reencode : wordListView (mixedStructWords.set 2 1408) pointerPatch 896=pointerPatch :=
  reencode mixedStructWords ⟨2,by decide⟩ 1408 mixedPhysical 896 oldReads

theorem aliases :
    (Source.readLoc (E:=mixedEnv) mixedReadFrame (.mem (τ:=.bytes .memory) 3 2)).run after=(.ok (.memRef rfl 5),after) ∧
    (Source.readLoc (E:=mixedEnv) mixedReadFrame (.mem (τ:=.bytes .memory) 3 3)).run after=(.ok (.memRef rfl 0),after) ∧
    (Source.bytesOfRV mixedReadFrame 0 (.val (Source.Val.memRef (τ:=.bytes .memory) rfl 5))).run after=(.ok mixedOther,after) := ⟨rfl,rfl,rfl⟩

theorem actual_safe : Source.MemOK mixedEnv mixedHeap.ty after :=
  canonicalStructState_MemOK mixedEnv _ mixedState mixedPlacement mixedEntries 3 mixedName pointerPatch
    (.ok (),after) pointer_writeback mixed_actual_MemOK

def boolFields := (mixedFields.setNth 0 (.val (Source.Val.bool (D:=mixedLayout) false))).toOption.getD mixedFields

theorem bool_writeback : canonicalStructState mixedState mixedPlacement mixedEntries 3 mixedName (mstore mixedPhysical 896 0)=
    some ((Source.writeLoc mixedReadFrame 0 (.mem 3 0) (Source.Val.bool (D:=mixedLayout) false)).run mixedState) :=
  writeback mixedState mixedPlacement mixedEntries mixed_coverage mixedReadFrame 0 3 mixedName mixedFields boolFields
    mixedStructWords fields supported rfl ⟨0,by decide⟩ (.bool false) 0 (.scalar _ _ rfl) rfl mixedPhysical oldReads

theorem wrong_field_type :
    (Source.writeLoc mixedReadFrame 0 (.mem 3 0) (uintValueOfWord mixedLayout 0)).run mixedState=
      (.error (.stuck "field type"),mixedState) := rfl

theorem noncanonical_bool_preparation : canonicalStructState mixedState mixedPlacement mixedEntries 3 mixedName
    (mstore mixedPhysical 896 2)=none := rfl
def scalarFields := (mixedFields.setNth 1 (.val (uintValueOfWord mixedLayout 42))).toOption.getD mixedFields

theorem scalar_writeback : canonicalStructState mixedState mixedPlacement mixedEntries 3 mixedName (mstore mixedPhysical 928 42)=
    some ((Source.writeLoc mixedReadFrame 0 (.mem 3 1) (uintValueOfWord mixedLayout 42)).run mixedState) :=
  writeback mixedState mixedPlacement mixedEntries mixed_coverage mixedReadFrame 0 3 mixedName mixedFields scalarFields
    mixedStructWords fields supported rfl ⟨1,by decide⟩ (uintValueOfWord mixedLayout 42) 42
    (.scalar _ _ (uintValueOfWord_word _ _)) rfl mixedPhysical oldReads

theorem sibling_and_padding : (mload pointerPatch 960).val=1408 ∧
    (mload pointerPatch 992).val=128 ∧ pointerPatch 1443=0xa5 := by decide
end Solidity.Yul.Views.StructWordStore.Controls
