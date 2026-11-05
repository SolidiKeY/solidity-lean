import Solidity.Yul.Views.MemoryDelete
import Solidity.Yul.Views.ByteElementStoreControls

/-! Actual deletion witnesses scalar fields, array elements and bytes. Failure
controls retain timeout/type/index distinctions. A reference deletion really
allocates and is deliberately not relabelled as a scalar-default preparation. -/
namespace Solidity.Yul.Views.MemoryDelete.Controls
open Solidity.Yul.Views.Controls
open ArrayWordStore

def arrayValues := replace mixedStaticVals ⟨1,by decide⟩ (uintValueOfWord mixedLayout 0)
def arrayAfter := withSourceHeap mixedState (mixedHeap.write 2
  (memberArrayData mixedLayout (.int Source.IntTy.u256) (some 2) 2 (fun _ eq => (Option.some.inj eq).symm) arrayValues) (by rfl))
def arrayPlacement := memberArrayWrittenPlacement mixedHeap mixedPlacement 2 (.int Source.IntTy.u256) (some 2) 2
  (fun _ eq => (Option.some.inj eq).symm) mixedStaticVals arrayValues rfl
def arrayHistory := ArrayWordRetained.history mixedHeap mixedPlacement mixedPlacement (retainInitial _ _) 2
  (.int Source.IntTy.u256) (some 2) 2 (fun _ eq => (Option.some.inj eq).symm) mixedStaticVals arrayValues rfl

theorem array_whole :
    (Source.deleteLoc mixedReadFrame 1 (.mem (τ:=.int Source.IntTy.u256) 2 1)).run mixedState=(.ok (),arrayAfter) ∧
    RetainedAllocation mixedPlacement arrayPlacement ∧
    encodeMixedHeap arrayPlacement (generatedHeapEntries arrayPlacement) (mstore mixedPhysical 672 0)=mstore mixedPhysical 672 0 ∧
    enumeratedMemoryWriteback arrayAfter mixedPlacement arrayPlacement arrayHistory (mstore mixedPhysical 672 0)=
      .ok (some (.ok (),arrayAfter)) :=
  array mixedHeap.ty mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixed_actual_MemOK
    StructWordHeap.Controls.support mixedReadFrame 0 2 (.int Source.IntTy.u256) (some 2) 2
    (fun _ eq => (Option.some.inj eq).symm) mixedStaticVals (fun i => if i.val=0 then 7 else 9)
    mixed_static_element rfl ⟨1,by decide⟩ (uintValueOfWord mixedLayout 0) 0 (.scalar _ _ (uintValueOfWord_word _ _))
    rfl mixedPhysical ByteElementStore.Controls.oldReads mixed_reserved

def boolAfter := withSourceHeap mixedState (mixedHeap.write 3 (.struct StructWordStore.Controls.boolFields) (by rfl))
def boolPlacement := structWrittenPlacement mixedHeap mixedPlacement 3 mixedName mixedFields StructWordStore.Controls.boolFields rfl
def boolHistory := StructWordRetained.history mixedHeap mixedPlacement mixedPlacement (retainInitial _ _) 3 mixedName
  mixedFields StructWordStore.Controls.boolFields rfl

theorem bool_whole :
    (Source.deleteLoc mixedReadFrame 1 (.mem (τ:=.bool) 3 0)).run mixedState=(.ok (),boolAfter) ∧
    RetainedAllocation mixedPlacement boolPlacement ∧
    encodeMixedHeap boolPlacement (generatedHeapEntries boolPlacement) (mstore mixedPhysical 896 0)=mstore mixedPhysical 896 0 ∧
    enumeratedMemoryWriteback boolAfter mixedPlacement boolPlacement boolHistory (mstore mixedPhysical 896 0)=
      .ok (some (.ok (),boolAfter)) :=
  strct mixedHeap.ty mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixed_actual_MemOK
    StructWordHeap.Controls.support mixedReadFrame 0 3 mixedName mixedFields StructWordStore.Controls.boolFields
    mixedStructWords StructWordStore.Controls.fields rfl ⟨0,by decide⟩ (.bool false) 0 (.scalar _ _ rfl) rfl rfl
    mixedPhysical ByteElementStore.Controls.oldReads mixed_reserved

def byteAfter := withSourceHeap mixedState (mixedHeap.write 0 (.bytes (mixedChild.set 1 0)) (by rfl))
def bytePlacement := ByteElementStore.placement mixedHeap mixedPlacement 0 false mixedChild rfl ⟨1,by decide⟩ 0

theorem byte_whole :
    (Source.deleteLoc mixedReadFrame 1 (.memByte 0 1)).run mixedState=(.ok (),byteAfter) ∧
    Source.MemOK mixedEnv mixedHeap.ty byteAfter ∧
    encodeMixedHeap bytePlacement (generatedHeapEntries bytePlacement) (saveByte mixedPhysical 161 0)=saveByte mixedPhysical 161 0 ∧
    ∃ history : RetainedAllocation mixedPlacement bytePlacement,
      enumeratedMemoryWriteback byteAfter mixedPlacement bytePlacement history (saveByte mixedPhysical 161 0)=
        .ok (some (.ok (),byteAfter)) ∧ ReservedOK (saveByte mixedPhysical 161 0) bytePlacement.free :=
  bytes mixedHeap.ty mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixed_actual_MemOK
    StructWordHeap.Controls.support mixedReadFrame 0 0 false mixedChild rfl ⟨1,by decide⟩ mixedPhysical
    ByteElementStore.Controls.oldReads mixed_reserved

theorem integer_default (t : Source.IntTy) {E Γ} (s : Source.EMState E Γ) (n : Nat) :
    (Source.zeroVal (n+1) (.int t)).run s=(.ok (.int 0 t.zero_mem),s) := rfl

theorem exact_reads_and_padding :
    (Source.readLoc (E:=mixedEnv) mixedReadFrame (.mem (τ:=.int Source.IntTy.u256) 2 0)).run arrayAfter=(.ok mixedSeven,arrayAfter) ∧
    (Source.readLoc (E:=mixedEnv) mixedReadFrame (.mem (τ:=.int Source.IntTy.u256) 2 1)).run arrayAfter=
      (.ok (uintValueOfWord mixedLayout 0),arrayAfter) ∧
    (Source.readLoc (E:=mixedEnv) mixedReadFrame (.mem (τ:=.bytes .memory) 3 2)).run boolAfter=(.ok (.memRef rfl 0),boolAfter) ∧
    (saveByte mixedPhysical 161 0) 162=0x33 ∧ (saveByte mixedPhysical 161 0) 163=0xa5 :=
  ⟨rfl,rfl,rfl,by decide,by decide⟩

theorem horizon_zero : (Source.deleteLoc mixedReadFrame 0 (.mem (τ:=.bool) 3 0)).run mixedState=
    (.error .timeout,mixedState) := rfl

theorem wrong_type : (Source.deleteLoc mixedReadFrame 1 (.mem (τ:=.int Source.IntTy.u256) 3 0)).run mixedState=
    (.error (.stuck "field type"),mixedState) := rfl

theorem out_of_bounds : (Source.deleteLoc mixedReadFrame 1 (.memByte 0 3)).run mixedState=
    (.error (.revert (Source.panicData .index)),mixedState) := rfl

def refFields := (mixedFields.setNth 2 (.val (Source.Val.memRef (τ:=.bytes .memory) rfl 6))).toOption.getD mixedFields
def allocated := objectAllocatedState mixedState (Source.Data.bytes (l:=.memory) [])
def referenceAfter := withSourceHeap allocated (allocated.2.heap.write 3 (.struct refFields) (by rfl))

theorem reference_delete_allocates :
    Source.Val.default mixedLayout (.bytes .memory)=none ∧
    (Source.deleteLoc mixedReadFrame 2 (.mem (τ:=.bytes .memory) 3 2)).run mixedState=(.ok (),referenceAfter) ∧
    referenceAfter.2.heap.next=7 ∧ referenceAfter.2.heap.get 6=some ⟨.bytes .memory,.bytes []⟩ ∧
    referenceAfter.2.heap.get 0=mixedHeap.get 0 := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem erased_default_negative : mload (mstore mixedPhysical 896 0) 896≠mload mixedPhysical 896 := by decide
end Solidity.Yul.Views.MemoryDelete.Controls
