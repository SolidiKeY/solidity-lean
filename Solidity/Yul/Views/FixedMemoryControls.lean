import Solidity.Yul.Views.FixedMemory
import Solidity.Yul.Views.NominalMemoryControls
import Solidity.Yul.Views.ComputedPlacement
import Solidity.Yul.Views.ScalarControls

/-! Scaled fixed-point words use full sign extension, with actual allocated
arrays and two aliases. Existing inventory dispatch is deliberately unchanged;
this standalone adapter does not claim whole-heap support or compiler adequacy. -/
namespace Solidity.Yul.Views.FixedMemory.Controls
open Solidity.Yul.Views

def env := NominalMemory.Controls.env
def f := Solidity.Yul.Views.Controls.scaled16
def inspect (w : Roadmap.Word) : Option Roadmap.Word := (decode env.layout f w).bind Source.Val.word

theorem negative_scaled : inspect (Source.intWord (-125))=some (Source.intWord (-125)) := by
  unfold inspect
  rw [decode_encode env.layout f (.fixed (-125) (by decide)) (Source.intWord (-125)) rfl]
  rfl

theorem minimum_scaled : inspect (Source.intWord (-32768))=some (Source.intWord (-32768)) := by
  unfold inspect
  rw [decode_encode env.layout f (.fixed (-32768) (by decide)) (Source.intWord (-32768)) rfl]
  rfl

theorem unsigned_payload_is_wrong : inspect 65411=none := by decide

theorem above_range : inspect 32768=none := by decide

theorem old_dispatch_still_explicit : decodeCanonicalScalar env.layout (.fixed f) 1=none := rfl

def ty : Source.STy := .array .memory (.fixed f) (some 2)
def lengthOK : ∀ z,(some 2:Option Nat)=some z → z=2 := fun _ h=>(Option.some.inj h).symm
def values : Fin 2 → Source.Val env.layout (.fixed f) :=
  fun i=>.fixed (if i.val=0 then -125 else 32767) (by split <;> decide)
def data : Source.Data env.layout ty := memberArrayData env.layout (.fixed f) (some 2) 2 lengthOK values
def heap : Source.Heap env.layout := (Source.Heap.empty.alloc ⟨ty,data⟩).1
def placement : Placement heap := ComputedPlacement.build heap (by decide) (by decide)
def state : Source.EMState env [ty,ty] :=
  (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil),{NominalMemory.Controls.state.2 with heap:=heap})
def raw : ByteView := mstore (mstore (fun _=>165) (placement.address 0) (Source.intWord (-125)))
  (placement.address 0+32) 32767

theorem two_word_reads (m : ByteView) (base : Nat) (first second : Roadmap.Word) (i : Fin 2) :
    mload (mstore (mstore m base first) (base+32) second) (base+i.val*32)=
      (if i.val=0 then first else second) := by
  first | (simp only;done) | decide | omega | rfl | skip
  by_cases zero : i.val=0
  · simp only [zero,Nat.zero_mul,Nat.add_zero,if_true]
    have same := mload_congr (mstore (mstore m base first) (base+32) second) (mstore m base first) base
      (fun j=>mstore_outside _ _ _ _ (by have bound:=j.isLt; omega))
    exact same.trans (mload_mstore m base first)
  · have one : i.val=1 := by have bound:=i.isLt; omega
    simp only [one,Nat.one_mul]
    exact mload_mstore _ _ _

theorem encoded : ∀ i,(values i).word=some (mload raw (placement.address 0+i.val*32)) := by
  intro i
  rw [show mload raw (placement.address 0+i.val*32)=
      (if i.val=0 then Source.intWord (-125) else 32767) from two_word_reads _ _ _ _ i]
  by_cases zero : i.val=0 <;> simp only [values,zero,if_true,if_false,Source.Val.word] <;> rfl

theorem actual_unchanged : arrayState state placement 0 f (some 2) 2 lengthOK raw=some (.ok (),state) :=
  arrayState_unchanged state placement 0 f (some 2) 2 lengthOK values rfl raw rfl encoded

theorem two_aliases : state.1.get .here=state.1.get (.there .here) := rfl

def changedValues : Fin 2 → Source.Val env.layout (.fixed f) :=
  fun i=>.fixed (if i.val=0 then -32768 else 0) (by split <;> decide)
def changedData : Source.Data env.layout ty := memberArrayData env.layout (.fixed f) (some 2) 2 lengthOK changedValues
def changedRaw : ByteView := mstore (mstore raw (placement.address 0) (Source.intWord (-32768))) (placement.address 0+32) 0

theorem changed_encoded : ∀ i,(changedValues i).word=some (mload changedRaw (placement.address 0+i.val*32)) := by
  intro i
  rw [show mload changedRaw (placement.address 0+i.val*32)=
      (if i.val=0 then Source.intWord (-32768) else 0) from two_word_reads _ _ _ _ i]
  by_cases zero : i.val=0 <;> simp only [changedValues,zero,if_true,if_false,Source.Val.word] <;> rfl

theorem actual_changed : arrayState state placement 0 f (some 2) 2 lengthOK changedRaw=
    some (.ok (),withSourceHeap state (heap.write 0 changedData (heap_ty_of_get heap 0 _ data rfl))) := by
  -- Direct automation exceeded the retained recursion limit; use the inverse.
  unfold arrayState
  simp only [arrayLengthChoice,Option.getD_some,BEq.rfl,if_true,arrayPayloadOffset,Option.isNone_some,Bool.false_eq_true,if_false,Nat.add_zero]
  rw [array_decode_encode env.layout f 2 changedRaw _ changedValues changed_encoded]
  simp only [Option.map_some]
  rw [memberArrayHeapPut_run state 0 (.fixed f) (some 2) 2 lengthOK changedValues (heap_ty_of_get heap 0 _ data rfl)]
  rfl

theorem retained_padding : changedRaw (placement.address 0+80)=165 := by decide
theorem actual_MemOK : Source.MemOK env heap.ty state := by
  refine ⟨⟨⟨?_,Solidity.Source.HeapTy.Le.refl _⟩,?_⟩,?_,?_⟩
  · apply Solidity.Source.HeapOK.alloc Solidity.Source.HeapOK.empty
    exact .array (fun i => .val (by trivial))
  · exact ⟨⟨Solidity.Yul.Views.FixedMemory.Controls.ty,rfl,rfl⟩,⟨⟨Solidity.Yul.Views.FixedMemory.Controls.ty,rfl,rfl⟩,trivial⟩⟩
  · apply Solidity.Source.HeapShaped.alloc Solidity.Source.HeapShaped.empty
    trivial
  · apply Solidity.Source.HeapInner.alloc (fun a x found => by cases found)
    exact fun i => ⟨Solidity.Yul.Views.FixedMemory.Controls.values i,rfl⟩

theorem changed_MemOK : Source.MemOK env heap.ty
    (withSourceHeap state (heap.write 0 changedData (heap_ty_of_get heap 0 _ data rfl))) :=
  arrayState_MemOK env heap.ty state placement 0 f (some 2) 2 lengthOK changedRaw _ actual_changed actual_MemOK

def oneLength : ∀ z,(some 1:Option Nat)=some z → z=1 := fun _ h=>(Option.some.inj h).symm
def oneValue : Fin 1 → Source.Val env.layout (.fixed f) := fun _=>.fixed (-125) (by decide)

theorem one_encoded : ∀ i,(oneValue i).word=some (mload raw (placement.address 0+i.val*32)) := by
  intro i
  have zero : i.val=0 := by have bound:=i.isLt; omega
  have first := encoded 0
  simpa only [oneValue,values,Fin.val_zero,if_true,zero] using first

theorem actual_type_error : arrayState state placement 0 f (some 1) 1 oneLength raw=
    some (.error (.stuck "memory write type"),state) := by
  unfold arrayState
  simp only [arrayLengthChoice,Option.getD_some,BEq.rfl,if_true,arrayPayloadOffset,Option.isNone_some,Bool.false_eq_true,if_false,Nat.add_zero]
  rw [array_decode_encode env.layout f 1 raw _ oneValue one_encoded]
  rfl

theorem dirty_preparation : (arrayState state placement 0 f (some 2) 2 lengthOK
    (mstore raw (placement.address 0) 65411)).isNone=true := by decide
end Solidity.Yul.Views.FixedMemory.Controls
