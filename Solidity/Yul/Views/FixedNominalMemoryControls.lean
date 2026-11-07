import Solidity.Yul.Views.FixedNominalMemory
import Solidity.Yul.Views.FixedMemoryControls

/-! A declared signed fixed16x2 UDVT uses scaled Source values and exact full
word sign extension. Actual two-alias array writes and dirty/missing-declaration
negatives distinguish this adapter from existing partial canonical dispatch. -/
namespace Solidity.Yul.Views.FixedNominalMemory.Controls
open Solidity.Yul.Views

def name : Source.DeclName := ⟨none,"Scaled"⟩
def missing : Source.DeclName := ⟨none,"Missing"⟩
def env : Source.Env := ⟨[⟨.udvt,"Scaled",none,true,
  .udvt "Scaled" (.fixed true (some ⟨16,2,by decide⟩))⟩]⟩
def f : Source.FixTy := Solidity.Yul.Views.Controls.scaled16

theorem actual_underlying : env.layout.underlying name=.fixed f := rfl

def inspect (w : Roadmap.Word) := (decodeDeclared env name w).bind Source.Val.word

theorem negative_scaled : inspect (Source.intWord (-125))=some (Source.intWord (-125)) := by
  unfold inspect decodeDeclared
  rw [show NominalMemory.declaredUDVT env name=true from rfl]
  rw [if_pos rfl,decode_encode env.layout name (by trivial)
    (Source.Val.udvt (.fixed (-125) (by decide))) (Source.intWord (-125)) rfl]
  rfl

theorem dirty_rejected : inspect 65411=none := by decide

theorem missing_declaration : decodeDeclared env missing 0=none := rfl

theorem old_decoder_gap : NominalMemory.decodeDeclared env name (Source.intWord (-125))=none := rfl

def ty : Source.STy := .array .memory (.udvt name) (some 2)
def values : Fin 2 → Source.Val env.layout (.udvt name) :=
  fun i=>.udvt (.fixed (if i.val=0 then -125 else 32767) (by split <;> decide))
def newValues : Fin 2 → Source.Val env.layout (.udvt name) :=
  fun i=>.udvt (.fixed (if i.val=0 then -32768 else 0) (by split <;> decide))
def data := memberArrayData env.layout (.udvt name) (some 2) 2 FixedMemory.Controls.lengthOK values
def newData := memberArrayData env.layout (.udvt name) (some 2) 2 FixedMemory.Controls.lengthOK newValues
def heap : Source.Heap env.layout := (Source.Heap.empty.alloc ⟨ty,data⟩).1
def placement : Placement heap := ComputedPlacement.build heap (by decide) (by decide)
def state : Source.EMState env [ty,ty] :=
  (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil),
    { ex:=⟨⟨fun _=>Source.Account.empty _⟩,.empty,[]⟩,heap:=heap,events:=[],logs:=[],fnLocals:=⟨[],.nil⟩ })
def raw : ByteView := mstore (mstore (fun _=>165) (placement.address 0) (Source.intWord (-125)))
  (placement.address 0+32) 32767
def changed : ByteView := mstore (mstore raw (placement.address 0) (Source.intWord (-32768)))
  (placement.address 0+32) 0

theorem changed_encoded (i : Fin 2) : (newValues i).word=some (mload changed (placement.address 0+i.val*32)) := by
  rw [show mload changed (placement.address 0+i.val*32)=
    if i.val=0 then Source.intWord (-32768) else 0 from FixedMemory.Controls.two_word_reads _ _ _ _ i]
  by_cases zero : i.val=0 <;> simp only [newValues,Source.Val.word,zero,if_true,if_false] <;> rfl

def expected := withSourceHeap state (heap.write 0 newData (heap_ty_of_get heap 0 _ data rfl))

theorem changed_source : arrayState state placement 0 name (some 2) 2 FixedMemory.Controls.lengthOK changed=
    some (.ok (),expected) := by
  unfold arrayState
  simp only [show NominalMemory.declaredUDVT env name=true from rfl,arrayLengthChoice,Option.getD_some,
    BEq.rfl,Bool.and_self,ite_true,arrayPayloadOffset,Option.isNone_some,Bool.false_eq_true,ite_false,Nat.add_zero]
  rw [array_decode_encode env.layout name (by trivial) 2 changed _ newValues changed_encoded]
  rw [Option.map_some,memberArrayHeapPut_run state 0 (.udvt name) (some 2) 2
    FixedMemory.Controls.lengthOK newValues (by rfl)]
  rfl

theorem both_aliases :
    ((do let loc ← Source.indexLoc NominalMemory.Controls.readFrame (expected.1.get .here) 0
         Source.readLoc NominalMemory.Controls.readFrame loc) :
      Source.EM env [ty,ty] (Source.Val env.layout (.udvt name))).run expected=(.ok (newValues 0),expected) ∧
    ((do let loc ← Source.indexLoc NominalMemory.Controls.readFrame (expected.1.get (.there .here)) 0
         Source.readLoc NominalMemory.Controls.readFrame loc) :
      Source.EM env [ty,ty] (Source.Val env.layout (.udvt name))).run expected=(.ok (newValues 0),expected) := by
  first | solve | rfl
        | exact ⟨rfl,rfl⟩

theorem missing_root_error : arrayState state placement 1 name (some 2) 2 FixedMemory.Controls.lengthOK
    (mstore (mstore (fun _=>0) (placement.address 1) 0) (placement.address 1+32) 0)=
    some (.error (.stuck "memory write type"),state) := by
  first | solve | rfl
        | solve | simp only [arrayState]

end Solidity.Yul.Views.FixedNominalMemory.Controls
