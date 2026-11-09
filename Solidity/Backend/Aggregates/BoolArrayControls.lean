import Solidity.Backend.Aggregates.BoolArrays
import Solidity.Backend.Aggregates.CalldataCopyControls

/-! Inhabited ABI-backed Source/intrinsic bool-array value/frame consumers.
The adapter's failure channel is Source.Halt, never a machine-step claim. -/
namespace Solidity.Backend.Aggregates.BoolArrayControls
open Solidity ByteParameterControls NestedCalldataControls BoolArrays

def goodData : Roadmap.Bytes := word 32 ++ word 2 ++ word 1 ++ word 0
def goodFrame : Source.Fr := {frame with cd := selector ++ goodData}
def values : List (Source.Val E.layout .bool) := [.bool true,.bool false]

theorem good_entry : Source.cdTail goodData 0 32 = .ok (68,2) := by
  have offset : Source.wordAt goodData 0 = 32 := by decide +kernel
  have count : Source.wordAt (goodData.drop 32) 0 = 2 := by decide +kernel
  have size : goodData.length = 128 := by decide +kernel
  simp only [Source.cdTail,offset,count,size]
  rfl

theorem first_word : Source.cdWordAt goodFrame 68 = 1 := by decide +kernel
theorem second_word : Source.cdWordAt goodFrame 100 = 0 := by decide +kernel

theorem validated : (List.range 2).mapM (fun j =>
    Source.decodeWord E.layout (Source.cdWordAt goodFrame (68+32*j)) .bool) = .ok values := by
  simp only [List.range_succ,List.range_zero,List.cons_append,List.nil_append,List.mapM_cons,List.mapM_nil]
  rw [show 68+32*0 = 68 from rfl,first_word,show 68+32*1 = 100 from rfl,second_word]
  rfl

def room : (values.map value).length < 2^256 :=
  capacity goodFrame selector goodData rfl rfl good_entry validated
def lowered := BoolArrays.lower aliasTarget values room

theorem phase_success : lowerCopy (E := E) aliasTarget goodFrame selector goodData rfl rfl good_entry =
    .ok lowered := lowerCopy_success aliasTarget goodFrame selector goodData rfl rfl good_entry validated

theorem related : Related ((Source.cdToMem goodFrame sourceTy 68 2).run sourceBefore).2.2.heap
    2 lowered.heap (aliasTarget.alloc (object aliasTarget.H values room)).2 :=
  copy_related goodFrame selector goodData rfl rfl good_entry sourceBefore aliasTarget validated

theorem ordered_contents : MObj.elems ArrTy.dyn (lowered.heap.get
    (aliasTarget.alloc (object aliasTarget.H values room)).2) = [true,false] :=
  target_contents aliasTarget values room

theorem joint_second :
    ((do let _ ← Source.cdToMem goodFrame sourceTy 68 2
         Source.readLoc goodFrame (.mem (τ := .bool) 2 1)) : Source.EM E caller _).run sourceBefore =
      (.ok (.bool false),((Source.cdToMem goodFrame sourceTy 68 2).run sourceBefore).2) ∧
    lowered.heap.readAddr (.index (aliasTarget.alloc (object aliasTarget.H values room)).2
      ArrTy.dyn (uintOfNat 1)) = some false := by
  obtain ⟨_,actual,read⟩ := copy_read_related goodFrame selector goodData rfl rfl good_entry
    sourceBefore aliasTarget validated ⟨1,by decide⟩
  exact ⟨actual,read⟩

theorem new_parameter : TEnv.get .here lowered.env =
    some (aliasTarget.alloc (object aliasTarget.H values room)).2 :=
  target_new_local aliasTarget values room

theorem protected_aliases : TEnv.get (.there .here) lowered.env =
    TEnv.get (.there (.there .here)) lowered.env := rfl

set_option backward.isDefEq.respectTransparency false in
theorem protected_object : MObj.elems ArrTy.dyn (lowered.heap.get
    (HRef.wk (List.prefix_append aliasTarget.H [boolR])
      ((State.init C).alloc oldObject).2)) = [170,187].map byteWord := by
  unfold lowered
  have kept := target_old_heap aliasTarget values room ((State.init C).alloc oldObject).2
  rw [kept]
  change MObj.elems ArrTy.dyn (MObj.wk _ bytesR
    (oldTarget.heap.get ((State.init C).alloc oldObject).2)) = _
  unfold oldTarget
  rw [State.allocPush_get]
  simp only [oldObject,bytesObj,wordsObj,MObj.wk,MObj.elems_dyn,List.map_map]
  rfl

theorem independent_ids : sourceBefore.2.heap.next ≠
    (aliasTarget.alloc (object aliasTarget.H values room)).2.id := by decide

theorem wrong_order : MObj.elems ArrTy.dyn (lowered.heap.get
    (aliasTarget.alloc (object aliasTarget.H values room)).2) ≠ [false,true] := by
  rw [ordered_contents]
  change ([true,false] : List Bool) ≠ [false,true]
  decide

def dirtyData : Roadmap.Bytes := word 32 ++ word 3 ++ word 1 ++ word 0 ++ word 2
def dirtyFrame : Source.Fr := {frame with cd := selector ++ dirtyData}

theorem dirty_entry : Source.cdTail dirtyData 0 32 = .ok (68,3) := by
  have offset : Source.wordAt dirtyData 0 = 32 := by decide +kernel
  have count : Source.wordAt (dirtyData.drop 32) 0 = 3 := by decide +kernel
  have size : dirtyData.length = 160 := by decide +kernel
  simp only [Source.cdTail,offset,count,size]
  rfl

theorem dirty_validation : (List.range 3).mapM (fun j =>
    Source.decodeWord E.layout (Source.cdWordAt dirtyFrame (68+32*j)) .bool) = .error (.revert []) := by
  have first : Source.cdWordAt dirtyFrame 68 = 1 := by decide +kernel
  have second : Source.cdWordAt dirtyFrame 100 = 0 := by decide +kernel
  have third : Source.cdWordAt dirtyFrame 132 = 2 := by decide +kernel
  simp only [List.range_succ,List.range_zero,List.cons_append,List.nil_append,List.mapM_cons,List.mapM_nil]
  rw [show 68+32*0 = 68 from rfl,first,show 68+32*1 = 100 from rfl,second,
    show 68+32*2 = 132 from rfl,third]
  rfl

theorem dirty_phase : lowerCopy (E := E) aliasTarget dirtyFrame selector dirtyData rfl rfl dirty_entry =
    .error (.revert []) :=
  lowerCopy_failure aliasTarget dirtyFrame selector dirtyData rfl rfl dirty_entry (.revert []) dirty_validation

theorem dirty_source : (Source.cdToMem dirtyFrame sourceTy 68 3).run sourceBefore =
    (.error (.revert []),sourceBefore) :=
  Source.cdToMem_array_failure dirtyFrame .bool 68 3 sourceBefore (.revert []) dirty_validation

def emptyData : Roadmap.Bytes := word 32 ++ word 0
def emptyFrame : Source.Fr := {frame with cd := selector ++ emptyData}

theorem empty_entry : Source.cdTail emptyData 0 32 = .ok (68,0) := by
  have offset : Source.wordAt emptyData 0 = 32 := by decide +kernel
  have count : Source.wordAt (emptyData.drop 32) 0 = 0 := by decide +kernel
  have size : emptyData.length = 64 := by decide +kernel
  simp only [Source.cdTail,offset,count,size]
  rfl

def emptyRoom : (([] : List (Source.Val E.layout .bool)).map value).length < 2^256 :=
  capacity emptyFrame selector emptyData rfl rfl empty_entry rfl

theorem empty_contents : MObj.elems ArrTy.dyn ((BoolArrays.lower aliasTarget [] emptyRoom).heap.get
    (aliasTarget.alloc (object aliasTarget.H [] emptyRoom)).2) = [] :=
  target_contents aliasTarget [] emptyRoom

theorem empty_phase : lowerCopy (E := E) aliasTarget emptyFrame selector emptyData rfl rfl empty_entry =
    .ok (BoolArrays.lower aliasTarget [] emptyRoom) :=
  lowerCopy_success aliasTarget emptyFrame selector emptyData rfl rfl empty_entry rfl

theorem good_not_refused (halt : Source.Halt) :
    lowerCopy (E := E) aliasTarget goodFrame selector goodData rfl rfl good_entry ≠ .error halt := by
  rw [phase_success]
  intro impossible
  cases impossible

theorem dirty_not_success : lowerCopy (E := E) aliasTarget dirtyFrame selector dirtyData rfl rfl dirty_entry ≠
    .ok lowered := by
  rw [dirty_phase]
  intro impossible
  cases impossible

theorem truncated_entry : Source.cdTail (dirtyData.take 128) 0 32 = .error (.revert []) := by
  have offset : Source.wordAt (dirtyData.take 128) 0 = 32 := by decide +kernel
  have count : Source.wordAt ((dirtyData.take 128).drop 32) 0 = 3 := by decide +kernel
  have size : (dirtyData.take 128).length = 128 := by decide +kernel
  simp only [Source.cdTail,offset,count,size]
  rfl

end Solidity.Backend.Aggregates.BoolArrayControls
