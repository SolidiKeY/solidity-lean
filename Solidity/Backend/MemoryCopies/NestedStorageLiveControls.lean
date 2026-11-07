import Solidity.Backend.MemoryCopies.NestedStorageLive
import Solidity.Evm.MemoryObjectArrayExamples

/-! Actual mixed dynamic copying retains arbitrary outer/child shadows in
storage, represents the original copied heap and preserves a populated old heap. -/
namespace Solidity.Backend.MemoryCopies.NestedStorageLiveControls
open Evm Evm.Memory
private abbrev Child : RefTy := .array (.prim .uint)
private abbrev Parent : RefTy := .array (.ref Child)
private def retained : SList (.prim .uint) := .cons (.prim (indexValue (wmod 83))) .nil
private def child (payloads : List (Fin W)) (bounded : payloads.length < W) : SVal (.ref Child) :=
  .array (SVec.ofList (payloads.map (fun word => .prim (indexValue word)))) retained (by rw [List.length_map]; exact bounded)
private def outerShadow : SList (.ref Child) := .cons (child [] (by decide)) .nil
private def original : SVal (.ref Parent) :=
  .array (.cons (child [wmod 11,wmod 23] (by decide)) (.cons (child [] (by decide)) .nil)) outerShadow (by decide)
private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def input : Input := ⟨_,_,_,_,ObjectArrayExamples.initial_allocator⟩
private def source : Slot := .root 0
private def store : WordStore := ⟨fun slot => match slot with
  | .root 0 => wmod 2
  | .data (.root 0) index => if index = 0 then wmod 2 else if index = 1 then wmod 0 else wmod 99
  | .data (.data (.root 0) index) offset =>
    if index = 0 then if offset = 0 then wmod 11 else if offset = 1 then wmod 23 else wmod 83 else wmod 83
  | _ => wmod 0⟩
private def machine : Machine := {input.machine with store := store}
private theorem allocator : Objects.AllocatorRepr input.heap input.base 8 (wmod 40) machine := input.allocator.mem_eq rfl

private theorem left_repr : ReprAt machine.store 128 (.ref Child) (.data source 0) (child [wmod 11,wmod 23] (by decide)) := by
  refine .array rfl (by decide) ?_
  intro index item selected
  simp only [SVec.toList_ofList,List.map_cons,List.map_nil] at selected
  cases index with
  | zero => cases selected; exact .prim (ReprV.uint_of rfl)
  | succ index => cases index with
    | zero => cases selected; exact .prim (ReprV.uint_of rfl)
    | succ index => cases selected
private theorem right_repr : ReprAt machine.store 128 (.ref Child) (.data source 1) (child [] (by decide)) := by
  refine .array rfl (by decide) ?_
  intro index item selected
  simp only [SVec.toList_ofList,List.map_nil,List.getElem?_nil] at selected
  cases selected
private theorem represented : ReprAt machine.store 128 (.ref Parent) source original := by
  refine .array rfl (by decide) ?_
  intro index item selected
  simp only [SVec.toList_cons,SVec.toList_nil] at selected
  cases index with
  | zero => cases selected; exact left_repr
  | succ index => cases index with
    | zero => cases selected; exact right_repr
    | succ index => cases selected
private theorem row_length : (nestedStorageLiveRows original).length = 2 := by
  simp only [nestedStorageLiveRows,original,SVal.view_array,List.length_map,SVec.length_toList]

private theorem demand : nestedStorageParentDemand (nestedStorageLiveRows original) = 7 := by with_unfolding_all rfl

theorem certificate_inhabited : NestedStorageLiveCertificate := nestedStorageLive

theorem arbitrary_values {primitive : PrimTy} (value : SVal (.ref (.array (.ref (.array (.prim primitive))))))
    {H : HTy} (heap : Heap H) :
    value.copyStToM heap rfl = (nestedStorageLiveCanonical value).copyStToM heap rfl := nested_storage_live_copy value heap

theorem shadow_counts : original.view.shadow.toList.length = 1 ∧
    (nestedStorageLiveCanonical original).view.shadow.toList.length = 0 := by
  constructor
  · simp only [original,SVal.view_array,outerShadow,SList.toList_cons,SList.toList_nil,List.length_cons,List.length_nil]
  · simp only [nestedStorageLiveCanonical,original,SVal.view_array,SList.toList_nil,List.length_nil]

theorem actual_copy :
    let grown := original.copyStToM input.heap rfl
    ∃ base target,
      run nestedStorageHeaderCode (machine.push (.slot source)) = .ok (target.push w[40]) 0 ∧
      Objects.AllocatorRepr grown.heap base 8 (wmod 47) target ∧ base grown.val.id = wmod 40 ∧
      grown.heap.len grown.val .dyn = 2 ∧ Heap.Keeps grown.ext input.heap grown.heap ∧
      MVal.copyMToSt grown.heap grown.val = original.strip ∧
      target.mem 0 = w[47] ∧ target.mem 47 = w[0] ∧ target.mem 17 = w[7] ∧ target.stack = [w[77]] ∧
      target.store.cells (.data source 2) = wmod 99 ∧ target.store.cells (.data (.data source 0) 2) = wmod 83 := by
  rcases nested_storage_live_correct input.heap original input.base 8 (wmod 40) machine source 128 allocator represented with success | refusal
  · obtain ⟨fits,base,target,ran,allocated,root,extension,shape,below,gaps,keeps,fresh,length,contents⟩ := success
    have actual : Objects.AllocatorRepr (original.copyStToM input.heap rfl).heap base 8 (wmod 47) target := by
      simpa only [demand] using allocated
    refine ⟨base,target,ran,actual,root,length.trans row_length,keeps,contents,actual.free.cell,actual.free.zero 47 (by decide),
      (below 17 (by decide) (by decide)).trans rfl,?_,?_,?_⟩
    · rw [shape]; rfl
    · rw [shape]; rfl
    · rw [shape]; rfl
  · have fits : (wmod 40).val + nestedStorageParentDemand (nestedStorageLiveRows original) < W := by rw [demand]; decide
    exact (refusal.1 fits).elim

private def saturated : Fin W := ⟨W-1,by have positive : 0 < W := W_pos; omega⟩
private def late : Machine := writeMachine machine 0 (.val saturated)
private theorem late_allocator : Objects.AllocatorRepr input.heap input.base 8 saturated late := by
  refine ⟨allocator.heap.localWrite 0 (by decide) (.val saturated),⟨by decide,by with_unfolding_all decide,rfl,?_⟩,?_⟩
  · intro address above
    have lower : 40 ≤ address := Nat.le_trans (by with_unfolding_all decide : 40 ≤ saturated.val) above
    change upd machine.mem 0 (.val saturated) address = w[0]
    rw [upd_other _ _ (show address ≠ 0 by omega)]
    exact allocator.free.zero address lower
  · intro R reference
    exact Nat.le_trans (allocator.live reference) (by with_unfolding_all decide)

theorem size_refusal : run nestedStorageHeaderCode (late.push (.slot source)) = .revert := by
  rcases nested_storage_live_correct input.heap original input.base 8 saturated late source 128 late_allocator represented with success | refusal
  · obtain ⟨fits,_⟩ := success
    rw [demand] at fits
    have impossible : ¬ saturated.val + 7 < W := by with_unfolding_all decide
    exact (impossible fits).elim
  · exact refusal.2

private def many : SVal (.ref Parent) := .array (SVec.replicate (child [] (by decide)) 64) outerShadow (by decide)
private def manyStore : WordStore := ⟨fun slot => match slot with | .root 0 => wmod 64 | _ => wmod 0⟩
private def manyMachine : Machine := {input.machine with store := manyStore}
private theorem many_repr : ReprAt manyMachine.store 128 (.ref Parent) source many := by
  refine .array rfl (by decide) ?_
  intro index item selected
  simp only [SVec.toList_replicate] at selected
  have selectedChild : item = child [] (by decide) := (List.mem_replicate.mp (List.mem_of_getElem? selected)).2
  subst item
  refine .array ?_ (by decide) ?_
  · cases index <;> rfl
  · intro offset word chosen
    simp only [SVec.toList_ofList,List.map_nil,List.getElem?_nil] at chosen
    cases chosen

theorem many_empty_children_success : ∃ fits, NestedStorageLiveResult input.heap many input.base 8 (wmod 40) manyMachine source fits := by
  rcases nested_storage_live_correct input.heap many input.base 8 (wmod 40) manyMachine source 128
      (input.allocator.mem_eq rfl) many_repr with success | refusal
  · exact success
  · have fits : (wmod 40).val + nestedStorageParentDemand (nestedStorageLiveRows many) < W := by with_unfolding_all decide
    exact (refusal.1 fits).elim

theorem wrong_shallow_demand : nestedStorageParentDemand (nestedStorageLiveRows original) ≠ 3 := by rw [demand]; decide

/--
info: 'Solidity.Backend.MemoryCopies.NestedStorageLiveControls.certificate_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms certificate_inhabited
/--
info: 'Solidity.Backend.MemoryCopies.NestedStorageLiveControls.arbitrary_values' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms arbitrary_values
/--
info: 'Solidity.Backend.MemoryCopies.NestedStorageLiveControls.shadow_counts' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms shadow_counts
/--
info: 'Solidity.Backend.MemoryCopies.NestedStorageLiveControls.actual_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_copy
/--
info: 'Solidity.Backend.MemoryCopies.NestedStorageLiveControls.size_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms size_refusal
/--
info: 'Solidity.Backend.MemoryCopies.NestedStorageLiveControls.many_empty_children_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms many_empty_children_success
/--
info: 'Solidity.Backend.MemoryCopies.NestedStorageLiveControls.wrong_shallow_demand' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms wrong_shallow_demand
end Solidity.Backend.MemoryCopies.NestedStorageLiveControls
