import Solidity.Backend.MemoryCopies.FixedReferenceLive
import Solidity.Evm.MemoryObjectArrayExamples

/-! Nonempty retained shadows change stored values without changing the live
copy. A real represented fixed-parent execution retains storage shadows and
allocates only live contents, with the original copied heap represented. -/
namespace Solidity.Backend.MemoryCopies.FixedReferenceLiveControls
open Evm Evm.Memory
private abbrev Leaf : RefTy := .array (.prim .uint)
private def child (live : List (Fin W)) (shadow : SList (.prim .uint)) (bounded : live.length < W) : SVal (.ref Leaf) :=
  .array (SVec.ofList (live.map (fun word => SVal.prim (indexValue word)))) shadow
    (by rw [List.length_map]; exact bounded)
private def retained71 : SList (.prim .uint) := .cons (.prim (indexValue (wmod 71))) .nil
private def retained83 : SList (.prim .uint) := .cons (.prim (indexValue (wmod 83))) .nil
private def stored (left right : SList (.prim .uint)) : SVal (.ref (.fixed (.ref Leaf) 2)) :=
  .fixed (.cons (child [wmod 11,wmod 23] left (by decide)) (.cons (child [] right (by decide)) .nil))
private def original : SVal (.ref (.fixed (.ref Leaf) 2)) := stored retained71 retained83
private def rows : List (PrimitiveStorageRow .uint) :=
  [⟨[indexValue (wmod 11),indexValue (wmod 23)],by decide⟩,⟨[],by decide⟩]
private theorem child_live (live : List (Fin W)) (shadow : SList (.prim .uint)) (bounded : live.length < W) :
    primitiveArrayLiveValues (child live shadow bounded) = live.map indexValue := by
  simp only [primitiveArrayLiveValues, child, SVal.view_array, SVec.toList_ofList, List.map_map, Function.comp_def, SVal.view_prim]

private theorem canonical_value : fixedReferenceLiveCanonical original = fixedReferenceStorageValue .uint rows := by
  apply congrArg SVal.fixed
  apply SVec.eq_of_toList_eq
  simp only [SVec.toList_ofLen, original, stored, SVal.view, SVec.toList_cons, SVec.toList_nil,
    List.map_cons, List.map_nil, fixedReferenceLiveChild, child_live, primitiveArrayValue,
    SVec.toList_ofList, nestedStorageValues, rows]
  with_unfolding_all rfl
private def firstShadow (value : SVal (.ref (.fixed (.ref Leaf) 2))) : Nat :=
  (value.view.toList[0]?.map (fun item => item.view.shadow.toList.length)).getD 0

theorem certificate_inhabited : FixedReferenceLiveCertificate original := fixedReferenceLive original

theorem all_values_inhabited {primitive : PrimTy} {count : Nat}
    (value : SVal (.ref (.fixed (.ref (.array (.prim primitive))) count))) : FixedReferenceLiveCertificate value :=
  fixedReferenceLive value

theorem all_shadows_same_copy {H : HTy} (heap : Heap H) (a b c d : SList (.prim .uint)) :
    (stored a b).copyStToM heap rfl = (stored c d).copyStToM heap rfl := by
  rw [fixed_reference_live_copy (stored a b) heap,fixed_reference_live_copy (stored c d) heap]
  simp only [fixedReferenceLiveCanonical, stored, SVal.view, SVec.toList_cons, SVec.toList_nil, SVec.ofLen, fixedReferenceLiveChild, primitiveArrayLiveValues, child, SVec.toList_ofList, List.map_cons, List.map_nil]

theorem stored_value_not_rewritten : firstShadow original = 1 ∧
    firstShadow (fixedReferenceLiveCanonical original) = 0 ∧ original ≠ fixedReferenceLiveCanonical original := by
  have zero : firstShadow (fixedReferenceLiveCanonical original) = 0 := by
    rw [canonical_value]
    simp only [firstShadow, fixedReferenceStorageValue, rows, nestedStorageValues, SVal.view, SVec.toList_cons, SVec.toList_nil, List.getElem?_cons_zero, Option.map_some, Option.getD_some, primitiveArrayValue, SList.toList_nil, List.length_nil]
  have one : firstShadow original = 1 := by
    simp only [firstShadow, original, stored, SVal.view, SVec.toList_cons, SVec.toList_nil, List.getElem?_cons_zero, Option.map_some, Option.getD_some, child, retained71, SList.toList_cons, SList.toList_nil, List.length_cons, List.length_nil]
  refine ⟨one,zero,?_⟩
  intro same
  have impossible : (1 : Nat) = 0 := one.symm.trans ((congrArg firstShadow same).trans zero)
  cases impossible

theorem exact_live_rows : fixedReferenceLiveRows original = rows := by
  simp only [fixedReferenceLiveRows, original, stored, SVal.view, SVec.toList_cons, SVec.toList_nil, List.map_cons, List.map_nil, fixedReferenceLiveRow, primitiveArrayLiveValues, child, SVec.toList_ofList]
  rfl

theorem zero_outer : FixedReferenceLiveCertificate (SVal.fixed (E := .ref Leaf) .nil) := fixedReferenceLive _

private def long : SVal (.ref (.fixed (.ref Leaf) 1)) :=
  .fixed (.cons (child (List.replicate 64 (wmod 11)) retained71 (by rw [List.length_replicate]; decide)) .nil)

theorem long_with_shadow : FixedReferenceLiveCertificate long := fixedReferenceLive long

private def many : SVal (.ref (.fixed (.ref Leaf) 64)) :=
  .fixed (SVec.replicate (child [] retained83 (by decide)) 64)

theorem many_empty_with_shadow : FixedReferenceLiveCertificate many := fixedReferenceLive many

private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def input : Input := ⟨_,_,_,_,ObjectArrayExamples.initial_allocator⟩
private def source : Slot := .data (.root 0) 0
private def store : WordStore := ⟨fun slot => match slot with
  | .data (.root 0) index => if index = 0 then wmod 2 else wmod 0
  | .data (.data (.root 0) index) offset =>
    if index = 0 then if offset = 0 then wmod 11 else if offset = 1 then wmod 23 else wmod 71
    else wmod 83
  | _ => wmod 0⟩
private def machine : Machine := {input.machine with store := store}
private theorem allocator : Objects.AllocatorRepr input.heap input.base 8 (wmod 40) machine := input.allocator.mem_eq rfl

private theorem left_repr : ReprAt machine.store 128 (.ref Leaf) source
    (child [wmod 11,wmod 23] retained71 (by decide)) := by
  refine .array rfl (by decide) ?_
  intro index value selected
  simp only [SVec.toList_ofList, List.map_cons, List.map_nil] at selected
  cases index with
  | zero => cases selected; exact .prim (ReprV.uint_of rfl)
  | succ index =>
    cases index with
    | zero => cases selected; exact .prim (ReprV.uint_of rfl)
    | succ index => cases selected

private theorem right_repr : ReprAt machine.store 128 (.ref Leaf) (source.add 1)
    (child [] retained83 (by decide)) := by
  refine .array rfl (by decide) ?_
  intro index value selected
  simp only [SVec.toList_ofList, List.map_nil, List.getElem?_nil] at selected
  cases selected

private theorem original_repr : ReprAt machine.store 128 (.ref (.fixed (.ref Leaf) 2)) source original := by
  refine .fixed ?_
  intro index value selected
  simp only [SVec.toList_cons, SVec.toList_nil] at selected
  cases index with
  | zero => cases selected; exact left_repr
  | succ index =>
    cases index with
    | zero => cases selected; exact right_repr
    | succ index => cases selected

private theorem original_copy : original.copyStToM input.heap rfl =
    (fixedReferenceStorageValue .uint rows).copyStToM input.heap rfl := by
  rw [fixed_reference_live_copy,canonical_value]

theorem actual_shadow_execution :
    let grown := original.copyStToM input.heap rfl
    ∃ (base : Nat → Fin W) (target : Machine),
      run (fixedReferenceStorageParentCode 2) (machine.push (.slot source)) = .ok (target.push w[40]) 0 ∧
      Objects.AllocatorRepr grown.heap base 8 (wmod 46) target ∧ base grown.val.id = wmod 40 ∧
      MVal.copyMToSt grown.heap grown.val = original.strip ∧
      target.mem 0 = w[46] ∧ target.mem 46 = w[0] ∧ target.mem 17 = w[7] ∧ target.stack = [w[77]] ∧
      target.store.cells (.data source 2) = wmod 71 ∧ target.store.cells (.data (source.add 1) 0) = wmod 83 := by
  have normalizedRepr : ReprAt machine.store 128 (.ref (.fixed (.ref Leaf) 2)) source
      (fixedReferenceStorageValue .uint rows) := by
    rw [← canonical_value]
    exact fixed_reference_live_representation original machine.store 128 source original_repr
  rcases fixed_reference_storage_parent_correct input.heap .uint rows input.base 8 (wmod 40) machine source 128
      allocator normalizedRepr with success | refusal
  · obtain ⟨fits,base,target,ran,allocated,root,extension,shape,below,gaps,keeps,fresh,length,contents,growth⟩ := success
    have representedOriginal : Objects.AllocatorRepr (original.copyStToM input.heap rfl).heap base 8 (wmod 46) target := by
      rw [original_copy]
      exact allocated
    have rootOriginal : base (original.copyStToM input.heap rfl).val.id = wmod 40 := by
      rw [original_copy]
      exact root
    have sameStore : target.store = machine.store := by simpa only [] using congrArg Machine.store shape
    refine ⟨base,target,ran,representedOriginal,rootOriginal,
      (storageHeapContents original rfl).contents input.heap,representedOriginal.free.cell,
      representedOriginal.free.zero 46 (by decide),(below 17 (by decide) (by decide)).trans rfl,?_,?_,?_⟩
    · rw [shape]
      rfl
    · rw [sameStore]
      rfl
    · rw [sameStore]
      rfl
  · have fits : (wmod 40).val + fixedReferenceStorageParentDemand rows < W := by decide
    exact (refusal.1 fits).elim

theorem wrong_shadow_as_live :
    firstShadow (fixedReferenceLiveCanonical original) ≠ 1 := by
  have zero : firstShadow (fixedReferenceLiveCanonical original) = 0 := stored_value_not_rewritten.2.1
  rw [zero]
  decide

/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceLiveControls.certificate_inhabited' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms certificate_inhabited
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceLiveControls.all_values_inhabited' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms all_values_inhabited
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceLiveControls.all_shadows_same_copy' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms all_shadows_same_copy
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceLiveControls.stored_value_not_rewritten' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms stored_value_not_rewritten
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceLiveControls.exact_live_rows' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms exact_live_rows
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceLiveControls.zero_outer' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms zero_outer
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceLiveControls.long_with_shadow' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms long_with_shadow
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceLiveControls.many_empty_with_shadow' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms many_empty_with_shadow
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceLiveControls.actual_shadow_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_shadow_execution
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceLiveControls.wrong_shadow_as_live' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms wrong_shadow_as_live
end Solidity.Backend.MemoryCopies.FixedReferenceLiveControls
