import Solidity.Backend.MemoryCopies.NestedLivePipeline
import Solidity.Evm.MemoryObjectArrayExamples

/-! Original outer/child shadows survive storage while two checked copies
allocate separate roots. Actual first and later capacity refusals stay distinct. -/
namespace Solidity.Backend.MemoryCopies.NestedLivePipelineControls
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


private def observe (outcome : Evm.Out) : Option Evm.Word :=
  match outcome with | .ok target _ => some (target.mem 0) | _ => none

private theorem successful : ∃ fits, NestedLivePipelineResult input.heap original input.base 8 (wmod 40) machine source fits := by
  rcases nested_live_pipeline_correct input.heap original input.base 8 (wmod 40) machine source 128 allocator represented with success | refusal
  · exact success
  · rcases refusal.1 with ⟨tooLarge,_⟩ | ⟨firstFits,base,intermediate,firstRun,firstAllocator,firstRoot,contents,tooLarge,secondRun⟩
    · have fits : (wmod 40).val + nestedStorageParentDemand (nestedStorageLiveRows original) < W := by rw [demand]; decide
      exact (tooLarge fits).elim
    · have fits : (wmod 40).val + 2 * nestedStorageParentDemand (nestedStorageLiveRows original) < W := by rw [demand]; decide
      exact (tooLarge fits).elim

theorem mixed_shadows_reach_two_fresh_copies :
    let first := original.copyStToM input.heap rfl
    let second := (MVal.copyMToSt first.heap first.val).copyStToM first.heap rfl
    ∃ base target,
      run (nestedLocationPipelineCode .uint) (machine.push (.slot source)) = .ok (target.push w[47]) 0 ∧
      Objects.AllocatorRepr second.heap base 8 (wmod 54) target ∧
      base second.val.id = wmod 47 ∧ base (first.val.wk second.ext).id = wmod 40 ∧
      first.val.id < second.val.id ∧ second.heap.len second.val .dyn = 2 ∧
      MVal.copyMToSt second.heap (first.val.wk second.ext) = original.strip ∧
      MVal.copyMToSt second.heap second.val = (MVal.copyMToSt first.heap first.val).strip ∧
      target.mem 17 = w[7] ∧ target.store.cells (.data source 2) = wmod 99 ∧
      target.store.cells (.data (.data source 0) 2) = wmod 83 := by
  obtain ⟨fits,firstFits,base₁,intermediate,secondFits,base₂,target,firstRun,firstAllocator,firstRoot,secondRun,ran,allocated,secondRoot,retainedRoot,extension,shape,below,middleBelow,gaps,keeps,firstKeeps,fresh,length,retained,contents⟩ := successful
  have actual : Objects.AllocatorRepr
      ((MVal.copyMToSt (original.copyStToM input.heap rfl).heap (original.copyStToM input.heap rfl).val).copyStToM (original.copyStToM input.heap rfl).heap rfl).heap
      base₂ 8 (wmod 54) target := by simpa only [demand] using allocated
  refine ⟨base₂,target,?_,actual,?_,retainedRoot,fresh,length.trans row_length,retained,contents,
    (below 17 (by decide) (by decide)).trans rfl,?_,?_⟩
  · simpa only [demand] using ran
  · simpa only [demand] using secondRoot
  · rw [shape]; rfl
  · rw [shape]; rfl

theorem final_cursor_observation : observe (run (nestedLocationPipelineCode .uint) (machine.push (.slot source))) = some w[54] := by
  obtain ⟨base,target,ran,allocated,_⟩ := mixed_shadows_reach_two_fresh_copies
  rw [ran]
  exact congrArg some allocated.free.cell

theorem shallow_cursor_refuted : observe (run (nestedLocationPipelineCode .uint) (machine.push (.slot source))) ≠ some w[47] := by
  rw [final_cursor_observation]
  decide +kernel

private def lateCursor (remaining : Nat) (positive : 0 < remaining) (small : remaining < 128) : Fin W :=
  ⟨W-remaining,by
    have wide : 128 < W := by decide
    omega⟩
private def late (remaining : Nat) (positive : 0 < remaining) (small : remaining < 128) : Machine :=
  writeMachine machine 0 (.val (lateCursor remaining positive small))
private theorem late_allocator (remaining : Nat) (positive : 0 < remaining) (small : remaining < 128) :
    Objects.AllocatorRepr input.heap input.base 8 (lateCursor remaining positive small) (late remaining positive small) := by
  have lower : 40 ≤ (lateCursor remaining positive small).val := by
    change 40 ≤ W-remaining
    have wide : 1024 < W := by decide
    omega
  refine ⟨allocator.heap.localWrite 0 (by decide) _,⟨by decide,by omega,rfl,?_⟩,?_⟩
  · intro address above
    change upd machine.mem 0 _ address = w[0]
    rw [upd_other _ _ (show address ≠ 0 by omega)]
    exact allocator.free.zero address (Nat.le_trans lower above)
  · intro R reference
    exact Nat.le_trans (allocator.live reference) lower

theorem first_capacity_refusal :
    ¬ (lateCursor 1 (by decide) (by decide)).val + nestedStorageParentDemand (nestedStorageLiveRows original) < W ∧
    run (nestedLocationPipelineCode .uint) ((late 1 (by decide) (by decide)).push (.slot source)) = .revert := by
  have tooLarge : ¬ (lateCursor 1 (by decide) (by decide)).val + nestedStorageParentDemand (nestedStorageLiveRows original) < W := by rw [demand]; with_unfolding_all decide
  rcases nested_live_pipeline_correct input.heap original input.base 8 (lateCursor 1 (by decide) (by decide)) (late 1 (by decide) (by decide)) source 128
      (late_allocator 1 (by decide) (by decide)) represented with success | refusal
  · obtain ⟨fits,firstFits,_⟩ := success
    exact (tooLarge firstFits).elim
  · exact ⟨tooLarge,refusal.2⟩

theorem second_refusal_retains_first :
    let cursor := lateCursor 10 (by decide) (by decide)
    let initial := late 10 (by decide) (by decide)
    let first := original.copyStToM input.heap rfl
    ∃ (fits : cursor.val + 7 < W), ∃ base intermediate,
      run nestedStorageHeaderCode (initial.push (.slot source)) = .ok (intermediate.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr first.heap base 8 ⟨cursor.val+7,fits⟩ intermediate ∧ base first.val.id = cursor ∧
      MVal.copyMToSt first.heap first.val = original.strip ∧
      run (nestedMemoryParentCode .uint) (intermediate.push (.val cursor)) = .revert ∧
      run (nestedLocationPipelineCode .uint) (initial.push (.slot source)) = .revert := by
  have firstFits : (lateCursor 10 (by decide) (by decide)).val + nestedStorageParentDemand (nestedStorageLiveRows original) < W := by rw [demand]; with_unfolding_all decide
  have tooLarge : ¬ (lateCursor 10 (by decide) (by decide)).val + 2 * nestedStorageParentDemand (nestedStorageLiveRows original) < W := by rw [demand]; with_unfolding_all decide
  rcases nested_live_pipeline_correct input.heap original input.base 8 (lateCursor 10 (by decide) (by decide)) (late 10 (by decide) (by decide)) source 128
      (late_allocator 10 (by decide) (by decide)) represented with success | refusal
  · exact (tooLarge success.choose).elim
  · rcases refusal.1 with ⟨failed,_⟩ | ⟨fits,base,intermediate,ran,allocated,root,contents,failed,secondRun⟩
    · exact (failed firstFits).elim
    · refine ⟨by simpa only [demand] using fits,base,intermediate,ran,?_,root,contents,secondRun,refusal.2⟩
      simpa only [demand] using allocated

/--
info: 'Solidity.Backend.MemoryCopies.NestedLivePipelineControls.mixed_shadows_reach_two_fresh_copies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms mixed_shadows_reach_two_fresh_copies
/--
info: 'Solidity.Backend.MemoryCopies.NestedLivePipelineControls.final_cursor_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms final_cursor_observation
/--
info: 'Solidity.Backend.MemoryCopies.NestedLivePipelineControls.shallow_cursor_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms shallow_cursor_refuted
/--
info: 'Solidity.Backend.MemoryCopies.NestedLivePipelineControls.first_capacity_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms first_capacity_refusal
/--
info: 'Solidity.Backend.MemoryCopies.NestedLivePipelineControls.second_refusal_retains_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms second_refusal_retains_first

end Solidity.Backend.MemoryCopies.NestedLivePipelineControls
