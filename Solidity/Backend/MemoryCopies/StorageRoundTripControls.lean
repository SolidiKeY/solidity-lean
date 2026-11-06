import Solidity.Backend.MemoryCopies.StorageRoundTrip
import Solidity.Evm.MemoryObjectArrayExamples

/-! Actual three-stage runs from represented nonzero/empty/long sources to
a four-element destination, with shrinking/growing cases and both refusal phases. -/
namespace Solidity.Backend.MemoryCopies.StorageRoundTripControls
open Evm Evm.Memory
private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def input : Input := ⟨_,_,_,_,ObjectArrayExamples.initial_allocator⟩
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private theorem wide : 128 < W := by decide
private theorem large_bound : 512 < W := by decide
private theorem boundary_large : 1024 < W := by decide
private def value (payloads : List (Fin W)) (bounded : payloads.length < 128) : SVal (.ref (.array (.prim .uint))) :=
  primitiveArrayValue .uint (values payloads) (by rw [values,List.length_map]; exact Nat.lt_trans bounded wide)
private def source : Slot := .root 0
private def store (payloads : List (Fin W)) : WordStore := ⟨fun slot => match slot with
  | .root 0 => wmod payloads.length
  | .data (.root 0) index => payloads[index]?.getD (wmod 0)
  | .root 1 => wmod 4
  | .data (.root 1) _ => wmod 99
  | .root 2 => wmod 77
  | _ => wmod 0⟩
private def machine (payloads : List (Fin W)) : Machine := {input.machine with store := store payloads}
private def grown (payloads : List (Fin W)) (bounded : payloads.length < 128) :=
  (value payloads bounded).copyStToM input.heap rfl
private theorem represented (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    ReprAt (machine payloads).store 128 (.ref (.array (.prim .uint))) source (value payloads bounded) := by
  refine .array ?_ (by simpa only [values,List.length_map] using bounded) ?_
  · simp only [values,List.length_map]
    exact Nat.mod_eq_of_lt (Nat.lt_trans bounded wide)
  · intro index item selected
    simp only [SVec.toList_ofList,values,List.getElem?_map] at selected
    cases chosen : payloads[index]? with
    | none => simp only [chosen,Option.map_none] at selected; cases selected
    | some payload =>
      simp only [chosen,Option.map_some] at selected
      cases selected
      simp only [size_prim,Nat.mul_one]
      refine .prim (ReprV.uint_of ?_)
      simp only [machine,store,source,chosen,Option.getD_some]
      rfl
private theorem allocator (payloads : List (Fin W)) :
    Objects.AllocatorRepr input.heap input.base 8 (wmod 40) (machine payloads) := input.allocator.mem_eq rfl


private def destination : Slot := .root 1
private def sentinel : Slot := .root 2
private def oldDestination : SVal (.ref (.array (.prim .uint))) :=
  value (List.replicate 4 (wmod 99)) (by decide)
private theorem destination_repr (payloads : List (Fin W)) :
    ReprAt (machine payloads).store 128 (.ref (.array (.prim .uint))) destination oldDestination := by
  refine .array rfl (by decide) ?_
  intro index item selected
  simp only [SVec.toList_ofList,values,List.map_replicate] at selected
  have same : item = SVal.prim (indexValue (wmod 99)) := (List.mem_replicate.mp (List.mem_of_getElem? selected)).2
  subst item
  simp only [size_prim,Nat.mul_one]
  exact .prim (ReprV.uint_of rfl)

private theorem payload_bound (payloads : List (Fin W)) (bounded : payloads.length < 128) : (values payloads).length < W := by
  rw [values,List.length_map]
  exact Nat.lt_trans bounded wide

private theorem completed (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    ∃ fits, StorageRoundTripResult input.heap .uint (values payloads) (payload_bound payloads bounded) input.base 8 (wmod 40)
      (machine payloads) source destination 128 oldDestination fits := by
  rcases storage_round_trip_correct input.heap .uint (values payloads) (payload_bound payloads bounded) input.base 8 (wmod 40)
      (machine payloads) source destination 128 oldDestination (allocator payloads) (represented payloads bounded)
      (destination_repr payloads) with success | refusal
  · exact success
  · have totalFits : (wmod 40).val + 2*((values payloads).length+1) < W := by
      rw [values,List.length_map]
      have large : 512 < W := large_bound
      change 40 + 2*(payloads.length+1) < W
      omega
    rcases refusal.1 with ⟨failed,_⟩ | ⟨fits,base,intermediate,ran,allocated,root,contents,failed,secondRun⟩
    · exact (failed (by omega)).elim
    · exact (failed totalFits).elim

private theorem uint_cell {st : WordStore} {slot : Slot} {word : Fin W}
    (represented : ReprAt st 128 (.prim .uint) slot (.prim (indexValue word))) : st slot = word.val := by
  cases represented with
  | prim typed =>
    obtain ⟨actual,equation,equal⟩ := typed
    have same : actual = word := Fin.ext (Int.ofNat_inj.mp equal.symm)
    subst actual
    exact congrArg Fin.val (Word.val.inj equation)

private theorem sentinel_outside : ¬ Occ (.ref (.array (.prim .uint))) destination sentinel := by
  intro occupied
  cases occupied with
  | elem index leaf => cases leaf

theorem pair_observation : ∃ final,
    run (storageRoundTripCode destination) ((machine [wmod 7,wmod 11]).push (.slot source)) = .ok final 0 ∧
    final.store destination = 2 ∧ final.store (.data destination 0) = 7 ∧ final.store (.data destination 1) = 11 ∧
    final.store (.data destination 2) = 0 ∧ final.store (.data destination 3) = 0 ∧
    final.store sentinel = 77 ∧ final.mem 0 = w[46] ∧ final.mem 17 = w[7] := by
  obtain ⟨fits,firstFits,base,middle,pipeline,pipelineRun,allocated,root,firstRoot,extension,fresh,ran,copyBack,finalAllocator,typed,length,live,tail,outside,mem,stack,below⟩ :=
    completed [wmod 7,wmod 11] (by decide)
  let address : Fin W := ⟨(wmod 40).val+((values [wmod 7,wmod 11]).length+1),firstFits⟩
  let words := fun i => payloadWord (middle.mem (address.val+1+i))
  let final : Machine := {middle with store := arrayCopyStore middle.store destination (values [wmod 7,wmod 11]).length words}
  have firstItem : ReprAt final.store 128 (.prim .uint) (.data destination 0) (.prim (indexValue (wmod 7))) := by
    simp only [oldDestination,value,primitiveArrayValue,SVal.overlay_array] at typed
    cases typed with
    | array header small entries => exact entries 0 _ (by with_unfolding_all rfl)
  have secondItem : ReprAt final.store 128 (.prim .uint) (.data destination 1) (.prim (indexValue (wmod 11))) := by
    simp only [oldDestination,value,primitiveArrayValue,SVal.overlay_array] at typed
    cases typed with
    | array header small entries => exact entries 1 _ (by with_unfolding_all rfl)
  exact ⟨final,ran,length,uint_cell firstItem,uint_cell secondItem,tail 2 (by decide) (by decide),
    tail 3 (by decide) (by decide),(outside sentinel sentinel_outside).trans rfl,finalAllocator.free.cell,
    (below 17 (by decide) (by decide)).trans rfl⟩

theorem uncleared_suffix_refuted : ∃ final,
    run (storageRoundTripCode destination) ((machine [wmod 7,wmod 11]).push (.slot source)) = .ok final 0 ∧
    final.store (.data destination 3) ≠ 99 := by
  obtain ⟨final,ran,length,left,right,cleared₂,cleared₃,rest⟩ := pair_observation
  refine ⟨final,ran,?_⟩
  rw [cleared₃]
  decide

theorem empty_success : ∃ fits, StorageRoundTripResult input.heap .uint (values []) (payload_bound [] (by decide)) input.base 8 (wmod 40)
    (machine []) source destination 128 oldDestination fits := completed [] (by decide)

theorem long_success : ∃ fits, StorageRoundTripResult input.heap .uint (values (List.replicate 64 (wmod 7))) (payload_bound _ (by decide)) input.base 8 (wmod 40)
    (machine (List.replicate 64 (wmod 7))) source destination 128 oldDestination fits :=
  completed (List.replicate 64 (wmod 7)) (by decide)

theorem same_slot_success : ∃ fits, StorageRoundTripResult input.heap .uint (values [wmod 7,wmod 11]) (payload_bound _ (by decide)) input.base 8 (wmod 40)
    (machine [wmod 7,wmod 11]) source source 128 (value [wmod 7,wmod 11] (by decide)) fits := by
  rcases storage_round_trip_correct input.heap .uint (values [wmod 7,wmod 11]) (payload_bound _ (by decide)) input.base 8 (wmod 40)
      (machine [wmod 7,wmod 11]) source source 128 (value [wmod 7,wmod 11] (by decide))
      (allocator [wmod 7,wmod 11]) (represented _ (by decide)) (represented _ (by decide)) with success | refusal
  · exact success
  · rcases refusal.1 with ⟨failed,_⟩ | ⟨fits,base,intermediate,ran,allocated,root,contents,failed,secondRun⟩
    · exact (failed (by decide)).elim
    · exact (failed (by decide)).elim

private def lateCursor (remaining : Nat) (positive : 0 < remaining) (small : remaining < 128) : Fin W :=
  ⟨W-remaining,by
    have wide : 128 < W := by decide
    omega⟩
private def late (remaining : Nat) (positive : 0 < remaining) (small : remaining < 128) : Machine :=
  writeMachine (machine [wmod 7,wmod 11]) 0 (.val (lateCursor remaining positive small))
private theorem late_allocator (remaining : Nat) (positive : 0 < remaining) (small : remaining < 128) :
    Objects.AllocatorRepr input.heap input.base 8 (lateCursor remaining positive small) (late remaining positive small) := by
  have lower : 40 ≤ (lateCursor remaining positive small).val := by
    change 40 ≤ W-remaining
    have wide : 1024 < W := boundary_large
    omega
  refine ⟨(allocator [wmod 7,wmod 11]).heap.localWrite 0 (by decide) _,⟨by decide,by omega,rfl,?_⟩,?_⟩
  · intro address above
    change upd (machine [wmod 7,wmod 11]).mem 0 _ address = w[0]
    rw [upd_other _ _ (show address ≠ 0 by omega)]
    exact (allocator [wmod 7,wmod 11]).free.zero address (Nat.le_trans lower above)
  · intro R reference
    exact Nat.le_trans ((allocator [wmod 7,wmod 11]).live reference) lower

theorem first_refusal :
    ¬ (lateCursor 1 (by decide) (by decide)).val + ((values [wmod 7,wmod 11]).length+1) < W ∧
    run (storageRoundTripCode destination) ((late 1 (by decide) (by decide)).push (.slot source)) = .revert := by
  have failed : ¬ (lateCursor 1 (by decide) (by decide)).val + ((values [wmod 7,wmod 11]).length+1) < W := by with_unfolding_all decide
  rcases storage_round_trip_correct input.heap .uint (values [wmod 7,wmod 11]) (payload_bound _ (by decide)) input.base 8 (lateCursor 1 (by decide) (by decide))
      (late 1 (by decide) (by decide)) source destination 128 oldDestination
      (late_allocator 1 (by decide) (by decide)) (represented _ (by decide)) (destination_repr _) with success | refusal
  · obtain ⟨fits,firstFits,_⟩ := success
    exact (failed firstFits).elim
  · exact ⟨failed,refusal.2⟩

theorem later_refusal_prefix :
    let cursor := lateCursor 5 (by decide) (by decide)
    let initial := late 5 (by decide) (by decide)
    let first := (value [wmod 7,wmod 11] (by decide)).copyStToM input.heap rfl
    ∃ (fits : cursor.val+3 < W), ∃ base intermediate,
      run checkedStorageArrayCode (initial.push (.slot source)) = .ok (intermediate.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr first.heap base 8 ⟨cursor.val+3,fits⟩ intermediate ∧ base first.val.id = cursor ∧
      run checkedMemoryArrayCode (intermediate.push (.val cursor)) = .revert ∧
      run (storageRoundTripCode destination) (initial.push (.slot source)) = .revert := by
  have firstFits : (lateCursor 5 (by decide) (by decide)).val + ((values [wmod 7,wmod 11]).length+1) < W := by with_unfolding_all decide
  have failed : ¬ (lateCursor 5 (by decide) (by decide)).val + 2*((values [wmod 7,wmod 11]).length+1) < W := by with_unfolding_all decide
  rcases storage_round_trip_correct input.heap .uint (values [wmod 7,wmod 11]) (payload_bound _ (by decide)) input.base 8 (lateCursor 5 (by decide) (by decide))
      (late 5 (by decide) (by decide)) source destination 128 oldDestination
      (late_allocator 5 (by decide) (by decide)) (represented _ (by decide)) (destination_repr _) with success | refusal
  · exact (failed success.choose).elim
  · rcases refusal.1 with ⟨tooLarge,_⟩ | ⟨fits,base,intermediate,ran,allocated,root,contents,failed,secondRun⟩
    · exact (tooLarge firstFits).elim
    · exact ⟨fits,base,intermediate,ran,allocated,root,secondRun,refusal.2⟩

/--
info: 'Solidity.Backend.MemoryCopies.StorageRoundTripControls.pair_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pair_observation
/--
info: 'Solidity.Backend.MemoryCopies.StorageRoundTripControls.uncleared_suffix_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms uncleared_suffix_refuted
/--
info: 'Solidity.Backend.MemoryCopies.StorageRoundTripControls.empty_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms empty_success
/--
info: 'Solidity.Backend.MemoryCopies.StorageRoundTripControls.long_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms long_success
/--
info: 'Solidity.Backend.MemoryCopies.StorageRoundTripControls.same_slot_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms same_slot_success
/--
info: 'Solidity.Backend.MemoryCopies.StorageRoundTripControls.first_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms first_refusal
/--
info: 'Solidity.Backend.MemoryCopies.StorageRoundTripControls.later_refusal_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms later_refusal_prefix

end Solidity.Backend.MemoryCopies.StorageRoundTripControls
