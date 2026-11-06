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

private theorem uint_word {word : Fin W} {actual : Evm.Word}
    (represented : ReprV .uint (indexValue word) actual) : actual = .val word := by
  obtain ⟨encoded,equation,equal⟩ := represented
  have same : encoded = word := Fin.ext (Int.ofNat_inj.mp equal.symm)
  subst encoded
  exact equation

private theorem pair_prefix : ∃ middle : Machine,
    run storageMemoryPipelineCode ((machine [wmod 7,wmod 11]).push (.slot source)) = .ok (middle.push w[43]) 0 ∧
    middle.mem 43 = w[2] ∧ middle.mem 44 = w[7] ∧ middle.mem 45 = w[11] ∧
    middle.store = store [wmod 7,wmod 11] ∧ middle.mem 0 = w[46] ∧ middle.mem 17 = w[7] := by
  have result : StorageMemoryPipelineResult input.heap .uint (values [wmod 7,wmod 11])
      (payload_bound _ (by decide)) input.base 8 (wmod 40) (machine [wmod 7,wmod 11]) source (by decide) :=
    storage_memory_pipeline_success input.heap .uint (values [wmod 7,wmod 11]) _ input.base 8 (wmod 40)
      (machine [wmod 7,wmod 11]) source 128 (allocator _) (represented _ (by decide)) (by decide)
  obtain ⟨firstFits,base₁,intermediate,base,middle,firstRun,firstAllocator,firstRoot,pipelineRun,allocated,root,
    retainedRoot,extension,shape,below,tail⟩ := result
  let first := (value [wmod 7,wmod 11] (by decide)).copyStToM input.heap rfl
  let second := (MVal.copyMToSt first.heap first.val).copyStToM first.heap rfl
  have contents : MObj.elems .dyn (second.heap.get second.val) = [indexValue (wmod 7),indexValue (wmod 11)] := by
    dsimp only [second,first,value]
    rw [pipeline_first_snapshot]
    rw [primitive_array_source,primitive_array_source]
    simp only [Grown.alloc,Heap.get_alloc,MObj.elems_dyn,MObj.wk,primitiveArrayObject,MVal.wk,
      values,List.map_cons,List.map_nil]
  have count : second.heap.len second.val .dyn = 2 := by
    dsimp only [second,first,value]
    rw [pipeline_first_snapshot]
    exact pipeline_first_length _ .uint _ _
  have array : Evm.Memory.ArrayRepr second.heap second.val (wmod 43) middle := by
    have atAddress : base second.val.id = wmod 43 := root
    exact Eq.mp (congrArg (fun address => Evm.Memory.ArrayRepr second.heap second.val address middle) atAddress)
      (allocated.heap.arrays .dyn second.val).primitive
  refine ⟨middle,pipelineRun,?_,?_,?_,?_,allocated.free.cell,(below 17 (by decide) (by decide)).trans rfl⟩
  · simpa only [count] using array.length
  · exact uint_word (array.elements 0 _ (by rw [contents]; rfl))
  · exact uint_word (array.elements 1 _ (by rw [contents]; rfl))
  · rw [shape]
    rfl

private def pairWords (index : Nat) : Fin W := [wmod 7,wmod 11][index]?.getD (wmod 0)
private def earlyLengthCode (dst : Slot) : List Instr := [.dup 1,.mloadAt,.push (.slot dst),.sstore]
private def lengthFirstCode : List Instr :=
  storageMemoryPipelineCode ++ earlyLengthCode destination ++ [.push (.slot destination)] ++ memoryArrayCopyCode

private theorem early_length_run (middle : Machine) (dst : Slot) (header : middle.mem 43 = w[2]) :
    run (earlyLengthCode dst) (middle.push w[43]) =
      .ok (({middle with store := WordStore.write middle.store dst 2} : Machine).push w[43]) 0 := by
  have loaded : run [.dup 1,.mloadAt] (middle.push w[43]) = .ok ((middle.push w[43]).push w[2]) 0 := by
    change (Evm.Out.ok ((middle.push w[43]).push (middle.mem 43)) 0) = _
    rw [header]
  change run ([.dup 1,.mloadAt] ++ [.push (.slot dst),.sstore]) (middle.push w[43]) = _
  rw [run_append_ok loaded]
  rfl

private theorem pair_copy_back (middle : Machine) (dst : Slot)
    (header : middle.mem 43 = w[2]) (left : middle.mem 44 = w[7]) (right : middle.mem 45 = w[11]) :
    run memoryArrayCopyCode ((middle.push w[43]).push (.slot dst)) =
      .ok {middle with store := arrayCopyStore middle.store dst 2 pairWords} 0 := by
  apply memoryArrayCopy_run middle (wmod 43) dst 2 pairWords (by decide) (by decide) header
  intro index within
  cases index with
  | zero => exact left
  | succ index => cases index with
    | zero => exact right
    | succ index => omega

private theorem push_destination (middle : Machine) (dst : Slot) :
    run [.push (.slot dst)] (middle.push w[43]) = .ok ((middle.push w[43]).push (.slot dst)) 0 := rfl

private def writeSlotCode (slot : Slot) (word : Fin W) : List Instr := [.push (.val word),.push (.slot slot),.sstore]
private theorem write_slot_run (middle : Machine) (slot : Slot) (word : Fin W) :
    run (writeSlotCode slot word) middle = .ok {middle with store := WordStore.write middle.store slot word.val} 0 := rfl

private def overwriteFourCode (slot : Slot) : List Instr :=
  writeSlotCode slot (wmod 4) ++ writeSlotCode (.data slot 0) (wmod 99) ++
  writeSlotCode (.data slot 1) (wmod 99) ++ writeSlotCode (.data slot 2) (wmod 99) ++ writeSlotCode (.data slot 3) (wmod 99)
private def overwriteFourStore (st : WordStore) (slot : Slot) : WordStore :=
  WordStore.write (WordStore.write (WordStore.write (WordStore.write (WordStore.write st slot 4)
    (.data slot 0) 99) (.data slot 1) 99) (.data slot 2) 99) (.data slot 3) 99
private def snapshotRestoreCode : List Instr :=
  storageMemoryPipelineCode ++ overwriteFourCode source ++ [.push (.slot source)] ++ memoryArrayCopyCode

private theorem overwrite_four_run (middle : Machine) (slot : Slot) :
    run (overwriteFourCode slot) (middle.push w[43]) =
      .ok (({middle with store := overwriteFourStore middle.store slot} : Machine).push w[43]) 0 := by
  let m₁ : Machine := {middle with store := WordStore.write middle.store slot 4}
  let m₂ : Machine := {m₁ with store := WordStore.write m₁.store (.data slot 0) 99}
  let m₃ : Machine := {m₂ with store := WordStore.write m₂.store (.data slot 1) 99}
  let m₄ : Machine := {m₃ with store := WordStore.write m₃.store (.data slot 2) 99}
  rw [overwriteFourCode,List.append_assoc,List.append_assoc,List.append_assoc,
    run_append_ok (write_slot_run (middle.push w[43]) slot (wmod 4))]
  change run (writeSlotCode (.data slot 0) (wmod 99) ++
    (writeSlotCode (.data slot 1) (wmod 99) ++
      (writeSlotCode (.data slot 2) (wmod 99) ++ writeSlotCode (.data slot 3) (wmod 99)))) (m₁.push w[43]) = _
  rw [run_append_ok (write_slot_run (m₁.push w[43]) (.data slot 0) (wmod 99))]
  change run (writeSlotCode (.data slot 1) (wmod 99) ++
    (writeSlotCode (.data slot 2) (wmod 99) ++ writeSlotCode (.data slot 3) (wmod 99))) (m₂.push w[43]) = _
  rw [run_append_ok (write_slot_run (m₂.push w[43]) (.data slot 1) (wmod 99))]
  change run (writeSlotCode (.data slot 2) (wmod 99) ++ writeSlotCode (.data slot 3) (wmod 99)) (m₃.push w[43]) = _
  rw [run_append_ok (write_slot_run (m₃.push w[43]) (.data slot 2) (wmod 99))]
  change run (writeSlotCode (.data slot 3) (wmod 99)) (m₄.push w[43]) = _
  exact write_slot_run (m₄.push w[43]) (.data slot 3) (wmod 99)

private theorem changed_source_repr :
    ReprAt (overwriteFourStore (store [wmod 7,wmod 11]) source) 128 (.ref (.array (.prim .uint))) source oldDestination := by
  refine .array (by with_unfolding_all rfl) (by decide) ?_
  intro index item selected
  simp only [SVec.toList_ofList,values,List.map_replicate] at selected
  have same : item = SVal.prim (indexValue (wmod 99)) := (List.mem_replicate.mp (List.mem_of_getElem? selected)).2
  have within : index < 4 := by simpa only [List.length_replicate] using lt_of_getElem? selected
  subst item
  simp only [size_prim,Nat.mul_one]
  have positions : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases positions with rfl | rfl | rfl | rfl <;> exact .prim (ReprV.uint_of rfl)

attribute [local irreducible] run exec Instr.step loopRun

theorem length_first_mutant_retains_stale_tail : ∃ final : Machine,
    run lengthFirstCode ((machine [wmod 7,wmod 11]).push (.slot source)) = .ok final 0 ∧
    final.store destination = 2 ∧ final.store (.data destination 0) = 7 ∧ final.store (.data destination 1) = 11 ∧
    final.store (.data destination 3) = 99 ∧ final.mem 0 = w[46] := by
  obtain ⟨middle,prefixRun,header,left,right,stored,cursor,old⟩ := pair_prefix
  let changed : Machine := {middle with store := WordStore.write middle.store destination 2}
  let final : Machine := {changed with store := arrayCopyStore changed.store destination 2 pairWords}
  have early : run (earlyLengthCode destination) (middle.push w[43]) = .ok (changed.push w[43]) 0 :=
    early_length_run middle destination header
  have back : run memoryArrayCopyCode ((changed.push w[43]).push (.slot destination)) = .ok final 0 :=
    pair_copy_back changed destination header left right
  refine ⟨final,?_,arrayCopyStore_length _ _ _ _ (by decide),arrayCopyStore_live _ _ _ _ 0 (by decide),
    arrayCopyStore_live _ _ _ _ 1 (by decide),?_,cursor⟩
  · rw [lengthFirstCode,List.append_assoc,List.append_assoc,run_append_ok prefixRun,run_append_ok early,
      run_append_ok (push_destination changed destination)]
    exact back
  · change arrayCopyStore (WordStore.write middle.store destination 2) destination 2 pairWords (.data destination 3) = 99
    rw [stored]
    with_unfolding_all rfl

theorem length_first_differs_from_round_trip : ∃ correct bad : Machine,
    run (storageRoundTripCode destination) ((machine [wmod 7,wmod 11]).push (.slot source)) = .ok correct 0 ∧
    run lengthFirstCode ((machine [wmod 7,wmod 11]).push (.slot source)) = .ok bad 0 ∧
    correct.store (.data destination 3) = 0 ∧ bad.store (.data destination 3) = 99 ∧ correct ≠ bad := by
  obtain ⟨correct,goodRun,goodLength,goodLeft,goodRight,good₂,good₃,goodRest⟩ := pair_observation
  obtain ⟨bad,badRun,badLength,badLeft,badRight,bad₃,badCursor⟩ := length_first_mutant_retains_stale_tail
  refine ⟨correct,bad,goodRun,badRun,good₃,bad₃,?_⟩
  intro same
  rw [same,bad₃] at good₃
  cases good₃

theorem same_slot_changed_contents_restored : ∃ middle changed final : Machine,
    run storageMemoryPipelineCode ((machine [wmod 7,wmod 11]).push (.slot source)) = .ok (middle.push w[43]) 0 ∧
    run (overwriteFourCode source) (middle.push w[43]) = .ok (changed.push w[43]) 0 ∧
    ReprAt changed.store 128 (.ref (.array (.prim .uint))) source oldDestination ∧
    changed.store source = 4 ∧ changed.store (.data source 0) = 99 ∧
    changed.store (.data source 0) ≠ (machine [wmod 7,wmod 11]).store (.data source 0) ∧ changed.mem 44 = w[7] ∧
    run memoryArrayCopyCode ((changed.push w[43]).push (.slot source)) = .ok final 0 ∧
    run snapshotRestoreCode ((machine [wmod 7,wmod 11]).push (.slot source)) = .ok final 0 ∧
    final.store source = 2 ∧ final.store (.data source 0) = 7 ∧ final.store (.data source 1) = 11 ∧
    final.store (.data source 3) = 0 ∧ final.store sentinel = 77 ∧ final.mem 0 = w[46] ∧ final.mem 17 = w[7] := by
  obtain ⟨middle,prefixRun,header,left,right,stored,cursor,old⟩ := pair_prefix
  let changed : Machine := {middle with store := overwriteFourStore middle.store source}
  let final : Machine := {changed with store := arrayCopyStore changed.store source 2 pairWords}
  have changedStore : changed.store = overwriteFourStore (store [wmod 7,wmod 11]) source := by
    change overwriteFourStore middle.store source = _
    rw [stored]
  have mutateRun : run (overwriteFourCode source) (middle.push w[43]) = .ok (changed.push w[43]) 0 :=
    overwrite_four_run middle source
  have backRun : run memoryArrayCopyCode ((changed.push w[43]).push (.slot source)) = .ok final 0 :=
    pair_copy_back changed source header left right
  refine ⟨middle,changed,final,prefixRun,mutateRun,?_,?_,?_,?_,left,backRun,?_,
    arrayCopyStore_length _ _ _ _ (by decide),arrayCopyStore_live _ _ _ _ 0 (by decide),
    arrayCopyStore_live _ _ _ _ 1 (by decide),?_,?_,cursor,old⟩
  · rw [changedStore]
    exact changed_source_repr
  · rw [changedStore]
    with_unfolding_all rfl
  · rw [changedStore]
    with_unfolding_all rfl
  · rw [changedStore]
    with_unfolding_all decide +kernel
  · rw [snapshotRestoreCode,List.append_assoc,List.append_assoc,run_append_ok prefixRun,run_append_ok mutateRun,
      run_append_ok (push_destination changed source)]
    exact backRun
  · change arrayCopyStore changed.store source 2 pairWords (.data source 3) = 0
    rw [changedStore]
    with_unfolding_all rfl
  · change arrayCopyStore changed.store source 2 pairWords sentinel = 77
    rw [changedStore]
    with_unfolding_all rfl

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

/--
info: 'Solidity.Backend.MemoryCopies.StorageRoundTripControls.length_first_mutant_retains_stale_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms length_first_mutant_retains_stale_tail
/--
info: 'Solidity.Backend.MemoryCopies.StorageRoundTripControls.length_first_differs_from_round_trip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms length_first_differs_from_round_trip
/--
info: 'Solidity.Backend.MemoryCopies.StorageRoundTripControls.same_slot_changed_contents_restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms same_slot_changed_contents_restored

end Solidity.Backend.MemoryCopies.StorageRoundTripControls
