import Solidity.Backend.MemoryCopies.StorageRoundTripInterface

/-! The existing reached two-copy allocator supplies the array words to the
published memory/storage copy-back theorem. No final store or payload run is
assumed, and the two allocation-refusal phases remain unchanged. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

private theorem push_destination_run (middle : Machine) (address : Fin W) (destination : Slot) :
    run [.push (.slot destination)] (middle.push (.val address)) =
      .ok ((middle.push (.val address)).push (.slot destination)) 0 := rfl

attribute [local irreducible] run exec Instr.step loopRun

theorem storage_round_trip_correct {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source destination : Slot) (L : Nat) (old : SVal (.ref (.array (.prim primitive))))
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array (.prim primitive))) source (primitiveArrayValue primitive values bounded))
    (destinationRepr : ReprAt machine.store L (.ref (.array (.prim primitive))) destination old) :
    (∃ fits, StorageRoundTripResult heap primitive values bounded base frame cursor machine source destination L old fits) ∨
    (StorageMemoryPipelineRefusal heap primitive values bounded base frame cursor machine source ∧
      run (storageRoundTripCode destination) (machine.push (.slot source)) = .revert) := by
  have liveBound : values.length < L := by
    cases represented with
    | array header small entries => simpa only [List.length_map] using small
  have oldLength : machine.store destination = old.view.n := by
    cases destinationRepr with
    | array header small entries => exact header
  rcases storage_memory_pipeline_correct heap primitive values bounded base frame cursor machine source L allocator represented with success | refusal
  · obtain ⟨fits,result⟩ := success
    have completed : StorageMemoryPipelineResult heap primitive values bounded base frame cursor machine source fits := result
    obtain ⟨firstFits,base₁,intermediate,base₂,middle,firstRun,firstAllocator,firstRoot,pipelineRun,allocated,root,retainedRoot,extension,shape,below,middleBelow,gaps,keeps,firstKeeps,fresh,retained,contents⟩ := result
    let value := primitiveArrayValue primitive values bounded
    let first := value.copyStToM heap rfl
    let second := (MVal.copyMToSt first.heap first.val).copyStToM first.heap rfl
    let address : Fin W := ⟨cursor.val+(values.length+1),firstFits⟩
    have secondLength : second.heap.len second.val .dyn = values.length := by
      dsimp only [second,first,value]
      rw [pipeline_first_snapshot]
      exact pipeline_first_length _ primitive values bounded
    have secondContents : MVal.copyMToSt second.heap second.val = value := by
      dsimp only [second,first,value]
      rw [pipeline_first_snapshot]
      exact pipeline_first_snapshot _ primitive values bounded
    have arrayRepr : Evm.Memory.ArrayRepr second.heap second.val address middle := by
      have actualArray : Evm.Memory.ArrayRepr second.heap second.val (base₂ second.val.id) middle :=
        (allocated.heap.arrays .dyn second.val).primitive
      have atAddress : base₂ second.val.id = address := root
      exact Eq.mp (congrArg (fun location => Evm.Memory.ArrayRepr second.heap second.val location middle) atAddress) actualArray
    let words := fun i => payloadWord (middle.mem (address.val+1+i))
    let final : Machine := {middle with store := arrayCopyStore middle.store destination values.length words}
    have payload : ∀ i, i < values.length → middle.mem (address.val+1+i) = .val (words i) := by
      intro i within
      have withinHeap : i < second.heap.len second.val .dyn := by rw [secondLength]; exact within
      let item := (MObj.elems .dyn (second.heap.get second.val))[i]'withinHeap
      exact ReprV.payload (arrayRepr.elements i item (getElem?_pos _ i withinHeap))
    have copyBack : run memoryArrayCopyCode ((middle.push (.val address)).push (.slot destination)) = .ok final 0 := by
      apply memoryArrayCopy_run middle address destination values.length words bounded
      · simpa only [secondLength] using arrayRepr.space
      · simpa only [secondLength] using arrayRepr.length
      · exact payload
    have destRepr : ReprAt final.store L (.ref (.array (.prim primitive))) destination (old.overlay value) := by
      have actual : ReprAt
          (arrayCopyStore middle.store destination (second.heap.len second.val .dyn)
            (fun i => payloadWord (middle.mem (address.val+1+i)))) L (.ref (.array (.prim primitive))) destination
          (old.overlay (MVal.copyMToSt second.heap second.val)) :=
        primitiveArray_copy_repr arrayRepr middle.store destination L (by rw [secondLength]; exact liveBound) old
      simpa only [secondLength,secondContents] using actual
    left
    refine ⟨fits,firstFits,base₂,middle,completed,pipelineRun,allocated,root,retainedRoot,extension,fresh,
      ?_,copyBack,allocated.mem_eq rfl,destRepr,arrayCopyStore_length _ _ _ _ bounded,
      ?_,?_,?_,rfl,?_,below⟩
    · rw [storageRoundTripCode,List.append_assoc,run_append_ok pipelineRun]
      change run ([.push (.slot destination)] ++ memoryArrayCopyCode) (middle.push (.val address)) = _
      rw [run_append_ok (push_destination_run middle address destination)]
      exact copyBack
    · intro i within
      exact arrayCopyStore_live middle.store destination values.length words i within
    · intro i lower upper
      have oldAtMiddle : middle.store destination = old.view.n := by rw [shape]; exact oldLength
      exact arrayCopyStore_tail middle.store destination values.length words i lower (by rw [oldAtMiddle]; exact upper)
    · intro slot outside
      exact (arrayCopyStore_other (p := primitive) middle.store destination values.length words slot outside).trans
        (by rw [shape])
    · change middle.stack = machine.stack
      rw [shape]
  · right
    refine ⟨refusal.1,?_⟩
    simpa only [storageRoundTripCode,List.append_assoc] using
      (run_append_revert (c₂ := [.push (.slot destination)] ++ memoryArrayCopyCode) refusal.2)

def storageRoundTrip : StorageRoundTripCertificate := ⟨storage_round_trip_correct⟩

/--
info: 'Solidity.Backend.MemoryCopies.storage_round_trip_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms storage_round_trip_correct
/--
info: 'Solidity.Backend.MemoryCopies.storageRoundTrip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms storageRoundTrip

end Solidity.Backend.MemoryCopies
