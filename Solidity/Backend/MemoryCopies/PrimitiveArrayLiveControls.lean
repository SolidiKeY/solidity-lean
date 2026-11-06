import Solidity.Backend.MemoryCopies.PrimitiveArrayLive
import Solidity.Evm.MemoryObjectArrayExamples

/-! Retained nonzero storage slots are not copied past the live array length.
The runtime fixture has a represented, populated old heap. -/
namespace Solidity.Backend.MemoryCopies.PrimitiveArrayLiveControls
open Evm Evm.Memory
private def sourceValue (live : List (Fin W)) (shadow : SList (.prim .uint))
    (bounded : live.length < W) : SVal (.ref (.array (.prim .uint))) :=
  .array (SVec.ofList (live.map (fun word => SVal.prim (indexValue word)))) shadow
    (by simpa only [List.length_map] using bounded)
private def retained : SList (.prim .uint) := .cons (.prim (indexValue (wmod 23))) .nil

theorem all_shadows_inhabited (live : List (Fin W)) (shadow : SList (.prim .uint))
    (bounded : live.length < W) : PrimitiveArrayLiveCertificate (sourceValue live shadow bounded) :=
  primitiveArrayLive _

theorem same_copy {H : HTy} (heap : Heap H) (live : List (Fin W))
    (left right : SList (.prim .uint)) (bounded : live.length < W) :
    (sourceValue live left bounded).copyStToM heap rfl =
      (sourceValue live right bounded).copyStToM heap rfl := by
  rw [primitive_live_copy (sourceValue live left bounded) heap,
    primitive_live_copy (sourceValue live right bounded) heap]
  rfl

theorem empty_with_shadow : PrimitiveArrayLiveCertificate (sourceValue [] retained (by decide)) :=
  all_shadows_inhabited _ _ _

theorem long_with_shadow : PrimitiveArrayLiveCertificate
    (sourceValue (List.replicate 64 (wmod 11)) retained (by decide)) := all_shadows_inhabited _ _ _

private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def input : Input := ⟨_,_,_,_,ObjectArrayExamples.initial_allocator⟩
private def store : WordStore := ⟨fun slot => match slot with
  | .root 0 => wmod 0
  | .data (.root 0) 0 => wmod 23
  | _ => wmod 0⟩
private def machine : Machine := {input.machine with store := store}
private def emptyValue : SVal (.ref (.array (.prim .uint))) := sourceValue [] retained (by decide)
private theorem empty_live : primitiveArrayLiveValues emptyValue = [] := by
  simp only [primitiveArrayLiveValues,emptyValue,sourceValue,SVal.view_array,SVec.toList_ofList,List.map_nil]
private theorem represented : ReprAt machine.store 128 (.ref (.array (.prim .uint))) (.root 0) emptyValue := by
  refine .array rfl (by decide) ?_
  intro index element selected
  simp only [SVec.toList_ofList,List.map_nil,List.getElem?_nil] at selected
  cases selected

theorem actual_shadow_runtime : ∃ (base' : Nat → Fin W) (target : Machine),
    run runtimeStorageArrayCode (machine.push (.slot (.root 0))) = .ok (target.push w[40]) 0 ∧
    Objects.AllocatorRepr (emptyValue.copyStToM input.heap rfl).heap base' 8 (wmod 41) target ∧
    target.mem 0 = w[41] ∧ target.mem 40 = w[0] ∧ target.mem 41 = w[0] ∧
    target.mem 17 = w[7] ∧ target.store.cells (.data (.root 0) 0) = wmod 23 := by
  obtain ⟨base',target,ran,allocated,root,_,shape,below,_⟩ :=
    runtime_primitive_live_success input.heap .uint emptyValue input.base 8 (wmod 40)
      machine (.root 0) 128 (input.allocator.mem_eq rfl) represented (by rw [empty_live]; decide)
  have rootAt : base' (emptyValue.copyStToM input.heap rfl).val.id = wmod 40 := root
  have length : (emptyValue.copyStToM input.heap rfl).heap.len
      (emptyValue.copyStToM input.heap rfl).val .dyn = 0 := by
    rw [primitive_live_copy,primitive_array_source]
    simp only [Grown.alloc,Heap.len,Heap.get_alloc,MObj.elems_dyn,MObj.wk,primitiveArrayObject,empty_live,List.map_nil,List.length_nil]
  have header : target.mem (base' (emptyValue.copyStToM input.heap rfl).val.id).val = w[0] := by
    have stored : target.mem (base' (emptyValue.copyStToM input.heap rfl).val.id).val =
        .val (wmod ((emptyValue.copyStToM input.heap rfl).heap.len
          (emptyValue.copyStToM input.heap rfl).val .dyn)) :=
      (allocated.heap.arrays .dyn (emptyValue.copyStToM input.heap rfl).val).length rfl
    rw [length] at stored
    exact stored
  rw [rootAt] at header
  have reached : Objects.AllocatorRepr (emptyValue.copyStToM input.heap rfl).heap base' 8 (wmod 41) target := by
    simpa only [empty_live,List.length_nil] using allocated
  refine ⟨base',target,ran,reached,reached.free.cell,header,
    reached.free.zero 41 (by decide),below 17 (by decide) (by decide),?_⟩
  rw [shape]
  rfl

theorem shadow_not_payload (target : Machine)
    (execution : run runtimeStorageArrayCode (machine.push (.slot (.root 0))) = .ok (target.push w[40]) 0) :
    target.mem 41 ≠ w[23] := by
  obtain ⟨_,actual,ran,_,_,_,tail,_,_⟩ := actual_shadow_runtime
  rw [execution] at ran
  have same : target.mem 41 = actual.mem 41 := congrArg (fun state => state.mem 41) (Out.ok.inj ran).1
  rw [same,tail]
  decide

#print axioms all_shadows_inhabited
#print axioms same_copy
#print axioms empty_with_shadow
#print axioms long_with_shadow
#print axioms actual_shadow_runtime
#print axioms shadow_not_payload
end Solidity.Backend.MemoryCopies.PrimitiveArrayLiveControls
