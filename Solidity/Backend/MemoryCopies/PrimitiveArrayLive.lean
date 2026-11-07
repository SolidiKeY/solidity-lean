import Solidity.Backend.MemoryCopies.PrimitiveArrayLiveInterface

/-! Every typed primitive array has a live canonical memory copy, including
arrays with retained storage shadows. Runtime code remains header-driven. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem primitive_live_roundtrip {primitive : PrimTy} (values : List (SVal (.prim primitive))) :
    (values.map (fun value => value.view)).map SVal.prim = values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    cases value with
    | prim value => simp only [List.map_cons,SVal.view_prim,ih]

theorem primitive_live_vector {primitive : PrimTy} {n : Nat} (elements : SVec (.prim primitive) n)
    {H : HTy} (heap : Heap H) :
    elements.copyStToM heap rfl =
      ⟨List.prefix_refl H,heap,⟨elements.toList.map (fun value => value.view),by
        rw [List.length_map,SVec.length_toList]⟩⟩ := by
  cases elements with
  | nil => simp only [SVec.copyStToM_nil,SVec.toList_nil,List.map_nil]
  | cons value elements =>
    cases value with
    | prim value =>
      simp only [SVec.copyStToM_cons,SVal.copyStToM_prim,SVec.toList_cons,List.map_cons,SVal.view_prim]
      with_unfolding_all exact Grown.prims_cons heap value _ _ _ (primitive_live_vector elements heap) _ _ _

theorem primitive_live_bound {primitive : PrimTy}
    (value : SVal (.ref (.array (.prim primitive)))) :
    (primitiveArrayLiveValues value).length < W := by
  cases value with
  | array elements shadow bounded =>
    simpa only [primitiveArrayLiveValues,SVal.view_array,List.length_map,SVec.length_toList] using bounded

theorem primitive_live_copy {primitive : PrimTy}
    (value : SVal (.ref (.array (.prim primitive)))) {H : HTy} (heap : Heap H) :
    value.copyStToM heap rfl =
      (primitiveArrayValue primitive (primitiveArrayLiveValues value) (primitive_live_bound value)).copyStToM heap rfl := by
  rw [primitive_array_source]
  cases value with
  | array elements shadow bounded =>
    rw [SVal.copyStToM_array,primitive_live_vector]
    rfl

theorem primitive_live_representation {primitive : PrimTy}
    (value : SVal (.ref (.array (.prim primitive)))) (store : WordStore) (limit : Nat) (source : Slot)
    (represented : ReprAt store limit (.ref (.array (.prim primitive))) source value) :
    ReprAt store limit (.ref (.array (.prim primitive))) source
      (primitiveArrayValue primitive (primitiveArrayLiveValues value) (primitive_live_bound value)) := by
  cases represented with
  | @array _ count _ elements shadow bounded header small entries =>
    apply ReprAt.array
    · simpa only [primitiveArrayLiveValues,SVal.view_array,List.length_map,SVec.length_toList] using header
    · simpa only [primitiveArrayLiveValues,SVal.view_array,List.length_map,SVec.length_toList] using small
    · intro index element selected
      simp only [SVec.toList_ofList,primitiveArrayLiveValues,SVal.view_array,primitive_live_roundtrip] at selected
      exact entries index element selected

def primitiveArrayLive {primitive : PrimTy}
    (value : SVal (.ref (.array (.prim primitive)))) : PrimitiveArrayLiveCertificate value :=
  ⟨primitive_live_bound value,primitive_live_copy value,primitive_live_representation value⟩

theorem runtime_primitive_live_success {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (value : SVal (.ref (.array (.prim primitive)))) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (source : Slot) (limit : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store limit (.ref (.array (.prim primitive))) source value)
    (fits : cursor.val + ((primitiveArrayLiveValues value).length + 1) < W) :
    let grown := value.copyStToM heap rfl
    ∃ base' target,
      run runtimeStorageArrayCode (machine.push (.slot source)) = .ok (target.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame
        ⟨cursor.val + ((primitiveArrayLiveValues value).length + 1),fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
      target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) := by
  rw [primitive_live_copy value heap]
  exact runtime_storage_array_success heap primitive (primitiveArrayLiveValues value)
    (primitive_live_bound value) base frame cursor machine source limit allocator
    (primitive_live_representation value machine.store limit source represented) fits

#print axioms primitive_live_roundtrip
#print axioms primitive_live_vector
#print axioms primitive_live_bound
#print axioms primitive_live_copy
#print axioms primitive_live_representation
#print axioms primitiveArrayLive
#print axioms runtime_primitive_live_success
end Solidity.Backend.MemoryCopies
