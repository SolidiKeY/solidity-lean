import Solidity.Backend.MemoryCopies.NestedStorageLiveInterface

/-! Intrinsic live normalization preserves the complete original copy before
reusing the existing checked dynamic outer-header/traversal execution. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem nested_storage_live_bound {primitive : PrimTy}
    (value : SVal (.ref (.array (.ref (.array (.prim primitive)))))) :
    (nestedStorageLiveRows value).length < W := by
  cases value with
  | array elements shadow bounded =>
    simpa only [nestedStorageLiveRows,SVal.view_array,List.length_map,SVec.length_toList] using bounded

theorem nested_storage_live_rows {primitive : PrimTy}
    (value : SVal (.ref (.array (.ref (.array (.prim primitive)))))) :
    (nestedStorageLiveCanonical value).view.elems.toList =
      (nestedStorageLiveRows value).map (fun row => primitiveArrayValue primitive row.val row.property) := by
  cases value with
  | array elements shadow bounded =>
    simp only [nestedStorageLiveCanonical,nestedStorageLiveRows,SVal.view_array,SVec.toList_ofLen,
      List.map_map,Function.comp_def,fixedReferenceLiveChild,fixedReferenceLiveRow]
    rfl

theorem nested_storage_live_copy {H : HTy} {primitive : PrimTy}
    (value : SVal (.ref (.array (.ref (.array (.prim primitive)))))) (heap : Heap H) :
    value.copyStToM heap rfl = (nestedStorageLiveCanonical value).copyStToM heap rfl := by
  cases value with
  | array elements shadow bounded =>
    simp only [nestedStorageLiveCanonical,SVal.copyStToM_array]
    rw [fixed_reference_live_vector_copy elements heap]

theorem nested_storage_live_representation {primitive : PrimTy}
    (value : SVal (.ref (.array (.ref (.array (.prim primitive)))))) (store : WordStore) (L : Nat) (source : Slot)
    (represented : ReprAt store L (.ref (.array (.ref (.array (.prim primitive))))) source value) :
    ReprAt store L (.ref (.array (.ref (.array (.prim primitive))))) source (nestedStorageLiveCanonical value) := by
  cases represented with
  | @array _ count _ elements shadow bounded header small entries =>
    refine .array header small ?_
    intro index item selected
    simp only [SVec.toList_ofLen,List.getElem?_map] at selected
    cases chosen : elements.toList[index]? with
    | none => simp only [chosen,Option.map_none] at selected; cases selected
    | some child =>
      simp only [chosen,Option.map_some] at selected
      cases selected
      exact primitive_live_representation child store L _ (entries index child chosen)

theorem nested_storage_live_correct {H : HTy} {primitive : PrimTy} (heap : Heap H)
    (value : SVal (.ref (.array (.ref (.array (.prim primitive))))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array (.ref (.array (.prim primitive))))) source value) :
    (∃ fits, NestedStorageLiveResult heap value base frame cursor machine source fits) ∨
    (¬ cursor.val + nestedStorageParentDemand (nestedStorageLiveRows value) < W ∧
      run nestedStorageHeaderCode (machine.push (.slot source)) = .revert) := by
  have canonicalRepr : ReprAt machine.store L (.ref (.array (.ref (.array (.prim primitive))))) source
      (nestedStorageLiveCanonical value) := nested_storage_live_representation value machine.store L source represented
  cases value with
  | @array _ count elements shadow bounded =>
    simp only [NestedStorageLiveResult]
    have countEq : (nestedStorageLiveRows (.array elements shadow bounded)).length = count := by
      simp only [nestedStorageLiveRows,SVal.view_array,List.length_map,SVec.length_toList]
    generalize rowsEq : nestedStorageLiveRows (.array elements shadow bounded) = rows at *
    subst count
    have canonical : nestedStorageLiveCanonical (.array elements shadow bounded) = nestedStorageParentValue primitive rows bounded := by
      apply congrArg (fun values : SVec (.ref (.array (.prim primitive))) rows.length => SVal.array values .nil bounded)
      apply SVec.eq_of_toList_eq
      change (nestedStorageLiveCanonical (.array elements shadow bounded)).view.elems.toList = (nestedStorageValues primitive rows).toList
      rw [nested_storage_live_rows,rowsEq,nested_storage_header_values]
    have sourceRepr : ReprAt machine.store L (.ref (.array (.ref (.array (.prim primitive))))) source
        (nestedStorageHeaderValue primitive rows bounded .nil) := by
      change ReprAt _ _ _ _ (nestedStorageParentValue primitive rows bounded)
      rw [← canonical]
      exact canonicalRepr
    have copying : (SVal.array elements shadow bounded).copyStToM heap rfl =
        (nestedStorageParentValue primitive rows bounded).copyStToM heap rfl := by
      rw [nested_storage_live_copy,canonical]
    rcases nested_storage_header_correct heap primitive rows bounded .nil base frame cursor machine source L allocator sourceRepr with success | refusal
    · obtain ⟨fits,base',target,ran,allocated,root,extension,shape,below,gaps,keeps,fresh,length,contents,canonicalCopy⟩ := success
      left
      refine ⟨fits,base',target,ran,?_,?_,extension,shape,below,?_,SVal.keeps_copyStToM _ rfl heap,?_,?_,?_⟩
      · rw [copying]; exact allocated
      · rw [copying]; exact root
      · rw [copying]; exact gaps
      · rw [copying]; exact fresh
      · rw [copying]; exact length
      · exact (storageHeapContents (SVal.array elements shadow bounded) rfl).contents heap
    · exact .inr refusal

def nestedStorageLive : NestedStorageLiveCertificate :=
  ⟨nested_storage_live_bound,nested_storage_live_copy,nested_storage_live_representation,nested_storage_live_correct⟩

/--
info: 'Solidity.Backend.MemoryCopies.nested_storage_live_bound' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms nested_storage_live_bound
/--
info: 'Solidity.Backend.MemoryCopies.nested_storage_live_rows' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms nested_storage_live_rows
/--
info: 'Solidity.Backend.MemoryCopies.nested_storage_live_copy' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms nested_storage_live_copy
/--
info: 'Solidity.Backend.MemoryCopies.nested_storage_live_representation' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms nested_storage_live_representation
/--
info: 'Solidity.Backend.MemoryCopies.nested_storage_live_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nested_storage_live_correct
/--
info: 'Solidity.Backend.MemoryCopies.nestedStorageLive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nestedStorageLive
end Solidity.Backend.MemoryCopies
