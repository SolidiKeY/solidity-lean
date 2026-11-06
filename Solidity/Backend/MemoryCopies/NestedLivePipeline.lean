import Solidity.Backend.MemoryCopies.NestedLivePipelineInterface

/-! Exact whole-copy and strip equalities transport the existing checked
pipeline to original storage values, without discarding live data or assuming
row-normalization from callers. No runtime compiler or traversal is duplicated. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

private def PipelineResultCore {H : HTy} (heap : Heap H) {primitive : PrimTy}
    (first : Grown H (MVal · (.ref (.array (.ref (.array (.prim primitive)))))))
    (contents : SVal (.ref (.array (.ref (.array (.prim primitive)))))) (count demand : Nat)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot)
    (fits : cursor.val + 2 * demand < W) : Prop :=
  let snapshot := MVal.copyMToSt first.heap first.val
  let second := snapshot.copyStToM first.heap rfl
  ∃ (firstFits : cursor.val + demand < W),
    ∃ (base₁ : Nat → Fin W) (intermediate : Machine)
      (_secondFits : cursor.val + demand + memoryParentDemand first.heap primitive first.val < W)
      (base₂ : Nat → Fin W) (target : Machine),
    run nestedStorageHeaderCode (machine.push (.slot source)) = .ok (intermediate.push (.val cursor)) 0 ∧
    Objects.AllocatorRepr first.heap base₁ frame ⟨cursor.val + demand, firstFits⟩ intermediate ∧
    base₁ first.val.id = cursor ∧
    run (nestedMemoryParentCode primitive) (intermediate.push (.val cursor)) =
      .ok (target.push (.val ⟨cursor.val + demand, firstFits⟩)) 0 ∧
    run (nestedLocationPipelineCode primitive) (machine.push (.slot source)) =
      .ok (target.push (.val ⟨cursor.val + demand, firstFits⟩)) 0 ∧
    Objects.AllocatorRepr second.heap base₂ frame ⟨cursor.val + 2 * demand, fits⟩ target ∧
    base₂ second.val.id = ⟨cursor.val + demand, firstFits⟩ ∧
    base₂ (first.val.wk second.ext).id = cursor ∧
    BaseExtends H base base₂ ∧ target = {machine with mem := target.mem} ∧
    (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
    (∀ address, 0 < address → address < cursor.val + demand →
      target.mem address = intermediate.mem address) ∧
    (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap second.heap base₂ lo hi) ∧
    Heap.Keeps (first.ext.trans second.ext) heap second.heap ∧ Heap.Keeps second.ext first.heap second.heap ∧
    first.val.id < second.val.id ∧ second.heap.len second.val .dyn = count ∧
    MVal.copyMToSt second.heap (first.val.wk second.ext) = contents ∧
    MVal.copyMToSt second.heap second.val = snapshot.strip

theorem nested_live_pipeline_correct {H : HTy} (heap : Heap H) {primitive : PrimTy}
    (value : SVal (.ref (.array (.ref (.array (.prim primitive))))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array (.ref (.array (.prim primitive))))) source value) :
    (∃ fits, NestedLivePipelineResult heap value base frame cursor machine source fits) ∨
    (NestedLivePipelineRefusal heap value base frame cursor machine source ∧
      run (nestedLocationPipelineCode primitive) (machine.push (.slot source)) = .revert) := by
  have canonicalRepr : ReprAt machine.store L (.ref (.array (.ref (.array (.prim primitive))))) source
      (nestedStorageLiveCanonical value) := nested_storage_live_representation value machine.store L source represented
  cases value with
  | @array _ count elements shadow bounded =>
    simp only [NestedLivePipelineResult,NestedLivePipelineRefusal]
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
    have oldContents :
        MVal.copyMToSt ((SVal.array elements shadow bounded).copyStToM heap rfl).heap
          ((SVal.array elements shadow bounded).copyStToM heap rfl).val = (SVal.array elements shadow bounded).strip := (storageHeapContents (SVal.array elements shadow bounded) rfl).contents heap
    rw [copying] at oldContents
    have canonicalContents :
        MVal.copyMToSt ((nestedStorageParentValue primitive rows bounded).copyStToM heap rfl).heap
          ((nestedStorageParentValue primitive rows bounded).copyStToM heap rfl).val = (nestedStorageParentValue primitive rows bounded).strip := (storageHeapContents (nestedStorageParentValue primitive rows bounded) rfl).contents heap
    have stripped : (SVal.array elements shadow bounded).strip = (nestedStorageParentValue primitive rows bounded).strip :=
      oldContents.symm.trans canonicalContents
    rcases nested_location_pipeline_correct heap primitive rows bounded .nil base frame cursor machine source L allocator sourceRepr with success | refusal
    · left
      obtain ⟨fits,result⟩ := success
      refine ⟨fits,?_⟩
      change PipelineResultCore heap ((SVal.array elements shadow bounded).copyStToM heap rfl)
        (SVal.array elements shadow bounded).strip rows.length (nestedStorageParentDemand rows) base frame cursor machine source fits
      rw [copying,stripped]
      exact result
    · right
      rcases refusal with ⟨phases,ran⟩
      refine ⟨?_,ran⟩
      rw [copying]
      simpa only [NestedLocationPipelineRefusal,stripped] using phases

def nestedLivePipeline : NestedLivePipelineCertificate := ⟨nested_live_pipeline_correct⟩

/--
info: 'Solidity.Backend.MemoryCopies.nested_live_pipeline_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nested_live_pipeline_correct
/--
info: 'Solidity.Backend.MemoryCopies.nestedLivePipeline' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nestedLivePipeline

end Solidity.Backend.MemoryCopies
