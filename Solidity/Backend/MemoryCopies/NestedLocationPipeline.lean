import Solidity.Backend.MemoryCopies.NestedLocationPipelineInterface

/-! Composition uses the actual first returned pointer and existing complete
copy certificates. No caller supplies a second count or a capacity assumption. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

private theorem primitive_elements_words {primitive : PrimTy} (values : List primitive.Denote) :
    elementWordCount (SVec.ofList (values.map SVal.prim)) = 0 := by
  induction values with
  | nil => simp only [List.map_nil, SVec.ofList, elementWordCount]
  | cons value values ih =>
    simp only [List.map_cons, SVec.ofList, elementWordCount, liveWordCount, ih, Nat.zero_add]

private theorem nested_elements_words (primitive : PrimTy) (rows : List (PrimitiveStorageRow primitive)) :
    elementWordCount (nestedStorageValues primitive rows) = nestedStorageDemand rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [nestedStorageValues, elementWordCount, liveWordCount, primitiveArrayValue,
      primitive_elements_words, nestedStorageDemand, List.length_map, ih]
    omega

theorem nested_location_memory_demand {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W) :
    let first := (nestedStorageParentValue primitive rows bounded).copyStToM heap rfl
    memoryParentDemand first.heap primitive first.val = nestedStorageParentDemand rows := by
  dsimp only
  rw [memory_parent_demand_snapshot,
    (storageHeapContents (nestedStorageParentValue primitive rows bounded) rfl).contents heap,
    liveWordCount_strip]
  simp only [nestedStorageParentValue, liveWordCount, nested_elements_words, nestedStorageParentDemand]
  omega

theorem nested_location_pipeline_after_first {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W)
    (shadow : SList (.ref (.array (.prim primitive))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot)
    (firstFits : cursor.val + nestedStorageParentDemand rows < W)
    (firstResult : NestedStorageHeaderResult heap primitive rows bounded shadow base frame cursor machine source firstFits)
    (fits : cursor.val + 2 * nestedStorageParentDemand rows < W) :
    NestedLocationPipelineResult heap primitive rows bounded base frame cursor machine source fits := by
  let value := nestedStorageParentValue primitive rows bounded
  let first := value.copyStToM heap rfl
  let snapshot := MVal.copyMToSt first.heap first.val
  let second := snapshot.copyStToM first.heap rfl
  let middle : Fin W := ⟨cursor.val + nestedStorageParentDemand rows, firstFits⟩
  have demand : memoryParentDemand first.heap primitive first.val = nestedStorageParentDemand rows :=
    nested_location_memory_demand heap primitive rows bounded
  have secondFits : middle.val + memoryParentDemand first.heap primitive first.val < W := by
    change cursor.val + nestedStorageParentDemand rows + memoryParentDemand first.heap primitive first.val < W
    rw [demand]
    omega
  obtain ⟨base₁, intermediate, firstRun, firstAllocator, firstRoot, firstExtension, firstShape,
    firstBelow, firstGaps, _, _, firstLength, _, _⟩ := firstResult
  obtain ⟨base₂, target, secondRun, secondAllocator, secondRoot, secondExtension, secondShape,
    secondBelow, secondGaps, secondKeeps, secondFresh, secondLength, secondContents, retained⟩ :=
    nested_memory_parent_success first.heap primitive first.val base₁ frame middle intermediate firstAllocator secondFits
  have cursorEq : (⟨middle.val + memoryParentDemand first.heap primitive first.val, secondFits⟩ : Fin W) =
      ⟨cursor.val + 2 * nestedStorageParentDemand rows, fits⟩ := by
    apply Fin.ext
    change cursor.val + nestedStorageParentDemand rows + memoryParentDemand first.heap primitive first.val =
      cursor.val + 2 * nestedStorageParentDemand rows
    simp only [demand, Nat.two_mul, Nat.add_assoc]
  rw [cursorEq] at secondAllocator
  have firstContents : snapshot = value.strip := (storageHeapContents value rfl).contents heap
  have memoryRun : run (nestedMemoryParentCode primitive) (intermediate.push (.val cursor)) =
      .ok (target.push (.val middle)) 0 := by
    rw [firstRoot] at secondRun
    exact secondRun
  refine ⟨firstFits, base₁, intermediate, secondFits, base₂, target, firstRun, firstAllocator,
    firstRoot, memoryRun, ?_, secondAllocator, secondRoot, ?_,
    BaseExtends.trans first.ext firstExtension secondExtension, ?_, ?_, ?_, ?_,
    Heap.Keeps.trans (SVal.keeps_copyStToM value rfl heap) secondKeeps, secondKeeps,
    Nat.lt_of_lt_of_le first.val.id_lt secondFresh, secondLength.trans firstLength,
    retained.trans firstContents, secondContents⟩
  · rw [nestedLocationPipelineCode, run_append_ok firstRun]
    exact memoryRun
  · exact (secondExtension first.val).trans firstRoot
  · rw [secondShape, firstShape]
  · intro address positive before
    exact (secondBelow address positive (by change address < cursor.val + nestedStorageParentDemand rows; omega)).trans
      (firstBelow address positive before)
  · intro address positive before
    exact secondBelow address positive before
  · intro lo hi gap before
    exact secondGaps lo hi (firstGaps lo hi gap before) (by change hi ≤ cursor.val + nestedStorageParentDemand rows; omega)

theorem nested_location_pipeline_success {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W)
    (shadow : SList (.ref (.array (.prim primitive))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array (.ref (.array (.prim primitive))))) source
      (nestedStorageHeaderValue primitive rows bounded shadow))
    (fits : cursor.val + 2 * nestedStorageParentDemand rows < W) :
    NestedLocationPipelineResult heap primitive rows bounded base frame cursor machine source fits := by
  have firstFits : cursor.val + nestedStorageParentDemand rows < W := by omega
  exact nested_location_pipeline_after_first heap primitive rows bounded shadow base frame cursor machine source firstFits
    (nested_storage_header_success heap primitive rows bounded shadow base frame cursor machine source L allocator represented firstFits) fits

theorem nested_location_pipeline_refusal {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W)
    (shadow : SList (.ref (.array (.prim primitive))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array (.ref (.array (.prim primitive))))) source
      (nestedStorageHeaderValue primitive rows bounded shadow))
    (tooLarge : ¬ cursor.val + 2 * nestedStorageParentDemand rows < W) :
    NestedLocationPipelineRefusal heap primitive rows bounded base frame cursor machine source ∧
      run (nestedLocationPipelineCode primitive) (machine.push (.slot source)) = .revert := by
  let value := nestedStorageParentValue primitive rows bounded
  let first := value.copyStToM heap rfl
  by_cases firstFits : cursor.val + nestedStorageParentDemand rows < W
  · let middle : Fin W := ⟨cursor.val + nestedStorageParentDemand rows, firstFits⟩
    obtain ⟨base₁, intermediate, firstRun, firstAllocator, firstRoot, _, _, _, _, _, _, _, _, _⟩ :=
      nested_storage_header_success heap primitive rows bounded shadow base frame cursor machine source L allocator represented firstFits
    have demand : memoryParentDemand first.heap primitive first.val = nestedStorageParentDemand rows :=
      nested_location_memory_demand heap primitive rows bounded
    have secondFails : ¬ middle.val + memoryParentDemand first.heap primitive first.val < W := by
      change ¬ cursor.val + nestedStorageParentDemand rows + memoryParentDemand first.heap primitive first.val < W
      rw [demand]
      omega
    have secondRun : run (nestedMemoryParentCode primitive) (intermediate.push (.val cursor)) = .revert := by
      rw [← firstRoot]
      exact nested_memory_parent_refusal first.heap primitive first.val base₁ frame middle intermediate firstAllocator secondFails
    have contents : MVal.copyMToSt first.heap first.val = value.strip := (storageHeapContents value rfl).contents heap
    refine ⟨Or.inr ⟨firstFits, base₁, intermediate, firstRun, firstAllocator, firstRoot, contents, tooLarge, secondRun⟩, ?_⟩
    rw [nestedLocationPipelineCode, run_append_ok firstRun, secondRun]
  · have firstRun : run nestedStorageHeaderCode (machine.push (.slot source)) = .revert :=
      nested_storage_header_refusal heap primitive rows bounded shadow base frame cursor machine source L allocator represented firstFits
    exact ⟨Or.inl ⟨firstFits, firstRun⟩, by rw [nestedLocationPipelineCode, run_append_revert firstRun]⟩

theorem nested_location_pipeline_correct {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W)
    (shadow : SList (.ref (.array (.prim primitive))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array (.ref (.array (.prim primitive))))) source
      (nestedStorageHeaderValue primitive rows bounded shadow)) :
    (∃ fits, NestedLocationPipelineResult heap primitive rows bounded base frame cursor machine source fits) ∨
    (NestedLocationPipelineRefusal heap primitive rows bounded base frame cursor machine source ∧
      run (nestedLocationPipelineCode primitive) (machine.push (.slot source)) = .revert) := by
  by_cases fits : cursor.val + 2 * nestedStorageParentDemand rows < W
  · exact .inl ⟨fits, nested_location_pipeline_success heap primitive rows bounded shadow base frame cursor machine source L allocator represented fits⟩
  · exact .inr (nested_location_pipeline_refusal heap primitive rows bounded shadow base frame cursor machine source L allocator represented fits)

def nestedLocationPipeline : NestedLocationPipelineCertificate := ⟨nested_location_pipeline_correct⟩

#print axioms nested_location_memory_demand
#print axioms nested_location_pipeline_after_first
#print axioms nested_location_pipeline_success
#print axioms nested_location_pipeline_refusal
#print axioms nested_location_pipeline_correct
#print axioms nestedLocationPipeline
end Solidity.Backend.MemoryCopies
