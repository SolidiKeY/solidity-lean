import Solidity.Backend.MemoryCopies.StorageMemoryPipelineInterface

/-! The first actual returned pointer feeds the existing checked memory copier.
Both allocation phases and their retained heaps are derived, not premises. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem pipeline_first_length {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W) :
    let first := (primitiveArrayValue primitive values bounded).copyStToM heap rfl
    first.heap.len first.val .dyn = values.length := by
  simpa only [primitiveArrayValue, SVal.view_array, List.length_map] using
    SVal.copyStToM_array_len heap (primitiveArrayValue primitive values bounded) rfl

private theorem pipeline_primitive_strip {primitive : PrimTy} : {n : Nat} →
    (items : SVec (.prim primitive) n) → items.strip = items
  | _, .nil => by rw [SVec.strip_nil]
  | _, .cons (.prim value) rest => by rw [SVec.strip_cons, SVal.strip_prim, pipeline_primitive_strip rest]

theorem pipeline_first_snapshot {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W) :
    let value := primitiveArrayValue primitive values bounded
    let first := value.copyStToM heap rfl
    MVal.copyMToSt first.heap first.val = value := by
  dsimp only
  rw [(storageHeapContents (primitiveArrayValue primitive values bounded) rfl).contents heap,
    primitiveArrayValue, SVal.strip_array, pipeline_primitive_strip]

theorem storage_memory_pipeline_success {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array (.prim primitive))) source (primitiveArrayValue primitive values bounded))
    (fits : cursor.val + 2 * (values.length + 1) < W) :
    StorageMemoryPipelineResult heap primitive values bounded base frame cursor machine source fits := by
  let value := primitiveArrayValue primitive values bounded
  let first := value.copyStToM heap rfl
  let snapshot := MVal.copyMToSt first.heap first.val
  let second := snapshot.copyStToM first.heap rfl
  have firstFits : cursor.val + (values.length + 1) < W := by omega
  let middle : Fin W := ⟨cursor.val + (values.length + 1), firstFits⟩
  have length : first.heap.len first.val .dyn = values.length := pipeline_first_length heap primitive values bounded
  have secondFits : middle.val + (first.heap.len first.val .dyn + 1) < W := by
    change cursor.val + (values.length + 1) + (first.heap.len first.val .dyn + 1) < W
    rw [length]
    omega
  obtain ⟨base₁, intermediate, firstRun, firstAllocator, firstRoot, firstExtension, firstShape, firstBelow, firstGaps⟩ :=
    checked_storage_array_success heap primitive values bounded base frame cursor machine source L allocator represented firstFits
  obtain ⟨base₂, target, secondRun, secondAllocator, secondRoot, secondExtension, secondShape, secondBelow, secondGaps, secondKeeps, fresh⟩ :=
    checked_memory_array_success first.heap primitive first.val base₁ frame middle intermediate firstAllocator secondFits
  have cursorEq : (⟨middle.val + (first.heap.len first.val .dyn + 1), secondFits⟩ : Fin W) =
      ⟨cursor.val + 2 * (values.length + 1), fits⟩ := by
    apply Fin.ext
    change cursor.val + (values.length + 1) + (first.heap.len first.val .dyn + 1) = _
    rw [length]
    change cursor.val + (values.length + 1) + (values.length + 1) = cursor.val + 2 * (values.length + 1)
    omega
  rw [cursorEq] at secondAllocator
  have retained : MVal.copyMToSt second.heap (first.val.wk second.ext) = value.strip :=
    mirror_contents second.heap value (first.val.wk second.ext) H.length
      (SVal.Mirrors.wk secondKeeps value first.val (SVal.mirrors_copyStToM heap value rfl))
  have finalContents : MVal.copyMToSt second.heap second.val = snapshot.strip :=
    (storageHeapContents snapshot rfl).contents first.heap
  refine ⟨firstFits, base₁, intermediate, base₂, target, firstRun, firstAllocator, firstRoot, ?_, secondAllocator,
    secondRoot, ?_, BaseExtends.trans first.ext firstExtension secondExtension, ?_, ?_, ?_, ?_,
    Heap.Keeps.trans (SVal.keeps_copyStToM value rfl heap) secondKeeps, secondKeeps, fresh, retained, finalContents⟩
  · rw [storageMemoryPipelineCode, run_append_ok firstRun]
    rw [firstRoot] at secondRun
    exact secondRun
  · exact (secondExtension first.val).trans firstRoot
  · rw [secondShape, firstShape]
  · intro address positive before
    exact (secondBelow address positive (by change address < cursor.val + (values.length + 1); omega)).trans
      (firstBelow address positive before)
  · intro address positive before
    exact secondBelow address positive before
  · intro lo hi gap before
    exact secondGaps lo hi (firstGaps lo hi gap before) (by change hi ≤ cursor.val + (values.length + 1); omega)

theorem storage_memory_pipeline_refusal {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array (.prim primitive))) source (primitiveArrayValue primitive values bounded))
    (tooLarge : ¬ cursor.val + 2 * (values.length + 1) < W) :
    StorageMemoryPipelineRefusal heap primitive values bounded base frame cursor machine source ∧
      run storageMemoryPipelineCode (machine.push (.slot source)) = .revert := by
  let value := primitiveArrayValue primitive values bounded
  let first := value.copyStToM heap rfl
  by_cases firstFits : cursor.val + (values.length + 1) < W
  · let middle : Fin W := ⟨cursor.val + (values.length + 1), firstFits⟩
    obtain ⟨base₁, intermediate, firstRun, firstAllocator, firstRoot, _, _, _, _⟩ :=
      checked_storage_array_success heap primitive values bounded base frame cursor machine source L allocator represented firstFits
    have length : first.heap.len first.val .dyn = values.length := pipeline_first_length heap primitive values bounded
    have secondFails : ¬ middle.val + (first.heap.len first.val .dyn + 1) < W := by
      change ¬ cursor.val + (values.length + 1) + (first.heap.len first.val .dyn + 1) < W
      rw [length]
      omega
    have secondRun : run checkedMemoryArrayCode (intermediate.push (.val cursor)) = .revert := by
      rw [← firstRoot, checked_memory_array_run first.heap primitive first.val base₁ frame middle intermediate firstAllocator, if_neg secondFails]
    have contents : MVal.copyMToSt first.heap first.val = value.strip := (storageHeapContents value rfl).contents heap
    refine ⟨Or.inr ⟨firstFits, base₁, intermediate, firstRun, firstAllocator, firstRoot, contents, tooLarge, secondRun⟩, ?_⟩
    rw [storageMemoryPipelineCode, run_append_ok firstRun, secondRun]
  · have firstRun : run checkedStorageArrayCode (machine.push (.slot source)) = .revert := by
      rw [checked_storage_array_run heap primitive values bounded base frame cursor machine source L allocator represented, if_neg firstFits]
    exact ⟨Or.inl ⟨firstFits, firstRun⟩, run_append_revert firstRun⟩

theorem storage_memory_pipeline_correct {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array (.prim primitive))) source (primitiveArrayValue primitive values bounded)) :
    (∃ fits, StorageMemoryPipelineResult heap primitive values bounded base frame cursor machine source fits) ∨
    (StorageMemoryPipelineRefusal heap primitive values bounded base frame cursor machine source ∧
      run storageMemoryPipelineCode (machine.push (.slot source)) = .revert) := by
  by_cases fits : cursor.val + 2 * (values.length + 1) < W
  · exact Or.inl ⟨fits, storage_memory_pipeline_success heap primitive values bounded base frame cursor machine source L allocator represented fits⟩
  · exact Or.inr (storage_memory_pipeline_refusal heap primitive values bounded base frame cursor machine source L allocator represented fits)

def storageMemoryPipeline : StorageMemoryPipelineCertificate := ⟨storage_memory_pipeline_correct⟩

#print axioms pipeline_first_snapshot
#print axioms pipeline_first_length
#print axioms storage_memory_pipeline_success
#print axioms storage_memory_pipeline_refusal
#print axioms storage_memory_pipeline_correct
#print axioms storageMemoryPipeline
end Solidity.Backend.MemoryCopies
