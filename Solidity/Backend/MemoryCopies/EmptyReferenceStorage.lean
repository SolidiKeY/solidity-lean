import Solidity.Backend.MemoryCopies.EmptyReferenceStorageInterface

/-! The existing header-driven runtime loop performs zero child turns. Typed
storage representation supplies the actual header; no desired run is assumed. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem empty_stored_copy {H : HTy} (heap : Heap H) (element : Ty) (shadow : SList element)
    (memory : (Ty.ref (.array element)).mapFree = true) :
    (emptyStoredArray element shadow).copyStToM heap memory = heap.allocDefault (.array element) memory := by
  rw [emptyStoredArray, Heap.allocDefault, SVal.dflt_array, SVal.copyStToM_array, SVec.copyStToM_nil]
  simp only [SVal.copyStToM_array, SVec.copyStToM_nil]

theorem empty_storage_header (machine : Machine) (source : Slot) (L : Nat)
    (element : Ty) (shadow : SList element)
    (represented : ReprAt machine.store L (.ref (.array element)) source (emptyStoredArray element shadow)) :
    machine.store.cells source = wmod 0 := by
  cases represented with
  | array header bounded children =>
    apply Fin.ext
    exact header

theorem empty_default_facts {H : HTy} (heap : Heap H) (element : Ty)
    (memory : (Ty.ref (.array element)).mapFree = true) :
    (heap.allocDefault (.array element) memory).val.id = H.length ∧
    (heap.allocDefault (.array element) memory).heap.len (heap.allocDefault (.array element) memory).val .dyn = 0 := by
  rw [Objects.emptyArray_copy]
  constructor
  · rfl
  · simp only [Grown.alloc, Heap.len, Heap.get_alloc, MObj.elems_dyn, MObj.wk,
      Objects.emptyArray, List.map_nil, List.length_nil]

theorem empty_storage_zero_run (machine : Machine) (cursor : Fin W) (source : Slot)
    (cell : machine.mem 0 = .val cursor) (header : machine.store.cells source = wmod 0)
    (fits : cursor.val + 1 < W) :
    run runtimeStorageArrayCode (machine.push (.slot source)) =
      .ok ((allocateMachine machine cursor (wmod 0)).push (.val cursor)) 0 := by
  have contents : ∀ (index : Nat) (word : Word), ([] : List Word)[index]? = some word →
      .val (machine.store.cells ((Slot.data source 0).add index)) = word := by
    intro index word selected
    simp only [List.getElem?_nil, reduceCtorEq] at selected
  simpa only [List.length_nil, arrayWordsMachine] using
    runtime_storage_array_run machine cursor source [] W_pos cell header contents
      (by simpa only [List.length_nil, Nat.add_zero] using fits)

theorem empty_storage_transport (machine : Machine) (cursor : Fin W) (source : Slot)
    (element : Ty) (memory : (Ty.ref (.array element)).mapFree = true)
    (cell : machine.mem 0 = .val cursor) (header : machine.store.cells source = wmod 0)
    (fits : cursor.val + 1 < W) :
    run runtimeStorageArrayCode (machine.push (.slot source)) =
      run (Objects.DefaultBuilder.empty element memory).code machine := by
  have contents : ∀ (index : Nat) (word : Word), ([] : List Word)[index]? = some word →
      .val (machine.store.cells ((Slot.data source 0).add index)) = word := by
    intro index word selected
    simp only [List.getElem?_nil, reduceCtorEq] at selected
  have transport : run runtimeStorageArrayCode (machine.push (.slot source)) = run (primitiveArrayCode []) machine :=
    runtime_storage_array_transport machine cursor source [] W_pos cell header contents (by simpa only [List.length_nil, Nat.add_zero] using fits)
  simpa only [primitiveArrayCode, List.length_nil, arrayWordsCode, List.append_nil, Objects.DefaultBuilder.empty] using transport

theorem empty_storage_runtime {H : HTy} (heap : Heap H) (element : Ty) (shadow : SList element)
    (memory : (Ty.ref (.array element)).mapFree = true) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array element)) source (emptyStoredArray element shadow))
    (fits : cursor.val + 1 < W) :
    EmptyStorageCopyResult runtimeStorageArrayCode heap element shadow memory base frame cursor machine source fits := by
  obtain ⟨base', target, execution, allocated, root, extension, shape, below, gaps⟩ :=
    (Objects.DefaultBuilder.empty element memory).correct heap base frame cursor machine allocator fits
  rw [EmptyStorageCopyResult, empty_stored_copy]
  refine ⟨base', target, ?_, allocated, root, extension, shape, below, gaps,
    (empty_default_facts heap element memory).1, (empty_default_facts heap element memory).2⟩
  rw [empty_storage_transport machine cursor source element memory allocator.free.cell
    (empty_storage_header machine source L element shadow represented) fits]
  exact execution

theorem empty_checked_storage_run (machine : Machine) (cursor : Fin W) (source : Slot)
    (cell : machine.mem 0 = .val cursor) (header : machine.store.cells source = wmod 0) :
    run checkedStorageArrayCode (machine.push (.slot source)) =
      if cursor.val + 1 < W then run runtimeStorageArrayCode (machine.push (.slot source)) else .revert := by
  have guard : run storageArrayCapacityGuard (machine.push (.slot source)) =
      if cursor.val + 1 < W then .ok (machine.push (.slot source)) 0 else .revert := by
    simpa only [show (wmod 0).val = 0 from rfl, Nat.zero_add] using
      storage_capacity_guard_run machine source cursor (wmod 0) cell header
  rw [checkedStorageArrayCode]
  by_cases fits : cursor.val + 1 < W
  · rw [if_pos fits] at guard
    rw [run_append_ok guard, if_pos fits]
  · rw [if_neg fits] at guard
    rw [run_append_revert guard, if_neg fits]

theorem empty_checked_storage_success {H : HTy} (heap : Heap H) (element : Ty) (shadow : SList element)
    (memory : (Ty.ref (.array element)).mapFree = true) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array element)) source (emptyStoredArray element shadow))
    (fits : cursor.val + 1 < W) :
    EmptyStorageCopyResult checkedStorageArrayCode heap element shadow memory base frame cursor machine source fits := by
  have execution : run checkedStorageArrayCode (machine.push (.slot source)) =
      run runtimeStorageArrayCode (machine.push (.slot source)) := by
    rw [empty_checked_storage_run machine cursor source allocator.free.cell
      (empty_storage_header machine source L element shadow represented), if_pos fits]
  unfold EmptyStorageCopyResult
  rw [execution]
  exact empty_storage_runtime heap element shadow memory base frame cursor machine source L allocator represented fits

theorem empty_checked_storage {H : HTy} (heap : Heap H) (element : Ty) (shadow : SList element)
    (memory : (Ty.ref (.array element)).mapFree = true) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array element)) source (emptyStoredArray element shadow)) :
    (∃ fits, EmptyStorageCopyResult checkedStorageArrayCode heap element shadow memory base frame cursor machine source fits) ∨
    (¬ cursor.val + 1 < W ∧ run checkedStorageArrayCode (machine.push (.slot source)) = .revert) := by
  by_cases fits : cursor.val + 1 < W
  · exact .inl ⟨fits, empty_checked_storage_success heap element shadow memory base frame cursor machine source L allocator represented fits⟩
  · refine .inr ⟨fits, ?_⟩
    rw [empty_checked_storage_run machine cursor source allocator.free.cell
      (empty_storage_header machine source L element shadow represented), if_neg fits]

def emptyStorageCopy : EmptyStorageCopyCertificate := ⟨empty_storage_runtime, empty_checked_storage⟩

#print axioms empty_stored_copy
#print axioms empty_storage_header
#print axioms empty_default_facts
#print axioms empty_storage_zero_run
#print axioms empty_storage_transport
#print axioms empty_storage_runtime
#print axioms empty_checked_storage_run
#print axioms empty_checked_storage_success
#print axioms empty_checked_storage
#print axioms emptyStorageCopy
end Solidity.Backend.MemoryCopies
