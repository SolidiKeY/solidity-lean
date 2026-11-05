import Solidity.Backend.MemoryCopies.EmptyReferenceMemoryInterface

/-! Reuse actual zero-turn memory code and the complete empty allocator.
Source bounds come from ownership, rather than new child or room premises. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem empty_memory_snapshot {H : HTy} (heap : Heap H) (element : Ty)
    (input : HRef H (.array element)) (empty : heap.len input .dyn = 0) :
    MVal.copyMToSt heap (T := .ref (.array element)) input = SVal.dflt (.ref (.array element)) := by
  have elements : (heap.get input).val = [] := List.length_eq_zero_iff.mp (by
    simpa only [Heap.len, MObj.elems_dyn] using empty)
  have object : heap.get input = Objects.emptyArray element := Subtype.ext elements
  let visit : MVal H element → SVal element :=
    MVal.copyAt heap (rankBound (.ref (.array element)))
      (MVal.copyBelow heap (rankBound (.ref (.array element)))) element
      (by simpa only [Semantics.tyRank] using Nat.lt_succ_of_le (tyRank_le_rankBound (.ref (.array element))))
  rw [SVal.dflt_array]
  unfold MVal.copyMToSt
  rw [MVal.copyBelow, MVal.copyAt, MVal.copyRefAt]
  simpa only [visit, Objects.emptyArray, List.map_nil, SVec.ofList] using
    (congrArg (fun value : {values : List (MVal H element) // values.length < 2 ^ 256} =>
      SVal.array (SVec.ofList (value.val.map visit)) SList.nil
        (by simpa only [List.length_map] using value.property)) object)

theorem empty_memory_header {H : HTy} (heap : Heap H) (element : Ty)
    (input : HRef H (.array element)) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (empty : heap.len input .dyn = 0)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    machine.mem (base input.id).val = .val (wmod 0) := by
  rw [(allocator.heap.arrays .dyn input).length rfl, empty]

theorem empty_memory_bounds {H : HTy} (heap : Heap H) (element : Ty)
    (input : HRef H (.array element)) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (empty : heap.len input .dyn = 0)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    0 < (base input.id).val ∧ (base input.id).val + 1 ≤ cursor.val := by
  refine ⟨Nat.lt_of_lt_of_le allocator.free.reserved (allocator.heap.owner.above input), ?_⟩
  have live : (base input.id).val + Objects.cells heap input ≤ cursor.val := allocator.live input
  simpa only [Objects.cells, empty, Nat.add_zero] using live

theorem empty_memory_zero_run (machine : Machine) (cursor source : Fin W)
    (cell : machine.mem 0 = .val cursor) (header : machine.mem source.val = .val (wmod 0))
    (positive : 0 < source.val) (sourceRoom : source.val + 1 ≤ cursor.val)
    (fits : cursor.val + 1 < W) :
    run runtimeMemoryArrayCode (machine.push (.val source)) =
      .ok ((allocateMachine machine cursor (wmod 0)).push (.val cursor)) 0 := by
  have contents : ∀ (index : Nat) (word : Word), ([] : List Word)[index]? = some word →
      machine.mem (source.val + 1 + index) = word := by
    intro index word selected
    simp only [List.getElem?_nil, reduceCtorEq] at selected
  simpa only [List.length_nil, arrayWordsMachine] using
    runtime_memory_array_run machine cursor source [] W_pos cell header positive
      (by simpa only [List.length_nil, Nat.add_zero] using sourceRoom) contents
      (by simpa only [List.length_nil, Nat.add_zero] using fits)

theorem empty_memory_transport (machine : Machine) (cursor source : Fin W) (element : Ty)
    (memory : (Ty.ref (.array element)).mapFree = true)
    (cell : machine.mem 0 = .val cursor) (header : machine.mem source.val = .val (wmod 0))
    (positive : 0 < source.val) (sourceRoom : source.val + 1 ≤ cursor.val)
    (fits : cursor.val + 1 < W) :
    run runtimeMemoryArrayCode (machine.push (.val source)) =
      run (Objects.DefaultBuilder.empty element memory).code machine := by
  have allocated : run (Objects.DefaultBuilder.empty element memory).code machine =
      .ok ((allocateMachine machine cursor (wmod 0)).push (.val cursor)) 0 := by
    change run ([.push (.val (wmod 0))] ++ allocateArrayCode) machine = _
    rw [run_append_ok (m' := machine.push (.val (wmod 0))) rfl]
    exact allocateArray_run machine cursor (wmod 0) cell
  exact (empty_memory_zero_run machine cursor source cell header positive sourceRoom fits).trans allocated.symm

theorem empty_memory_runtime {H : HTy} (heap : Heap H) (element : Ty) (input : HRef H (.array element))
    (memory : (Ty.ref (.array element)).mapFree = true) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine) (empty : heap.len input .dyn = 0)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) (fits : cursor.val + 1 < W) :
    EmptyMemoryCopyResult runtimeMemoryArrayCode heap element input memory base frame cursor machine fits := by
  obtain ⟨base', target, execution, allocated, root, extension, shape, below, gaps⟩ :=
    (Objects.DefaultBuilder.empty element memory).correct heap base frame cursor machine allocator fits
  have bounds : 0 < (base input.id).val ∧ (base input.id).val + 1 ≤ cursor.val :=
    empty_memory_bounds heap element input base frame cursor machine empty allocator
  have copied : (MVal.copyMToSt heap (T := .ref (.array element)) input).copyStToM heap memory =
      heap.allocDefault (.array element) memory :=
    congrArg (fun value : SVal (.ref (.array element)) => value.copyStToM heap memory)
      (empty_memory_snapshot heap element input empty)
  unfold EmptyMemoryCopyResult
  refine ⟨base', target, ?_, ?_, ?_, extension, shape, below, ?_,
    SVal.keeps_copyStToM _ memory heap, ?_, ?_, ?_⟩
  · rw [empty_memory_transport machine cursor (base input.id) element memory allocator.free.cell
      (empty_memory_header heap element input base frame cursor machine empty allocator) bounds.1 bounds.2 fits]
    exact execution
  · rw [copied]
    exact allocated
  · rw [copied]
    exact root
  · intro lo hi gap belowCursor
    rw [copied]
    exact gaps lo hi gap belowCursor
  · rw [copied, (empty_default_facts heap element memory).1]
    exact input.id_lt
  · rw [copied]
    exact (empty_default_facts heap element memory).1
  · rw [copied]
    exact (empty_default_facts heap element memory).2

theorem empty_checked_memory_run (machine : Machine) (source cursor : Fin W)
    (cell : machine.mem 0 = .val cursor) (header : machine.mem source.val = .val (wmod 0)) :
    run checkedMemoryArrayCode (machine.push (.val source)) =
      if cursor.val + 1 < W then run runtimeMemoryArrayCode (machine.push (.val source)) else .revert := by
  have guard : run memoryArrayCapacityGuard (machine.push (.val source)) =
      if cursor.val + 1 < W then .ok (machine.push (.val source)) 0 else .revert := by
    simpa only [show (wmod 0).val = 0 from rfl, Nat.zero_add] using
      memory_capacity_guard_run machine source cursor (wmod 0) cell header
  rw [checkedMemoryArrayCode]
  by_cases fits : cursor.val + 1 < W
  · rw [if_pos fits] at guard
    rw [run_append_ok guard, if_pos fits]
  · rw [if_neg fits] at guard
    rw [run_append_revert guard, if_neg fits]

theorem empty_checked_memory_success {H : HTy} (heap : Heap H) (element : Ty) (input : HRef H (.array element))
    (memory : (Ty.ref (.array element)).mapFree = true) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine) (empty : heap.len input .dyn = 0)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) (fits : cursor.val + 1 < W) :
    EmptyMemoryCopyResult checkedMemoryArrayCode heap element input memory base frame cursor machine fits := by
  have execution : run checkedMemoryArrayCode (machine.push (.val (base input.id))) =
      run runtimeMemoryArrayCode (machine.push (.val (base input.id))) := by
    rw [empty_checked_memory_run machine (base input.id) cursor allocator.free.cell
      (empty_memory_header heap element input base frame cursor machine empty allocator), if_pos fits]
  unfold EmptyMemoryCopyResult
  rw [execution]
  exact empty_memory_runtime heap element input memory base frame cursor machine empty allocator fits

theorem empty_checked_memory {H : HTy} (heap : Heap H) (element : Ty) (input : HRef H (.array element))
    (memory : (Ty.ref (.array element)).mapFree = true) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine) (empty : heap.len input .dyn = 0)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    (∃ fits, EmptyMemoryCopyResult checkedMemoryArrayCode heap element input memory base frame cursor machine fits) ∨
    (¬ cursor.val + 1 < W ∧ run checkedMemoryArrayCode (machine.push (.val (base input.id))) = .revert) := by
  by_cases fits : cursor.val + 1 < W
  · exact .inl ⟨fits, empty_checked_memory_success heap element input memory base frame cursor machine empty allocator fits⟩
  · refine .inr ⟨fits, ?_⟩
    rw [empty_checked_memory_run machine (base input.id) cursor allocator.free.cell
      (empty_memory_header heap element input base frame cursor machine empty allocator), if_neg fits]

def emptyMemoryCopy : EmptyMemoryCopyCertificate := ⟨empty_memory_runtime, empty_checked_memory⟩

#print axioms empty_memory_snapshot
#print axioms empty_memory_header
#print axioms empty_memory_bounds
#print axioms empty_memory_zero_run
#print axioms empty_memory_transport
#print axioms empty_memory_runtime
#print axioms empty_checked_memory_run
#print axioms empty_checked_memory_success
#print axioms empty_checked_memory
#print axioms emptyMemoryCopy
end Solidity.Backend.MemoryCopies
