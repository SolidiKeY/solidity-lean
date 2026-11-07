import Solidity.Backend.MemoryCopies.NestedStorageHeaderInterface

/-! The runtime header and all child representations come from one outer
storage representation. The parent copy is reused without new assumptions. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem nested_storage_header_values (primitive : PrimTy) (rows : List (PrimitiveStorageRow primitive)) :
    (nestedStorageValues primitive rows).toList = rows.map (fun row => primitiveArrayValue primitive row.val row.property) := by
  induction rows with
  | nil => simp only [nestedStorageValues, SVec.toList_nil, List.map_nil]
  | cons row rows ih =>
    simp only [nestedStorageValues, SVec.toList_cons, List.map_cons, ih]

theorem nested_storage_header_copy {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W)
    (shadow : SList (.ref (.array (.prim primitive)))) :
    (nestedStorageHeaderValue primitive rows bounded shadow).copyStToM heap rfl =
      (nestedStorageParentValue primitive rows bounded).copyStToM heap rfl := by
  simp only [nestedStorageHeaderValue, nestedStorageParentValue, SVal.copyStToM_array]

theorem nested_storage_header_inputs (primitive : PrimTy) (rows : List (PrimitiveStorageRow primitive))
    (bounded : rows.length < W) (shadow : SList (.ref (.array (.prim primitive))))
    (machine : Machine) (source : Slot) (L : Nat)
    (represented : ReprAt machine.store L (.ref (.array (.ref (.array (.prim primitive))))) source
      (nestedStorageHeaderValue primitive rows bounded shadow)) :
    machine.store.cells source = wmod rows.length ∧
      NestedStorageRowsRepr primitive rows machine (.data source 0) 0 L := by
  cases represented with
  | array header limit elements =>
    refine ⟨?_, ?_⟩
    · apply Fin.ext
      have actual : (machine.store.cells source).val = rows.length := header
      exact actual.trans (Nat.mod_eq_of_lt bounded).symm
    · intro offset row chosen
      have selected : (nestedStorageValues primitive rows).toList[offset]? =
          some (primitiveArrayValue primitive row.val row.property) := by
        rw [nested_storage_header_values, List.getElem?_map, chosen]
        rfl
      have child : ReprAt machine.store L (.ref (.array (.prim primitive)))
          (.data source (offset * size (.ref (.array (.prim primitive)))))
          (primitiveArrayValue primitive row.val row.property) := elements offset _ selected
      simpa only [size_array, Nat.mul_one, Slot.add, Nat.zero_add] using child

theorem nested_storage_header_enter (machine : Machine) (source : Slot) (size : Fin W)
    (header : machine.store.cells source = size) :
    run nestedStorageHeaderEnter (machine.push (.slot source)) =
      .ok ((machine.push (.slot (.data source 0))).push (.val size)) 0 := by
  simp only [nestedStorageHeaderEnter, run, exec_cons_zero, Instr.step, Machine.next, Machine.push,
    Out.ok_bind, List.getElem?_cons_zero, List.set_cons_zero, exec_nil, Nat.reduceSub, header]

theorem nested_storage_header_run (primitive : PrimTy) (rows : List (PrimitiveStorageRow primitive))
    (bounded : rows.length < W) (shadow : SList (.ref (.array (.prim primitive))))
    (machine : Machine) (source : Slot) (L : Nat)
    (represented : ReprAt machine.store L (.ref (.array (.ref (.array (.prim primitive))))) source
      (nestedStorageHeaderValue primitive rows bounded shadow)) :
    run nestedStorageHeaderCode (machine.push (.slot source)) =
      run nestedStorageParentCode ((machine.push (.slot (.data source 0))).push (.val (wmod rows.length))) := by
  have header : machine.store.cells source = wmod rows.length :=
    (nested_storage_header_inputs primitive rows bounded shadow machine source L represented).1
  rw [nestedStorageHeaderCode, run_append_ok (nested_storage_header_enter machine source _ header)]

theorem nested_storage_header_success {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W)
    (shadow : SList (.ref (.array (.prim primitive))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array (.ref (.array (.prim primitive))))) source
      (nestedStorageHeaderValue primitive rows bounded shadow))
    (fits : cursor.val + nestedStorageParentDemand rows < W) :
    NestedStorageHeaderResult heap primitive rows bounded shadow base frame cursor machine source fits := by
  have inputs : machine.store.cells source = wmod rows.length ∧
      NestedStorageRowsRepr primitive rows machine (.data source 0) 0 L :=
    nested_storage_header_inputs primitive rows bounded shadow machine source L represented
  obtain ⟨base', target, ran, allocated, root, extension, shape, below, gaps, keeps, fresh, length, mirror⟩ :=
    nested_storage_parent_success heap primitive rows bounded base frame cursor machine (.data source 0) (wmod rows.length) L
      allocator (Nat.mod_eq_of_lt bounded).symm inputs.2 fits
  refine ⟨base', target, ?_, allocated, root, extension, shape, below, gaps, keeps, fresh, length, mirror,
    nested_storage_header_copy heap primitive rows bounded shadow⟩
  rw [nested_storage_header_run primitive rows bounded shadow machine source L represented]
  exact ran

theorem nested_storage_header_refusal {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W)
    (shadow : SList (.ref (.array (.prim primitive))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array (.ref (.array (.prim primitive))))) source
      (nestedStorageHeaderValue primitive rows bounded shadow))
    (tooLarge : ¬ cursor.val + nestedStorageParentDemand rows < W) :
    run nestedStorageHeaderCode (machine.push (.slot source)) = .revert := by
  have inputs : machine.store.cells source = wmod rows.length ∧
      NestedStorageRowsRepr primitive rows machine (.data source 0) 0 L :=
    nested_storage_header_inputs primitive rows bounded shadow machine source L represented
  rw [nested_storage_header_run primitive rows bounded shadow machine source L represented]
  exact nested_storage_parent_refusal heap primitive rows bounded base frame cursor machine (.data source 0) (wmod rows.length) L
    allocator (Nat.mod_eq_of_lt bounded).symm inputs.2 tooLarge

theorem nested_storage_header_correct {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W)
    (shadow : SList (.ref (.array (.prim primitive))))
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array (.ref (.array (.prim primitive))))) source
      (nestedStorageHeaderValue primitive rows bounded shadow)) :
    (∃ fits, NestedStorageHeaderResult heap primitive rows bounded shadow base frame cursor machine source fits) ∨
    (¬ cursor.val + nestedStorageParentDemand rows < W ∧ run nestedStorageHeaderCode (machine.push (.slot source)) = .revert) := by
  by_cases fits : cursor.val + nestedStorageParentDemand rows < W
  · exact .inl ⟨fits, nested_storage_header_success heap primitive rows bounded shadow base frame cursor machine source L allocator represented fits⟩
  · exact .inr ⟨fits, nested_storage_header_refusal heap primitive rows bounded shadow base frame cursor machine source L allocator represented fits⟩

def nestedStorageHeader : NestedStorageHeaderCertificate := ⟨nested_storage_header_correct⟩

#print axioms nested_storage_header_values
#print axioms nested_storage_header_copy
#print axioms nested_storage_header_inputs
#print axioms nested_storage_header_enter
#print axioms nested_storage_header_run
#print axioms nested_storage_header_success
#print axioms nested_storage_header_refusal
#print axioms nested_storage_header_correct
#print axioms nestedStorageHeader
end Solidity.Backend.MemoryCopies
