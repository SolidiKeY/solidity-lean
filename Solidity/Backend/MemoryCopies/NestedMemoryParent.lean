import Solidity.Backend.MemoryCopies.NestedMemoryParentInterface

/-! The actual header supplies the count; existing checked turns populate a
reservation before the existing typed adoption theorem installs the parent. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem nested_memory_parent_enter {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    run [.dup 1, .mloadAt] (machine.push (.val (base source.id))) =
      .ok ((machine.push (.val (base source.id))).push (.val (memoryChildCount heap primitive source))) 0 := by
  have count : wmod (heap.len source .dyn) = memoryChildCount heap primitive source :=
    Fin.ext (Nat.mod_eq_of_lt (heap.len_dyn_lt source))
  have header : machine.mem (base source.id).val = .val (memoryChildCount heap primitive source) := by
    rw [← count]
    exact (allocator.heap.arrays .dyn source).length rfl
  simp only [run, exec_cons_zero, Instr.step, Machine.next, Machine.push, Out.ok_bind,
    List.getElem?_cons_zero, exec_nil, Nat.reduceSub, header]

theorem nested_memory_parent_guard (machine : Machine) (source cursor size : Fin W)
    (cell : machine.mem 0 = .val cursor) :
    run (referenceCapacityGuard 0) ((machine.push (.val source)).push (.val size)) =
      if cursor.val + size.val + 1 < W then .ok ((machine.push (.val source)).push (.val size)) 0 else .revert := by
  simpa only [Nat.mul_zero, Nat.add_zero, ← Nat.add_assoc] using
    reference_capacity_guard_run 0 (machine.push (.val source)) cursor size cell

theorem nested_memory_parent_prefix (machine : Machine) (source cursor size : Fin W)
    (cell : machine.mem 0 = .val cursor) :
    run Objects.nestedPrefix ((machine.push (.val source)).push (.val size)) =
      .ok (nestedMemoryControl (allocateMachine machine cursor size) source cursor size (wmod 0)) 0 :=
  Objects.nestedPrefix_run (machine.push (.val source)) cursor size cell

theorem nested_memory_parent_exit (machine : Machine) (source parent size : Fin W) :
    run nestedStorageParentExit (nestedMemoryControl machine source parent size size) =
      .ok (machine.push (.val parent)) 0 := by rfl

theorem nested_memory_parent_success {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (fits : cursor.val + memoryParentDemand heap primitive source < W) :
    NestedMemoryParentResult heap primitive source base frame cursor machine fits := by
  let rows := memoryChildRows heap primitive source
  let size := memoryChildCount heap primitive source
  have count : rows.length = size.val := memory_rows_length heap primitive source
  have bounded : rows.length < W := count ▸ size.isLt
  have parentFits : cursor.val + size.val + 1 < W := by
    change cursor.val + nestedStorageParentDemand rows < W at fits
    simp only [nestedStorageParentDemand, count] at fits
    omega
  let start := allocateMachine machine cursor size
  let next : Fin W := ⟨cursor.val + size.val + 1, parentFits⟩
  have reserved : Objects.AllocatorRepr heap base frame next start ∧
      Objects.Gap heap base cursor.val (cursor.val + size.val + 1) := allocator.reserveArray size parentFits
  have gap : Objects.Gap heap base cursor.val (cursor.val + 1 + size.val) := by
    intro Q reference
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using reserved.2 reference
  have childFits : next.val + nestedStorageDemand rows < W := by
    change cursor.val + size.val + 1 + nestedStorageDemand rows < W
    change cursor.val + (rows.length + 1 + nestedStorageDemand rows) < W at fits
    simpa only [count, Nat.add_assoc] using fits
  obtain ⟨base1, target, iteration, loopRun, allocated, extension, finalGap, contents, shape, below, gaps, keeps, fresh, retained⟩ :=
    nested_memory_loop_success heap primitive rows base frame next start source cursor size (wmod 0)
      reserved.1 gap allocator.free.above (by change cursor.val + 1 + size.val ≤ cursor.val + size.val + 1; omega)
      (by simpa only [show (wmod 0).val = 0 from rfl, Nat.zero_add] using count) (memory_rows_repr heap primitive source) childFits
  let children := (nestedStorageValues primitive rows).copyStToM heap rfl
  let object : MObj children.H' (.array (.ref (.array (.prim primitive)))) :=
    ⟨children.val.1, by rw [children.val.2]; exact bounded⟩
  let snapshot := MVal.copyMToSt heap (T := .ref (.array (.ref (.array (.prim primitive))))) source
  let grown := snapshot.copyStToM heap rfl
  have sourceEq : grown = Grown.alloc (R := .array (.ref (.array (.prim primitive)))) ⟨children.ext, children.heap, object⟩ :=
    (memory_parent_copy_agreement heap primitive source).trans (nested_storage_parent_source heap primitive rows bounded)
  let finalBase := upd base1 children.H'.length cursor
  have positive : 0 < cursor.val := Nat.lt_of_lt_of_le allocator.free.reserved allocator.free.above
  have adopted : Objects.AllocatorRepr (children.heap.alloc object).1 finalBase frame
      ⟨cursor.val + memoryParentDemand heap primitive source, fits⟩ target := by
    have ownership : Objects.AllocatorRepr (children.heap.alloc object).1 finalBase frame
        ⟨next.val + nestedStorageDemand rows, childFits⟩ target :=
      allocated.adoptDefaultParent children .dyn object (by rw [MObj.elems_dyn]) allocator.free.above
        (by
          intro Q reference
          have span : max 1 (1 + size.val) = 1 + size.val := by omega
          simpa only [Objects.header, count, span, Nat.add_assoc] using finalGap reference)
        (by
          have span : max 1 (1 + rows.length) = 1 + rows.length := by omega
          simp only [Objects.header, span]
          change cursor.val + (1 + rows.length) ≤ next.val + nestedStorageDemand rows
          dsimp only [next]
          omega)
        (fun _ => by
          rw [below cursor.val positive (by change cursor.val < cursor.val + size.val + 1; omega)
            (.inl (by change cursor.val < cursor.val + 1 + 0; omega))]
          exact (allocateMachine_header machine cursor size (by omega)).trans (by
            rw [count]
            exact congrArg Word.val (Fin.ext (Nat.mod_eq_of_lt size.isLt).symm)))
        (fun offset reference chosen => by
          have stored : target.mem (cursor.val + 1 + (wmod 0).val + offset) = .val (base1 reference.id) :=
            contents offset reference chosen
          simpa only [Objects.header, Nat.add_zero] using stored)
    have cursorEq : next.val + nestedStorageDemand rows = cursor.val + memoryParentDemand heap primitive source := by
      change cursor.val + size.val + 1 + nestedStorageDemand rows = cursor.val + nestedStorageParentDemand rows
      simp only [nestedStorageParentDemand, count, Nat.add_assoc]
    simpa only [cursorEq] using ownership
  have execution : run (nestedMemoryParentCode primitive) (machine.push (.val (base source.id))) =
      .ok (target.push (.val cursor)) 0 := by
    have guard : run (referenceCapacityGuard 0) ((machine.push (.val (base source.id))).push (.val size)) =
        .ok ((machine.push (.val (base source.id))).push (.val size)) 0 := by
      rw [nested_memory_parent_guard machine (base source.id) cursor size allocator.free.cell, if_pos parentFits]
    rw [nestedMemoryParentCode, run_append_ok (nested_memory_parent_enter heap primitive source base frame cursor machine allocator),
      nestedMemoryParentBody, run_append_ok guard,
      run_append_ok (nested_memory_parent_prefix machine (base source.id) cursor size allocator.free.cell), run_append_ok loopRun]
    exact nested_memory_parent_exit target (base source.id) cursor size
  dsimp only [NestedMemoryParentResult]
  refine ⟨finalBase, target, execution, ?_, ?_,
    BaseExtends.trans children.ext extension (fun reference => allocationBase_old base1 cursor reference), ?_, ?_, ?_,
    SVal.keeps_copyStToM snapshot rfl heap, SVal.copyStToM_id_ge heap snapshot rfl, ?_,
    (storageHeapContents snapshot rfl).contents heap, ?_⟩
  · exact (congrArg (fun result : Grown H (MVal · (.ref (.array (.ref (.array (.prim primitive)))))) =>
      Objects.AllocatorRepr result.heap finalBase frame ⟨cursor.val + memoryParentDemand heap primitive source, fits⟩ target) sourceEq).mpr adopted
  · exact (congrArg (fun result : Grown H (MVal · (.ref (.array (.ref (.array (.prim primitive)))))) => finalBase result.val.id = cursor) sourceEq).mpr
      (upd_same _ _ _)
  · calc
      target = {start with mem := target.mem} := shape
      _ = {machine with mem := target.mem} := rfl
  · intro address nonzero lower
    rw [below address nonzero (by change address < cursor.val + size.val + 1; omega)
      (.inl (by change address < cursor.val + 1 + 0; omega))]
    exact allocateMachine_other machine cursor size address (by omega) (by omega)
  · intro lo hi oldGap upper
    have childGap : Objects.Gap children.heap base1 lo hi := gaps lo hi oldGap (by
      change hi ≤ cursor.val + size.val + 1
      omega)
    have adoptedGap : Objects.Gap (children.heap.alloc object).1 finalBase lo hi := childGap.adoptSingle object cursor upper
    apply (congrArg (fun result : Grown H (MVal · (.ref (.array (.ref (.array (.prim primitive)))))) => Objects.Gap result.heap finalBase lo hi) sourceEq).mpr
    exact adoptedGap
  · apply (congrArg (fun result : Grown H (MVal · (.ref (.array (.ref (.array (.prim primitive)))))) => result.heap.len result.val .dyn = heap.len source .dyn) sourceEq).mpr
    simpa only [Grown.alloc, Heap.len, Heap.get_alloc, MObj.elems_dyn, MObj.wk, object,
      List.length_map] using children.val.2.trans (memory_rows_length heap primitive source)
  · exact kept_snapshot grown.ext heap grown.heap (SVal.keeps_copyStToM snapshot rfl heap)
      (.ref (.array (.ref (.array (.prim primitive))))) source

theorem nested_memory_parent_refusal {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (tooLarge : ¬ cursor.val + memoryParentDemand heap primitive source < W) :
    run (nestedMemoryParentCode primitive) (machine.push (.val (base source.id))) = .revert := by
  let rows := memoryChildRows heap primitive source
  let size := memoryChildCount heap primitive source
  have count : rows.length = size.val := memory_rows_length heap primitive source
  have guard : run (referenceCapacityGuard 0) ((machine.push (.val (base source.id))).push (.val size)) =
      if cursor.val + size.val + 1 < W then .ok ((machine.push (.val (base source.id))).push (.val size)) 0 else .revert :=
    nested_memory_parent_guard machine (base source.id) cursor size allocator.free.cell
  rw [nestedMemoryParentCode, run_append_ok (nested_memory_parent_enter heap primitive source base frame cursor machine allocator)]
  by_cases parentFits : cursor.val + size.val + 1 < W
  · rw [if_pos parentFits] at guard
    let start := allocateMachine machine cursor size
    let next : Fin W := ⟨cursor.val + size.val + 1, parentFits⟩
    have reserved : Objects.AllocatorRepr heap base frame next start ∧
        Objects.Gap heap base cursor.val (cursor.val + size.val + 1) := allocator.reserveArray size parentFits
    have gap : Objects.Gap heap base cursor.val (cursor.val + 1 + size.val) := by
      intro Q reference
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using reserved.2 reference
    have childTooLarge : ¬ next.val + nestedStorageDemand rows < W := by
      change ¬ cursor.val + size.val + 1 + nestedStorageDemand rows < W
      change ¬ cursor.val + (rows.length + 1 + nestedStorageDemand rows) < W at tooLarge
      simpa only [count, Nat.add_assoc] using tooLarge
    have refusal : run (nestedMemoryLoopCode primitive) (nestedMemoryControl start (base source.id) cursor size (wmod 0)) = .revert :=
      (nested_memory_loop_refusal heap primitive rows base frame next start source cursor size (wmod 0)
        reserved.1 gap allocator.free.above (by change cursor.val + 1 + size.val ≤ cursor.val + size.val + 1; omega)
        (by simpa only [show (wmod 0).val = 0 from rfl, Nat.zero_add] using count) (memory_rows_repr heap primitive source) childTooLarge).2
    rw [nestedMemoryParentBody, run_append_ok guard,
      run_append_ok (nested_memory_parent_prefix machine (base source.id) cursor size allocator.free.cell), run_append_revert refusal]
  · rw [if_neg parentFits] at guard
    rw [nestedMemoryParentBody, run_append_revert guard]

theorem nested_memory_parent_correct {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (source : HRef H (.array (.ref (.array (.prim primitive))))) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    (∃ fits, NestedMemoryParentResult heap primitive source base frame cursor machine fits) ∨
    (¬ cursor.val + memoryParentDemand heap primitive source < W ∧
      run (nestedMemoryParentCode primitive) (machine.push (.val (base source.id))) = .revert) := by
  by_cases fits : cursor.val + memoryParentDemand heap primitive source < W
  · exact .inl ⟨fits, nested_memory_parent_success heap primitive source base frame cursor machine allocator fits⟩
  · exact .inr ⟨fits, nested_memory_parent_refusal heap primitive source base frame cursor machine allocator fits⟩

def nestedMemoryParent : NestedMemoryParentCertificate := ⟨nested_memory_parent_correct⟩

#print axioms nested_memory_parent_enter
#print axioms nested_memory_parent_guard
#print axioms nested_memory_parent_prefix
#print axioms nested_memory_parent_exit
#print axioms nested_memory_parent_success
#print axioms nested_memory_parent_refusal
#print axioms nested_memory_parent_correct
#print axioms nestedMemoryParent
end Solidity.Backend.MemoryCopies
