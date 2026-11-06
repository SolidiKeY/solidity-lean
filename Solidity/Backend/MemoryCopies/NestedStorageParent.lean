import Solidity.Backend.MemoryCopies.NestedStorageParentInterface

/-! Reserve the physical parent first, traverse actual children, then adopt the
intrinsic parent after them. All execution uses existing target components. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem nested_storage_parent_source {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W) :
    let children := (nestedStorageValues primitive rows).copyStToM heap rfl
    (nestedStorageParentValue primitive rows bounded).copyStToM heap rfl =
      Grown.alloc (R := .array (.ref (.array (.prim primitive)))) ⟨children.ext, children.heap,
        ⟨children.val.1, by rw [children.val.2]; exact bounded⟩⟩ := by
  simp only [nestedStorageParentValue, SVal.copyStToM_array]

theorem nested_storage_parent_guard (machine : Machine) (source : Slot) (cursor size : Fin W)
    (cell : machine.mem 0 = .val cursor) :
    run (referenceCapacityGuard 0) ((machine.push (.slot source)).push (.val size)) =
      if cursor.val + size.val + 1 < W then .ok ((machine.push (.slot source)).push (.val size)) 0 else .revert := by
  simpa only [Nat.mul_zero, Nat.add_zero, ← Nat.add_assoc] using
    reference_capacity_guard_run 0 (machine.push (.slot source)) cursor size cell

theorem nested_storage_parent_prefix (machine : Machine) (source : Slot) (cursor size : Fin W)
    (cell : machine.mem 0 = .val cursor) :
    run Objects.nestedPrefix ((machine.push (.slot source)).push (.val size)) =
      .ok (nestedStorageControl (allocateMachine machine cursor size) source cursor size (wmod 0)) 0 :=
  Objects.nestedPrefix_run (machine.push (.slot source)) cursor size cell

theorem nested_storage_parent_exit (machine : Machine) (source : Slot) (parent size : Fin W) :
    run nestedStorageParentExit (nestedStorageControl machine source parent size size) =
      .ok (machine.push (.val parent)) 0 := by
  rfl

theorem nested_storage_parent_success {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : Slot) (size : Fin W) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) (count : rows.length = size.val)
    (represented : NestedStorageRowsRepr primitive rows machine source 0 L)
    (fits : cursor.val + nestedStorageParentDemand rows < W) :
    NestedStorageParentResult heap primitive rows bounded base frame cursor machine source size fits := by
  have parentFits : cursor.val + size.val + 1 < W := by
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
    simpa only [nestedStorageParentDemand, count, Nat.add_assoc] using fits
  obtain ⟨base1, target, iteration, loopRun, allocated, extension, finalGap, contents, shape, below, gaps, keeps⟩ :=
    nested_storage_loop_success heap primitive rows base frame next start source cursor size (wmod 0) L
      reserved.1 gap allocator.free.above (by change cursor.val + 1 + size.val ≤ cursor.val + size.val + 1; omega)
      (by simpa only [show (wmod 0).val = 0 from rfl, Nat.zero_add] using count) represented childFits
  let children := (nestedStorageValues primitive rows).copyStToM heap rfl
  let object : MObj children.H' (.array (.ref (.array (.prim primitive)))) :=
    ⟨children.val.1, by rw [children.val.2]; exact bounded⟩
  have sourceEq : (nestedStorageParentValue primitive rows bounded).copyStToM heap rfl =
      Grown.alloc (R := .array (.ref (.array (.prim primitive)))) ⟨children.ext, children.heap, object⟩ :=
    nested_storage_parent_source heap primitive rows bounded
  let finalBase := upd base1 children.H'.length cursor
  have positive : 0 < cursor.val := Nat.lt_of_lt_of_le allocator.free.reserved allocator.free.above
  have adopted : Objects.AllocatorRepr (children.heap.alloc object).1 finalBase frame
      ⟨cursor.val + nestedStorageParentDemand rows, fits⟩ target := by
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
    have cursorEq : next.val + nestedStorageDemand rows = cursor.val + nestedStorageParentDemand rows := by
      simp only [next, nestedStorageParentDemand, count, Nat.add_assoc]
    simpa only [cursorEq] using ownership
  have execution : run nestedStorageParentCode ((machine.push (.slot source)).push (.val size)) =
      .ok (target.push (.val cursor)) 0 := by
    have guard : run (referenceCapacityGuard 0) ((machine.push (.slot source)).push (.val size)) =
        if cursor.val + size.val + 1 < W then .ok ((machine.push (.slot source)).push (.val size)) 0 else .revert :=
      nested_storage_parent_guard machine source cursor size allocator.free.cell
    rw [if_pos parentFits] at guard
    rw [nestedStorageParentCode, run_append_ok guard,
      run_append_ok (nested_storage_parent_prefix machine source cursor size allocator.free.cell), run_append_ok loopRun]
    exact nested_storage_parent_exit target source cursor size
  dsimp only [NestedStorageParentResult]
  refine ⟨finalBase, target, execution, ?_, ?_,
    BaseExtends.trans children.ext extension (fun reference => allocationBase_old base1 cursor reference), ?_, ?_, ?_,
    SVal.keeps_copyStToM (nestedStorageParentValue primitive rows bounded) rfl heap,
    SVal.copyStToM_id_ge heap (nestedStorageParentValue primitive rows bounded) rfl, ?_,
    (storageHeapContents (nestedStorageParentValue primitive rows bounded) rfl).contents heap⟩
  · exact (congrArg (fun grown : Grown H (MVal · (.ref (.array (.ref (.array (.prim primitive)))))) =>
      Objects.AllocatorRepr grown.heap finalBase frame ⟨cursor.val + nestedStorageParentDemand rows, fits⟩ target) sourceEq).mpr adopted
  · exact (congrArg (fun grown : Grown H (MVal · (.ref (.array (.ref (.array (.prim primitive)))))) => finalBase grown.val.id = cursor) sourceEq).mpr
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
    apply (congrArg (fun grown : Grown H (MVal · (.ref (.array (.ref (.array (.prim primitive)))))) => Objects.Gap grown.heap finalBase lo hi) sourceEq).mpr
    exact adoptedGap
  · apply (congrArg (fun grown : Grown H (MVal · (.ref (.array (.ref (.array (.prim primitive)))))) => grown.heap.len grown.val .dyn = rows.length) sourceEq).mpr
    simpa only [Grown.alloc, Heap.len, Heap.get_alloc, MObj.elems_dyn, MObj.wk, object,
      List.length_map] using children.val.2

theorem nested_storage_parent_refusal {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (_bounded : rows.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : Slot) (size : Fin W) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) (count : rows.length = size.val)
    (represented : NestedStorageRowsRepr primitive rows machine source 0 L)
    (tooLarge : ¬ cursor.val + nestedStorageParentDemand rows < W) :
    run nestedStorageParentCode ((machine.push (.slot source)).push (.val size)) = .revert := by
  have guard : run (referenceCapacityGuard 0) ((machine.push (.slot source)).push (.val size)) =
        if cursor.val + size.val + 1 < W then .ok ((machine.push (.slot source)).push (.val size)) 0 else .revert :=
      nested_storage_parent_guard machine source cursor size allocator.free.cell
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
      simpa only [nestedStorageParentDemand, count, Nat.add_assoc] using tooLarge
    have refusal : run nestedStorageLoopCode (nestedStorageControl start source cursor size (wmod 0)) = .revert :=
      (nested_storage_loop_refusal heap primitive rows base frame next start source cursor size (wmod 0) L
        reserved.1 gap allocator.free.above (by change cursor.val + 1 + size.val ≤ cursor.val + size.val + 1; omega)
        (by simpa only [show (wmod 0).val = 0 from rfl, Nat.zero_add] using count) represented childTooLarge).2
    rw [nestedStorageParentCode, run_append_ok guard,
      run_append_ok (nested_storage_parent_prefix machine source cursor size allocator.free.cell), run_append_revert refusal]
  · rw [if_neg parentFits] at guard
    rw [nestedStorageParentCode, run_append_revert guard]

theorem nested_storage_parent_correct {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (bounded : rows.length < W)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (source : Slot) (size : Fin W) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) (count : rows.length = size.val)
    (represented : NestedStorageRowsRepr primitive rows machine source 0 L) :
    (∃ fits, NestedStorageParentResult heap primitive rows bounded base frame cursor machine source size fits) ∨
    (¬ cursor.val + nestedStorageParentDemand rows < W ∧
      run nestedStorageParentCode ((machine.push (.slot source)).push (.val size)) = .revert) := by
  by_cases fits : cursor.val + nestedStorageParentDemand rows < W
  · exact .inl ⟨fits, nested_storage_parent_success heap primitive rows bounded base frame cursor machine source size L
      allocator count represented fits⟩
  · exact .inr ⟨fits, nested_storage_parent_refusal heap primitive rows bounded base frame cursor machine source size L
      allocator count represented fits⟩

def nestedStorageParent : NestedStorageParentCertificate := ⟨nested_storage_parent_correct⟩

#print axioms nested_storage_parent_source
#print axioms nested_storage_parent_guard
#print axioms nested_storage_parent_prefix
#print axioms nested_storage_parent_exit
#print axioms nested_storage_parent_success
#print axioms nested_storage_parent_refusal
#print axioms nested_storage_parent_correct
#print axioms nestedStorageParent
end Solidity.Backend.MemoryCopies
