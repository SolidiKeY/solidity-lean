import Solidity.Backend.MemoryCopies.FixedReferenceStorageParentInterface
import Solidity.Backend.MemoryCopies.NestedStorageHeader

/-! Existing reservation and headerless traversal are followed by actual typed
fixed-parent adoption. Full fixed storage representation supplies all children. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

private theorem primitive_words {primitive : PrimTy} (items : List primitive.Denote) :
    elementWordCount (SVec.ofList (items.map SVal.prim)) = 0 := by
  induction items with
  | nil => simp only [List.map_nil,SVec.ofList,elementWordCount]
  | cons item items ih => simp only [List.map_cons,SVec.ofList,elementWordCount,liveWordCount,ih,Nat.zero_add]

private theorem child_words (primitive : PrimTy) (rows : List (PrimitiveStorageRow primitive)) :
    elementWordCount (nestedStorageValues primitive rows) = nestedStorageDemand rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [nestedStorageValues,elementWordCount,primitiveArrayValue,liveWordCount,
      primitive_words,List.length_map,nestedStorageDemand,ih]
    omega

theorem fixed_reference_storage_parent_demand (primitive : PrimTy) (rows : List (PrimitiveStorageRow primitive)) :
    liveWordCount (fixedReferenceStorageValue primitive rows) = fixedReferenceStorageParentDemand rows := by
  simp only [fixedReferenceStorageValue,liveWordCount,child_words,fixedReferenceStorageParentDemand,Nat.add_comm]

theorem fixed_reference_storage_parent_growth {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) :
    heapWords ((fixedReferenceStorageValue primitive rows).copyStToM heap rfl).heap =
      heapWords heap + fixedReferenceStorageParentDemand rows := by
  rw [valueCopy_words,fixed_reference_storage_parent_demand]

theorem fixed_reference_storage_parent_inputs (primitive : PrimTy) (rows : List (PrimitiveStorageRow primitive))
    (machine : Machine) (source : Slot) (L : Nat)
    (represented : ReprAt machine.store L (.ref (.fixed (.ref (.array (.prim primitive))) rows.length)) source
      (fixedReferenceStorageValue primitive rows)) :
    NestedStorageRowsRepr primitive rows machine source 0 L := by
  cases represented with
  | fixed elements =>
    intro offset row chosen
    have selected : (nestedStorageValues primitive rows).toList[offset]? =
        some (primitiveArrayValue primitive row.val row.property) := by
      rw [nested_storage_header_values,List.getElem?_map,chosen]
      rfl
    have child : ReprAt machine.store L (.ref (.array (.prim primitive)))
        (source.add (offset * size (.ref (.array (.prim primitive)))))
        (primitiveArrayValue primitive row.val row.property) := elements offset _ selected
    simpa only [size_array,Nat.mul_one,Nat.zero_add] using child

theorem fixed_reference_storage_parent_repr (primitive : PrimTy) (rows : List (PrimitiveStorageRow primitive))
    (machine : Machine) (source : Slot) (L : Nat)
    (represented : NestedStorageRowsRepr primitive rows machine source 0 L) :
    ReprAt machine.store L (.ref (.fixed (.ref (.array (.prim primitive))) rows.length)) source
      (fixedReferenceStorageValue primitive rows) := by
  refine .fixed ?_
  intro offset value selected
  rw [nested_storage_header_values,List.getElem?_map] at selected
  obtain ⟨row,chosen,rfl⟩ := Option.map_eq_some_iff.mp selected
  simpa only [Nat.zero_add,size_array,Nat.mul_one] using represented offset row chosen

theorem fixed_reference_storage_parent_source {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) :
    let children := (nestedStorageValues primitive rows).copyStToM heap rfl
    (fixedReferenceStorageValue primitive rows).copyStToM heap rfl =
      Grown.alloc (R := .fixed (.ref (.array (.prim primitive))) rows.length)
        ⟨children.ext,children.heap,⟨children.val.1,children.val.2⟩⟩ := by
  simp only [fixedReferenceStorageValue,SVal.copyStToM_fixed]
  rfl

theorem fixed_reference_storage_parent_guard (machine : Machine) (source : Slot) (cursor : Fin W)
    (count : Nat) (cell : machine.mem 0 = .val cursor) :
    run (defaultCapacityGuard (max 1 count)) (machine.push (.slot source)) =
      if cursor.val + max 1 count < W then .ok (machine.push (.slot source)) 0 else .revert :=
  default_capacity_guard_run _ (by have positive : 1 ≤ max 1 count := Nat.le_max_left _ _; omega)
    (machine.push (.slot source)) cursor cell

theorem fixed_reference_storage_parent_prefix (machine : Machine) (source : Slot) (cursor : Fin W)
    (count : Nat) (cell : machine.mem 0 = .val cursor) :
    run (Objects.fixedDefaultPrefix count) (machine.push (.slot source)) =
      .ok (nestedStorageControl (allocateStructMachine machine cursor (max 1 count))
        source cursor (wmod count) (wmod 0)) 0 :=
  Objects.fixedDefaultPrefix_run (machine.push (.slot source)) cursor count cell

theorem fixed_reference_storage_parent_success_rows {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : NestedStorageRowsRepr primitive rows machine source 0 L)
    (fits : cursor.val + fixedReferenceStorageParentDemand rows < W) :
    FixedReferenceStorageParentResult heap primitive rows base frame cursor machine source fits := by
  have parentFits : cursor.val + max 1 rows.length < W := by
    simp only [fixedReferenceStorageParentDemand] at fits
    omega
  have countBound : rows.length < W := by
    have upper : rows.length ≤ max 1 rows.length := Nat.le_max_right _ _
    omega
  have countValue : (wmod rows.length).val = rows.length := Nat.mod_eq_of_lt countBound
  let start := allocateStructMachine machine cursor (max 1 rows.length)
  let next : Fin W := ⟨cursor.val + max 1 rows.length,parentFits⟩
  have reserved : Objects.AllocatorRepr heap base frame next start ∧
      Objects.Gap heap base cursor.val (cursor.val + max 1 rows.length) :=
    allocator.reserveFixed rows.length parentFits
  have gap : Objects.Gap heap base cursor.val (cursor.val + max 1 (wmod rows.length).val) := by
    intro Q reference
    simpa only [countValue] using reserved.2 reference
  have childFits : next.val + nestedStorageDemand rows < W := by
    change cursor.val + max 1 rows.length + nestedStorageDemand rows < W
    simpa only [fixedReferenceStorageParentDemand,Nat.add_assoc] using fits
  obtain ⟨base1,target,iteration,loopRun,allocated,extension,finalGap,contents,shape,below,gaps,keeps⟩ :=
    fixed_reference_storage_loop_success heap primitive rows base frame next start source cursor (wmod rows.length) (wmod 0) L
      reserved.1 gap allocator.free.above (by change cursor.val + max 1 (wmod rows.length).val ≤ cursor.val + max 1 rows.length; rw [countValue]; exact Nat.le_refl _)
      (by simp only [show (wmod 0).val = 0 from rfl,Nat.zero_add,countValue]) represented childFits
  let children := (nestedStorageValues primitive rows).copyStToM heap rfl
  let object : MObj children.H' (.fixed (.ref (.array (.prim primitive))) rows.length) :=
    ⟨children.val.1,children.val.2⟩
  have sourceEq : (fixedReferenceStorageValue primitive rows).copyStToM heap rfl =
      Grown.alloc (R := .fixed (.ref (.array (.prim primitive))) rows.length)
        ⟨children.ext,children.heap,object⟩ := fixed_reference_storage_parent_source heap primitive rows
  let finalBase := upd base1 children.H'.length cursor
  have adopted : Objects.AllocatorRepr (children.heap.alloc object).1 finalBase frame
      ⟨cursor.val + fixedReferenceStorageParentDemand rows,fits⟩ target := by
    have ownership : Objects.AllocatorRepr (children.heap.alloc object).1 finalBase frame
        ⟨next.val + nestedStorageDemand rows,childFits⟩ target :=
      allocated.adoptDefaultParent children .fixed object (by rw [MObj.elems_fixed]) allocator.free.above
        (by intro Q reference; simpa only [Objects.header,Nat.zero_add,countValue] using finalGap reference)
        (by simp only [Objects.header,Nat.zero_add]; change cursor.val + max 1 rows.length ≤ next.val + nestedStorageDemand rows; dsimp only [next]; omega)
        (fun impossible => by cases impossible)
        (fun offset reference chosen => by
          have stored : target.mem (cursor.val + (wmod 0).val + offset) = .val (base1 reference.id) :=
            contents offset reference chosen
          simpa only [Objects.header,Nat.add_zero] using stored)
    have cursorEq : next.val + nestedStorageDemand rows = cursor.val + fixedReferenceStorageParentDemand rows := by
      simp only [next,fixedReferenceStorageParentDemand,Nat.add_assoc]
    simpa only [cursorEq] using ownership
  have execution : run (fixedReferenceStorageParentCode rows.length) (machine.push (.slot source)) =
      .ok (target.push (.val cursor)) 0 := by
    have guard : run (defaultCapacityGuard (max 1 rows.length)) (machine.push (.slot source)) =
        if cursor.val + max 1 rows.length < W then .ok (machine.push (.slot source)) 0 else .revert :=
      fixed_reference_storage_parent_guard machine source cursor rows.length allocator.free.cell
    rw [if_pos parentFits] at guard
    rw [fixedReferenceStorageParentCode,run_append_ok guard,
      run_append_ok (fixed_reference_storage_parent_prefix machine source cursor rows.length allocator.free.cell),
      run_append_ok loopRun]
    exact nested_storage_parent_exit target source cursor (wmod rows.length)
  dsimp only [FixedReferenceStorageParentResult]
  refine ⟨finalBase,target,execution,?_,?_,
    BaseExtends.trans children.ext extension (fun reference => allocationBase_old base1 cursor reference),?_,?_,?_,
    SVal.keeps_copyStToM (fixedReferenceStorageValue primitive rows) rfl heap,
    SVal.copyStToM_id_ge heap (fixedReferenceStorageValue primitive rows) rfl,?_,
    (storageHeapContents (fixedReferenceStorageValue primitive rows) rfl).contents heap,
    fixed_reference_storage_parent_growth heap primitive rows⟩
  · exact (congrArg (fun grown : Grown H (MVal · (.ref (.fixed (.ref (.array (.prim primitive))) rows.length))) =>
      Objects.AllocatorRepr grown.heap finalBase frame ⟨cursor.val + fixedReferenceStorageParentDemand rows,fits⟩ target) sourceEq).mpr adopted
  · exact (congrArg (fun grown : Grown H (MVal · (.ref (.fixed (.ref (.array (.prim primitive))) rows.length))) =>
      finalBase grown.val.id = cursor) sourceEq).mpr (upd_same _ _ _)
  · calc
      target = {start with mem := target.mem} := shape
      _ = {machine with mem := target.mem} := rfl
  · intro address nonzero lower
    rw [below address nonzero (by change address < cursor.val + max 1 rows.length; omega)
      (.inl (by change address < cursor.val + (wmod 0).val; simpa only [show (wmod 0).val = 0 from rfl,Nat.add_zero] using lower))]
    exact allocateStructMachine_other machine cursor _ address (by omega)
  · intro lo hi oldGap upper
    have childGap : Objects.Gap children.heap base1 lo hi := gaps lo hi oldGap (by
      change hi ≤ cursor.val + max 1 rows.length
      omega)
    have adoptedGap : Objects.Gap (children.heap.alloc object).1 finalBase lo hi := childGap.adoptSingle object cursor upper
    apply (congrArg (fun grown : Grown H (MVal · (.ref (.fixed (.ref (.array (.prim primitive))) rows.length))) =>
      Objects.Gap grown.heap finalBase lo hi) sourceEq).mpr
    exact adoptedGap
  · apply (congrArg (fun grown : Grown H (MVal · (.ref (.fixed (.ref (.array (.prim primitive))) rows.length))) =>
      grown.heap.len grown.val .fixed = rows.length) sourceEq).mpr
    simpa only [Grown.alloc,Heap.len,Heap.get_alloc,MObj.elems_fixed,MObj.wk,object,List.length_map] using children.val.2

theorem fixed_reference_storage_parent_refusal_rows {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : NestedStorageRowsRepr primitive rows machine source 0 L)
    (tooLarge : ¬ cursor.val + fixedReferenceStorageParentDemand rows < W) :
    run (fixedReferenceStorageParentCode rows.length) (machine.push (.slot source)) = .revert := by
  have guard : run (defaultCapacityGuard (max 1 rows.length)) (machine.push (.slot source)) =
      if cursor.val + max 1 rows.length < W then .ok (machine.push (.slot source)) 0 else .revert :=
    fixed_reference_storage_parent_guard machine source cursor rows.length allocator.free.cell
  by_cases parentFits : cursor.val + max 1 rows.length < W
  · rw [if_pos parentFits] at guard
    have countBound : rows.length < W := by
      have upper : rows.length ≤ max 1 rows.length := Nat.le_max_right _ _
      omega
    have countValue : (wmod rows.length).val = rows.length := Nat.mod_eq_of_lt countBound
    let start := allocateStructMachine machine cursor (max 1 rows.length)
    let next : Fin W := ⟨cursor.val + max 1 rows.length,parentFits⟩
    have reserved : Objects.AllocatorRepr heap base frame next start ∧
        Objects.Gap heap base cursor.val (cursor.val + max 1 rows.length) := allocator.reserveFixed rows.length parentFits
    have gap : Objects.Gap heap base cursor.val (cursor.val + max 1 (wmod rows.length).val) := by
      intro Q reference
      simpa only [countValue] using reserved.2 reference
    have childTooLarge : ¬ next.val + nestedStorageDemand rows < W := by
      change ¬ cursor.val + max 1 rows.length + nestedStorageDemand rows < W
      simpa only [fixedReferenceStorageParentDemand,Nat.add_assoc] using tooLarge
    have refusal : run fixedReferenceStorageLoopCode
        (nestedStorageControl start source cursor (wmod rows.length) (wmod 0)) = .revert :=
      (fixed_reference_storage_loop_refusal heap primitive rows base frame next start source cursor (wmod rows.length) (wmod 0) L
        reserved.1 gap allocator.free.above
        (by change cursor.val + max 1 (wmod rows.length).val ≤ cursor.val + max 1 rows.length; rw [countValue]; exact Nat.le_refl _)
        (by simp only [show (wmod 0).val = 0 from rfl,Nat.zero_add,countValue]) represented childTooLarge).2
    rw [fixedReferenceStorageParentCode,run_append_ok guard,
      run_append_ok (fixed_reference_storage_parent_prefix machine source cursor rows.length allocator.free.cell),run_append_revert refusal]
  · rw [if_neg parentFits] at guard
    rw [fixedReferenceStorageParentCode,run_append_revert guard]

theorem fixed_reference_storage_parent_correct {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (rows : List (PrimitiveStorageRow primitive)) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.fixed (.ref (.array (.prim primitive))) rows.length)) source
      (fixedReferenceStorageValue primitive rows)) :
    (∃ fits, FixedReferenceStorageParentResult heap primitive rows base frame cursor machine source fits) ∨
    (¬ cursor.val + fixedReferenceStorageParentDemand rows < W ∧
      run (fixedReferenceStorageParentCode rows.length) (machine.push (.slot source)) = .revert) := by
  have children : NestedStorageRowsRepr primitive rows machine source 0 L :=
    fixed_reference_storage_parent_inputs primitive rows machine source L represented
  by_cases fits : cursor.val + fixedReferenceStorageParentDemand rows < W
  · exact .inl ⟨fits,fixed_reference_storage_parent_success_rows heap primitive rows base frame cursor machine source L allocator children fits⟩
  · exact .inr ⟨fits,fixed_reference_storage_parent_refusal_rows heap primitive rows base frame cursor machine source L allocator children fits⟩

def fixedReferenceStorageParent : FixedReferenceStorageParentCertificate :=
  ⟨fixed_reference_storage_parent_correct,fixed_reference_storage_parent_demand,fixed_reference_storage_parent_growth⟩

/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_storage_parent_demand' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_storage_parent_demand
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_storage_parent_growth' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_storage_parent_growth
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_storage_parent_inputs' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms fixed_reference_storage_parent_inputs
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_storage_parent_repr' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_storage_parent_repr
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_storage_parent_source' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms fixed_reference_storage_parent_source
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_storage_parent_guard' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_storage_parent_guard
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_storage_parent_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_storage_parent_prefix
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_storage_parent_success_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_storage_parent_success_rows
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_storage_parent_refusal_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_storage_parent_refusal_rows
/--
info: 'Solidity.Backend.MemoryCopies.fixed_reference_storage_parent_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fixed_reference_storage_parent_correct
/--
info: 'Solidity.Backend.MemoryCopies.fixedReferenceStorageParent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fixedReferenceStorageParent
end Solidity.Backend.MemoryCopies
