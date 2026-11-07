import Solidity.Backend.MemoryCopies.FixedReferenceStorageParent
import Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls
import Solidity.Evm.MemoryObjectArrayExamples
import Solidity.Backend.MemoryCopies.TraversalFresh

/-! Actual checked outer allocation and typed-parent adoption over the existing
represented source fixture, with mixed retained words and capacity boundaries. -/
namespace Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls
open Evm Evm.Memory
private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def input : Input := ⟨_, _, _, _, ObjectArrayExamples.initial_allocator⟩
private abbrev Row := {payloads : List (Fin W) // payloads.length < 128}
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private theorem wide : 1024 < W := by decide
private def convert (row : Row) : PrimitiveStorageRow .uint :=
  ⟨values row.val, by rw [values, List.length_map]; have bound : row.val.length < 128 := row.property; have large : 1024 < W := wide; omega⟩
private def rows (entries : List Row) : List (PrimitiveStorageRow .uint) := entries.map convert
private def payloadAt (entries : List Row) (offset : Nat) : List (Fin W) := (entries[offset]?.map Subtype.val).getD []
private def source : Slot := .data (.root 0) 0
private def store (entries : List Row) (start : Nat) : WordStore := ⟨fun slot => match slot with
  | .data (.root 0) offset => if start ≤ offset then wmod (payloadAt entries (offset - start)).length else wmod 0
  | .data (.data (.root 0) offset) item => if start ≤ offset then (payloadAt entries (offset - start))[item]?.getD (wmod 0) else wmod 0
  | _ => wmod 0⟩
private def machine (entries : List Row) (start : Nat) : Machine :=
  allocateStructMachine {input.machine with store := store entries start} (wmod 40) 3
private theorem initial (entries : List Row) (start : Nat) :
    Objects.AllocatorRepr input.heap input.base 8 (wmod 43) (machine entries start) ∧
    Objects.Gap input.heap input.base 40 43 := by
  have old : Objects.AllocatorRepr input.heap input.base 8 (wmod 40)
      {input.machine with store := store entries start} := input.allocator.mem_eq rfl
  exact old.reserveFixed 3 (by decide)
private theorem represented (entries : List Row) (start : Nat) :
    NestedStorageRowsRepr .uint (rows entries) (machine entries start) source start 128 := by
  intro offset selected chosen
  simp only [rows, List.getElem?_map] at chosen
  cases picked : entries[offset]? with
  | none => simp only [picked, Option.map_none] at chosen; cases chosen
  | some row =>
    simp only [picked, Option.map_some] at chosen
    cases chosen
    refine .array ?_ (by simpa only [convert, values, List.length_map] using row.property) ?_
    · simp only [machine, allocateStructMachine, writeMachine, store, source, Slot.add, Nat.zero_add,
        WordStore.read, Nat.le_add_right, if_true, Nat.add_sub_cancel_left,
        payloadAt, picked, Option.map_some, Option.getD_some, convert, values, List.length_map]
      exact Nat.mod_eq_of_lt (show row.val.length < W by have large : 1024 < W := wide; have bound : row.val.length < 128 := row.property; omega)
    · intro item value chosen
      simp only [SVec.toList_ofList, convert, values, List.getElem?_map] at chosen
      cases found : row.val[item]? with
      | none => simp only [found, Option.map_none] at chosen; cases chosen
      | some payload =>
        simp only [found, Option.map_some] at chosen
        cases chosen
        simp only [size_prim, Nat.mul_one]
        refine .prim (ReprV.uint_of ?_)
        simp only [machine, allocateStructMachine, writeMachine, store, source, Slot.add, Nat.zero_add,
          Nat.le_add_right, if_true, Nat.add_sub_cancel_left, payloadAt, picked, Option.map_some, Option.getD_some,
          found]
        rfl
private theorem demand_bound (entries : List Row) : nestedStorageDemand (rows entries) ≤ 128 * entries.length := by
  induction entries with
  | nil => exact Nat.le_refl 0
  | cons row entries ih =>
    simp only [rows, List.map_cons, nestedStorageDemand, convert, values, List.length_map, List.length_cons,
      Nat.mul_add, Nat.mul_one]
    have bound : row.val.length < 128 := row.property
    simp only [rows] at ih
    omega

private def before (entries : List Row) : Machine := {input.machine with store := store entries 0}
private theorem allocator (entries : List Row) : Objects.AllocatorRepr input.heap input.base 8 (wmod 40) (before entries) :=
  input.allocator.mem_eq rfl
private theorem parent_repr (entries : List Row) :
    ReprAt (before entries).store 128 (.ref (.fixed (.ref (.array (.prim .uint))) (rows entries).length)) source
      (fixedReferenceStorageValue .uint (rows entries)) :=
  fixed_reference_storage_parent_repr .uint (rows entries) (before entries) source 128 (represented entries 0)

theorem certificate_inhabited : FixedReferenceStorageParentCertificate := fixedReferenceStorageParent

theorem actual_typed (entries : List Row) (bounded : entries.length < 4) :
    ∃ fits, FixedReferenceStorageParentResult input.heap .uint (rows entries) input.base 8 (wmod 40)
      (before entries) source fits := by
  have cost : nestedStorageDemand (rows entries) ≤ 128 * entries.length := demand_bound entries
  have fits : (wmod 40).val + fixedReferenceStorageParentDemand (rows entries) < W := by
    simp only [fixedReferenceStorageParentDemand,rows,List.length_map]
    have large : 1024 < W := wide
    change 40 + (max 1 entries.length + nestedStorageDemand (entries.map convert)) < W
    change nestedStorageDemand (entries.map convert) ≤ 128 * entries.length at cost
    omega
  rcases fixed_reference_storage_parent_correct input.heap .uint (rows entries) input.base 8 (wmod 40)
      (before entries) source 128 (allocator entries) (parent_repr entries) with success | refusal
  · exact success
  · exact (refusal.1 fits).elim

theorem actual_runtime (entries : List Row) (bounded : entries.length < 4) : ∃ target : Machine,
    run (fixedReferenceStorageParentCode (rows entries).length) ((before entries).push (.slot source)) =
      .ok (target.push w[40]) 0 ∧
    target.mem 0 = .val (wmod (40 + fixedReferenceStorageParentDemand (rows entries))) ∧
    target.mem 17 = w[7] ∧ target.stack = [w[77]] ∧ target.store = (before entries).store := by
  obtain ⟨fits,base',target,ran,allocated,root,extension,shape,below,gaps,keeps,fresh,length,mirror,words⟩ :=
    actual_typed entries bounded
  refine ⟨target,ran,allocated.free.cell.trans ?_,(below 17 (by decide) (by decide)).trans rfl,?_,?_⟩
  · apply congrArg Word.val
    apply Fin.ext
    change 40 + fixedReferenceStorageParentDemand (rows entries) = (40 + fixedReferenceStorageParentDemand (rows entries)) % W
    exact (Nat.mod_eq_of_lt fits).symm
  · exact congrArg Machine.stack shape
  · simpa only [] using congrArg Machine.store shape

private def empty : Row := ⟨[],by decide⟩
private def pair : Row := ⟨[wmod 11,wmod 23],by decide⟩
private def long : Row := ⟨List.ofFn (fun index : Fin 64 => wmod (index.val + 1)),by rw [List.length_ofFn]; decide⟩
private def mixed : List Row := [pair,empty,long]

theorem empty_parent : ∃ target : Machine,
    run (fixedReferenceStorageParentCode 0) ((before []).push (.slot source)) = .ok (target.push w[40]) 0 ∧
    target.mem 0 = w[41] ∧ target.mem 40 = w[0] ∧ target.mem 17 = w[7] ∧ target.stack = [w[77]] := by
  let target := allocateStructMachine (before []) (wmod 40) 1
  have iteration : loopIterN (run Objects.childrenCondition) (run fixedReferenceStorageTurnCode) 1
      (nestedStorageControl target source (wmod 40) (wmod 0) (wmod 0)) =
      .inr (.ok (nestedStorageControl target source (wmod 40) (wmod 0) (wmod 0)) 0) := by
    rw [loopIterN,fixed_reference_storage_loop_done]
  have guard : run (defaultCapacityGuard (max 1 0)) ((before []).push (.slot source)) =
      .ok ((before []).push (.slot source)) 0 := by
    rw [fixed_reference_storage_parent_guard _ _ (wmod 40) 0 (allocator []).free.cell,if_pos (by decide)]
  refine ⟨target,?_,rfl,rfl,rfl,rfl⟩
  rw [fixedReferenceStorageParentCode,run_append_ok guard,
    run_append_ok (fixed_reference_storage_parent_prefix _ _ (wmod 40) 0 (allocator []).free.cell),
    show max 1 (0 : Nat) = 1 from by decide,run_append_ok (fixed_reference_storage_loop_run iteration)]
  exact nested_storage_parent_exit target source (wmod 40) (wmod 0)

theorem empty_parent_typed : ∃ fits,
    FixedReferenceStorageParentResult input.heap .uint (rows []) input.base 8 (wmod 40) (before []) source fits :=
  actual_typed [] (by decide)

theorem mixed_parent_payloads : ∃ target : Machine,
    run (fixedReferenceStorageParentCode 3) ((before mixed).push (.slot source)) = .ok (target.push w[40]) 0 ∧
    target.mem 40 = w[43] ∧ target.mem 41 = w[46] ∧ target.mem 42 = w[47] ∧
    target.mem 43 = w[2] ∧ target.mem 46 = w[0] ∧ target.mem 47 = w[64] ∧
    target.mem 44 = w[11] ∧ target.mem 45 = w[23] ∧ target.mem 48 = w[1] ∧ target.mem 111 = w[64] := by
  obtain ⟨target,loopRun,pointer1,pointer2,pointer3,header1,header2,header3,payload1,payload2,payload3,payload4⟩ :=
    FixedReferenceStorageLoopControls.heterogeneous_pointers_payloads
  have actualLoop : run fixedReferenceStorageLoopCode
      (nestedStorageControl (allocateStructMachine (before mixed) (wmod 40) 3) source (wmod 40) (wmod 3) (wmod 0)) =
      .ok (nestedStorageControl target source (wmod 40) (wmod 3) (wmod 3)) 0 := loopRun
  have guard : run (defaultCapacityGuard (max 1 3)) ((before mixed).push (.slot source)) =
      .ok ((before mixed).push (.slot source)) 0 := by
    rw [fixed_reference_storage_parent_guard _ _ (wmod 40) 3 (allocator mixed).free.cell,if_pos (by decide)]
  refine ⟨target,?_,pointer1,pointer2,pointer3,header1,header2,header3,payload1,payload2,payload3,payload4⟩
  rw [fixedReferenceStorageParentCode,run_append_ok guard,
    run_append_ok (fixed_reference_storage_parent_prefix _ _ (wmod 40) 3 (allocator mixed).free.cell),show max 1 (3 : Nat) = 3 from by decide,run_append_ok actualLoop]
  exact nested_storage_parent_exit target source (wmod 40) (wmod 3)

theorem mixed_exact_growth :
    fixedReferenceStorageParentDemand (rows mixed) = 72 ∧
    heapWords ((fixedReferenceStorageValue .uint (rows mixed)).copyStToM input.heap rfl).heap = heapWords input.heap + 72 := by
  have demand : fixedReferenceStorageParentDemand (rows mixed) = 72 := by
    simp only [fixedReferenceStorageParentDemand,mixed,rows,List.map_cons,List.map_nil,List.length_cons,List.length_nil,
      nestedStorageDemand,convert,values,List.length_map,pair,empty,long,List.length_ofFn]
    decide
  exact ⟨demand,(fixed_reference_storage_parent_growth input.heap .uint (rows mixed)).trans (by rw [demand])⟩

theorem parent_identity_after_children :
    ((fixedReferenceStorageValue .uint (rows mixed)).copyStToM input.heap rfl).val.id = input.H.length + 3 := by
  rw [fixed_reference_storage_parent_source]
  simp only [mixed,rows,List.map_cons,List.map_nil,nestedStorageValues,SVec.copyStToM_cons,SVec.copyStToM_nil,
    primitive_array_source,Grown.alloc,Heap.alloc,List.length_append,List.length_cons,List.length_nil]

theorem repeated_parent : ∃ fits,
    FixedReferenceStorageParentResult input.heap .uint (rows [pair,pair,pair]) input.base 8 (wmod 40)
      (before [pair,pair,pair]) source fits := actual_typed _ (by decide)

theorem wrong_dynamic_header (target : Machine)
    (ran : run (fixedReferenceStorageParentCode 3) ((before mixed).push (.slot source)) = .ok (target.push w[40]) 0) :
    target.mem 40 ≠ w[3] := by
  obtain ⟨actual,execution,pointer,_⟩ := mixed_parent_payloads
  rw [ran] at execution
  have equal : target.mem 40 = actual.mem 40 := congrArg (fun machine => machine.mem 40) (Out.ok.inj execution).1
  rw [equal,pointer]
  decide

theorem wrong_returned_parent (target : Machine) :
    run (fixedReferenceStorageParentCode 3) ((before mixed).push (.slot source)) ≠ .ok (target.push w[43]) 0 := by
  intro wrong
  obtain ⟨actual,ran,_⟩ := mixed_parent_payloads
  rw [wrong] at ran
  have equal : (w[43] : Word) = w[40] := (List.cons.inj (congrArg Machine.stack (Out.ok.inj ran).1)).1
  exact (by decide : (w[43] : Word) ≠ w[40]) equal

private def moved (entries : List Row) (cursor : Fin W) : Machine := writeMachine (before entries) 0 (.val cursor)
private theorem moved_allocator (entries : List Row) (cursor : Fin W) (above : 40 ≤ cursor.val) :
    Objects.AllocatorRepr input.heap input.base 8 cursor (moved entries cursor) := by
  have old : Objects.AllocatorRepr input.heap input.base 8 (wmod 40) (before entries) := allocator entries
  refine ⟨old.heap.localWrite 0 (by decide) (.val cursor),⟨by decide,by omega,?_,?_⟩,?_⟩
  · rfl
  · intro address lower
    exact (upd_other _ _ (by omega : address ≠ 0)).trans (old.free.zero address (by change 40 ≤ address; omega))
  · intro Q reference
    have live : (input.base reference.id).val + Objects.cells input.heap reference ≤ 40 := old.live reference
    omega

theorem actual_refusal (entries : List Row) (cursor : Fin W) (above : 40 ≤ cursor.val)
    (noRoom : ¬ cursor.val + fixedReferenceStorageParentDemand (rows entries) < W) :
    run (fixedReferenceStorageParentCode (rows entries).length) ((moved entries cursor).push (.slot source)) = .revert := by
  rcases fixed_reference_storage_parent_correct input.heap .uint (rows entries) input.base 8 cursor
      (moved entries cursor) source 128 (moved_allocator entries cursor above) (parent_repr entries) with success | refusal
  · exact (noRoom success.choose).elim
  · exact refusal.2

theorem empty_parent_saturated_refusal :
    run (fixedReferenceStorageParentCode 0) ((moved [] wMax).push (.slot source)) = .revert :=
  actual_refusal [] wMax (by decide) (by change ¬ W - 1 + 1 < W; omega)

theorem empty_parent_last_fit : ∃ fits,
    FixedReferenceStorageParentResult input.heap .uint (rows []) input.base 8 (wmod (W - 2))
      (moved [] (wmod (W - 2))) source fits := by
  have large : 1024 < W := wide
  have cursorValue : (wmod (W - 2)).val = W - 2 := Nat.mod_eq_of_lt (by omega)
  have above : 40 ≤ (wmod (W - 2)).val := by rw [cursorValue]; omega
  have fits : (wmod (W - 2)).val + fixedReferenceStorageParentDemand (rows []) < W := by
    change (wmod (W - 2)).val + 1 < W
    rw [cursorValue]
    omega
  exact ⟨fits,fixed_reference_storage_parent_success_rows input.heap .uint (rows []) input.base 8 _ _ source 128
    (moved_allocator [] _ above) (represented [] 0) fits⟩

theorem oversized_static_refusal (count : Nat) (large : W ≤ count) :
    run (fixedReferenceStorageParentCode count) ((before []).push (.slot source)) = .revert := by
  have guard : run (defaultCapacityGuard (max 1 count)) ((before []).push (.slot source)) = .revert := by
    rw [fixed_reference_storage_parent_guard _ _ (wmod 40) count (allocator []).free.cell]
    apply if_neg
    have bigger : count ≤ max 1 count := Nat.le_max_right _ _
    omega
  rw [fixedReferenceStorageParentCode,run_append_revert guard]

theorem old_aliases_preserved : ∃ target : Machine,
    run (fixedReferenceStorageParentCode 3) ((before mixed).push (.slot source)) = .ok (target.push w[40]) 0 ∧
    target.mem 1 = w[24] ∧ target.mem 2 = w[24] ∧ target.mem 3 = w[32] ∧ target.mem 17 = w[7] := by
  obtain ⟨_,_,target,ran,_,_,_,_,below,_⟩ := actual_typed mixed (by decide)
  exact ⟨target,ran,(below 1 (by decide) (by decide)).trans rfl,(below 2 (by decide) (by decide)).trans rfl,
    (below 3 (by decide) (by decide)).trans rfl,(below 17 (by decide) (by decide)).trans rfl⟩

private def many : List Row := List.replicate 64 empty

theorem long_parent_success : ∃ fits,
    FixedReferenceStorageParentResult input.heap .uint (rows many) input.base 8 (wmod 40) (before many) source fits :=
  ⟨by decide +kernel,fixed_reference_storage_parent_success_rows input.heap .uint (rows many) input.base 8
    (wmod 40) (before many) source 128 (allocator many) (represented many 0) (by decide +kernel)⟩

theorem parent_reserved_before_child_refusal :
    let cursor := wmod (W - 2)
    ∃ reserved : Machine,
      run (defaultCapacityGuard (max 1 1) ++ Objects.fixedDefaultPrefix 1)
        ((moved [empty] cursor).push (.slot source)) =
        .ok (nestedStorageControl reserved source cursor (wmod 1) (wmod 0)) 0 ∧
      Objects.AllocatorRepr input.heap input.base 8 wMax reserved ∧
      reserved.mem cursor.val = w[0] ∧ reserved.mem 0 = .val wMax ∧
      run fixedReferenceStorageLoopCode (nestedStorageControl reserved source cursor (wmod 1) (wmod 0)) = .revert ∧
      run (fixedReferenceStorageParentCode 1) ((moved [empty] cursor).push (.slot source)) = .revert := by
  let cursor := wmod (W - 2)
  have large : 1024 < W := wide
  have cursorValue : cursor.val = W - 2 := Nat.mod_eq_of_lt (by omega)
  have above : 40 ≤ cursor.val := by rw [cursorValue]; omega
  have parentFits : cursor.val + max 1 1 < W := by change cursor.val + 1 < W; rw [cursorValue]; omega
  let reserved := allocateStructMachine (moved [empty] cursor) cursor (max 1 1)
  have initialAllocator : Objects.AllocatorRepr input.heap input.base 8 cursor (moved [empty] cursor) :=
    moved_allocator [empty] cursor above
  have reservation : Objects.AllocatorRepr input.heap input.base 8 ⟨cursor.val + max 1 1,parentFits⟩ reserved ∧
      Objects.Gap input.heap input.base cursor.val (cursor.val + max 1 1) :=
    initialAllocator.reserveFixed 1 parentFits
  have nextCursor : (⟨cursor.val + max 1 1,parentFits⟩ : Fin W) = wMax := by
    apply Fin.ext
    change cursor.val + 1 = W - 1
    omega
  have allocated : Objects.AllocatorRepr input.heap input.base 8 wMax reserved := by
    rw [nextCursor] at reservation
    exact reservation.1
  have gap : Objects.Gap input.heap input.base cursor.val (cursor.val + max 1 (wmod 1).val) := by
    intro Q reference
    exact reservation.2 reference
  have guard : run (defaultCapacityGuard (max 1 1)) ((moved [empty] cursor).push (.slot source)) =
      .ok ((moved [empty] cursor).push (.slot source)) 0 := by
    rw [fixed_reference_storage_parent_guard _ _ cursor 1 initialAllocator.free.cell,if_pos parentFits]
  have prefixRun : run (defaultCapacityGuard (max 1 1) ++ Objects.fixedDefaultPrefix 1)
      ((moved [empty] cursor).push (.slot source)) =
      .ok (nestedStorageControl reserved source cursor (wmod 1) (wmod 0)) 0 := by
    rw [run_append_ok guard]
    exact fixed_reference_storage_parent_prefix _ _ cursor 1 initialAllocator.free.cell
  have rejected : run fixedReferenceStorageLoopCode
      (nestedStorageControl reserved source cursor (wmod 1) (wmod 0)) = .revert :=
    (fixed_reference_storage_loop_refusal input.heap .uint (rows [empty]) input.base 8 wMax reserved source cursor
      (wmod 1) (wmod 0) 128 allocated gap (by omega) (by change cursor.val + 1 ≤ W - 1; omega)
      rfl (represented [empty] 0) (by change ¬ W - 1 + 1 < W; omega)).2
  refine ⟨reserved,prefixRun,allocated,?_,allocated.free.cell,rejected,?_⟩
  · exact (allocateStructMachine_other _ cursor _ cursor.val (by omega)).trans (initialAllocator.free.zero _ (Nat.le_refl _))
  · exact actual_refusal [empty] cursor above (by change ¬ cursor.val + 2 < W; rw [cursorValue]; omega)

/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls.certificate_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms certificate_inhabited
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls.actual_typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_typed
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls.actual_runtime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_runtime
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls.empty_parent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms empty_parent
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls.empty_parent_typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms empty_parent_typed
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls.mixed_parent_payloads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms mixed_parent_payloads
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls.mixed_exact_growth' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms mixed_exact_growth
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls.parent_identity_after_children' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms parent_identity_after_children
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls.repeated_parent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms repeated_parent
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls.wrong_dynamic_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms wrong_dynamic_header
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls.wrong_returned_parent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms wrong_returned_parent
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls.actual_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_refusal
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls.empty_parent_saturated_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms empty_parent_saturated_refusal
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls.empty_parent_last_fit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms empty_parent_last_fit
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls.oversized_static_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms oversized_static_refusal
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls.old_aliases_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms old_aliases_preserved
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls.long_parent_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms long_parent_success
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls.parent_reserved_before_child_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms parent_reserved_before_child_refusal
end Solidity.Backend.MemoryCopies.FixedReferenceStorageParentControls
