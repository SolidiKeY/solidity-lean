import Solidity.Backend.MemoryCopies.NestedStorageParent
import Solidity.Backend.MemoryCopies.NestedStorageLoopControls
import Solidity.Evm.MemoryObjectArrayExamples
import Solidity.Backend.MemoryCopies.TraversalFresh

/-! Actual checked outer allocation and typed-parent adoption over the existing
represented source fixture, with mixed retained words and capacity boundaries. -/
namespace Solidity.Backend.MemoryCopies.NestedStorageParentControls
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
  allocateMachine {input.machine with store := store entries start} (wmod 40) (wmod 3)
private theorem initial (entries : List Row) (start : Nat) :
    Objects.AllocatorRepr input.heap input.base 8 (wmod 44) (machine entries start) ∧
    Objects.Gap input.heap input.base 40 44 := by
  have old : Objects.AllocatorRepr input.heap input.base 8 (wmod 40)
      {input.machine with store := store entries start} := input.allocator.mem_eq rfl
  exact old.reserveArray (wmod 3) (by decide)
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
    · simp only [machine, allocateMachine, writeMachine, store, source, Slot.add, Nat.zero_add,
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
        simp only [machine, allocateMachine, writeMachine, store, source, Slot.add, Nat.zero_add,
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
private theorem rowBound (entries : List Row) (bounded : entries.length < 4) : (rows entries).length < W := by
  simp only [rows, List.length_map]
  have large : 1024 < W := wide
  omega

theorem certificate_inhabited : NestedStorageParentCertificate := nestedStorageParent

theorem actual_typed (entries : List Row) (bounded : entries.length < 4) :
    ∃ fits, NestedStorageParentResult input.heap .uint (rows entries) (rowBound entries bounded) input.base 8 (wmod 40)
      (before entries) source (wmod entries.length) fits := by
  have cost : nestedStorageDemand (rows entries) ≤ 128 * entries.length := demand_bound entries
  have fits : (wmod 40).val + nestedStorageParentDemand (rows entries) < W := by
    simp only [nestedStorageParentDemand, rows, List.length_map]
    have large : 1024 < W := wide
    change 40 + (entries.length + 1 + nestedStorageDemand (entries.map convert)) < W
    change nestedStorageDemand (entries.map convert) ≤ 128 * entries.length at cost
    omega
  exact ⟨fits, nested_storage_parent_success input.heap .uint (rows entries) (rowBound entries bounded) input.base 8 (wmod 40)
    (before entries) source (wmod entries.length) 128 (allocator entries)
    (by simp only [rows, List.length_map]; exact (Nat.mod_eq_of_lt (by have large : 1024 < W := wide; omega)).symm)
    (represented entries 0) fits⟩

theorem actual_runtime (entries : List Row) (bounded : entries.length < 4) : ∃ target : Machine,
    run nestedStorageParentCode (((before entries).push (.slot source)).push (.val (wmod entries.length))) =
      .ok (target.push w[40]) 0 ∧
    target.mem 0 = .val (wmod (40 + nestedStorageParentDemand (rows entries))) ∧
    target.mem 40 = .val (wmod entries.length) ∧ target.mem 17 = w[7] ∧
    target.stack = [w[77]] ∧ target.store = (before entries).store := by
  obtain ⟨fits, base', target, ran, allocated, root, extension, shape, below, gaps, keeps, fresh, length, mirror⟩ :=
    actual_typed entries bounded
  let grown := (nestedStorageParentValue .uint (rows entries) (rowBound entries bounded)).copyStToM input.heap rfl
  change base' grown.val.id = wmod 40 at root
  change grown.heap.len grown.val .dyn = (rows entries).length at length
  have header : target.mem 40 = .val (wmod entries.length) := by
    have cell : target.mem (base' grown.val.id).val = .val (wmod (grown.heap.len grown.val .dyn)) :=
      (allocated.heap.arrays .dyn grown.val).length rfl
    rw [root, length] at cell
    simpa only [rows, List.length_map] using cell
  refine ⟨target, ran, allocated.free.cell.trans ?_, header, (below 17 (by decide) (by decide)).trans rfl, ?_, ?_⟩
  · apply congrArg Word.val
    apply Fin.ext
    change 40 + nestedStorageParentDemand (rows entries) = (40 + nestedStorageParentDemand (rows entries)) % W
    exact (Nat.mod_eq_of_lt fits).symm
  · exact congrArg Machine.stack shape
  · simpa only [] using congrArg Machine.store shape

private def empty : Row := ⟨[], by decide⟩
private def pair : Row := ⟨[wmod 11, wmod 23], by decide⟩
private def long : Row := ⟨List.ofFn (fun index : Fin 64 => wmod (index.val + 1)), by rw [List.length_ofFn]; decide⟩
private def mixed : List Row := [pair, empty, long]

theorem empty_parent : ∃ target : Machine,
    run nestedStorageParentCode (((before []).push (.slot source)).push w[0]) = .ok (target.push w[40]) 0 ∧
    target.mem 0 = w[41] ∧ target.mem 40 = w[0] ∧ target.mem 17 = w[7] ∧ target.stack = [w[77]] := by
  obtain ⟨target, ran, cursor, header, old, stack, _⟩ := actual_runtime [] (by decide)
  exact ⟨target, ran, cursor, header, old, stack⟩

theorem mixed_parent_payloads : ∃ target : Machine,
    run nestedStorageParentCode (((before mixed).push (.slot source)).push w[3]) = .ok (target.push w[40]) 0 ∧
    target.mem 40 = w[3] ∧ target.mem 41 = w[44] ∧ target.mem 42 = w[47] ∧ target.mem 43 = w[48] ∧
    target.mem 45 = w[11] ∧ target.mem 46 = w[23] ∧ target.mem 49 = w[1] ∧ target.mem 112 = w[64] := by
  obtain ⟨target, loopRun, pointer1, pointer2, pointer3, header1, header2, header3, payload1, payload2, payload3, payload4⟩ :=
    NestedStorageLoopControls.heterogeneous_pointers_payloads
  have actualLoop : run nestedStorageLoopCode (nestedStorageControl (allocateMachine (before mixed) (wmod 40) (wmod 3))
      source (wmod 40) (wmod 3) (wmod 0)) =
      .ok (nestedStorageControl target source (wmod 40) (wmod 3) (wmod 3)) 0 := loopRun
  have wholeRun : run nestedStorageParentCode (((before mixed).push (.slot source)).push (.val (wmod 3))) =
      .ok (target.push (.val (wmod 40))) 0 := by
    have guard : run (referenceCapacityGuard 0) (((before mixed).push (.slot source)).push (.val (wmod 3))) =
        .ok (((before mixed).push (.slot source)).push (.val (wmod 3))) 0 := by
      rw [nested_storage_parent_guard (before mixed) source (wmod 40) (wmod 3) (allocator mixed).free.cell, if_pos (by decide)]
    rw [nestedStorageParentCode, run_append_ok guard,
      run_append_ok (nested_storage_parent_prefix (before mixed) source (wmod 40) (wmod 3) (allocator mixed).free.cell),
      run_append_ok actualLoop]
    exact nested_storage_parent_exit target source (wmod 40) (wmod 3)
  obtain ⟨other, otherRun, cursor, header, old, stack, store⟩ := actual_runtime mixed (by decide)
  change run nestedStorageParentCode (((before mixed).push (.slot source)).push (.val (wmod 3))) =
    .ok (other.push (.val (wmod 40))) 0 at otherRun
  rw [wholeRun] at otherRun
  have equal : other.mem 40 = target.mem 40 := (congrArg (fun machine => machine.mem 40) (Out.ok.inj otherRun).1).symm
  exact ⟨target, wholeRun, equal ▸ header, pointer1, pointer2, pointer3, payload1, payload2, payload3, payload4⟩

theorem parent_identity_after_children :
    ((nestedStorageParentValue .uint (rows mixed) (rowBound mixed (by decide))).copyStToM input.heap rfl).val.id = input.H.length + 3 := by
  rw [nested_storage_parent_source input.heap .uint (rows mixed) (rowBound mixed (by decide))]
  simp only [mixed, rows, List.map_cons, List.map_nil, nestedStorageValues, SVec.copyStToM_cons, SVec.copyStToM_nil,
    primitive_array_source, Grown.alloc, Heap.alloc, List.length_append, List.length_cons, List.length_nil]

theorem repeated_parent : ∃ fits,
    NestedStorageParentResult input.heap .uint (rows [pair, pair, pair]) (rowBound _ (by decide)) input.base 8 (wmod 40)
      (before [pair, pair, pair]) source (wmod 3) fits := actual_typed _ (by decide)

theorem wrong_first_parent_identity :
    ((nestedStorageParentValue .uint (rows mixed) (rowBound mixed (by decide))).copyStToM input.heap rfl).val.id ≠ input.H.length := by
  rw [parent_identity_after_children]
  omega

theorem wrong_returned_parent (target : Machine) :
    run nestedStorageParentCode (((before mixed).push (.slot source)).push w[3]) ≠ .ok (target.push w[44]) 0 := by
  intro wrong
  obtain ⟨actual, ran, rest⟩ := mixed_parent_payloads
  rw [wrong] at ran
  have equal : (w[44] : Word) = w[40] := (List.cons.inj (congrArg Machine.stack (Out.ok.inj ran).1)).1
  exact (by decide : (w[44] : Word) ≠ w[40]) equal

private def moved (entries : List Row) (cursor : Fin W) : Machine := writeMachine (before entries) 0 (.val cursor)
private theorem moved_allocator (entries : List Row) (cursor : Fin W) (above : 40 ≤ cursor.val) :
    Objects.AllocatorRepr input.heap input.base 8 cursor (moved entries cursor) := by
  have old : Objects.AllocatorRepr input.heap input.base 8 (wmod 40) (before entries) := allocator entries
  refine ⟨old.heap.localWrite 0 (by decide) (.val cursor), ⟨by decide, by omega, ?_, ?_⟩, ?_⟩
  · rfl
  · intro address lower
    exact (upd_other _ _ (by omega : address ≠ 0)).trans (old.free.zero address (by change 40 ≤ address; omega))
  · intro Q reference
    have live : (input.base reference.id).val + Objects.cells input.heap reference ≤ 40 := old.live reference
    omega

theorem actual_refusal (entries : List Row) (bounded : entries.length < 4) (cursor : Fin W)
    (above : 40 ≤ cursor.val) (noRoom : ¬ cursor.val + nestedStorageParentDemand (rows entries) < W) :
    run nestedStorageParentCode (((moved entries cursor).push (.slot source)).push (.val (wmod entries.length))) = .revert :=
  nested_storage_parent_refusal input.heap .uint (rows entries) (rowBound entries bounded) input.base 8 cursor (moved entries cursor)
    source (wmod entries.length) 128 (moved_allocator entries cursor above)
    (by simp only [rows, List.length_map]; exact (Nat.mod_eq_of_lt (by have large : 1024 < W := wide; omega)).symm)
    (represented entries 0) noRoom

theorem empty_parent_saturated_refusal :
    run nestedStorageParentCode (((moved [] wMax).push (.slot source)).push w[0]) = .revert :=
  actual_refusal [] (by decide) wMax (by decide) (by change ¬ W - 1 + 1 < W; have positive : 0 < W := W_pos; omega)

theorem empty_parent_last_fit : ∃ fits,
    NestedStorageParentResult input.heap .uint (rows []) (rowBound [] (by decide)) input.base 8 (wmod (W - 2))
      (moved [] (wmod (W - 2))) source (wmod 0) fits := by
  have large : 1024 < W := wide
  have cursorValue : (wmod (W - 2)).val = W - 2 := Nat.mod_eq_of_lt (by omega)
  have above : 40 ≤ (wmod (W - 2)).val := by rw [cursorValue]; omega
  have fits : (wmod (W - 2)).val + nestedStorageParentDemand (rows []) < W := by
    change (wmod (W - 2)).val + 1 < W
    rw [cursorValue]
    omega
  exact ⟨fits, nested_storage_parent_success input.heap .uint (rows []) (rowBound [] (by decide)) input.base 8 _ _ source (wmod 0) 128
    (moved_allocator [] _ above) rfl (represented [] 0) fits⟩

theorem child_refusal_after_parent :
    run nestedStorageParentCode (((moved [empty] (wmod (W - 3))).push (.slot source)).push w[1]) = .revert := by
  have large : 1024 < W := wide
  have cursorValue : (wmod (W - 3)).val = W - 3 := Nat.mod_eq_of_lt (by omega)
  exact actual_refusal [empty] (by decide) _ (by rw [cursorValue]; omega) (by
    change ¬ (wmod (W - 3)).val + 3 < W
    rw [cursorValue]
    omega)

theorem parent_reserved_before_child_refusal :
    let cursor := wmod (W - 3)
    ∃ reserved : Machine,
      run (referenceCapacityGuard 0 ++ Objects.nestedPrefix) (((moved [empty] cursor).push (.slot source)).push (.val (wmod 1))) =
        .ok (nestedStorageControl reserved source cursor (wmod 1) (wmod 0)) 0 ∧
      Objects.AllocatorRepr input.heap input.base 8 wMax reserved ∧
      reserved.mem cursor.val = w[1] ∧ reserved.mem 0 = .val wMax ∧
      run nestedStorageLoopCode (nestedStorageControl reserved source cursor (wmod 1) (wmod 0)) = .revert ∧
      run nestedStorageParentCode (((moved [empty] cursor).push (.slot source)).push (.val (wmod 1))) = .revert := by
  let cursor := wmod (W - 3)
  have large : 1024 < W := wide
  have cursorValue : cursor.val = W - 3 := Nat.mod_eq_of_lt (by omega)
  have above : 40 ≤ cursor.val := by rw [cursorValue]; omega
  have parentFits : cursor.val + (wmod 1).val + 1 < W := by
    change cursor.val + 1 + 1 < W
    rw [cursorValue]
    omega
  let reserved := allocateMachine (moved [empty] cursor) cursor (wmod 1)
  have initialAllocator : Objects.AllocatorRepr input.heap input.base 8 cursor (moved [empty] cursor) := moved_allocator [empty] cursor above
  have reservation : Objects.AllocatorRepr input.heap input.base 8 ⟨cursor.val + (wmod 1).val + 1, parentFits⟩ reserved ∧
      Objects.Gap input.heap input.base cursor.val (cursor.val + (wmod 1).val + 1) :=
    initialAllocator.reserveArray (wmod 1) parentFits
  have nextCursor : (⟨cursor.val + (wmod 1).val + 1, parentFits⟩ : Fin W) = wMax := by
    apply Fin.ext
    change cursor.val + 1 + 1 = W - 1
    omega
  have allocated : Objects.AllocatorRepr input.heap input.base 8 wMax reserved := by
    rw [nextCursor] at reservation
    exact reservation.1
  have guard : run (referenceCapacityGuard 0) (((moved [empty] cursor).push (.slot source)).push (.val (wmod 1))) =
      .ok (((moved [empty] cursor).push (.slot source)).push (.val (wmod 1))) 0 := by
    rw [nested_storage_parent_guard (moved [empty] cursor) source cursor (wmod 1) initialAllocator.free.cell,
      if_pos parentFits]
  have prefixRun : run (referenceCapacityGuard 0 ++ Objects.nestedPrefix)
      (((moved [empty] cursor).push (.slot source)).push (.val (wmod 1))) =
      .ok (nestedStorageControl reserved source cursor (wmod 1) (wmod 0)) 0 := by
    rw [run_append_ok guard]
    exact nested_storage_parent_prefix (moved [empty] cursor) source cursor (wmod 1) initialAllocator.free.cell
  have rejected : run nestedStorageLoopCode (nestedStorageControl reserved source cursor (wmod 1) (wmod 0)) = .revert :=
    (nested_storage_loop_refusal input.heap .uint (rows [empty]) input.base 8 wMax reserved source cursor (wmod 1) (wmod 0) 128
      allocated reservation.2 (by omega) (by change cursor.val + 1 + 1 ≤ W - 1; omega) rfl
      (represented [empty] 0) (by change ¬ W - 1 + 1 < W; omega)).2
  exact ⟨reserved, prefixRun, allocated, allocateMachine_header _ _ _ (by omega), allocated.free.cell,
    rejected, child_refusal_after_parent⟩

theorem wrong_parent_header (target : Machine)
    (ran : run nestedStorageParentCode (((before mixed).push (.slot source)).push w[3]) = .ok (target.push w[40]) 0) :
    target.mem 40 ≠ w[0] := by
  obtain ⟨actual, execution, header, rest⟩ := mixed_parent_payloads
  rw [ran] at execution
  have equal : target.mem 40 = actual.mem 40 := congrArg (fun machine => machine.mem 40) (Out.ok.inj execution).1
  rw [equal, header]
  decide

theorem old_aliases_preserved : ∃ target : Machine,
    run nestedStorageParentCode (((before mixed).push (.slot source)).push (.val (wmod 3))) = .ok (target.push w[40]) 0 ∧
    target.mem 1 = w[24] ∧ target.mem 2 = w[24] ∧ target.mem 3 = w[32] ∧ target.mem 17 = w[7] := by
  obtain ⟨_, _, target, ran, _, _, _, _, below, _⟩ := actual_typed mixed (by decide)
  exact ⟨target, ran, (below 1 (by decide) (by decide)).trans rfl,
    (below 2 (by decide) (by decide)).trans rfl, (below 3 (by decide) (by decide)).trans rfl,
    (below 17 (by decide) (by decide)).trans rfl⟩

private def many : List Row := List.replicate 64 empty

theorem long_parent_success : ∃ fits,
    NestedStorageParentResult input.heap .uint (rows many) (by rw [rows, List.length_map, many, List.length_replicate]; decide)
      input.base 8 (wmod 40) (before many) source (wmod 64) fits := by
  have cost : nestedStorageDemand (rows many) ≤ 128 * 64 := by
    simpa only [many, List.length_replicate] using demand_bound many
  have large : 16384 < W := by decide
  have fits : (wmod 40).val + nestedStorageParentDemand (rows many) < W := by
    change 40 + ((rows many).length + 1 + nestedStorageDemand (rows many)) < W
    rw [rows, List.length_map, many, List.length_replicate]
    change nestedStorageDemand (List.map convert (List.replicate 64 empty)) ≤ 128 * 64 at cost
    omega
  exact ⟨fits, nested_storage_parent_success input.heap .uint (rows many) _ input.base 8 (wmod 40) (before many) source
    (wmod 64) 128 (allocator many) (by rw [rows, List.length_map, many, List.length_replicate]; rfl)
    (represented many 0) fits⟩

#print axioms certificate_inhabited
#print axioms actual_typed
#print axioms actual_runtime
#print axioms empty_parent
#print axioms mixed_parent_payloads
#print axioms parent_identity_after_children
#print axioms repeated_parent
#print axioms wrong_first_parent_identity
#print axioms wrong_returned_parent
#print axioms actual_refusal
#print axioms empty_parent_saturated_refusal
#print axioms empty_parent_last_fit
#print axioms child_refusal_after_parent
#print axioms parent_reserved_before_child_refusal
#print axioms wrong_parent_header
#print axioms old_aliases_preserved
#print axioms long_parent_success
end Solidity.Backend.MemoryCopies.NestedStorageParentControls
