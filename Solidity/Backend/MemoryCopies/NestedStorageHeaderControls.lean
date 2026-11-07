import Solidity.Backend.MemoryCopies.NestedStorageHeader
import Solidity.Evm.MemoryObjectArrayExamples
import Solidity.Backend.MemoryCopies.TraversalFresh

/-! Actual outer headers select counts and symbolic child bases. The complete
copy retains mixed payloads and admits arbitrary outer storage shadows. -/
namespace Solidity.Backend.MemoryCopies.NestedStorageHeaderControls
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
  | .root 0 => wmod entries.length
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

private def outer : Slot := .root 0
private def before (entries : List Row) : Machine := {input.machine with store := store entries 0}
private abbrev Shadow := SList (.ref (.array (.prim .uint)))
private theorem allocator (entries : List Row) : Objects.AllocatorRepr input.heap input.base 8 (wmod 40) (before entries) :=
  input.allocator.mem_eq rfl
private theorem rowBound (entries : List Row) (bounded : entries.length < 128) : (rows entries).length < W := by
  rw [rows, List.length_map]
  have large : 1024 < W := wide
  omega
private theorem outer_repr (entries : List Row) (bounded : entries.length < 128) (shadow : Shadow) :
    ReprAt (before entries).store 128 (.ref (.array (.ref (.array (.prim .uint))))) outer
      (nestedStorageHeaderValue .uint (rows entries) (rowBound entries bounded) shadow) := by
  refine .array ?_ (by simpa only [rows, List.length_map] using bounded) ?_
  · simp only [before, store, outer, WordStore.read, rows, List.length_map]
    exact Nat.mod_eq_of_lt (by have large : 1024 < W := wide; omega)
  · intro offset selected chosen
    simp only [nested_storage_header_values, rows, List.map_map, List.getElem?_map] at chosen
    obtain ⟨row, picked, equal⟩ := Option.map_eq_some_iff.mp chosen
    cases equal
    have child : ReprAt (before entries).store 128 (.ref (.array (.prim .uint))) (source.add (0 + offset))
        (primitiveArrayValue .uint (convert row).val (convert row).property) :=
      represented entries 0 offset (convert row) (by simp only [rows, List.getElem?_map, picked, Option.map_some])
    simpa only [outer, source, Slot.add, Nat.zero_add, size_array, Nat.mul_one] using child

theorem certificate_inhabited : NestedStorageHeaderCertificate := nestedStorageHeader

theorem actual_typed (entries : List Row) (bounded : entries.length < 4) (shadow : Shadow) :
    ∃ fits, NestedStorageHeaderResult input.heap .uint (rows entries) (rowBound entries (by omega)) shadow input.base 8
      (wmod 40) (before entries) outer fits := by
  have cost : nestedStorageDemand (rows entries) ≤ 128 * entries.length := demand_bound entries
  have fits : (wmod 40).val + nestedStorageParentDemand (rows entries) < W := by
    simp only [nestedStorageParentDemand, rows, List.length_map]
    change 40 + (entries.length + 1 + nestedStorageDemand (entries.map convert)) < W
    change nestedStorageDemand (entries.map convert) ≤ 128 * entries.length at cost
    have large : 1024 < W := wide
    omega
  exact ⟨fits, nested_storage_header_success input.heap .uint (rows entries) _ shadow input.base 8 (wmod 40) (before entries)
    outer 128 (allocator entries) (outer_repr entries (by omega) shadow) fits⟩

theorem actual_runtime (entries : List Row) (bounded : entries.length < 4) (shadow : Shadow) : ∃ target : Machine,
    run nestedStorageHeaderCode ((before entries).push (.slot outer)) = .ok (target.push w[40]) 0 ∧
    target.mem 0 = .val (wmod (40 + nestedStorageParentDemand (rows entries))) ∧
    target.mem 40 = .val (wmod entries.length) ∧ target.mem 17 = w[7] ∧ target.stack = [w[77]] := by
  obtain ⟨fits, base', target, ran, allocated, root, extension, shape, below, gaps, keeps, fresh, length, mirror, shadowCopy⟩ :=
    actual_typed entries bounded shadow
  let grown := (nestedStorageParentValue .uint (rows entries) (rowBound entries (by omega))).copyStToM input.heap rfl
  change base' grown.val.id = wmod 40 at root
  change grown.heap.len grown.val .dyn = (rows entries).length at length
  have header : target.mem 40 = .val (wmod entries.length) := by
    have cell : target.mem (base' grown.val.id).val = .val (wmod (grown.heap.len grown.val .dyn)) :=
      (allocated.heap.arrays .dyn grown.val).length rfl
    rw [root, length] at cell
    simpa only [rows, List.length_map] using cell
  refine ⟨target, ran, allocated.free.cell.trans ?_, header, (below 17 (by decide) (by decide)).trans rfl, ?_⟩
  · apply congrArg Word.val
    apply Fin.ext
    change 40 + nestedStorageParentDemand (rows entries) = (40 + nestedStorageParentDemand (rows entries)) % W
    exact (Nat.mod_eq_of_lt fits).symm
  · exact congrArg Machine.stack shape

private def empty : Row := ⟨[], by decide⟩
private def pair : Row := ⟨[wmod 11, wmod 23], by decide⟩
private def long : Row := ⟨List.ofFn (fun index : Fin 64 => wmod (index.val + 1)), by rw [List.length_ofFn]; decide⟩
private def mixed : List Row := [pair, empty, long]
private def shadows : Nat → Shadow
  | 0 => .nil
  | count + 1 => .cons (primitiveArrayValue .uint (convert pair).val (convert pair).property) (shadows count)

theorem shadow_controls :
    (∃ fits, NestedStorageHeaderResult input.heap .uint (rows mixed) (rowBound mixed (by decide)) (shadows 0) input.base 8
      (wmod 40) (before mixed) outer fits) ∧
    (∃ fits, NestedStorageHeaderResult input.heap .uint (rows mixed) (rowBound mixed (by decide)) (shadows 64) input.base 8
      (wmod 40) (before mixed) outer fits) :=
  ⟨actual_typed mixed (by decide) _, actual_typed mixed (by decide) _⟩

theorem empty_runtime : ∃ target : Machine,
    run nestedStorageHeaderCode ((before []).push (.slot outer)) = .ok (target.push w[40]) 0 ∧
    target.mem 0 = w[41] ∧ target.mem 40 = w[0] ∧ target.mem 17 = w[7] ∧ target.stack = [w[77]] :=
  actual_runtime [] (by decide) .nil

private theorem observed_turn {H : HTy} (heap : Heap H) (base : Nat → Fin W)
    (cursor : Fin W) (before : Machine) (index : Fin W) (row : Row)
    (allocator : Objects.AllocatorRepr heap base 8 cursor before)
    (gap : Objects.Gap heap base 40 44) (above : 44 ≤ cursor.val) (more : index.val < 3)
    (represented : ReprAt before.store 128 (.ref (.array (.prim .uint))) (source.add index.val)
      (primitiveArrayValue .uint (convert row).val (convert row).property))
    (fits : cursor.val + ((convert row).val.length + 1) < W) :
    let grown := (primitiveArrayValue .uint (convert row).val (convert row).property).copyStToM heap rfl
    ∃ base' target,
      run nestedStorageTurnCode (nestedStorageControl before source (wmod 40) (wmod 3) index) =
        .ok (nestedStorageControl target source (wmod 40) (wmod 3) (wmod (index.val + 1))) 0 ∧
      Objects.AllocatorRepr grown.heap base' 8 ⟨cursor.val + ((convert row).val.length + 1), fits⟩ target ∧
      Objects.Gap grown.heap base' 40 44 ∧ target.store = before.store ∧
      target.mem (41 + index.val) = .val cursor ∧ target.mem cursor.val = .val (wmod row.val.length) ∧
      (∀ offset payload, row.val[offset]? = some payload → target.mem (cursor.val + 1 + offset) = .val payload) ∧
      (∀ address, 0 < address → address < cursor.val → address ≠ 41 + index.val → target.mem address = before.mem address) := by
  let grown := (primitiveArrayValue .uint (convert row).val (convert row).property).copyStToM heap rfl
  obtain ⟨base', target, ran, allocated, root, extension, keptGap, pointer, shape, below, gaps, keeps, id, length⟩ :=
    nested_storage_turn_success heap .uint (convert row).val (convert row).property base 8 cursor before source
      (wmod 40) (wmod 3) index 128 allocator gap (by decide) above more represented fits
  change base' grown.val.id = cursor at root
  change grown.heap.len grown.val .dyn = (convert row).val.length at length
  have header : target.mem cursor.val = .val (wmod row.val.length) := by
    have cell : target.mem (base' grown.val.id).val = .val (wmod (grown.heap.len grown.val .dyn)) :=
      (allocated.heap.arrays .dyn grown.val).length rfl
    rw [root, length] at cell
    simpa only [convert, values, List.length_map] using cell
  refine ⟨base', target, ran, allocated, keptGap, ?_, pointer, header, ?_, below⟩
  · simpa only [] using congrArg Machine.store shape
  · intro offset payload picked
    have item : (MObj.elems .dyn (grown.heap.get grown.val))[offset]? = some (indexValue payload) := by
      dsimp only [grown]
      rw [primitive_array_source]
      simp only [Grown.alloc, Heap.get_alloc, MObj.elems_dyn, MObj.wk, primitiveArrayObject,
        MVal.wk, convert, values, List.getElem?_map, picked, Option.map_some]
    have contents : ReprV .uint (indexValue payload) (target.mem ((base' grown.val.id).val + 1 + offset)) :=
      (allocated.heap.arrays .dyn grown.val).elements offset (indexValue payload) item
    obtain ⟨word, stored, equal⟩ := contents
    have same : word = payload := Fin.ext (Int.ofNat_inj.mp equal.symm)
    subst word
    rw [root] at stored
    exact stored

private theorem mixed_loop_words : ∃ target : Machine,
    run nestedStorageLoopCode (nestedStorageControl (machine mixed 0) source (wmod 40) (wmod 3) (wmod 0)) =
      .ok (nestedStorageControl target source (wmod 40) (wmod 3) (wmod 3)) 0 ∧
    target.mem 41 = w[44] ∧ target.mem 42 = w[47] ∧ target.mem 43 = w[48] ∧
    target.mem 44 = w[2] ∧ target.mem 47 = w[0] ∧ target.mem 48 = w[64] ∧
    target.mem 45 = w[11] ∧ target.mem 46 = w[23] ∧ target.mem 49 = w[1] ∧ target.mem 112 = w[64] := by
  let first := (primitiveArrayValue .uint (convert pair).val (convert pair).property).copyStToM input.heap rfl
  have represented1 : ReprAt (machine mixed 0).store 128 (.ref (.array (.prim .uint))) (source.add (wmod 0).val)
      (primitiveArrayValue .uint (convert pair).val (convert pair).property) := represented mixed 0 0 (convert pair) rfl
  obtain ⟨base1, target1, body1, allocated1, gap1, store1, pointer1, header1, contents1, below1⟩ :=
    observed_turn input.heap input.base (wmod 44) (machine mixed 0) (wmod 0) pair
      (initial mixed 0).1 (initial mixed 0).2 (by decide) (by decide) represented1 (by decide)
  have represented2 : ReprAt target1.store 128 (.ref (.array (.prim .uint))) (source.add (wmod 1).val)
      (primitiveArrayValue .uint (convert empty).val (convert empty).property) := by
    rw [store1]
    exact represented mixed 0 1 (convert empty) rfl
  let second := (primitiveArrayValue .uint (convert empty).val (convert empty).property).copyStToM first.heap rfl
  obtain ⟨base2, target2, body2, allocated2, gap2, store2, pointer2, header2, contents2, below2⟩ :=
    observed_turn first.heap base1 (wmod 47) target1 (wmod 1) empty allocated1 gap1 (by decide) (by decide)
      represented2 (by decide)
  have represented3 : ReprAt target2.store 128 (.ref (.array (.prim .uint))) (source.add (wmod 2).val)
      (primitiveArrayValue .uint (convert long).val (convert long).property) := by
    rw [store2, store1]
    exact represented mixed 0 2 (convert long) rfl
  obtain ⟨base3, target3, body3, allocated3, gap3, store3, pointer3, header3, contents3, below3⟩ :=
    observed_turn second.heap base2 (wmod 48) target2 (wmod 2) long allocated2 gap2 (by decide) (by decide)
      represented3 (by simp only [convert, values, List.length_map, long, List.length_ofFn]; decide)
  change run nestedStorageTurnCode (nestedStorageControl (machine mixed 0) source (wmod 40) (wmod 3) (wmod 0)) =
    .ok (nestedStorageControl target1 source (wmod 40) (wmod 3) (wmod 1)) 0 at body1
  change run nestedStorageTurnCode (nestedStorageControl target1 source (wmod 40) (wmod 3) (wmod 1)) =
    .ok (nestedStorageControl target2 source (wmod 40) (wmod 3) (wmod 2)) 0 at body2
  change run nestedStorageTurnCode (nestedStorageControl target2 source (wmod 40) (wmod 3) (wmod 2)) =
    .ok (nestedStorageControl target3 source (wmod 40) (wmod 3) (wmod 3)) 0 at body3
  have iteration : loopIterN (run Objects.childrenCondition) (run nestedStorageTurnCode) 4
      (nestedStorageControl (machine mixed 0) source (wmod 40) (wmod 3) (wmod 0)) =
      .inr (.ok (nestedStorageControl target3 source (wmod 40) (wmod 3) (wmod 3)) 0) := by
    simp only [loopIterN, nested_storage_loop_more _ _ _ _ _ _ (by decide) body1,
      nested_storage_loop_more _ _ _ _ _ _ (by decide) body2,
      nested_storage_loop_more _ _ _ _ _ _ (by decide) body3, nested_storage_loop_done]
  refine ⟨target3, nested_storage_loop_run iteration, ?_, ?_, pointer3, ?_, ?_, header3, ?_, ?_, ?_, ?_⟩
  · exact (below3 41 (by decide) (by decide) (by decide)).trans
      ((below2 41 (by decide) (by decide) (by decide)).trans pointer1)
  · exact (below3 42 (by decide) (by decide) (by decide)).trans pointer2
  · exact (below3 44 (by decide) (by decide) (by decide)).trans
      ((below2 44 (by decide) (by decide) (by decide)).trans header1)
  · exact (below3 47 (by decide) (by decide) (by decide)).trans header2
  · exact (below3 45 (by decide) (by decide) (by decide)).trans
      ((below2 45 (by decide) (by decide) (by decide)).trans (contents1 0 (wmod 11) rfl))
  · exact (below3 46 (by decide) (by decide) (by decide)).trans
      ((below2 46 (by decide) (by decide) (by decide)).trans (contents1 1 (wmod 23) rfl))
  · exact contents3 0 (wmod 1) (by decide +kernel)
  · exact contents3 63 (wmod 64) (by decide +kernel)

theorem mixed_runtime : ∃ target : Machine,
    run nestedStorageHeaderCode ((before mixed).push (.slot outer)) = .ok (target.push w[40]) 0 ∧
    target.mem 40 = w[3] ∧ target.mem 41 = w[44] ∧ target.mem 42 = w[47] ∧ target.mem 43 = w[48] ∧
    target.mem 45 = w[11] ∧ target.mem 46 = w[23] ∧ target.mem 49 = w[1] ∧ target.mem 112 = w[64] := by
  obtain ⟨target, loopRun, p1, p2, p3, h1, h2, h3, v1, v2, v3, v4⟩ := mixed_loop_words
  have actualLoop : run nestedStorageLoopCode (nestedStorageControl (allocateMachine (before mixed) (wmod 40) (wmod 3))
      source (wmod 40) (wmod 3) (wmod 0)) =
      .ok (nestedStorageControl target source (wmod 40) (wmod 3) (wmod 3)) 0 := loopRun
  have enter : run nestedStorageHeaderEnter ((before mixed).push (.slot outer)) =
      .ok (((before mixed).push (.slot source)).push (.val (wmod 3))) 0 :=
    nested_storage_header_enter (before mixed) outer (wmod 3) rfl
  have guard : run (referenceCapacityGuard 0) (((before mixed).push (.slot source)).push (.val (wmod 3))) =
      .ok (((before mixed).push (.slot source)).push (.val (wmod 3))) 0 := by
    rw [nested_storage_parent_guard (before mixed) source (wmod 40) (wmod 3) (allocator mixed).free.cell, if_pos (by decide)]
  have wholeRun : run nestedStorageHeaderCode ((before mixed).push (.slot outer)) = .ok (target.push (.val (wmod 40))) 0 := by
    rw [nestedStorageHeaderCode, run_append_ok enter, nestedStorageParentCode, run_append_ok guard,
      run_append_ok (nested_storage_parent_prefix (before mixed) source (wmod 40) (wmod 3) (allocator mixed).free.cell),
      run_append_ok actualLoop]
    exact nested_storage_parent_exit target source (wmod 40) (wmod 3)
  obtain ⟨other, otherRun, cursor, header, old, stack⟩ := actual_runtime mixed (by decide) .nil
  rw [wholeRun] at otherRun
  have equal : target.mem 40 = other.mem 40 := congrArg (fun machine => machine.mem 40) (Out.ok.inj otherRun).1
  exact ⟨target, wholeRun, equal.trans header, p1, p2, p3, v1, v2, v3, v4⟩

theorem wrong_outer_header :
    ¬ ReprAt (before mixed).store 128 (.ref (.array (.ref (.array (.prim .uint))))) outer
      (nestedStorageHeaderValue .uint (rows []) (rowBound [] (by decide)) .nil) := by
  intro proposed
  cases proposed with
  | array header bound elements =>
    have impossible : (3 : Nat) = 0 := by
      simpa only [before, store, outer, WordStore.read, mixed, rows, List.length_map,
        List.length_cons, List.length_nil, wmod_def] using header
    cases impossible

theorem wrong_retained_payload (target : Machine)
    (ran : run nestedStorageHeaderCode ((before mixed).push (.slot outer)) = .ok (target.push w[40]) 0) : target.mem 45 ≠ w[0] := by
  obtain ⟨actual, execution, header, p1, p2, p3, first, rest⟩ := mixed_runtime
  rw [ran] at execution
  have equal : target.mem 45 = actual.mem 45 := congrArg (fun machine => machine.mem 45) (Out.ok.inj execution).1
  rw [equal, first]
  decide

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

theorem actual_refusal (entries : List Row) (bounded : entries.length < 4) (shadow : Shadow) (cursor : Fin W)
    (above : 40 ≤ cursor.val) (noRoom : ¬ cursor.val + nestedStorageParentDemand (rows entries) < W) :
    run nestedStorageHeaderCode ((moved entries cursor).push (.slot outer)) = .revert :=
  nested_storage_header_refusal input.heap .uint (rows entries) (rowBound entries (by omega)) shadow input.base 8 cursor
    (moved entries cursor) outer 128 (moved_allocator entries cursor above) (outer_repr entries (by omega) shadow) noRoom

theorem saturated_empty_refusal : run nestedStorageHeaderCode ((moved [] wMax).push (.slot outer)) = .revert :=
  actual_refusal [] (by decide) .nil wMax (by decide) (by change ¬ W - 1 + 1 < W; have positive : 0 < W := W_pos; omega)

theorem header_selects_capacity :
    (∃ fits, NestedStorageHeaderResult input.heap .uint (rows []) (rowBound [] (by decide)) .nil input.base 8
      (wmod (W - 2)) (moved [] (wmod (W - 2))) outer fits) ∧
    run nestedStorageHeaderCode ((moved [empty] (wmod (W - 2))).push (.slot outer)) = .revert := by
  have large : 1024 < W := wide
  have cursorValue : (wmod (W - 2)).val = W - 2 := Nat.mod_eq_of_lt (by omega)
  have above : 40 ≤ (wmod (W - 2)).val := by rw [cursorValue]; omega
  have fits : (wmod (W - 2)).val + nestedStorageParentDemand (rows []) < W := by
    change (wmod (W - 2)).val + 1 < W
    rw [cursorValue]
    omega
  exact ⟨⟨fits, nested_storage_header_success input.heap .uint (rows []) _ .nil input.base 8 _ _ outer 128
    (moved_allocator [] _ above) (outer_repr [] (by decide) .nil) fits⟩,
    actual_refusal [empty] (by decide) .nil _ above (by change ¬ (wmod (W - 2)).val + 3 < W; rw [cursorValue]; omega)⟩

theorem child_refusal_after_header :
    run nestedStorageHeaderCode ((moved [empty] (wmod (W - 3))).push (.slot outer)) = .revert := by
  have large : 1024 < W := wide
  have cursorValue : (wmod (W - 3)).val = W - 3 := Nat.mod_eq_of_lt (by omega)
  exact actual_refusal [empty] (by decide) .nil _ (by rw [cursorValue]; omega) (by
    change ¬ (wmod (W - 3)).val + 3 < W
    rw [cursorValue]
    omega)

private def many : List Row := List.replicate 64 empty

theorem long_header_success : ∃ fits,
    NestedStorageHeaderResult input.heap .uint (rows many) (rowBound many (by rw [many, List.length_replicate]; decide)) .nil
      input.base 8 (wmod 40) (before many) outer fits := by
  have cost : nestedStorageDemand (rows many) ≤ 128 * 64 := by
    simpa only [many, List.length_replicate] using demand_bound many
  have large : 16384 < W := by decide
  have fits : (wmod 40).val + nestedStorageParentDemand (rows many) < W := by
    change 40 + ((rows many).length + 1 + nestedStorageDemand (rows many)) < W
    rw [rows, List.length_map, many, List.length_replicate]
    change nestedStorageDemand (List.map convert (List.replicate 64 empty)) ≤ 128 * 64 at cost
    omega
  exact ⟨fits, nested_storage_header_success input.heap .uint (rows many) _ .nil input.base 8 (wmod 40) (before many) outer 128
    (allocator many) (outer_repr many (by rw [many, List.length_replicate]; decide) .nil) fits⟩

#print axioms certificate_inhabited
#print axioms actual_typed
#print axioms actual_runtime
#print axioms shadow_controls
#print axioms empty_runtime
#print axioms mixed_runtime
#print axioms wrong_outer_header
#print axioms wrong_retained_payload
#print axioms actual_refusal
#print axioms saturated_empty_refusal
#print axioms header_selects_capacity
#print axioms child_refusal_after_header
#print axioms long_header_success
end Solidity.Backend.MemoryCopies.NestedStorageHeaderControls
