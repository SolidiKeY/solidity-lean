import Solidity.Backend.MemoryCopies.FixedReferenceStorageLoop
import Solidity.Evm.MemoryObjectArrayExamples
import Solidity.Backend.MemoryCopies.TraversalFresh

/-! Inhabited complete reservations with heterogeneous child lengths, suffix
traversal, exact demand, negative controls and first/later capacity refusal. -/
namespace Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls
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

theorem certificate_inhabited : FixedReferenceStorageLoopCertificate := fixedReferenceStorageLoop

theorem actual_typed (entries : List Row) (start : Fin 4) (remaining : start.val + entries.length = 3) :
    ∃ fits, FixedReferenceStorageLoopResult input.heap .uint (rows entries) input.base 8 (wmod 43)
      (machine entries start.val) source (wmod 40) (wmod 3)
      ⟨start.val, Nat.lt_trans start.isLt (by decide)⟩ fits := by
  have fits : (wmod 43).val + nestedStorageDemand (rows entries) < W := by
    have cost : nestedStorageDemand (rows entries) ≤ 128 * entries.length := demand_bound entries
    have large : 1024 < W := wide
    change 43 + nestedStorageDemand (rows entries) < W
    omega
  exact ⟨fits, fixed_reference_storage_loop_success input.heap .uint (rows entries) input.base 8 (wmod 43)
    (machine entries start.val) source (wmod 40) (wmod 3) _ 128 (initial entries start.val).1
    (initial entries start.val).2 (by decide) (by decide)
    (by simpa only [rows, List.length_map] using remaining) (represented entries start.val) fits⟩

theorem actual_cursor (entries : List Row) (start : Fin 4) (remaining : start.val + entries.length = 3) :
    ∃ target : Machine,
      run fixedReferenceStorageLoopCode (nestedStorageControl (machine entries start.val) source (wmod 40) (wmod 3)
        ⟨start.val, Nat.lt_trans start.isLt (by decide)⟩) =
        .ok (nestedStorageControl target source (wmod 40) (wmod 3) (wmod 3)) 0 ∧
      target.mem 0 = .val (wmod (43 + nestedStorageDemand (rows entries))) ∧
      target.mem 17 = w[7] ∧ target.stack = [w[77]] := by
  obtain ⟨fits, base', target, iteration, ran, allocated, extension, gap, contents, shape, below, gaps, keeps⟩ :=
    actual_typed entries start remaining
  refine ⟨target, ran, ?_, ?_, ?_⟩
  · refine allocated.free.cell.trans ?_
    apply congrArg Word.val
    apply Fin.ext
    change 43 + nestedStorageDemand (rows entries) = (43 + nestedStorageDemand (rows entries)) % W
    exact (Nat.mod_eq_of_lt fits).symm
  · exact (below 17 (by decide) (by decide) (.inl (by change 17 < 40 + start.val; omega))).trans
      (by simp only [machine,allocateStructMachine,writeMachine,upd,↓reduceIte]; rfl)
  · exact congrArg Machine.stack shape

private def empty : Row := ⟨[], by decide⟩
private def pair : Row := ⟨[wmod 11, wmod 23], by decide⟩
private def long : Row := ⟨List.ofFn (fun index : Fin 64 => wmod (index.val + 1)), by rw [List.length_ofFn]; decide⟩
private def mixed : List Row := [pair, empty, long]

theorem heterogeneous_cost : nestedStorageDemand (rows mixed) = 69 := by
  simp only [mixed, rows, List.map_cons, List.map_nil, nestedStorageDemand, convert, values, List.length_map,
    pair, empty, long, List.length_cons, List.length_nil, List.length_ofFn]

theorem heterogeneous_runtime : ∃ target : Machine,
    run fixedReferenceStorageLoopCode (nestedStorageControl (machine mixed 0) source (wmod 40) (wmod 3) (wmod 0)) =
      .ok (nestedStorageControl target source (wmod 40) (wmod 3) (wmod 3)) 0 ∧
    target.mem 0 = w[112] ∧ target.mem 17 = w[7] ∧ target.stack = [w[77]] := by
  simpa only [heterogeneous_cost] using actual_cursor mixed ⟨0, by decide⟩ (by decide)

theorem repeated_children : ∃ fits,
    FixedReferenceStorageLoopResult input.heap .uint (rows [pair, pair, pair]) input.base 8 (wmod 43)
      (machine [pair, pair, pair] 0) source (wmod 40) (wmod 3) (wmod 0) fits :=
  actual_typed [pair, pair, pair] ⟨0, by decide⟩ (by decide)

theorem suffix_prefix_preserved : ∃ target : Machine,
    run fixedReferenceStorageLoopCode (nestedStorageControl (machine [pair] 2) source (wmod 40) (wmod 3) (wmod 2)) =
      .ok (nestedStorageControl target source (wmod 40) (wmod 3) (wmod 3)) 0 ∧ target.mem 40 = w[0] := by
  obtain ⟨_, _, target, _, ran, _, _, _, _, _, below, _⟩ := actual_typed [pair] ⟨2, by decide⟩ (by decide)
  exact ⟨target, ran, (below 40 (by decide) (by decide) (.inl (by decide))).trans
    (by simp only [machine,allocateStructMachine,writeMachine,upd,↓reduceIte]; rfl)⟩

theorem wrong_total_cursor (target : Machine)
    (ran : run fixedReferenceStorageLoopCode (nestedStorageControl (machine mixed 0) source (wmod 40) (wmod 3) (wmod 0)) =
      .ok (nestedStorageControl target source (wmod 40) (wmod 3) (wmod 3)) 0) : target.mem 0 ≠ w[47] := by
  obtain ⟨actual, execution, cursor, _⟩ := heterogeneous_runtime
  rw [ran] at execution
  have equal : target.mem 0 = actual.mem 0 := congrArg (fun machine => machine.mem 0) (Out.ok.inj execution).1
  rw [equal, cursor]
  decide

private def moved (entries : List Row) (start : Nat) (cursor : Fin W) : Machine :=
  writeMachine (machine entries start) 0 (.val cursor)
private theorem moved_allocator (entries : List Row) (start : Nat) (cursor : Fin W) (above : 43 ≤ cursor.val) :
    Objects.AllocatorRepr input.heap input.base 8 cursor (moved entries start cursor) := by
  have old : Objects.AllocatorRepr input.heap input.base 8 (wmod 43) (machine entries start) := (initial entries start).1
  refine ⟨old.heap.localWrite 0 (by decide) (.val cursor), ⟨by decide, by omega, ?_, ?_⟩, ?_⟩
  · rfl
  · intro address lower
    exact (upd_other _ _ (by omega : address ≠ 0)).trans (old.free.zero address (by change 43 ≤ address; omega))
  · intro Q reference
    have live : (input.base reference.id).val + Objects.cells input.heap reference ≤ 43 := old.live reference
    omega

theorem saturated_empty_success : ∃ fits,
    FixedReferenceStorageLoopResult input.heap .uint (rows []) input.base 8 wMax (moved [] 3 wMax)
      source (wmod 40) (wmod 3) (wmod 3) fits := by
  have representation : NestedStorageRowsRepr .uint (rows []) (moved [] 3 wMax) source 3 128 :=
    represented [] 3
  exact ⟨by change W - 1 + 0 < W; have positive : 0 < W := W_pos; omega,
    fixed_reference_storage_loop_success input.heap .uint (rows []) input.base 8 wMax (moved [] 3 wMax)
      source (wmod 40) (wmod 3) (wmod 3) 128 (moved_allocator [] 3 wMax (by decide))
      (initial [] 3).2 (by decide) (by decide) (by decide) representation _⟩

theorem actual_refusal (entries : List Row) (start : Fin 4) (remaining : start.val + entries.length = 3)
    (cursor : Fin W) (above : 43 ≤ cursor.val) (noRoom : ¬ cursor.val + nestedStorageDemand (rows entries) < W) :
    run fixedReferenceStorageLoopCode (nestedStorageControl (moved entries start.val cursor) source (wmod 40) (wmod 3)
      ⟨start.val, Nat.lt_trans start.isLt (by decide)⟩) = .revert := by
  exact (fixed_reference_storage_loop_refusal input.heap .uint (rows entries) input.base 8 cursor (moved entries start.val cursor)
    source (wmod 40) (wmod 3) ⟨start.val, Nat.lt_trans start.isLt (by decide)⟩ 128 (moved_allocator entries start.val cursor above) (initial entries start.val).2
    (by decide) (by change 40 + 3 ≤ cursor.val; omega)
    (by simpa only [rows, List.length_map] using remaining) (represented entries start.val) noRoom).2

theorem saturated_first_refusal :
    run fixedReferenceStorageLoopCode (nestedStorageControl (moved [pair] 2 wMax) source (wmod 40) (wmod 3) (wmod 2)) = .revert :=
  actual_refusal [pair] ⟨2, by decide⟩ (by decide) wMax (by decide) (by
    change ¬ W - 1 + 3 < W
    have large : 1024 < W := wide
    omega)

theorem repeated_freshness :
    let copied := (nestedStorageValues .uint (rows [pair, pair, pair])).copyStToM input.heap rfl
    (∀ identity, identity ∈ copied.val.1.map (fun reference => reference.id) → input.H.length ≤ identity) ∧
      (copied.val.1.map (fun reference => reference.id)).Nodup :=
  ⟨(traversalFresh _ rfl input.heap).fresh, traversal_no_duplicate_ids _ rfl input.heap⟩

theorem wrong_first_child :
    ¬ NestedStorageRowsRepr .uint (rows [empty, pair, long]) (machine mixed 0) source 0 128 := by
  intro proposed
  have first : ReprAt (machine mixed 0).store 128 (.ref (.array (.prim .uint))) source
      (primitiveArrayValue .uint (convert empty).val (convert empty).property) := proposed 0 (convert empty) rfl
  cases first with
  | array header bound elements =>
    have impossible : (2 : Nat) = 0 := by
      simpa only [machine, allocateStructMachine, writeMachine, store, source, WordStore.read,
        Nat.le_refl, if_true, Nat.sub_zero, payloadAt, mixed, List.getElem?_cons_zero,
        Option.map_some, Option.getD_some, pair, empty, convert, values, List.length_map,
        List.length_cons, List.length_nil, wmod_def] using header
    cases impossible

theorem later_refusal_has_prefix :
    let first := (primitiveArrayValue .uint (convert empty).val (convert empty).property).copyStToM input.heap rfl
    ∃ base' target,
      run fixedReferenceStorageTurnCode (nestedStorageControl (moved [empty, empty] 1 (wmod (W - 2))) source
        (wmod 40) (wmod 3) (wmod 1)) =
        .ok (nestedStorageControl target source (wmod 40) (wmod 3) (wmod 2)) 0 ∧
      Objects.AllocatorRepr first.heap base' 8 wMax target ∧
      target.mem 41 = .val (wmod (W - 2)) ∧
      run fixedReferenceStorageTurnCode (nestedStorageControl target source (wmod 40) (wmod 3) (wmod 2)) = .revert ∧
      run fixedReferenceStorageLoopCode (nestedStorageControl (moved [empty, empty] 1 (wmod (W - 2))) source
        (wmod 40) (wmod 3) (wmod 1)) = .revert := by
  have large : 1024 < W := wide
  have cursorValue : (wmod (W - 2)).val = W - 2 := Nat.mod_eq_of_lt (by omega)
  have above : 43 ≤ (wmod (W - 2)).val := by rw [cursorValue]; omega
  have firstFits : (wmod (W - 2)).val + ((convert empty).val.length + 1) < W := by
    rw [cursorValue]
    change W - 2 + (0 + 1) < W
    omega
  have head : ReprAt (moved [empty, empty] 1 (wmod (W - 2))).store 128 (.ref (.array (.prim .uint)))
      (source.add (wmod 1).val) (primitiveArrayValue .uint (convert empty).val (convert empty).property) :=
    represented [empty, empty] 1 0 (convert empty) rfl
  obtain ⟨base', target, body, allocated, root, extension, gap, pointer, shape, below, gaps, keeps, id, length⟩ :=
    fixed_reference_storage_turn_success input.heap .uint (convert empty).val (convert empty).property input.base 8 (wmod (W - 2))
      (moved [empty, empty] 1 (wmod (W - 2))) source (wmod 40) (wmod 3) (wmod 1) 128
      (moved_allocator [empty, empty] 1 _ above) (initial [empty, empty] 1).2 (by decide)
      (by change 43 ≤ (wmod (W - 2)).val; exact above) (by decide) head firstFits
  have nextCursor : (⟨(wmod (W - 2)).val + ((convert empty).val.length + 1), firstFits⟩ : Fin W) = wMax := by
    apply Fin.ext
    change (wmod (W - 2)).val + (0 + 1) = W - 1
    omega
  rw [nextCursor] at allocated
  have second : ReprAt target.store 128 (.ref (.array (.prim .uint))) (source.add (wmod 2).val)
      (primitiveArrayValue .uint (convert empty).val (convert empty).property) := by
    have saved : target.store = (moved [empty, empty] 1 (wmod (W - 2))).store := by
      simpa only [] using congrArg Machine.store shape
    rw [saved]
    exact represented [empty, empty] 1 1 (convert empty) rfl
  have secondRun : run fixedReferenceStorageTurnCode (nestedStorageControl target source (wmod 40) (wmod 3) (wmod 2)) = .revert := by
    rcases fixed_reference_storage_turn_correct _ .uint (convert empty).val (convert empty).property base' 8 wMax target source
      (wmod 40) (wmod 3) (wmod 2) 128 allocated gap (by decide) (by decide) (by decide) second with success | refusal
    · have impossible : W - 1 + (0 + 1) < W := success.choose
      omega
    · exact refusal.2
  exact ⟨base', target, body, allocated, pointer, secondRun,
    actual_refusal [empty, empty] ⟨1, by decide⟩ (by decide) _ above (by
      change ¬ (wmod (W - 2)).val + 2 < W
      rw [cursorValue]
      omega)⟩

private theorem observed_turn {H : HTy} (heap : Heap H) (base : Nat → Fin W)
    (cursor : Fin W) (before : Machine) (index : Fin W) (row : Row)
    (allocator : Objects.AllocatorRepr heap base 8 cursor before)
    (gap : Objects.Gap heap base 40 43) (above : 43 ≤ cursor.val) (more : index.val < 3)
    (represented : ReprAt before.store 128 (.ref (.array (.prim .uint))) (source.add index.val)
      (primitiveArrayValue .uint (convert row).val (convert row).property))
    (fits : cursor.val + ((convert row).val.length + 1) < W) :
    let grown := (primitiveArrayValue .uint (convert row).val (convert row).property).copyStToM heap rfl
    ∃ base' target,
      run fixedReferenceStorageTurnCode (nestedStorageControl before source (wmod 40) (wmod 3) index) =
        .ok (nestedStorageControl target source (wmod 40) (wmod 3) (wmod (index.val + 1))) 0 ∧
      Objects.AllocatorRepr grown.heap base' 8 ⟨cursor.val + ((convert row).val.length + 1), fits⟩ target ∧
      Objects.Gap grown.heap base' 40 43 ∧ target.store = before.store ∧
      target.mem (40 + index.val) = .val cursor ∧ target.mem cursor.val = .val (wmod row.val.length) ∧
      (∀ offset payload, row.val[offset]? = some payload → target.mem (cursor.val + 1 + offset) = .val payload) ∧
      (∀ address, 0 < address → address < cursor.val → address ≠ 40 + index.val → target.mem address = before.mem address) := by
  let grown := (primitiveArrayValue .uint (convert row).val (convert row).property).copyStToM heap rfl
  obtain ⟨base', target, ran, allocated, root, extension, keptGap, pointer, shape, below, gaps, keeps, id, length⟩ :=
    fixed_reference_storage_turn_success heap .uint (convert row).val (convert row).property base 8 cursor before source
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

theorem heterogeneous_pointers_payloads : ∃ target : Machine,
    run fixedReferenceStorageLoopCode (nestedStorageControl (machine mixed 0) source (wmod 40) (wmod 3) (wmod 0)) =
      .ok (nestedStorageControl target source (wmod 40) (wmod 3) (wmod 3)) 0 ∧
    target.mem 40 = w[43] ∧ target.mem 41 = w[46] ∧ target.mem 42 = w[47] ∧
    target.mem 43 = w[2] ∧ target.mem 46 = w[0] ∧ target.mem 47 = w[64] ∧
    target.mem 44 = w[11] ∧ target.mem 45 = w[23] ∧ target.mem 48 = w[1] ∧ target.mem 111 = w[64] := by
  let first := (primitiveArrayValue .uint (convert pair).val (convert pair).property).copyStToM input.heap rfl
  have represented1 : ReprAt (machine mixed 0).store 128 (.ref (.array (.prim .uint))) (source.add (wmod 0).val)
      (primitiveArrayValue .uint (convert pair).val (convert pair).property) := represented mixed 0 0 (convert pair) rfl
  obtain ⟨base1, target1, body1, allocated1, gap1, store1, pointer1, header1, contents1, below1⟩ :=
    observed_turn input.heap input.base (wmod 43) (machine mixed 0) (wmod 0) pair
      (initial mixed 0).1 (initial mixed 0).2 (by decide) (by decide) represented1 (by decide)
  have represented2 : ReprAt target1.store 128 (.ref (.array (.prim .uint))) (source.add (wmod 1).val)
      (primitiveArrayValue .uint (convert empty).val (convert empty).property) := by
    rw [store1]
    exact represented mixed 0 1 (convert empty) rfl
  let second := (primitiveArrayValue .uint (convert empty).val (convert empty).property).copyStToM first.heap rfl
  obtain ⟨base2, target2, body2, allocated2, gap2, store2, pointer2, header2, contents2, below2⟩ :=
    observed_turn first.heap base1 (wmod 46) target1 (wmod 1) empty allocated1 gap1 (by decide) (by decide)
      represented2 (by decide)
  have represented3 : ReprAt target2.store 128 (.ref (.array (.prim .uint))) (source.add (wmod 2).val)
      (primitiveArrayValue .uint (convert long).val (convert long).property) := by
    rw [store2, store1]
    exact represented mixed 0 2 (convert long) rfl
  obtain ⟨base3, target3, body3, allocated3, gap3, store3, pointer3, header3, contents3, below3⟩ :=
    observed_turn second.heap base2 (wmod 47) target2 (wmod 2) long allocated2 gap2 (by decide) (by decide)
      represented3 (by simp only [convert, values, List.length_map, long, List.length_ofFn]; decide)
  change run fixedReferenceStorageTurnCode (nestedStorageControl (machine mixed 0) source (wmod 40) (wmod 3) (wmod 0)) =
    .ok (nestedStorageControl target1 source (wmod 40) (wmod 3) (wmod 1)) 0 at body1
  change run fixedReferenceStorageTurnCode (nestedStorageControl target1 source (wmod 40) (wmod 3) (wmod 1)) =
    .ok (nestedStorageControl target2 source (wmod 40) (wmod 3) (wmod 2)) 0 at body2
  change run fixedReferenceStorageTurnCode (nestedStorageControl target2 source (wmod 40) (wmod 3) (wmod 2)) =
    .ok (nestedStorageControl target3 source (wmod 40) (wmod 3) (wmod 3)) 0 at body3
  have iteration : loopIterN (run Objects.childrenCondition) (run fixedReferenceStorageTurnCode) 4
      (nestedStorageControl (machine mixed 0) source (wmod 40) (wmod 3) (wmod 0)) =
      .inr (.ok (nestedStorageControl target3 source (wmod 40) (wmod 3) (wmod 3)) 0) := by
    simp only [loopIterN, fixed_reference_storage_loop_more _ _ _ _ _ _ (by decide) body1,
      fixed_reference_storage_loop_more _ _ _ _ _ _ (by decide) body2,
      fixed_reference_storage_loop_more _ _ _ _ _ _ (by decide) body3, fixed_reference_storage_loop_done]
  refine ⟨target3, fixed_reference_storage_loop_run iteration, ?_, ?_, pointer3, ?_, ?_, header3, ?_, ?_, ?_, ?_⟩
  · exact (below3 40 (by decide) (by decide) (by decide)).trans
      ((below2 40 (by decide) (by decide) (by decide)).trans pointer1)
  · exact (below3 41 (by decide) (by decide) (by decide)).trans pointer2
  · exact (below3 43 (by decide) (by decide) (by decide)).trans
      ((below2 43 (by decide) (by decide) (by decide)).trans header1)
  · exact (below3 46 (by decide) (by decide) (by decide)).trans header2
  · exact (below3 44 (by decide) (by decide) (by decide)).trans
      ((below2 44 (by decide) (by decide) (by decide)).trans (contents1 0 (wmod 11) rfl))
  · exact (below3 45 (by decide) (by decide) (by decide)).trans
      ((below2 45 (by decide) (by decide) (by decide)).trans (contents1 1 (wmod 23) rfl))
  · exact contents3 0 (wmod 1) (by decide +kernel)
  · exact contents3 63 (wmod 64) (by decide +kernel)

theorem wrong_retained_payload (target : Machine)
    (ran : run fixedReferenceStorageLoopCode (nestedStorageControl (machine mixed 0) source (wmod 40) (wmod 3) (wmod 0)) =
      .ok (nestedStorageControl target source (wmod 40) (wmod 3) (wmod 3)) 0) : target.mem 44 ≠ w[0] := by
  obtain ⟨actual, execution, p1, p2, p3, h1, h2, h3, first, rest⟩ := heterogeneous_pointers_payloads
  rw [ran] at execution
  have equal : target.mem 44 = actual.mem 44 := congrArg (fun machine => machine.mem 44) (Out.ok.inj execution).1
  rw [equal, first]
  decide

private def zeroParent : Machine := allocateStructMachine input.machine (wmod 40) 1

theorem zero_outer_reservation :
    ∃ fits, FixedReferenceStorageLoopResult input.heap .uint [] input.base 8 (wmod 41)
      zeroParent source (wmod 40) (wmod 0) (wmod 0) fits ∧
      zeroParent.mem 0 = w[41] ∧ zeroParent.mem 40 = w[0] := by
  have reserved : Objects.AllocatorRepr input.heap input.base 8 (wmod 41) zeroParent ∧
      Objects.Gap input.heap input.base 40 41 := input.allocator.reserveFixed 0 (by decide)
  refine ⟨by decide,fixed_reference_storage_loop_success input.heap .uint [] input.base 8 (wmod 41)
    zeroParent source (wmod 40) (wmod 0) (wmod 0) 128 reserved.1 reserved.2
    (by decide) (by decide) (by decide) ?_ (by decide),rfl,rfl⟩
  intro offset row chosen
  cases chosen

/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls.certificate_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms certificate_inhabited
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls.actual_typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_typed
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls.actual_cursor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_cursor
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls.heterogeneous_cost' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms heterogeneous_cost
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls.heterogeneous_runtime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms heterogeneous_runtime
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls.repeated_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms repeated_children
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls.suffix_prefix_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms suffix_prefix_preserved
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls.wrong_total_cursor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms wrong_total_cursor
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls.saturated_empty_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms saturated_empty_success
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls.actual_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_refusal
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls.saturated_first_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms saturated_first_refusal
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls.repeated_freshness' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms repeated_freshness
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls.wrong_first_child' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms wrong_first_child
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls.later_refusal_has_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms later_refusal_has_prefix
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls.heterogeneous_pointers_payloads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms heterogeneous_pointers_payloads
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls.wrong_retained_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms wrong_retained_payload
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls.zero_outer_reservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms zero_outer_reservation
end Solidity.Backend.MemoryCopies.FixedReferenceStorageLoopControls
