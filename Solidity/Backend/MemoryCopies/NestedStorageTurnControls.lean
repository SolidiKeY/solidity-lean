import Solidity.Backend.MemoryCopies.NestedStorageTurn
import Solidity.Evm.MemoryObjectArrayExamples

/-! Real parent reservations with dynamic child payloads, exact control-stack
restoration and checked refusal. The parent remains an unadopted reservation. -/
namespace Solidity.Backend.MemoryCopies.NestedStorageTurnControls
open Evm Evm.Memory
private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def input : Input := ⟨_, _, _, _, ObjectArrayExamples.initial_allocator⟩
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private theorem wide : 128 < W := by decide
private def value (payloads : List (Fin W)) (bounded : payloads.length < 128) : SVal (.ref (.array (.prim .uint))) :=
  primitiveArrayValue .uint (values payloads) (by rw [values, List.length_map]; exact Nat.lt_trans bounded wide)
private def source : Slot := .data (.root 0) 0
private def store (payloads : List (Fin W)) (selected : Fin 2) : WordStore := ⟨fun slot => match slot with
  | .data (.root 0) index => if index = selected.val then wmod payloads.length else wmod 0
  | .data (.data (.root 0) index) offset => if index = selected.val then payloads[offset]?.getD (wmod 0) else wmod 0
  | _ => wmod 0⟩
private def machine (payloads : List (Fin W)) (selected : Fin 2) : Machine :=
  allocateMachine {input.machine with store := store payloads selected} (wmod 40) (wmod 2)
private def grown (payloads : List (Fin W)) (bounded : payloads.length < 128) :=
  (value payloads bounded).copyStToM input.heap rfl
private theorem represented (payloads : List (Fin W)) (bounded : payloads.length < 128) (selected : Fin 2) :
    ReprAt (machine payloads selected).store 128 (.ref (.array (.prim .uint)))
      (source.add selected.val) (value payloads bounded) := by
  refine .array ?_ (by simpa only [values, List.length_map] using bounded) ?_
  · simp only [machine, allocateMachine, writeMachine, store, source, Slot.add, Nat.zero_add, values, List.length_map]
    simp only [WordStore.read]
    exact Nat.mod_eq_of_lt (Nat.lt_trans bounded wide)
  · intro index item chosen
    simp only [SVec.toList_ofList, values, List.getElem?_map] at chosen
    cases picked : payloads[index]? with
    | none => simp only [picked, Option.map_none] at chosen; cases chosen
    | some payload =>
      simp only [picked, Option.map_some] at chosen
      cases chosen
      simp only [size_prim, Nat.mul_one]
      refine .prim (ReprV.uint_of ?_)
      simp only [machine, allocateMachine, writeMachine, store, source, Slot.add, Nat.zero_add,
        picked, Option.getD_some]
      rfl
private theorem initial (payloads : List (Fin W)) (selected : Fin 2) :
    Objects.AllocatorRepr input.heap input.base 8 (wmod 43) (machine payloads selected) ∧
    Objects.Gap input.heap input.base 40 43 := by
  have inputAllocator : Objects.AllocatorRepr input.heap input.base 8 (wmod 40)
      {input.machine with store := store payloads selected} := input.allocator.mem_eq rfl
  exact inputAllocator.reserveArray (wmod 2) (by decide)

theorem certificate_inhabited : NestedStorageTurnCertificate := nestedStorageTurn

theorem actual_typed (payloads : List (Fin W)) (bounded : payloads.length < 128) (selected : Fin 2) :
    NestedStorageTurnResult input.heap .uint (values payloads)
      (by rw [values, List.length_map]; exact Nat.lt_trans bounded wide)
      input.base 8 (wmod 43) (machine payloads selected) source (wmod 40) (wmod 2)
      ⟨selected.val, Nat.lt_trans selected.isLt (by decide)⟩ (by
        change 43 + ((values payloads).length + 1) < W
        rw [values, List.length_map]
        have large : 256 < W := by decide
        omega) :=
  nested_storage_turn_success input.heap .uint _ _ input.base 8 (wmod 43) (machine payloads selected)
    source (wmod 40) (wmod 2) _ 128 (initial payloads selected).1 (initial payloads selected).2
    (by decide) (by decide) selected.isLt (represented payloads bounded selected) _

theorem actual_runtime (payloads : List (Fin W)) (bounded : payloads.length < 128) (selected : Fin 2) :
    ∃ target : Machine,
      run nestedStorageTurnCode (nestedStorageControl (machine payloads selected) source (wmod 40) (wmod 2)
        ⟨selected.val, Nat.lt_trans selected.isLt (by decide)⟩) =
        .ok (nestedStorageControl target source (wmod 40) (wmod 2) (wmod (selected.val + 1))) 0 ∧
      target.mem (41 + selected.val) = w[43] ∧ target.mem 40 = w[2] ∧
      target.mem 43 = .val (wmod payloads.length) ∧ target.mem 17 = w[7] ∧
      target.stack = [w[77]] ∧ target.store = (machine payloads selected).store ∧
      (∀ offset payload, payloads[offset]? = some payload → target.mem (44 + offset) = .val payload) := by
  obtain ⟨base', target, ran, allocated, root, extension, gap, pointer, shape, below, gaps, keeps, identity, length⟩ :=
    actual_typed payloads bounded selected
  change base' (grown payloads bounded).val.id = wmod 43 at root
  change (grown payloads bounded).heap.len (grown payloads bounded).val .dyn = (values payloads).length at length
  have header : target.mem 43 = .val (wmod payloads.length) := by
    have cell : target.mem (base' (grown payloads bounded).val.id).val =
        .val (wmod ((grown payloads bounded).heap.len (grown payloads bounded).val .dyn)) :=
      (allocated.heap.arrays .dyn (grown payloads bounded).val).length rfl
    rw [root, length] at cell
    simpa only [values, List.length_map] using cell
  refine ⟨target, ran, pointer, ?_, header, ?_, ?_, ?_, ?_⟩
  · exact (below 40 (by decide) (by decide) (by change 40 ≠ 40 + 1 + selected.val; omega)).trans (by
      exact allocateMachine_header _ _ _ (by decide))
  · exact (below 17 (by decide) (by decide) (by change 17 ≠ 40 + 1 + selected.val; omega)).trans (by
      exact (allocateMachine_other _ _ _ _ (by decide) (by decide)).trans rfl)
  · exact congrArg Machine.stack shape
  · simpa only [] using congrArg Machine.store shape
  · intro offset payload picked
    have item : (MObj.elems .dyn ((grown payloads bounded).heap.get (grown payloads bounded).val))[offset]? = some (indexValue payload) := by
      dsimp only [grown, value]
      rw [primitive_array_source]
      simp only [Grown.alloc, Heap.get_alloc, MObj.elems_dyn, MObj.wk, primitiveArrayObject, MVal.wk,
        values, List.getElem?_map, picked, Option.map_some]
    have representedItem : ReprV .uint (indexValue payload)
        (target.mem ((base' (grown payloads bounded).val.id).val + 1 + offset)) :=
      (allocated.heap.arrays .dyn (grown payloads bounded).val).elements offset (indexValue payload) item
    obtain ⟨word, stored, equal⟩ := representedItem
    have same : word = payload := Fin.ext (Int.ofNat_inj.mp equal.symm)
    subst word
    rw [root] at stored
    exact stored

theorem empty_first : ∃ target : Machine,
    run nestedStorageTurnCode (nestedStorageControl (machine [] ⟨0, by decide⟩) source (wmod 40) (wmod 2) (wmod 0)) =
      .ok (nestedStorageControl target source (wmod 40) (wmod 2) (wmod 1)) 0 ∧
    target.mem 41 = w[43] ∧ target.mem 43 = w[0] := by
  obtain ⟨target, ran, pointer, _, header, _⟩ := actual_runtime [] (by decide) ⟨0, by decide⟩
  exact ⟨target, ran, pointer, header⟩

theorem pair_last : ∃ target : Machine,
    run nestedStorageTurnCode (nestedStorageControl (machine [wmod 11, wmod 23] ⟨1, by decide⟩)
      source (wmod 40) (wmod 2) (wmod 1)) =
      .ok (nestedStorageControl target source (wmod 40) (wmod 2) (wmod 2)) 0 ∧
    target.mem 42 = w[43] ∧ target.mem 40 = w[2] ∧ target.mem 43 = w[2] ∧
    target.mem 44 = w[11] ∧ target.mem 45 = w[23] ∧ target.mem 17 = w[7] ∧ target.stack = [w[77]] := by
  obtain ⟨target, ran, pointer, parentHeader, childHeader, old, stack, _, contents⟩ :=
    actual_runtime [wmod 11, wmod 23] (by decide) ⟨1, by decide⟩
  exact ⟨target, ran, pointer, parentHeader, childHeader, contents 0 _ rfl, contents 1 _ rfl, old, stack⟩

private def long : List (Fin W) := List.ofFn (fun index : Fin 64 => wmod (index.val + 1))

theorem long_first : ∃ target : Machine,
    run nestedStorageTurnCode (nestedStorageControl (machine long ⟨0, by decide⟩)
      source (wmod 40) (wmod 2) (wmod 0)) =
      .ok (nestedStorageControl target source (wmod 40) (wmod 2) (wmod 1)) 0 ∧
    target.mem 41 = w[43] ∧ target.mem 40 = w[2] ∧ target.mem 43 = w[64] ∧
    target.mem 44 = w[1] ∧ target.mem 107 = w[64] ∧ target.mem 17 = w[7] := by
  obtain ⟨target, ran, pointer, parentHeader, childHeader, old, _, _, contents⟩ :=
    actual_runtime long (by rw [long, List.length_ofFn]; decide) ⟨0, by decide⟩
  exact ⟨target, ran, pointer, parentHeader, childHeader,
    contents 0 (wmod 1) (by decide +kernel), contents 63 (wmod 64) (by decide +kernel), old⟩

theorem actual_cursor (payloads : List (Fin W)) (bounded : payloads.length < 128) (selected : Fin 2) :
    ∃ target : Machine,
      run nestedStorageTurnCode (nestedStorageControl (machine payloads selected) source (wmod 40) (wmod 2)
        ⟨selected.val, Nat.lt_trans selected.isLt (by decide)⟩) =
        .ok (nestedStorageControl target source (wmod 40) (wmod 2) (wmod (selected.val + 1))) 0 ∧
      target.mem 0 = .val (wmod (44 + payloads.length)) := by
  obtain ⟨_, target, ran, allocated, _⟩ := actual_typed payloads bounded selected
  refine ⟨target, ran, allocated.free.cell.trans ?_⟩
  apply congrArg Word.val
  apply Fin.ext
  have room : 44 + payloads.length < W := by
    have large : 256 < W := by decide
    omega
  simp only [values, List.length_map, wmod_def, Nat.mod_eq_of_lt (show 43 < W by decide),
    Nat.mod_eq_of_lt room]
  omega

theorem wrong_child_slot :
    ¬ ReprAt (machine [wmod 11, wmod 23] ⟨0, by decide⟩).store 128 (.ref (.array (.prim .uint)))
      (source.add 1) (value [wmod 11, wmod 23] (by decide)) := by
  intro proposed
  cases proposed with
  | array header bound elements =>
    have impossible : (0 : Nat) = 2 := by
      simpa only [machine, allocateMachine, writeMachine, store, source, Slot.add, Nat.zero_add,
        WordStore.read, WordStore.cells, Nat.one_ne_zero, if_false, wmod_def, Nat.zero_mod,
        value, primitiveArrayValue, values, List.length_map, List.length_cons, List.length_nil] using header
    cases impossible

theorem strict_freshness (payloads : List (Fin W)) (bounded : payloads.length < 128)
    {R : RefTy} (old : HRef input.H R) : old.id < (grown payloads bounded).val.id :=
  Nat.lt_of_lt_of_le old.id_lt (SVal.copyStToM_id_ge input.heap (value payloads bounded) rfl)

theorem wrong_pointer (target : Machine)
    (ran : run nestedStorageTurnCode (nestedStorageControl (machine [wmod 11, wmod 23] ⟨1, by decide⟩)
      source (wmod 40) (wmod 2) (wmod 1)) =
      .ok (nestedStorageControl target source (wmod 40) (wmod 2) (wmod 2)) 0) : target.mem 42 ≠ w[40] := by
  obtain ⟨actual, execution, pointer, _⟩ := pair_last
  rw [ran] at execution
  have equal : target.mem 42 = actual.mem 42 :=
    congrArg (fun machine => machine.mem 42) (Out.ok.inj execution).1
  rw [equal, pointer]
  decide

theorem wrong_payload (target : Machine)
    (ran : run nestedStorageTurnCode (nestedStorageControl (machine [wmod 11, wmod 23] ⟨1, by decide⟩)
      source (wmod 40) (wmod 2) (wmod 1)) =
      .ok (nestedStorageControl target source (wmod 40) (wmod 2) (wmod 2)) 0) : target.mem 45 ≠ w[0] := by
  obtain ⟨actual, execution, _, _, _, _, second, _⟩ := pair_last
  rw [ran] at execution
  have equal : target.mem 45 = actual.mem 45 :=
    congrArg (fun machine => machine.mem 45) (Out.ok.inj execution).1
  rw [equal, second]
  decide

private def saturated (payloads : List (Fin W)) (selected : Fin 2) : Machine :=
  writeMachine (machine payloads selected) 0 (.val wMax)
private theorem saturated_allocator (payloads : List (Fin W)) (selected : Fin 2) :
    Objects.AllocatorRepr input.heap input.base 8 wMax (saturated payloads selected) := by
  have old : Objects.AllocatorRepr input.heap input.base 8 (wmod 43) (machine payloads selected) :=
    (initial payloads selected).1
  refine ⟨old.heap.localWrite 0 (by decide) (.val wMax), ⟨by decide, by decide, ?_, ?_⟩, ?_⟩
  · rfl
  · intro address lower
    have large : 256 < W := by decide
    change W - 1 ≤ address at lower
    have different : address ≠ 0 := by omega
    have above : (wmod 43).val ≤ address := by change 43 ≤ address; omega
    exact (upd_other _ _ different).trans (old.free.zero address above)
  · intro Q reference
    have live : (input.base reference.id).val + Objects.cells input.heap reference ≤ 43 := old.live reference
    have wide : 256 < W := by decide
    change _ ≤ W - 1
    omega

theorem saturated_refusal (payloads : List (Fin W)) (bounded : payloads.length < 128) (selected : Fin 2) :
    run nestedStorageTurnCode (nestedStorageControl (saturated payloads selected) source (wmod 40) (wmod 2)
      ⟨selected.val, Nat.lt_trans selected.isLt (by decide)⟩) = .revert := by
  have representation : ReprAt (saturated payloads selected).store 128 (.ref (.array (.prim .uint)))
      (source.add selected.val) (value payloads bounded) := represented payloads bounded selected
  rcases nested_storage_turn_correct input.heap .uint (values payloads)
      (by rw [values, List.length_map]; exact Nat.lt_trans bounded wide)
      input.base 8 wMax (saturated payloads selected) source (wmod 40) (wmod 2)
      ⟨selected.val, Nat.lt_trans selected.isLt (by decide)⟩ 128
      (saturated_allocator payloads selected) (initial payloads selected).2 (by decide) (by decide)
      selected.isLt representation with success | refusal
  · obtain ⟨fits, _⟩ := success
    have positive : 0 < W := W_pos
    change W - 1 + (_ + 1) < W at fits
    omega
  · exact refusal.2

theorem empty_saturated_refusal :
    run nestedStorageTurnCode (nestedStorageControl (saturated [] ⟨0, by decide⟩) source
      (wmod 40) (wmod 2) (wmod 0)) = .revert := saturated_refusal [] (by decide) ⟨0, by decide⟩

theorem pair_saturated_refusal :
    run nestedStorageTurnCode (nestedStorageControl (saturated [wmod 11, wmod 23] ⟨1, by decide⟩) source
      (wmod 40) (wmod 2) (wmod 1)) = .revert := saturated_refusal _ (by decide) ⟨1, by decide⟩

#print axioms certificate_inhabited
#print axioms actual_typed
#print axioms actual_runtime
#print axioms empty_first
#print axioms pair_last
#print axioms long_first
#print axioms actual_cursor
#print axioms wrong_child_slot
#print axioms strict_freshness
#print axioms wrong_pointer
#print axioms wrong_payload
#print axioms saturated_refusal
#print axioms empty_saturated_refusal
#print axioms pair_saturated_refusal
end Solidity.Backend.MemoryCopies.NestedStorageTurnControls
