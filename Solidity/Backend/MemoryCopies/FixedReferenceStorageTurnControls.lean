import Solidity.Backend.MemoryCopies.FixedReferenceStorageTurn
import Solidity.Evm.MemoryObjectArrayExamples

/-! Real parent reservations with dynamic child payloads, exact control-stack
restoration and checked refusal. The parent remains an unadopted reservation. -/
namespace Solidity.Backend.MemoryCopies.FixedReferenceStorageTurnControls
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
  allocateStructMachine {input.machine with store := store payloads selected} (wmod 40) 2
private def grown (payloads : List (Fin W)) (bounded : payloads.length < 128) :=
  (value payloads bounded).copyStToM input.heap rfl
private theorem represented (payloads : List (Fin W)) (bounded : payloads.length < 128) (selected : Fin 2) :
    ReprAt (machine payloads selected).store 128 (.ref (.array (.prim .uint)))
      (source.add selected.val) (value payloads bounded) := by
  refine .array ?_ (by simpa only [values, List.length_map] using bounded) ?_
  · simp only [machine, allocateStructMachine, writeMachine, store, source, Slot.add, Nat.zero_add, values, List.length_map]
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
      simp only [machine, allocateStructMachine, writeMachine, store, source, Slot.add, Nat.zero_add,
        picked, Option.getD_some]
      rfl
private theorem initial (payloads : List (Fin W)) (selected : Fin 2) :
    Objects.AllocatorRepr input.heap input.base 8 (wmod 42) (machine payloads selected) ∧
    Objects.Gap input.heap input.base 40 42 := by
  have inputAllocator : Objects.AllocatorRepr input.heap input.base 8 (wmod 40)
      {input.machine with store := store payloads selected} := input.allocator.mem_eq rfl
  exact inputAllocator.reserveFixed 2 (by decide)

theorem certificate_inhabited : FixedReferenceStorageTurnCertificate := fixedReferenceStorageTurn

theorem actual_typed (payloads : List (Fin W)) (bounded : payloads.length < 128) (selected : Fin 2) :
    FixedReferenceStorageTurnResult input.heap .uint (values payloads)
      (by rw [values, List.length_map]; exact Nat.lt_trans bounded wide)
      input.base 8 (wmod 42) (machine payloads selected) source (wmod 40) (wmod 2)
      ⟨selected.val, Nat.lt_trans selected.isLt (by decide)⟩ (by
        change 42 + ((values payloads).length + 1) < W
        rw [values, List.length_map]
        have large : 256 < W := by decide
        omega) :=
  fixed_reference_storage_turn_success input.heap .uint _ _ input.base 8 (wmod 42) (machine payloads selected)
    source (wmod 40) (wmod 2) _ 128 (initial payloads selected).1 (initial payloads selected).2
    (by decide) (by decide) selected.isLt (represented payloads bounded selected) _

theorem actual_runtime (payloads : List (Fin W)) (bounded : payloads.length < 128) (selected : Fin 2) :
    ∃ target : Machine,
      run fixedReferenceStorageTurnCode (nestedStorageControl (machine payloads selected) source (wmod 40) (wmod 2)
        ⟨selected.val, Nat.lt_trans selected.isLt (by decide)⟩) =
        .ok (nestedStorageControl target source (wmod 40) (wmod 2) (wmod (selected.val + 1))) 0 ∧
      target.mem (40 + selected.val) = w[42] ∧ target.mem 42 = .val (wmod payloads.length) ∧ target.mem 17 = w[7] ∧
      target.stack = [w[77]] ∧ target.store = (machine payloads selected).store ∧
      (∀ offset payload, payloads[offset]? = some payload → target.mem (43 + offset) = .val payload) := by
  obtain ⟨base', target, ran, allocated, root, extension, gap, pointer, shape, below, gaps, keeps, identity, length⟩ :=
    actual_typed payloads bounded selected
  change base' (grown payloads bounded).val.id = wmod 42 at root
  change (grown payloads bounded).heap.len (grown payloads bounded).val .dyn = (values payloads).length at length
  have header : target.mem 42 = .val (wmod payloads.length) := by
    have cell : target.mem (base' (grown payloads bounded).val.id).val =
        .val (wmod ((grown payloads bounded).heap.len (grown payloads bounded).val .dyn)) :=
      (allocated.heap.arrays .dyn (grown payloads bounded).val).length rfl
    rw [root, length] at cell
    simpa only [values, List.length_map] using cell
  refine ⟨target, ran, pointer, header, ?_, ?_, ?_, ?_⟩
  · exact (below 17 (by decide) (by decide) (by change 17 ≠ 40 + selected.val; omega)).trans (by
      simp only [machine,allocateStructMachine,writeMachine,upd,↓reduceIte]
      rfl)
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
    run fixedReferenceStorageTurnCode (nestedStorageControl (machine [] ⟨0,by decide⟩) source
      (wmod 40) (wmod 2) (wmod 0)) =
      .ok (nestedStorageControl target source (wmod 40) (wmod 2) (wmod 1)) 0 ∧
    target.mem 40 = w[42] ∧ target.mem 42 = w[0] := by
  obtain ⟨target,ran,pointer,header,_⟩ := actual_runtime [] (by decide) ⟨0,by decide⟩
  exact ⟨target,ran,pointer,header⟩

theorem pair_last : ∃ target : Machine,
    run fixedReferenceStorageTurnCode (nestedStorageControl (machine [wmod 11,wmod 23] ⟨1,by decide⟩)
      source (wmod 40) (wmod 2) (wmod 1)) =
      .ok (nestedStorageControl target source (wmod 40) (wmod 2) (wmod 2)) 0 ∧
    target.mem 41 = w[42] ∧ target.mem 42 = w[2] ∧ target.mem 43 = w[11] ∧
    target.mem 44 = w[23] ∧ target.mem 17 = w[7] ∧ target.stack = [w[77]] := by
  obtain ⟨target,ran,pointer,header,old,stack,_,contents⟩ :=
    actual_runtime [wmod 11,wmod 23] (by decide) ⟨1,by decide⟩
  exact ⟨target,ran,pointer,header,contents 0 _ rfl,contents 1 _ rfl,old,stack⟩

private def long : List (Fin W) := List.ofFn (fun index : Fin 64 => wmod (index.val + 1))

theorem long_first : ∃ target : Machine,
    run fixedReferenceStorageTurnCode (nestedStorageControl (machine long ⟨0,by decide⟩)
      source (wmod 40) (wmod 2) (wmod 0)) =
      .ok (nestedStorageControl target source (wmod 40) (wmod 2) (wmod 1)) 0 ∧
    target.mem 40 = w[42] ∧ target.mem 42 = w[64] ∧ target.mem 43 = w[1] ∧
    target.mem 106 = w[64] ∧ target.mem 17 = w[7] := by
  obtain ⟨target,ran,pointer,header,old,_,_,contents⟩ :=
    actual_runtime long (by rw [long,List.length_ofFn]; decide) ⟨0,by decide⟩
  exact ⟨target,ran,pointer,header,contents 0 (wmod 1) (by decide +kernel),
    contents 63 (wmod 64) (by decide +kernel),old⟩

theorem wrong_headerless_pointer (target : Machine)
    (ran : run fixedReferenceStorageTurnCode (nestedStorageControl (machine [] ⟨0,by decide⟩)
      source (wmod 40) (wmod 2) (wmod 0)) =
      .ok (nestedStorageControl target source (wmod 40) (wmod 2) (wmod 1)) 0) :
    target.mem 40 ≠ w[2] := by
  obtain ⟨actual,execution,pointer,_⟩ := empty_first
  rw [ran] at execution
  have equal : target.mem 40 = actual.mem 40 :=
    congrArg (fun machine => machine.mem 40) (Out.ok.inj execution).1
  rw [equal,pointer]
  decide

private def saturated (payloads : List (Fin W)) (selected : Fin 2) : Machine :=
  writeMachine (machine payloads selected) 0 (.val wMax)
private theorem saturated_allocator (payloads : List (Fin W)) (selected : Fin 2) :
    Objects.AllocatorRepr input.heap input.base 8 wMax (saturated payloads selected) := by
  have old : Objects.AllocatorRepr input.heap input.base 8 (wmod 42) (machine payloads selected) :=
    (initial payloads selected).1
  refine ⟨old.heap.localWrite 0 (by decide) (.val wMax), ⟨by decide, by decide, ?_, ?_⟩, ?_⟩
  · rfl
  · intro address lower
    have large : 256 < W := by decide
    change W - 1 ≤ address at lower
    have different : address ≠ 0 := by omega
    have above : (wmod 42).val ≤ address := by change 42 ≤ address; omega
    exact (upd_other _ _ different).trans (old.free.zero address above)
  · intro Q reference
    have live : (input.base reference.id).val + Objects.cells input.heap reference ≤ 42 := old.live reference
    have wide : 256 < W := by decide
    change _ ≤ W - 1
    omega

theorem saturated_refusal (payloads : List (Fin W)) (bounded : payloads.length < 128) (selected : Fin 2) :
    run fixedReferenceStorageTurnCode (nestedStorageControl (saturated payloads selected) source (wmod 40) (wmod 2)
      ⟨selected.val, Nat.lt_trans selected.isLt (by decide)⟩) = .revert := by
  have representation : ReprAt (saturated payloads selected).store 128 (.ref (.array (.prim .uint)))
      (source.add selected.val) (value payloads bounded) := represented payloads bounded selected
  rcases fixed_reference_storage_turn_correct input.heap .uint (values payloads)
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
    run fixedReferenceStorageTurnCode (nestedStorageControl (saturated [] ⟨0, by decide⟩) source
      (wmod 40) (wmod 2) (wmod 0)) = .revert := saturated_refusal [] (by decide) ⟨0, by decide⟩

theorem pair_saturated_refusal :
    run fixedReferenceStorageTurnCode (nestedStorageControl (saturated [wmod 11, wmod 23] ⟨1, by decide⟩) source
      (wmod 40) (wmod 2) (wmod 1)) = .revert := saturated_refusal _ (by decide) ⟨1, by decide⟩

/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageTurnControls.certificate_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms certificate_inhabited
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageTurnControls.actual_typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_typed
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageTurnControls.actual_runtime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms actual_runtime
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageTurnControls.empty_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms empty_first
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageTurnControls.pair_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pair_last
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageTurnControls.long_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms long_first
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageTurnControls.wrong_headerless_pointer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms wrong_headerless_pointer
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageTurnControls.saturated_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms saturated_refusal
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageTurnControls.empty_saturated_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms empty_saturated_refusal
/--
info: 'Solidity.Backend.MemoryCopies.FixedReferenceStorageTurnControls.pair_saturated_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pair_saturated_refusal
end Solidity.Backend.MemoryCopies.FixedReferenceStorageTurnControls
