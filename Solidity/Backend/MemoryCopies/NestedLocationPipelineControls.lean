import Solidity.Backend.MemoryCopies.NestedLocationPipelineObservations
import Solidity.Backend.MemoryCopies.NestedStorageHeaderControls
import Solidity.Evm.MemoryObjectArrayExamples

/-! Inhabited two-phase copies, observed headers/cursors, and distinct phase
refusals. Initial allocator witnesses reuse the existing populated heap. -/
namespace Solidity.Backend.MemoryCopies.NestedLocationPipelineControls
open Evm Evm.Memory

structure Witness where
  H : HTy
  heap : Heap H
  rows : List (PrimitiveStorageRow .uint)
  bounded : rows.length < W
  base : Nat → Fin W
  frame : Nat
  cursor : Fin W
  machine : Machine
  source : Slot
  fits : cursor.val + 2 * nestedStorageParentDemand rows < W
  result : NestedLocationPipelineResult heap .uint rows bounded base frame cursor machine source fits

def Witness.primitive (_item : Witness) : PrimTy := .uint

private def witness {H : HTy} {heap : Heap H}
    {rows : List (PrimitiveStorageRow .uint)} {bounded : rows.length < W}
    {base : Nat → Fin W} {frame : Nat} {cursor : Fin W} {machine : Machine} {source : Slot}
    {fits : cursor.val + 2 * nestedStorageParentDemand rows < W}
    (result : NestedLocationPipelineResult heap .uint rows bounded base frame cursor machine source fits) : Witness :=
  ⟨H, heap, rows, bounded, base, frame, cursor, machine, source, fits, result⟩

theorem certificate_inhabited : NestedLocationPipelineCertificate := nestedLocationPipeline

theorem empty_inhabited : ∃ item : Witness,
    item.cursor = wmod 40 ∧ item.rows.length = 0 ∧ nestedStorageParentDemand item.rows = 1 := by
  obtain ⟨firstFits, firstResult⟩ := NestedStorageHeaderControls.actual_typed [] (by decide) .nil
  exact ⟨witness (nested_location_pipeline_after_first _ _ _ _ _ _ _ _ _ _ firstFits firstResult (by decide)), rfl, rfl, rfl⟩

private def row (entry : {payloads : List (Fin W) // payloads.length < 128}) : PrimitiveStorageRow .uint :=
  ⟨entry.val.map indexValue, by
    rw [List.length_map]
    have large : 128 < W := by decide
    exact Nat.lt_trans entry.property large⟩
def mixedPayloads : List {payloads : List (Fin W) // payloads.length < 128} :=
  [⟨[wmod 11, wmod 23], by decide⟩, ⟨[], by decide⟩,
    ⟨List.ofFn (fun index : Fin 64 => wmod (index.val + 1)), by rw [List.length_ofFn]; decide⟩]
def mixedRows : List (PrimitiveStorageRow .uint) := mixedPayloads.map row
def mixedValue : SVal (.ref (.array (.ref (.array (.prim .uint))))) :=
  nestedStorageParentValue .uint mixedRows (by decide)

theorem mixed_inhabited : ∃ item : Witness,
    item.cursor = wmod 40 ∧ item.rows.length = 3 ∧ nestedStorageParentDemand item.rows = 73 ∧ item.rows = mixedRows := by
  obtain ⟨firstFits, firstResult⟩ := NestedStorageHeaderControls.actual_typed mixedPayloads (by decide) .nil
  exact ⟨witness (nested_location_pipeline_after_first _ _ _ _ _ _ _ _ _ _ firstFits firstResult (by decide)), rfl, rfl, rfl, rfl⟩

def MixedSnapshots (item : Witness) : Prop :=
  let value := nestedStorageParentValue .uint item.rows item.bounded
  let first := value.copyStToM item.heap rfl
  let snapshot := MVal.copyMToSt first.heap first.val
  let second := snapshot.copyStToM first.heap rfl
  MVal.copyMToSt second.heap (first.val.wk second.ext) = mixedValue ∧
    MVal.copyMToSt second.heap second.val = mixedValue

private theorem rows_value_equal (values : List (PrimitiveStorageRow .uint)) (bounded : values.length < W)
    (same : values = mixedRows) : nestedStorageParentValue .uint values bounded = mixedValue := by
  cases same
  rfl

private theorem primitive_strip : {n : Nat} → (values : SVec (.prim .uint) n) → values.strip = values
  | _, .nil => by rw [SVec.strip_nil]
  | _, .cons (.prim value) rest => by rw [SVec.strip_cons, SVal.strip_prim, primitive_strip rest]

private theorem rows_strip (entries : List (PrimitiveStorageRow .uint)) :
    (nestedStorageValues .uint entries).strip = nestedStorageValues .uint entries := by
  induction entries with
  | nil => simp only [nestedStorageValues, SVec.strip_nil]
  | cons entry entries ih =>
    simp only [nestedStorageValues, SVec.strip_cons, primitiveArrayValue, SVal.strip_array, primitive_strip, ih]

theorem mixed_contents : ∃ item : Witness, item.rows = mixedRows ∧ MixedSnapshots item := by
  obtain ⟨item, _, _, _, same⟩ := mixed_inhabited
  let value := nestedStorageParentValue .uint item.rows item.bounded
  let first := value.copyStToM item.heap rfl
  let snapshot := MVal.copyMToSt first.heap first.val
  let second := snapshot.copyStToM first.heap rfl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, retained, copied⟩ := item.result
  have equal : value = mixedValue := rows_value_equal item.rows item.bounded same
  have pure : mixedValue.strip = mixedValue := by
    simp only [mixedValue, nestedStorageParentValue, SVal.strip_array, rows_strip]
  have expected : value.strip = mixedValue := (congrArg SVal.strip equal).trans pure
  have firstContents : snapshot = value.strip := (storageHeapContents value rfl).contents item.heap
  exact ⟨item, same, retained.trans expected,
    copied.trans ((congrArg SVal.strip (firstContents.trans expected)).trans pure)⟩

theorem empty_runtime : ∃ (item : Witness) (target : Machine),
    run (nestedLocationPipelineCode item.primitive) (item.machine.push (.slot item.source)) =
      .ok (target.push w[41]) 0 ∧ target.mem 0 = w[42] ∧ target.mem 40 = w[0] ∧ target.mem 41 = w[0] := by
  obtain ⟨item, cursor, count, demand⟩ := empty_inhabited
  obtain ⟨target, ran, free, first, second, _, _⟩ := nested_location_pipeline_observations
    item.heap item.primitive item.rows item.bounded item.base item.frame item.cursor item.machine item.source item.fits item.result
    (by rw [cursor]; decide)
  rw [cursor] at ran free first second
  rw [demand] at ran free second
  rw [count] at first second
  exact ⟨item, target, ran, free, first, second⟩

theorem mixed_runtime : ∃ (item : Witness) (target : Machine),
    run (nestedLocationPipelineCode item.primitive) (item.machine.push (.slot item.source)) =
      .ok (target.push w[113]) 0 ∧ target.mem 0 = w[186] ∧ target.mem 40 = w[3] ∧ target.mem 113 = w[3] := by
  obtain ⟨item, cursor, count, demand, _⟩ := mixed_inhabited
  obtain ⟨target, ran, free, first, second, _, _⟩ := nested_location_pipeline_observations
    item.heap item.primitive item.rows item.bounded item.base item.frame item.cursor item.machine item.source item.fits item.result
    (by rw [cursor]; decide)
  rw [cursor] at ran free first second
  rw [demand] at ran free second
  rw [count] at first second
  exact ⟨item, target, ran, free, first, second⟩

theorem mixed_erased_header_rejected : ∃ (item : Witness) (target : Machine),
    run (nestedLocationPipelineCode item.primitive) (item.machine.push (.slot item.source)) =
      .ok (target.push w[113]) 0 ∧ target.mem 113 ≠ w[0] := by
  obtain ⟨item, target, ran, _, _, header⟩ := mixed_runtime
  exact ⟨item, target, ran, by rw [header]; decide⟩

private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def input : Input := ⟨_, _, _, _, ObjectArrayExamples.initial_allocator⟩
private def zeroStore : WordStore := ⟨fun _ => wmod 0⟩
private def moved (cursor : Fin W) : Machine := writeMachine {input.machine with store := zeroStore} 0 (.val cursor)
private theorem allocator (cursor : Fin W) (above : 40 ≤ cursor.val) :
    Objects.AllocatorRepr input.heap input.base 8 cursor (moved cursor) := by
  have old : Objects.AllocatorRepr input.heap input.base 8 (wmod 40) {input.machine with store := zeroStore} :=
    input.allocator.mem_eq rfl
  refine ⟨old.heap.localWrite 0 (by decide) (.val cursor), ⟨by decide, by omega, ?_, ?_⟩, ?_⟩
  · rfl
  · intro address lower
    exact (upd_other _ _ (by omega : address ≠ 0)).trans (old.free.zero address (by change 40 ≤ address; omega))
  · intro Q reference
    have live : (input.base reference.id).val + Objects.cells input.heap reference ≤ 40 := old.live reference
    omega
private theorem represented (cursor : Fin W) :
    ReprAt (moved cursor).store 128 (.ref (.array (.ref (.array (.prim .uint))))) (.root 0)
      (nestedStorageHeaderValue .uint [] (by decide) .nil) := by
  refine .array rfl (by decide) ?_
  intro index value chosen
  simp only [nestedStorageValues, SVec.toList_nil, List.getElem?_nil] at chosen
  cases chosen

theorem first_phase_empty_refusal :
    run nestedStorageHeaderCode ((moved wMax).push (.slot (.root 0))) = .revert ∧
    run (nestedLocationPipelineCode .uint) ((moved wMax).push (.slot (.root 0))) = .revert := by
  have firstRun : run nestedStorageHeaderCode ((moved wMax).push (.slot (.root 0))) = .revert :=
    nested_storage_header_refusal input.heap .uint [] (by decide) .nil input.base 8 wMax (moved wMax)
      (.root 0) 128 (allocator wMax (by decide)) (represented wMax)
      (by change ¬ W - 1 + 1 < W; have positive : 0 < W := W_pos; omega)
  exact ⟨firstRun, by rw [nestedLocationPipelineCode, run_append_revert firstRun]⟩

theorem second_phase_empty_refusal : ∃ firstFits base₁ intermediate,
    run nestedStorageHeaderCode ((moved (wmod (W - 2))).push (.slot (.root 0))) = .ok (intermediate.push (.val (wmod (W - 2)))) 0 ∧
    Objects.AllocatorRepr ((nestedStorageParentValue .uint [] (by decide)).copyStToM input.heap rfl).heap base₁ 8
      ⟨(wmod (W - 2)).val + 1, firstFits⟩ intermediate ∧
    run (nestedMemoryParentCode .uint) (intermediate.push (.val (wmod (W - 2)))) = .revert ∧
    run (nestedLocationPipelineCode .uint) ((moved (wmod (W - 2))).push (.slot (.root 0))) = .revert := by
  obtain ⟨phase, wholeRun⟩ := nested_location_pipeline_refusal input.heap .uint [] (by decide) .nil input.base 8 (wmod (W - 2)) (moved (wmod (W - 2)))
    (.root 0) 128 (allocator _ (by decide)) (represented _)
    (by
      change ¬ (W - 2) % W + 2 < W
      have large : 1024 < W := by decide
      rw [Nat.mod_eq_of_lt (by omega : W - 2 < W)]
      omega)
  rcases phase with first | second
  · have possible : (wmod (W - 2)).val + nestedStorageParentDemand ([] : List (PrimitiveStorageRow .uint)) < W := by
      change (W - 2) % W + 1 < W
      have large : 1024 < W := by decide
      rw [Nat.mod_eq_of_lt (by omega : W - 2 < W)]
      omega
    exact (first.1 possible).elim
  · obtain ⟨firstFits, base₁, intermediate, ran, allocated, _, _, _, refused⟩ := second
    exact ⟨firstFits, base₁, intermediate, ran, allocated, refused, wholeRun⟩

#print axioms certificate_inhabited
#print axioms empty_inhabited
#print axioms mixed_inhabited
#print axioms mixed_contents
#print axioms empty_runtime
#print axioms mixed_runtime
#print axioms mixed_erased_header_rejected
#print axioms first_phase_empty_refusal
#print axioms second_phase_empty_refusal
end Solidity.Backend.MemoryCopies.NestedLocationPipelineControls
