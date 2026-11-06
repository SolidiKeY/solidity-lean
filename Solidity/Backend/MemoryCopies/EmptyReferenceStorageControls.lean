import Solidity.Backend.MemoryCopies.EmptyReferenceStorage
import Solidity.Evm.MemoryObjectArrayExamples

/-! Existing code copies a real zero storage header without reading reference
children or shadows. All capacity controls retain complete allocator inputs. -/
namespace Solidity.Backend.MemoryCopies.EmptyReferenceStorageControls
open Evm Evm.Memory
private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def input : Input := ⟨_, _, _, _, ObjectArrayExamples.initial_allocator⟩
private def source : Slot := .root 0
private def store (noise : Fin W) : WordStore := ⟨fun slot => if slot = source then wmod 0 else noise⟩
private def machine (noise : Fin W) : Machine := {input.machine with store := store noise}
private def element : Ty := .ref (.array (.prim .uint))
private def child : SVal element := .array (.cons (.prim ⟨7, by decide⟩) .nil) .nil (by decide)
private def shadows : Nat → SList element
  | 0 => .nil
  | count + 1 => .cons child (shadows count)
private theorem represented (E : Ty) (shadow : SList E) (noise : Fin W) :
    ReprAt (machine noise).store 128 (.ref (.array E)) source (emptyStoredArray E shadow) := by
  refine .array ?_ (by decide) ?_
  · change (if source = source then wmod 0 else noise).val = 0
    rw [if_pos rfl]
    rfl
  · intro index value selected
    simp only [SVec.toList_nil, List.getElem?_nil, reduceCtorEq] at selected
private theorem allocator (noise : Fin W) :
    Objects.AllocatorRepr input.heap input.base 8 (wmod 40) (machine noise) := input.allocator.mem_eq rfl
private def observe : Evm.Out → Option (Nat × Nat × Nat × Nat × List Word)
  | .ok target _ => match target.stack, target.mem 0, target.mem 40, target.mem 17 with
    | .val root :: rest, .val cursor, .val header, .val old => some (root.val, cursor.val, header.val, old.val, rest)
    | _, _, _, _ => none
  | _ => none

theorem certificate_inhabited : EmptyStorageCopyCertificate := emptyStorageCopy

theorem actual_typed (E : Ty) (shadow : SList E) (memory : (Ty.ref (.array E)).mapFree = true)
    (noise : Fin W) :
    EmptyStorageCopyResult checkedStorageArrayCode input.heap E shadow memory input.base 8 (wmod 40)
      (machine noise) source (by decide) :=
  empty_checked_storage_success input.heap E shadow memory input.base 8 (wmod 40)
    (machine noise) source 128 (allocator noise) (represented E shadow noise) (by decide)

theorem shadow_independent_heap (count : Nat) :
    ((emptyStoredArray element (shadows count)).copyStToM input.heap rfl).val.id = 3 ∧
    ((emptyStoredArray element (shadows count)).copyStToM input.heap rfl).H'.length = 4 ∧
    ((emptyStoredArray element (shadows count)).copyStToM input.heap rfl).heap.len
      ((emptyStoredArray element (shadows count)).copyStToM input.heap rfl).val .dyn = 0 := by
  rw [empty_stored_copy, Objects.emptyArray_copy]
  refine ⟨rfl, rfl, ?_⟩
  simp only [Grown.alloc, Heap.len, Heap.get_alloc, MObj.elems_dyn, MObj.wk,
    Objects.emptyArray, List.map_nil, List.length_nil]

theorem shadow_zero_and_long :
    EmptyStorageCopyResult checkedStorageArrayCode input.heap element (shadows 0) rfl input.base 8 (wmod 40)
      (machine (wmod 99)) source (by decide) ∧
    EmptyStorageCopyResult checkedStorageArrayCode input.heap element (shadows 64) rfl input.base 8 (wmod 40)
      (machine (wmod 99)) source (by decide) :=
  ⟨actual_typed _ _ rfl _, actual_typed _ _ rfl _⟩

theorem unread_storage_run (noise : Fin W) :
    run checkedStorageArrayCode ((machine noise).push (.slot source)) =
      .ok ((allocateMachine (machine noise) (wmod 40) (wmod 0)).push (.val (wmod 40))) 0 := by
  have header : (machine noise).store.cells source = wmod 0 :=
    empty_storage_header (machine noise) source 128 element (shadows 0) (represented _ _ _)
  rw [empty_checked_storage_run (machine noise) (wmod 40) source (allocator noise).free.cell header,
    if_pos (by decide : (wmod 40).val + 1 < W)]
  exact empty_storage_zero_run (machine noise) (wmod 40) source (allocator noise).free.cell header (by decide)

theorem actual_observation : observe (run checkedStorageArrayCode ((machine (wmod 99)).push (.slot source))) =
    some (40, 41, 0, 7, [w[77]]) := by
  rw [unread_storage_run]
  decide +kernel

theorem unread_noise_independent (noise : Fin W) :
    observe (run checkedStorageArrayCode ((machine noise).push (.slot source))) =
      observe (run checkedStorageArrayCode ((machine (wmod 99)).push (.slot source))) := by
  rw [unread_storage_run, unread_storage_run]
  rfl

/-- The unused struct child's narrower default compiler refuses it; no child
compiler is called by the actual empty storage-copy routine. -/
theorem unused_struct_child : ReferenceDefaults.compileDefault (.struct "Basket") rfl = none ∧
    EmptyStorageCopyResult checkedStorageArrayCode input.heap (.ref (.struct "Basket")) .nil rfl
      input.base 8 (wmod 40) (machine (wmod 99)) source (by decide) :=
  ⟨rfl, actual_typed _ _ rfl _⟩

theorem unused_huge_child :
    EmptyStorageCopyResult checkedStorageArrayCode input.heap (.ref (.fixed (.prim .uint) W)) .nil rfl
      input.base 8 (wmod 40) (machine (wmod 99)) source (by decide) := actual_typed _ _ rfl _

private def saturated : Machine := writeMachine (machine (wmod 99)) 0 (.val wMax)
private theorem saturated_allocator : Objects.AllocatorRepr input.heap input.base 8 wMax saturated := by
  have initial : Objects.AllocatorRepr input.heap input.base 8 (wmod 40) (machine (wmod 99)) := allocator _
  have high : 40 ≤ wMax.val := by decide
  refine ⟨initial.heap.localWrite 0 (by decide) (.val wMax), ⟨by decide, by omega, ?_, ?_⟩, ?_⟩
  · rfl
  · intro address lower
    exact (upd_other _ _ (by omega : address ≠ 0)).trans (initial.free.zero address (by change 40 ≤ address; omega))
  · intro R reference
    have live : (input.base reference.id).val + Objects.cells input.heap reference ≤ 40 := initial.live reference
    exact Nat.le_trans live high

theorem saturated_input : Objects.AllocatorRepr input.heap input.base 8 wMax saturated ∧
    ReprAt saturated.store 128 (.ref (.array element)) source (emptyStoredArray element (shadows 64)) :=
  ⟨saturated_allocator, represented _ _ _⟩

theorem saturated_refusal : run checkedStorageArrayCode (saturated.push (.slot source)) = .revert := by
  rw [empty_checked_storage_run saturated wMax source saturated_allocator.free.cell
    (empty_storage_header saturated source 128 element (shadows 64) saturated_input.2)]
  apply if_neg
  change ¬ (W - 1 + 1 < W)
  have positive : 0 < W := W_pos
  omega

private def wrongHeader : Machine := {machine (wmod 99) with store := ⟨fun _ => wmod 1⟩}
theorem wrong_header_not_represented :
    ¬ ReprAt wrongHeader.store 128 (.ref (.array element)) source (emptyStoredArray element (shadows 64)) := by
  intro representation
  have header : wrongHeader.store.cells source = wmod 0 :=
    empty_storage_header wrongHeader source 128 element (shadows 64) representation
  have impossible : (wmod 1 : Fin W) ≠ wmod 0 := by decide
  exact impossible header

theorem wrong_payload_header_rejected :
    observe (run checkedStorageArrayCode ((machine (wmod 99)).push (.slot source))) ≠
      some (40, 41, 99, 7, [w[77]]) := by
  rw [actual_observation]
  decide

#print axioms certificate_inhabited
#print axioms actual_typed
#print axioms shadow_independent_heap
#print axioms shadow_zero_and_long
#print axioms actual_observation
#print axioms unread_storage_run
#print axioms unread_noise_independent
#print axioms unused_struct_child
#print axioms unused_huge_child
#print axioms saturated_input
#print axioms saturated_refusal
#print axioms wrong_header_not_represented
#print axioms wrong_payload_header_rejected
end Solidity.Backend.MemoryCopies.EmptyReferenceStorageControls
