import Solidity.Backend.MemoryCopies.EmptyReferenceMemory
import Solidity.Evm.MemoryObjectArrayExamples

/-! Build an actual empty reference object above a populated represented heap.
Its header ends exactly where the fresh copy begins; old aliases stay valid. -/
namespace Solidity.Backend.MemoryCopies.EmptyReferenceMemoryControls
open Evm Evm.Memory
private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def initial : Input := ⟨_, _, _, _, ObjectArrayExamples.initial_allocator⟩
private def heap (element : Ty) := (initial.heap.alloc (Objects.emptyArray element)).1
private def source (element : Ty) := (initial.heap.alloc (Objects.emptyArray element)).2
private def base : Nat → Fin W := upd initial.base initial.H.length (wmod 40)
private def machine : Machine := allocateMachine initial.machine (wmod 40) (wmod 0)
private def cursor : Fin W := ⟨41, by decide⟩
private theorem allocator (element : Ty) : Objects.AllocatorRepr (heap element) base 8 cursor machine :=
  initial.allocator.allocateEmpty element (by decide)
private theorem empty (element : Ty) : (heap element).len (source element) .dyn = 0 := by
  simp only [heap, source, Heap.len, Heap.get_alloc, MObj.elems_dyn, MObj.wk,
    Objects.emptyArray, List.map_nil, List.length_nil]
private theorem source_base (element : Ty) : base (source element).id = wmod 40 := upd_same _ _ _
private def element : Ty := .ref (.array (.prim .uint))
private def copied := (MVal.copyMToSt (heap element) (T := .ref (.array element))
  (source element)).copyStToM (heap element) rfl
private def observe : Evm.Out → Option (Nat × Nat × Nat × Nat × Nat × List Word)
  | .ok target _ => match target.stack, target.mem 0, target.mem 40, target.mem 41, target.mem 17 with
    | .val root :: rest, .val next, .val oldHeader, .val header, .val oldPayload =>
      some (root.val, next.val, oldHeader.val, header.val, oldPayload.val, rest)
    | _, _, _, _, _ => none
  | _ => none

theorem certificate_inhabited : EmptyMemoryCopyCertificate := emptyMemoryCopy

theorem actual_typed (E : Ty) (memory : (Ty.ref (.array E)).mapFree = true) :
    EmptyMemoryCopyResult checkedMemoryArrayCode (heap E) E (source E) memory base 8 cursor machine (by decide) :=
  empty_checked_memory_success (heap E) E (source E) memory base 8 cursor machine (empty E) (allocator E) (by decide)

theorem adjacent_source_bound : (base (source element).id).val + 1 = cursor.val := by
  rw [source_base]
  rfl

theorem exact_runtime (E : Ty) :
    run checkedMemoryArrayCode (machine.push (.val (base (source E).id))) =
      .ok ((allocateMachine machine cursor (wmod 0)).push (.val cursor)) 0 := by
  have header : machine.mem (base (source E).id).val = .val (wmod 0) :=
    empty_memory_header (heap E) E (source E) base 8 cursor machine (empty E) (allocator E)
  have bounds : 0 < (base (source E).id).val ∧ (base (source E).id).val + 1 ≤ cursor.val :=
    empty_memory_bounds (heap E) E (source E) base 8 cursor machine (empty E) (allocator E)
  rw [empty_checked_memory_run machine _ cursor (allocator E).free.cell header, if_pos (by decide : cursor.val + 1 < W)]
  exact empty_memory_zero_run machine cursor _ (allocator E).free.cell header bounds.1 bounds.2 (by decide)

theorem actual_observation : observe (run checkedMemoryArrayCode (machine.push (.val (base (source element).id)))) =
    some (41, 42, 0, 0, 7, [w[77]]) := by
  rw [exact_runtime]
  rfl

theorem fresh_identity_and_length : (source element).id = 3 ∧ copied.val.id = 4 ∧
    copied.H'.length = 5 ∧ copied.heap.len copied.val .dyn = 0 := by
  have allocation : copied = (heap element).allocDefault (.array element) rfl :=
    congrArg (fun value : SVal (.ref (.array element)) => value.copyStToM (heap element) rfl)
      (empty_memory_snapshot (heap element) element (source element) (empty element))
  rw [allocation, Objects.emptyArray_copy]
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp only [Grown.alloc, Heap.len, Heap.get_alloc, MObj.elems_dyn, MObj.wk,
    Objects.emptyArray, List.map_nil, List.length_nil]

theorem old_aliases_kept : Heap.Keeps copied.ext (heap element) copied.heap ∧
    (heap element).len (source element) .dyn = 0 :=
  ⟨SVal.keeps_copyStToM _ rfl _, empty element⟩

theorem caller_alias_preserved :
    EmptyMemoryCopyResult checkedMemoryArrayCode (heap element) element (source element) rfl base 8 cursor
      (machine.push (.val (base (source element).id))) (by decide) := by
  exact empty_checked_memory_success (heap element) element (source element) rfl base 8 cursor _ (empty element)
    ((allocator element).stack (machine.push (.val (base (source element).id))).stack) (by decide)

theorem unused_struct_child : ReferenceDefaults.compileDefault (.struct "Basket") rfl = none ∧
    EmptyMemoryCopyResult checkedMemoryArrayCode (heap (.ref (.struct "Basket"))) (.ref (.struct "Basket"))
      (source (.ref (.struct "Basket"))) rfl base 8 cursor machine (by decide) :=
  ⟨rfl, actual_typed _ rfl⟩

theorem unused_huge_child :
    EmptyMemoryCopyResult checkedMemoryArrayCode (heap (.ref (.fixed (.prim .uint) W))) (.ref (.fixed (.prim .uint) W))
      (source (.ref (.fixed (.prim .uint) W))) rfl base 8 cursor machine (by decide) := actual_typed _ rfl

private def saturated : Machine := writeMachine machine 0 (.val wMax)
private theorem saturated_allocator : Objects.AllocatorRepr (heap element) base 8 wMax saturated := by
  have initial : Objects.AllocatorRepr (heap element) base 8 cursor machine := allocator element
  have high : cursor.val ≤ wMax.val := by decide
  have frame : 8 ≤ cursor.val := initial.free.above
  refine ⟨initial.heap.localWrite 0 (by decide) (.val wMax), ⟨by decide, by omega, ?_, ?_⟩, ?_⟩
  · rfl
  · intro address lower
    have zero : address ≠ 0 := by
      have positive : 0 < cursor.val := by decide
      omega
    exact (upd_other _ _ zero).trans (initial.free.zero address (by omega))
  · intro R reference
    exact Nat.le_trans (initial.live reference) high

theorem saturated_input : Objects.AllocatorRepr (heap element) base 8 wMax saturated ∧
    (heap element).len (source element) .dyn = 0 := ⟨saturated_allocator, empty element⟩

theorem saturated_refusal : run checkedMemoryArrayCode (saturated.push (.val (base (source element).id))) = .revert := by
  rw [empty_checked_memory_run saturated _ wMax saturated_allocator.free.cell
    (empty_memory_header (heap element) element (source element) base 8 wMax saturated (empty element) saturated_allocator)]
  apply if_neg
  change ¬ (W - 1 + 1 < W)
  have positive : 0 < W := W_pos
  omega

theorem old_alias_is_not_fresh_copy :
    observe (run checkedMemoryArrayCode (machine.push (.val (base (source element).id)))) ≠
      some (40, 41, 0, 0, 7, [w[77]]) := by
  rw [actual_observation]
  intro wrong
  have roots : (41 : Nat) = 40 := congrArg Prod.fst (Option.some.inj wrong)
  omega

#print axioms certificate_inhabited
#print axioms actual_typed
#print axioms adjacent_source_bound
#print axioms exact_runtime
#print axioms actual_observation
#print axioms fresh_identity_and_length
#print axioms old_aliases_kept
#print axioms caller_alias_preserved
#print axioms unused_struct_child
#print axioms unused_huge_child
#print axioms saturated_input
#print axioms saturated_refusal
#print axioms old_alias_is_not_fresh_copy
end Solidity.Backend.MemoryCopies.EmptyReferenceMemoryControls
