import Solidity.Backend.MemoryCopies.SelectedDefaultDemandInterface

/-! Actual selected default demand. The existing compiler, default fold and
capacity guard are unchanged; unavailable selections assert no coverage. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory Semantics

private theorem primitive_default_field_words : (fields : List (Name × Ty)) →
    primitiveMembers fields = true → fieldWordCount (SFields.dflt fields) = 0
  | [], _ => rfl
  | (_, .prim _) :: rest, primitive => by
    change 0 + fieldWordCount (SFields.dflt rest) = 0
    simpa only [Nat.zero_add] using primitive_default_field_words rest primitive
  | (_, .ref _) :: _, primitive => by cases primitive

theorem selected_default_words (root : RefTy) (memory : (Ty.ref root).mapFree = true)
    (selected : (ReferenceDefaults.compileDefault root memory).isSome = true) :
    liveWordCount (SVal.dflt (.ref root)) = ReferenceDefaults.defaultCells (.ref root) := by
  cases root with
  | array element => exact dynamic_default_words element
  | struct name =>
    by_cases primitive : primitiveMembers (structDef name) = true
    · rw [SVal.dflt_struct, liveWordCount, primitive_default_field_words _ primitive]
      simp only [ReferenceDefaults.defaultCells, structAllocationSize, Nat.zero_add]
    · change (if h : primitiveMembers (structDef name) = true then
        some (Objects.DefaultBuilder.primitiveStruct h memory) else none).isSome = true at selected
      rw [dif_neg primitive] at selected
      cases selected
  | fixed element count =>
    rw [fixed_default_words]
    cases element with
    | prim primitive =>
      rw [SVal.dflt_prim]
      simp only [liveWordCount, Nat.mul_zero, Nat.add_zero, ReferenceDefaults.defaultCells]
    | ref child =>
      change ((ReferenceDefaults.compileDefault child memory).bind
        (fun builder => some (Objects.DefaultBuilder.fixedReference builder count))).isSome = true at selected
      cases chosen : ReferenceDefaults.compileDefault child memory with
      | none => rw [chosen] at selected; cases selected
      | some builder =>
        have childSelected : (ReferenceDefaults.compileDefault child memory).isSome = true := by
          rw [chosen]; rfl
        rw [selected_default_words child memory childSelected]
        rfl
  | mapping key value => cases memory
termination_by sizeOf root

theorem selected_default_allocation {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) {H : HTy} (heap : Heap H) :
    heapWords (heap.allocDefault root memory).heap =
      heapWords heap + ReferenceDefaults.defaultCells (.ref root) := by
  have available : (ReferenceDefaults.compileDefault root memory).isSome = true := by
    rw [selected.selected]; rfl
  rw [default_allocation_words, selected_default_words root memory available]

theorem selected_default_checked_demand {root : RefTy} {memory : (Ty.ref root).mapFree = true}
    (selected : SelectedCheckedDefault root memory) {H : HTy} (heap : Heap H)
    (base : Nat → Fin W) (frame : Nat) (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    run selected.code machine =
      if cursor.val + liveWordCount (SVal.dflt (.ref root)) < W
      then run selected.builder.code machine else .revert := by
  have available : (ReferenceDefaults.compileDefault root memory).isSome = true := by
    rw [selected.selected]; rfl
  rw [selected_default_words root memory available]
  exact selected.run_checked heap base frame cursor machine allocator

def selectedDefaultDemand : SelectedDefaultDemandCertificate :=
  ⟨selected_default_words, selected_default_allocation, selected_default_checked_demand⟩

/--
info: 'Solidity.Backend.MemoryCopies.selected_default_words' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms selected_default_words
/--
info: 'Solidity.Backend.MemoryCopies.selected_default_allocation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms selected_default_allocation
/--
info: 'Solidity.Backend.MemoryCopies.selected_default_checked_demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms selected_default_checked_demand
/--
info: 'Solidity.Backend.MemoryCopies.selectedDefaultDemand' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms selectedDefaultDemand
end Solidity.Backend.MemoryCopies
