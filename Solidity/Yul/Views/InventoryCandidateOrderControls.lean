import Solidity.Yul.Views.InventoryCandidateOrder
import Solidity.Yul.Views.InventoryDecodeOrderControls

/-! Reorder both candidates and visits in the changed six-root heap. Shared
pointer targets and duplicate candidate entries keep their identity; omitted,
interior and wrong-shape pointers remain unsupported canonical preparation. -/
namespace Solidity.Yul.Views.Controls

theorem candidates_reverse_source :
    inventoryStateWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries.reverse inventoryPhysical=
      some (.ok (),inventoryAfter) :=
  (inventoryStateWriteback_perm mixedState mixedPlacement mixedPlacement (retainInitial _ _)
    mixedEntries mixedEntries.reverse (List.reverse_perm _).symm mixed_distinct inventoryPhysical).symm.trans inventory_source_step

theorem candidates_reverse_sequential :
    (sequentialInventory mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries.reverse mixedHeap
      mixedPlacement (retainInitial _ _) rfl mixedEntries.reverse inventoryPhysical).map
      (fun result=>((.ok () : Except Source.Halt Unit),withSourceHeap mixedState result.heap))=
      some (.ok (),inventoryAfter) :=
  (inventoryStateWriteback_sequential_candidates_perm mixedState mixedPlacement mixedPlacement (retainInitial _ _)
    mixedEntries mixedEntries.reverse (List.reverse_perm _).symm mixed_distinct inventoryPhysical).symm.trans inventory_source_step

theorem candidates_reverse_aliases :
    inventoryStateWriteback jointAliasState mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries.reverse inventoryPhysical=
      some (.ok (),inventoryAliasAfter) := by
  unfold inventoryStateWriteback
  rw [← decodeInventoryUpdates_candidates mixedPlacement mixedPlacement mixedEntries mixedEntries.reverse
    (List.reverse_perm _).symm mixedEntries.reverse inventoryPhysical]
  exact changed_reverse_alias_state

private def duplicateCandidates := [mixedEntry0,mixedEntry0,mixedEntry1]

theorem duplicate_pointer_order :
    decodeMemoryPointer mixedPlacement duplicateCandidates (.bytes .memory) rfl 128=
      decodeMemoryPointer mixedPlacement duplicateCandidates.reverse (.bytes .memory) rfl 128 :=
  decodeMemoryPointer_perm mixedPlacement duplicateCandidates duplicateCandidates.reverse (List.reverse_perm _).symm _ rfl 128

theorem duplicate_pointer_value :
    decodeMemoryPointer mixedPlacement duplicateCandidates.reverse (.bytes .memory) rfl 128=some (.memRef rfl 0) := rfl

private def invalidCandidateRaw := mstore inventoryPhysical 896 2

theorem invalid_candidates_reverse :
    inventoryStateWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries.reverse invalidCandidateRaw=none := by
  rw [← inventoryStateWriteback_perm mixedState mixedPlacement mixedPlacement (retainInitial _ _)
    mixedEntries mixedEntries.reverse (List.reverse_perm _).symm mixed_distinct invalidCandidateRaw]
  unfold inventoryStateWriteback
  have bad : decodeInventoryUpdates mixedPlacement mixedPlacement mixedEntries mixedEntries invalidCandidateRaw=none := invalid_forward
  rw [bad]
  rfl

private def observed : List Nat :=
  match inventoryStateWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries.reverse inventoryPhysical with
  | some (.ok (),out)=>
    let a:=((Source.heapBytes (E:=mixedEnv) (Γ:=_) 0).run out).1.toOption.getD []
    let b:=((Source.heapBytes (E:=mixedEnv) (Γ:=_) 1).run out).1.toOption.getD []
    [out.2.heap.next]++a.map UInt8.toNat++b.map UInt8.toNat
  | _=>[]
/-- info: [6, 255, 0, 128, 254, 171, 97, 0] -/
#guard_msgs in #eval observed
/-- info: (false, false, false) -/
#guard_msgs in #eval
  ((decodeMemoryPointer mixedPlacement [mixedEntry1] (.bytes .memory) rfl 128).isSome,
   (decodeMemoryPointer mixedPlacement duplicateCandidates (.bytes .memory) rfl 129).isSome,
   (decodeMemoryPointer mixedPlacement duplicateCandidates (.array .memory .bool none) rfl 128).isSome)
/-- info: true -/
#guard_msgs in #eval
  (inventoryStateWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries.reverse invalidCandidateRaw).isNone
end Solidity.Yul.Views.Controls
