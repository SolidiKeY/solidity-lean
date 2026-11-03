import Solidity.Yul.Views.InventoryUnchanged
import Solidity.Yul.Views.InventoryOrder
import Solidity.Yul.Views.InventoryView
import Solidity.Yul.Views.InventorySourceReads
import Solidity.Yul.Views.JointRetainedControls

namespace Solidity.Yul.Views.Controls

theorem inventory_mixed_support (e : MixedHeapEntry mixedPlacement) (member : e ∈ mixedEntries) : InventoryTypeSupported mixedEnv e.ty := by
  simp only [mixedEntries,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with eq | eq | eq | eq | eq | eq
  · subst e; trivial
  · subst e; trivial
  · subst e; exact Or.inl (Or.inr (Or.inl rfl))
  · subst e; exact fun τ mem => Or.inl (mixed_member_support τ mem)
  · subst e; exact Or.inl (Or.inr (Or.inr rfl))
  · subst e; trivial

theorem inventory_initial_whole_state : inventoryStateWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries mixedPhysical = some (.ok (),mixedState) :=
  inventoryStateWriteback_unchanged mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries mixed_coverage inventory_mixed_support mixedPhysical mixed_all_reads

def inventoryNewBytes : List UInt8 := [0xff,0,0x80,0xfe]
def inventoryNewString : List UInt8 := [0xab,0x61,0]
def inventoryPhysical := bytesObjectView inventoryNewBytes (by decide)
  (bytesObjectView inventoryNewString (by decide) (wordListView [7,42] jointPhysical 640) 384) 128

/-- The actual six-root decoder, not a supplied list of inverse/safety laws. -/
theorem inventory_decode_inhabited : (decodeInventoryUpdates mixedPlacement mixedPlacement mixedEntries mixedEntries inventoryPhysical).isSome := by decide

def inventoryUpdates := (decodeInventoryUpdates mixedPlacement mixedPlacement mixedEntries mixedEntries inventoryPhysical).get inventory_decode_inhabited

theorem inventory_decoded : decodeInventoryUpdates mixedPlacement mixedPlacement mixedEntries mixedEntries inventoryPhysical = some inventoryUpdates :=
  (Option.some_get inventory_decode_inhabited).symm

def inventoryRealized := realizeInventory mixedPlacement mixedPlacement (retainInitial _ _) inventoryUpdates mixedHeap mixedPlacement (retainInitial _ _) rfl mixedEntries
def inventoryAfter := withSourceHeap mixedState inventoryRealized.heap

theorem inventory_source_step : inventoryStateWriteback mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries inventoryPhysical = some (.ok (),inventoryAfter) := by
  unfold inventoryStateWriteback
  rw [inventory_decoded,Option.map_some]
  exact congrArg some (realizeInventory_run mixedPlacement mixedPlacement (retainInitial _ _) inventoryUpdates mixedState mixedPlacement (retainInitial _ _) rfl mixedEntries)

theorem inventory_all_H_MemOK (H : Source.HeapTy) (ok : Source.MemOK mixedEnv H mixedState) : Source.MemOK mixedEnv H inventoryAfter :=
  inventoryStateWriteback_MemOK H mixedState mixedPlacement mixedPlacement (retainInitial _ _) mixedEntries inventoryPhysical _ inventory_source_step ok

theorem inventory_actual_MemOK : Source.MemOK mixedEnv mixedHeap.ty inventoryAfter := inventory_all_H_MemOK _ mixed_actual_MemOK

theorem inventory_history_and_coverage : RetainedAllocation mixedPlacement inventoryRealized.placement ∧ CoversMixedHeap inventoryRealized.entries :=
  ⟨inventoryRealized.history,realizeInventory_coverage _ _ _ inventoryUpdates _ _ _ rfl mixedEntries mixed_coverage⟩

theorem inventory_full_raw_roundtrip : reencodeInventory inventoryUpdates inventoryPhysical = inventoryPhysical :=
  reencodeInventory_raw _ _ _ _ _ _ inventory_decoded

def inventoryAliasAfter := withSourceHeap jointAliasState inventoryRealized.heap

theorem inventory_cell0 : inventoryRealized.heap.get 0 = some ⟨.bytes .memory,.bytes inventoryNewBytes⟩ := by
  have symbolic : inventoryRealized.heap.get 0 = some ⟨.bytes .memory,decodeBytesObject mixedLayout inventoryPhysical 128⟩ := rfl
  have decoded : decodeBytesObject mixedLayout inventoryPhysical 128 = .bytes inventoryNewBytes :=
    decode_bytesObjectView mixedLayout inventoryNewBytes (by decide) (bytesObjectView inventoryNewString (by decide) (wordListView [7,42] jointPhysical 640) 384) 128
  rw [decoded] at symbolic
  exact symbolic

theorem inventory_string_decode : decodeStringObject mixedLayout inventoryPhysical 384 = .string inventoryNewString := by
  let inner := bytesObjectView inventoryNewString (by decide) (wordListView [7,42] jointPhysical 640) 384
  have header : mload inventoryPhysical 384 = ⟨inventoryNewString.length,by decide⟩ := by
    rw [mload_congr inventoryPhysical inner 384 (fun i => bytesObject_residual inventoryNewBytes (by decide) _ 128 _ (Or.inr (by have hi := i.isLt; change 128+32+4 ≤ 384+i.val; omega)))]
    exact bytesObject_header inventoryNewString (by decide) _ 384
  unfold decodeStringObject
  rw [header]
  apply congrArg (Source.Data.string (D := mixedLayout) (l := .memory))
  calc
    _ = readBytes inner 416 3 := readBytes_congr_on inventoryPhysical inner 416 3 (fun i _ => bytesObject_residual inventoryNewBytes (by decide) _ 128 _ (Or.inr (by change 128+32+4 ≤ 416+i; omega)))
    _ = inventoryNewString := bytesObject_payload_list inventoryNewString (by decide) _ 384

theorem inventory_cell1 : inventoryRealized.heap.get 1 = some ⟨.string .memory,.string inventoryNewString⟩ := by
  have symbolic : inventoryRealized.heap.get 1 = some ⟨.string .memory,decodeStringObject mixedLayout inventoryPhysical 384⟩ := rfl
  rw [inventory_string_decode] at symbolic
  exact symbolic

def inventoryRValues : Fin 2 → Source.Val mixedLayout (.bytes .memory) := Fin.cases (.memRef rfl 1) (Fin.cases (.memRef rfl 1) Fin.elim0)
theorem inventory_cell4 : inventoryRealized.heap.get 4 = some ⟨mixedArrayTy,dynamicMemberData mixedLayout (.bytes .memory) 2 inventoryRValues⟩ := rfl

theorem inventory_cell3 : inventoryRealized.heap.get 3 = some ⟨.struct .memory mixedName,.struct allChangedFields⟩ := rfl

theorem inventory_alias_panic (horizon : Nat) : (readJointAlias false 2 horizon).run inventoryAliasAfter =
    (.error (.revert (Source.panicData .index)),inventoryAliasAfter) := rfl

theorem inventory_original_types_next_locals_world : inventoryRealized.heap.ty = mixedHeap.ty ∧ inventoryRealized.heap.next = mixedHeap.next ∧
    inventoryAfter.1 = mixedState.1 ∧ inventoryAfter.2.ex = mixedState.2.ex ∧ inventoryAfter.2.events = mixedState.2.events :=
  ⟨realizeInventory_types _ _ _ inventoryUpdates _ _ _ rfl mixedEntries,(realizeInventory_choices _ _ _ inventoryUpdates _ _ _ rfl mixedEntries).2.2,rfl,rfl,rfl⟩

theorem inventory_reverse_order : (runInventoryUpdates inventoryUpdates.reverse).run mixedState = (runInventoryUpdates inventoryUpdates).run mixedState := by
  have ids := decodeInventoryUpdates_ids mixedPlacement mixedPlacement mixedEntries mixedEntries inventoryPhysical inventoryUpdates inventory_decoded
  have nd : (inventoryUpdates.map (fun u => u.entry.id)).Nodup := by rw [ids]; exact mixed_distinct
  exact (runInventoryUpdates_perm (List.reverse_perm inventoryUpdates).symm nd mixedState rfl).symm

theorem inventory_beyond_owned_extent : (decodeInventoryUpdates mixedPlacement mixedPlacement mixedEntries mixedEntries (mstore inventoryPhysical 128 33)).isNone := by decide

theorem inventory_missing_pointer_candidates : (decodeInventoryUpdates mixedPlacement mixedPlacement (mixedEntries.drop 2) (mixedEntries.drop 2) inventoryPhysical).isNone := by decide

end Solidity.Yul.Views.Controls
