import Solidity.Yul.Views.SnapshotHashBinding
import Solidity.Yul.Views.InventoryControls

/-! Actual source keccak on changed raw memory, including two incoming aliases.
Byte controls discriminate wrong header/padding ranges without claiming hash
injectivity for arbitrary approved Fixed parameters. -/
namespace Solidity.Yul.Views.Controls

theorem changed_snapshot_hash (G : Source.Glob mixedEnv) (n : Nat) :
    let value:=Source.mkBytes (D:=mixedLayout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash inventoryNewBytes))
    (Source.evalE G mixedReadFrame (n+4) (sourceMemoryHashExpr Source.Idx.here)).run inventoryAfter=
      (.ok (.val value),inventoryAfter) ∧ value.word=some (keccak256 G.fixed.evm inventoryPhysical 160 4) := by
  obtain ⟨r,run,safe,hash⟩ := sourceMemoryHash_snapshot G mixedReadFrame n mixedState mixedPlacement
    mixedPlacement (retainInitial _ _) mixedEntries mixed_coverage mixed_distinct inventoryPhysical
    (.ok (),inventoryAfter) inventory_source_step
  have stateEq : inventoryAfter=withSourceHeap mixedState r.heap := congrArg Prod.snd run
  have heaps : r.heap=inventoryRealized.heap := (congrArg (fun s=>s.2.heap) stateEq).symm
  have found : r.heap.get 0=some ⟨.bytes .memory,Source.Data.bytes inventoryNewBytes⟩ := by
    rw [heaps]
    exact inventory_cell0
  have answer := hash .here 0 inventoryNewBytes rfl found
  have address : r.placement.address 0=128 := congrFun r.history.addresses 0
  rw [← stateEq,address] at answer
  exact answer

private def hashAliases : Source.EMState mixedEnv [.bytes .memory,.bytes .memory] :=
  (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil),mixedState.2)
private def hashAliasesAfter := withSourceHeap hashAliases inventoryRealized.heap
private theorem aliasStep : inventoryStateWriteback hashAliases mixedPlacement mixedPlacement (retainInitial _ _)
    mixedEntries inventoryPhysical=some (.ok (),hashAliasesAfter) := by
  unfold inventoryStateWriteback
  rw [inventory_decoded,Option.map_some]
  exact congrArg some (realizeInventory_run mixedPlacement mixedPlacement (retainInitial _ _)
    inventoryUpdates hashAliases mixedPlacement (retainInitial _ _) rfl mixedEntries)

theorem changed_alias_hash (G : Source.Glob mixedEnv) (n : Nat) (first : Bool) :
    let index : Source.Idx [.bytes .memory,.bytes .memory] (.bytes .memory):=if first then .here else .there .here
    let value:=Source.mkBytes (D:=mixedLayout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash inventoryNewBytes))
    (Source.evalE G mixedReadFrame (n+4) (sourceMemoryHashExpr index)).run hashAliasesAfter=
      (.ok (.val value),hashAliasesAfter) ∧ value.word=some (keccak256 G.fixed.evm inventoryPhysical 160 4) := by
  obtain ⟨r,run,safe,hash⟩ := sourceMemoryHash_snapshot G mixedReadFrame n hashAliases mixedPlacement
    mixedPlacement (retainInitial _ _) mixedEntries mixed_coverage mixed_distinct inventoryPhysical
    (.ok (),hashAliasesAfter) aliasStep
  have stateEq : hashAliasesAfter=withSourceHeap hashAliases r.heap := congrArg Prod.snd run
  have heaps : r.heap=inventoryRealized.heap := (congrArg (fun s=>s.2.heap) stateEq).symm
  have found : r.heap.get 0=some ⟨.bytes .memory,Source.Data.bytes inventoryNewBytes⟩ := by
    rw [heaps]
    exact inventory_cell0
  have localValue : hashAliases.1.get (if first then .here else .there .here)=Source.Val.memRef rfl 0 := by cases first <;> rfl
  have answer := hash (if first then .here else .there .here) 0 inventoryNewBytes localValue found
  have address : r.placement.address 0=128 := congrFun r.history.addresses 0
  rw [← stateEq,address] at answer
  exact answer

theorem changed_hash_timeout (G : Source.Glob mixedEnv) :
    (Source.evalE G mixedReadFrame 0 (sourceMemoryHashExpr Source.Idx.here)).run inventoryAfter=
      (.error .timeout,inventoryAfter) := rfl

theorem changed_payload : readBytes inventoryPhysical 160 4=inventoryNewBytes :=
  bytesObject_payload_list inventoryNewBytes (by decide) _ 128

theorem wrong_header_range : readBytes inventoryPhysical 128 4≠inventoryNewBytes := by
  intro same
  have first := congrArg (fun xs : List UInt8=>xs[0]?) same
  change some (0 : UInt8)=some 255 at first
  exact (by decide : (0 : UInt8)≠255) (Option.some.inj first)

theorem wrong_padding_range : readBytes inventoryPhysical 160 32≠inventoryNewBytes := by
  intro same
  have length:=congrArg List.length same
  simp only [readBytes,List.length_map,List.length_range,inventoryNewBytes,List.length_cons,List.length_nil] at length
  cases length
end Solidity.Yul.Views.Controls
