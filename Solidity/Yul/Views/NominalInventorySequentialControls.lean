import Solidity.Yul.Views.NominalInventorySequential
import Solidity.Yul.Views.NominalInventoryDynamicControls
import Solidity.Yul.Views.NominalInventoryUnchangedControls

/-! Executable sequential preparation controls: generated mixed inventories,
retained regrowth, duplicates, and first/late unsupported preparation. A late
None discards a pure preparation plan; it is not a source rollback verdict. -/
namespace Solidity.Yul.Views.NominalInventory.SequentialControls
open Solidity.Yul.Views

/-- The actual generated mixed inventory reaches its complete source result. -/
theorem generated_sequence : ∃ r : InventoryRealization UnchangedControls.placement,
    sequential UnchangedControls.placement UnchangedControls.placement .initial
      (generatedHeapEntries UnchangedControls.placement) UnchangedControls.state.2.heap
      UnchangedControls.placement .initial rfl (generatedHeapEntries UnchangedControls.placement)
      (encodeMixedHeap UnchangedControls.placement (generatedHeapEntries UnchangedControls.placement) UnchangedControls.residual)=some r ∧
    UnchangedControls.state=withSourceHeap UnchangedControls.state r.heap := by
  have actual := (writeback_sequential UnchangedControls.state UnchangedControls.placement
    UnchangedControls.placement .initial (generatedHeapEntries UnchangedControls.placement) _).symm.trans
    UnchangedControls.generated_whole_state.2
  obtain ⟨r,prepared,out⟩ := Option.map_eq_some_iff.mp actual
  exact ⟨r,prepared,(congrArg Prod.snd out).symm⟩

/-- Current zero-length shape refreshes to a genuine retained regrown state. -/
theorem regrow_sequence : ∃ r : InventoryRealization NominalMemory.RetainedControls.placement,
    sequential NominalMemory.RetainedControls.placement NominalMemory.RetainedControls.shrunkPlacement
      NominalMemory.RetainedControls.shrunkHistory [DynamicControls.emptyEntry]
      NominalMemory.RetainedControls.shrunkHeap NominalMemory.RetainedControls.shrunkPlacement
      NominalMemory.RetainedControls.shrunkHistory rfl [DynamicControls.emptyEntry]
      NominalMemory.RetainedControls.regrownRaw=some r ∧
    NominalMemory.RetainedControls.regrownState=withSourceHeap NominalMemory.RetainedControls.shrunkState r.heap ∧
    RetainedAllocation NominalMemory.RetainedControls.placement r.placement := by
  have actual := (writeback_sequential NominalMemory.RetainedControls.shrunkState
    NominalMemory.RetainedControls.placement NominalMemory.RetainedControls.shrunkPlacement
    NominalMemory.RetainedControls.shrunkHistory [DynamicControls.emptyEntry] _).symm.trans DynamicControls.inventory_regrow
  obtain ⟨r,prepared,out⟩ := Option.map_eq_some_iff.mp actual
  exact ⟨r,prepared,(congrArg Prod.snd out).symm,r.history⟩

def mixedRaw : ByteView := encodeMixedHeap UnchangedControls.placement UnchangedControls.entries UnchangedControls.residual
def lateRaw : ByteView := mstore (mstore (mstore mixedRaw 128 ⟨2^256-32768,by decide⟩) 160 0) 192 4
def beyondRaw : ByteView := mstore lateRaw 192 33
def firstRaw : ByteView := mstore mixedRaw 128 65535

private def sequentialReady (es : List (MixedHeapEntry UnchangedControls.placement)) (m : ByteView) : Bool :=
  (sequential UnchangedControls.placement UnchangedControls.placement .initial es UnchangedControls.state.2.heap
    UnchangedControls.placement .initial rfl es m).isSome

/- Four bytes fit the original rounded payload allocation. -/
/-- info: (true, true, true) -/
#guard_msgs in #eval
  ((update UnchangedControls.placement UnchangedControls.placement UnchangedControls.entries UnchangedControls.nominal lateRaw).isSome,
   (decode UnchangedControls.placement UnchangedControls.entries UnchangedControls.bytes.ty lateRaw 192).isSome,
   sequentialReady UnchangedControls.entries lateRaw)
/- Thirty-three bytes require another payload word; decoding still succeeds. -/
/-- info: (true, true, false) -/
#guard_msgs in #eval
  ((update UnchangedControls.placement UnchangedControls.placement UnchangedControls.entries UnchangedControls.nominal beyondRaw).isSome,
   (decode UnchangedControls.placement UnchangedControls.entries UnchangedControls.bytes.ty beyondRaw 192).isSome,
   sequentialReady UnchangedControls.entries beyondRaw)
/-- info: (false, false) -/
#guard_msgs in #eval
  ((update UnchangedControls.placement UnchangedControls.placement UnchangedControls.entries UnchangedControls.nominal firstRaw).isSome,
   sequentialReady UnchangedControls.entries firstRaw)
/-- info: (true, true) -/
#guard_msgs in #eval (sequentialReady UnchangedControls.entries mixedRaw,
  sequentialReady UnchangedControls.repeatedEntries mixedRaw)

end Solidity.Yul.Views.NominalInventory.SequentialControls
