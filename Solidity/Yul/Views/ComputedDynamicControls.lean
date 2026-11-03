import Solidity.Yul.Views.ComputedDynamicSnapshot
import Solidity.Yul.Views.DynamicInventoryControls

namespace Solidity.Yul.Views.Controls

/-- Both declared array headers choose their live indices. This equality is
computed, not a supplied complete-inventory/coverage law. -/
theorem dyn_computed_snapshot_inventory : dynComputed.snapshotInventory dynTestFixed dynSnapshot = dynRegistry account := rfl

theorem dyn_computed_snapshot_ready : (dynComputed.snapshotWriteback dynTestFixed dynSnapshot
    (dynStorageState.2.ex.world.accounts account).storage).isSome := by
  unfold ComputedStorage.snapshotWriteback
  dsimp only
  rw [dyn_computed_snapshot_inventory]
  have checked := (packedSeparationCheck_iff _).mpr dyn_registry_separated
  rw [checked]
  exact dyn_store_ready

def dynComputedStore := (dynComputed.snapshotWriteback dynTestFixed dynSnapshot
  (dynStorageState.2.ex.world.accounts account).storage).get dyn_computed_snapshot_ready

theorem dyn_computed_whole_map : finiteEncode (dynComputed.snapshotInventory dynTestFixed dynSnapshot)
    dynComputedStore.1 dynComputedStore.2 = some dynSnapshot :=
  dynComputed.snapshot_reencode dynTestFixed dynSnapshot _ _ _ (Option.get_mem dyn_computed_snapshot_ready)

theorem dyn_computed_source_store_exact : dynComputedStore = dynStore := by
  have step : dynComputed.snapshotWriteback dynTestFixed dynSnapshot (dynStorageState.2.ex.world.accounts account).storage = some dynComputedStore :=
    Option.get_mem dyn_computed_snapshot_ready
  unfold ComputedStorage.snapshotWriteback at step
  dsimp only at step
  rw [dyn_computed_snapshot_inventory,(packedSeparationCheck_iff _).mpr dyn_registry_separated] at step
  exact (Option.some.inj ((Option.get_mem dyn_store_ready).symm.trans step)).symm

end Solidity.Yul.Views.Controls
