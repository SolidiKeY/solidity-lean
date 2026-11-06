import Solidity.Yul.Views.DynamicInventoryWriteback
import Solidity.Yul.Views.DynamicAdministration

namespace Solidity.Yul.Views.Controls

theorem dyn_complete_live_paths : (dynX.inventory dynTestFixed account 2).map ScalarPath.path =
    [dynPath "xs",⟨dynName "xs",[.index 0]⟩,⟨dynName "xs",[.index 1]⟩] := rfl

theorem dyn_complete_live_separation : finiteSeparated (dynX.inventory dynTestFixed account 2) :=
  dynX.inventory_separated dynTestFixed account 2 8 dynRoots dynPreimages dyn_test_regions (by decide) (by decide) (by decide) (by decide)

theorem dyn_live_snapshot_ready : (dynX.snapshotWriteback dynTestFixed account dynSnapshot
    (dynStorageState.2.ex.world.accounts account).storage).isSome := by decide

def dynLiveStore := (dynX.snapshotWriteback dynTestFixed account dynSnapshot
  (dynStorageState.2.ex.world.accounts account).storage).get dyn_live_snapshot_ready

theorem dyn_complete_live_full_raw_map : finiteEncode (dynX.inventory dynTestFixed account (dynSnapshot (dynX.registration account).slot))
    dynLiveStore.1 dynLiveStore.2 = some dynSnapshot :=
  dynX.snapshot_reencode dynTestFixed account 8 dynRoots dynPreimages dyn_test_regions (by decide) dynSnapshot (by decide)
    (by decide) (by decide) _ _ _ (Option.get_mem dyn_live_snapshot_ready)

theorem dyn_live_only_preserves_other_array : dynLiveStore.1.cell (dynPath "ys") = none ∧
    dynLiveStore.1.cell ⟨dynName "ys",[.index 0]⟩ = none ∧ dynLiveStore.2 1002 = 77 := ⟨rfl,rfl,rfl⟩

def dynGrowSnapshot : SlotView := fun q => if q = 43 then 3 else dynSnapshot q

theorem dyn_grow_live_ready : (dynX.snapshotWriteback dynTestFixed account dynGrowSnapshot dynLiveStore.1).isSome := by decide

def dynGrowLiveStore := (dynX.snapshotWriteback dynTestFixed account dynGrowSnapshot dynLiveStore.1).get dyn_grow_live_ready

theorem dyn_new_live_tail_decoded : dynGrowLiveStore.1.read (dynPath "xs") = some (.int 3 (by decide)) ∧
    dynGrowLiveStore.1.read ⟨dynName "xs",[.index 2]⟩ = some (.int 77 (by decide)) := ⟨rfl,rfl⟩

theorem dyn_grown_full_raw_map : finiteEncode (dynX.inventory dynTestFixed account (dynGrowSnapshot (dynX.registration account).slot))
    dynGrowLiveStore.1 dynGrowLiveStore.2 = some dynGrowSnapshot :=
  dynX.snapshot_reencode dynTestFixed account 8 dynRoots dynPreimages dyn_test_regions (by decide) dynGrowSnapshot (by decide)
    (by decide) (by decide) _ _ _ (Option.get_mem dyn_grow_live_ready)

end Solidity.Yul.Views.Controls
