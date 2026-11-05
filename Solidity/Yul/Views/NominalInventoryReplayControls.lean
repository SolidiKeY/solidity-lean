import Solidity.Yul.Views.NominalInventoryReplay
import Solidity.Yul.Views.NominalInventoryViewControls
import Solidity.Yul.Views.NominalInventoryUnchangedControls

/-! Actual changed-state replay and a two-root mixed reverse-order witness.
These are source/kernel controls, not compiler or reachability evidence. -/
namespace Solidity.Yul.Views.NominalInventory.ReplayControls
open Solidity.Yul.Views
open Solidity.Yul.Views.NominalMemory.Controls

theorem single_profile (a : Nat) (τ : Source.STy) (d : Source.Data env.layout τ)
    (found : heap.get a=some ⟨τ,d⟩) : TypeSupported env τ := by
  have bound : a<heap.next := by
    apply Nat.lt_of_not_le
    intro high
    have absent := heap.bounded a high
    change heap.cells a=some ⟨τ,d⟩ at found
    rw [absent] at found
    cases found
  change a<1 at bound
  have zero : a=0 := by omega
  subst a
  change (some ⟨arrayTy,data⟩ : Option (Σ t,Source.Data env.layout t))=some ⟨τ,d⟩ at found
  cases found
  exact ⟨rfl,by trivial⟩

theorem changed_replay : ∃ r : InventoryRealization placement,
    newState=withSourceHeap state r.heap ∧ RetainedAllocation placement r.placement ∧
    writeback (withSourceHeap state r.heap) placement r.placement r.history r.entries.reverse newRaw=
      some (.ok (),withSourceHeap state r.heap) ∧
    Source.MemOK env heap.ty (withSourceHeap state r.heap) := by
  obtain ⟨r,run,types,covers,nodup,raw,safe,replay⟩ := writeback_replay state placement placement .initial
    [NominalInventory.Controls.entry] NominalInventory.ViewControls.coverage (by decide) single_profile
    newRaw _ NominalInventory.Controls.changed_source
  exact ⟨r,congrArg Prod.snd run,r.history,replay _ (List.reverse_perm _).symm,safe _ actual_MemOK⟩

/-- A nonempty actual changed preparation inhabits the prefix/refresh law. -/
theorem actual_prefix_refresh : ∃ us : List (OwnedInventoryUpdate placement placement),
    updates placement placement [NominalInventory.Controls.entry] [NominalInventory.Controls.entry] newRaw=some us ∧
    us.length=1 ∧
    let selected := us.take 1
    let r := realizeInventory placement placement (.initial : RetainedAllocation placement placement)
      selected heap placement .initial rfl [NominalInventory.Controls.entry]
    newState=withSourceHeap state r.heap ∧
    (∀ τ m base,decode r.placement r.entries τ m base=
      (decode placement [NominalInventory.Controls.entry] τ m base).map
        (InventoryObject.transport r.placement
          (realizeInventory_types placement placement .initial selected heap placement .initial rfl [NominalInventory.Controls.entry])
          (realizeInventory_choices placement placement .initial selected heap placement .initial rfl [NominalInventory.Controls.entry]).1)) := by
  obtain ⟨us,decoded,run⟩ := Option.map_eq_some_iff.mp NominalInventory.Controls.changed_source
  have ids := updates_ids placement placement [NominalInventory.Controls.entry]
    [NominalInventory.Controls.entry] newRaw us decoded
  have length : us.length=1 := by
    have size := congrArg List.length ids
    simpa only [List.length_map,List.length_cons,List.length_nil] using size
  have taken : us.take 1=us := by rw [←length,List.take_length]
  have actual : (runInventoryUpdates (us.take 1)).run state=(.ok (),newState) := by rw [taken]; exact run
  have transported := prefix_transport state placement placement .initial us [NominalInventory.Controls.entry] 1
  exact ⟨us,decoded,length,congrArg Prod.snd (actual.symm.trans transported.1),transported.2⟩

theorem actual_change : newState≠state := by
  have different : aliasRead newState .here 0≠aliasRead state .here 0 := by decide
  intro same
  exact different (congrArg (fun s => aliasRead s .here 0) same)

/-- Both output root IDs are actually present, so reversing this output is a
nontrivial permutation rather than a singleton-order witness. -/
theorem mixed_reverse_replay : ∃ r : InventoryRealization UnchangedControls.placement,
    UnchangedControls.state=withSourceHeap UnchangedControls.state r.heap ∧
    0 ∈ r.entries.map MixedHeapEntry.id ∧ 1 ∈ r.entries.map MixedHeapEntry.id ∧
    writeback (withSourceHeap UnchangedControls.state r.heap) UnchangedControls.placement
      r.placement r.history r.entries.reverse
      (encodeMixedHeap UnchangedControls.placement UnchangedControls.entries UnchangedControls.residual)=
      some (.ok (),withSourceHeap UnchangedControls.state r.heap) := by
  obtain ⟨r,run,types,covers,nodup,raw,safe,replay⟩ := writeback_replay UnchangedControls.state
    UnchangedControls.placement UnchangedControls.placement .initial UnchangedControls.entries
    UnchangedControls.coverage (by decide) UnchangedControls.heap_profile _ _ UnchangedControls.whole_state
  have heaps : r.heap=UnchangedControls.state.2.heap := (congrArg (fun out => out.2.2.heap) run).symm
  obtain ⟨a,memA,idA⟩ := covers 0 (by rw [heaps]; rfl)
  obtain ⟨b,memB,idB⟩ := covers 1 (by rw [heaps]; rfl)
  exact ⟨r,congrArg Prod.snd run,List.mem_map.mpr ⟨a,memA,idA⟩,
    List.mem_map.mpr ⟨b,memB,idB⟩,replay _ (List.reverse_perm _).symm⟩

end Solidity.Yul.Views.NominalInventory.ReplayControls
