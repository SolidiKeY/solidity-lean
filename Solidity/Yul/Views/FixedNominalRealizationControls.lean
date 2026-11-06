import Solidity.Yul.Views.FixedNominalInventoryReplay
import Solidity.Yul.Views.FixedNominalGeneratedControls
import Solidity.Yul.Views.FixedNominalUnchangedControls

/-! Actual changed fixed16x2 nominal data constructs a physical view and replay
certificate. Both aliases observe the reached value, not stale initial data.
These are kernel heap fixtures, not allocation/compiler provenance evidence. -/
namespace Solidity.Yul.Views.FixedNominalInventory.RealizationControls
open Solidity.Yul.Views
open Solidity.Yul.Views.FixedNominalInventory.Controls

theorem changed_view : ∃ r : InventoryRealization FixedNominalMemory.Controls.placement,
    withSourceHeap FixedNominalMemory.Controls.state r.heap=expectedState ∧
    CoversMixedHeap r.entries ∧ (r.entries.map MixedHeapEntry.id).Nodup ∧
    r.placement.address=FixedNominalMemory.Controls.placement.address ∧
    r.placement.free=FixedNominalMemory.Controls.placement.free ∧
    encodeMixedHeap r.placement r.entries FixedNominalMemory.Controls.changed=FixedNominalMemory.Controls.changed := by
  first | solve | simp only
        | obtain ⟨r,run,covers,distinct,_,_,addresses,free,raw⟩ := writeback_view
            FixedNominalMemory.Controls.state FixedNominalMemory.Controls.placement
            FixedNominalMemory.Controls.placement .initial [entry] UnchangedControls.coverage
            (by decide) FixedNominalMemory.Controls.changed _ changed_source
          exact ⟨r,(congrArg Prod.snd run).symm,covers,distinct,addresses,free,raw⟩

theorem changed_replay : ∃ r : InventoryRealization FixedNominalMemory.Controls.placement,
    withSourceHeap FixedNominalMemory.Controls.state r.heap=expectedState ∧
    writeback (withSourceHeap FixedNominalMemory.Controls.state r.heap) FixedNominalMemory.Controls.placement
      r.placement r.history r.entries FixedNominalMemory.Controls.changed=some (.ok (),expectedState) ∧
    Source.MemOK FixedNominalMemory.Controls.env FixedNominalMemory.Controls.heap.ty
      (withSourceHeap FixedNominalMemory.Controls.state r.heap) := by
  first | solve | simp only
        | obtain ⟨r,run,_,_,_,safe,replay⟩ := writeback_replay FixedNominalMemory.Controls.state
            FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.placement .initial [entry]
            UnchangedControls.coverage (by decide) GeneratedControls.heap_profile
            FixedNominalMemory.Controls.changed _ changed_source
          have same := (congrArg Prod.snd run).symm
          exact ⟨r,same,replay.trans (congrArg (fun s=>some ((.ok () : Except Source.Halt Unit),s)) same),
            safe _ GeneratedControls.actual_MemOK⟩

def readFirst (s : Source.EMState FixedNominalMemory.Controls.env
    [FixedNominalMemory.Controls.ty,FixedNominalMemory.Controls.ty])
    (alias : Source.Idx [FixedNominalMemory.Controls.ty,FixedNominalMemory.Controls.ty] FixedNominalMemory.Controls.ty) :=
  ((do let loc ← Source.indexLoc NominalMemory.Controls.readFrame (s.1.get alias) 0
       Source.readLoc NominalMemory.Controls.readFrame loc) :
    Source.EM FixedNominalMemory.Controls.env [FixedNominalMemory.Controls.ty,FixedNominalMemory.Controls.ty]
      (Source.Val FixedNominalMemory.Controls.env.layout (.udvt FixedNominalMemory.Controls.name))).run s

theorem replay_aliases : ∃ r : InventoryRealization FixedNominalMemory.Controls.placement,
    writeback (withSourceHeap FixedNominalMemory.Controls.state r.heap) FixedNominalMemory.Controls.placement
      r.placement r.history r.entries FixedNominalMemory.Controls.changed=some (.ok (),expectedState) ∧
    readFirst (withSourceHeap FixedNominalMemory.Controls.state r.heap) .here=
      (.ok (FixedNominalMemory.Controls.newValues 0),expectedState) ∧
    readFirst (withSourceHeap FixedNominalMemory.Controls.state r.heap) (.there .here)=
      (.ok (FixedNominalMemory.Controls.newValues 0),expectedState) := by
  first | solve | simp only
        | obtain ⟨r,same,replay,_⟩ := changed_replay
          refine ⟨r,replay,?_,?_⟩ <;> rw [same] <;> rfl

theorem stale_state_rejected : expectedState≠FixedNominalMemory.Controls.state := by
  first | solve | decide
        | intro same
          have observed := congrArg (fun s=>match (readFirst s .here).1 with
            | .ok (.udvt (.fixed n _)) => n | _ => 0) same
          exact (by decide : (-32768 : Int)≠ -125) observed

end Solidity.Yul.Views.FixedNominalInventory.RealizationControls
