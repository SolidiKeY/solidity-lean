import Solidity.Yul.Views.MixedNominalInventoryReplay
import Solidity.Yul.Views.MixedNominalGeneratedControls

/-! A changed real mixed struct constructs its reached physical view and replay.
The full Source result and both alias field reads stay tied to actual writes;
no output view, decoder support or desired safety law is supplied. -/
namespace Solidity.Yul.Views.MixedNominalInventory.RealizationControls
open Solidity.Yul.Views
open Solidity.Yul.Views.FixedNominalMember.StructControls

theorem changed_view (residual : ByteView) : ∃ r : InventoryRealization placement,
    withSourceHeap state r.heap=expected ∧ CoversMixedHeap r.entries ∧
    (r.entries.map MixedHeapEntry.id).Nodup ∧ r.placement.address=placement.address ∧
    r.placement.free=placement.free ∧ encodeMixedHeap r.placement r.entries (changed residual)=changed residual := by
  first | solve | simp only
        | obtain ⟨r,run,covers,distinct,_,_,addresses,free,raw⟩ :=
            writeback_view state placement placement .initial [entry] covered (by decide)
              (changed residual) _ (Controls.changed_source residual)
          exact ⟨r,(congrArg Prod.snd run).symm,covers,distinct,addresses,free,raw⟩

theorem changed_replay (residual : ByteView) : ∃ r : InventoryRealization placement,
    withSourceHeap state r.heap=expected ∧
    writeback (withSourceHeap state r.heap) placement r.placement r.history r.entries (changed residual)=some (.ok (),expected) ∧
    Source.MemOK env heap.ty (withSourceHeap state r.heap) := by
  first | solve | simp only
        | obtain ⟨r,run,_,_,_,safe,replay⟩ := writeback_replay state placement placement .initial [entry]
            covered (by decide) GeneratedControls.heap_profile (changed residual) _ (Controls.changed_source residual)
          have same := (congrArg Prod.snd run).symm
          exact ⟨r,same,replay.trans (congrArg (fun s=>some ((.ok () : Except Source.Halt Unit),s)) same),
            safe _ GeneratedControls.actual_MemOK⟩

def readFirst (s : Source.EMState env [ty,ty]) (alias : Source.Idx [ty,ty] ty) :=
  match s.1.get alias with
  | .memRef _ root=>some ((Source.readLoc NominalMemory.Controls.readFrame (.mem root 0) :
      Source.EM env [ty,ty] (Source.Val env.layout (.fixed Solidity.Yul.Views.Controls.scaled16))).run s)
  | _=>none

theorem replay_aliases (residual : ByteView) : ∃ r : InventoryRealization placement,
    writeback (withSourceHeap state r.heap) placement r.placement r.history r.entries (changed residual)=some (.ok (),expected) ∧
    readFirst (withSourceHeap state r.heap) .here=some (.ok (.fixed (-32768) (by decide)),expected) ∧
    readFirst (withSourceHeap state r.heap) (.there .here)=some (.ok (.fixed (-32768) (by decide)),expected) := by
  first | solve | simp only
        | obtain ⟨r,same,replay,_⟩ := changed_replay residual
          refine ⟨r,replay,?_,?_⟩ <;> rw [same] <;> rfl

theorem stale_state_rejected : expected≠state := by
  first | solve | decide
        | intro same
          have observed := congrArg (fun s=>match readFirst s .here with
            | some (.ok (.fixed n _),_)=>n | _=>0) same
          exact (by decide : (-32768 : Int)≠ -125) observed

end Solidity.Yul.Views.MixedNominalInventory.RealizationControls
