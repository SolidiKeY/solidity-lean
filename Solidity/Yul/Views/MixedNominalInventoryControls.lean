import Solidity.Yul.Views.MixedNominalInventoryLaws
import Solidity.Yul.Views.FixedNominalStructControls
import Solidity.Yul.Views.InventoryUnchanged

/-! Actual mixed fixed/nominal struct inventory writes retain full Source state
and both aliases' first-field reads. Dirty preparation and old dispatcher gaps
are distinct from successful typed writeback. -/
namespace Solidity.Yul.Views.MixedNominalInventory.Controls
open Solidity.Yul.Views
open Solidity.Yul.Views.FixedNominalMember.StructControls

theorem changed_source (residual : ByteView) :
    writeback state placement placement .initial [entry] (changed residual)=some (.ok (),expected) := by
  obtain ⟨o,prepared,data⟩ := Option.map_eq_some_iff.mp (changed_snapshot residual)
  have shape : o.shape=.strct 3 := memoryShape_unique o.shaped (data.symm ▸ HasMemoryShape.strct newFields)
  have capacity : o.shape.size≤(placement.shape entry.id).size := by rw [shape]; decide
  have decoded : decode placement [entry] entry.ty (changed residual) (placement.address entry.id)=some o := prepared
  unfold writeback updates update
  rw [decoded]
  dsimp only [Bind.bind,Pure.pure,Option.bind,updates]
  rw [dif_pos capacity]
  dsimp only [Option.bind,Option.map]
  rw [runInventoryUpdates,Source.Hoare.run_bind,data]
  dsimp only [entry,ty]
  rw [structHeapPut_run state 0 box newFields (by rfl)]
  rfl

def aliasRead (alias : Source.Idx [ty,ty] ty) :=
  (writeback state placement placement .initial [entry] (changed (fun _=>165))).map fun result=>
    match result.2.1.get alias with
    | .memRef _ root => some ((Source.readLoc NominalMemory.Controls.readFrame (.mem root 0) :
        Source.EM env [ty,ty] (Source.Val env.layout (.fixed Solidity.Yul.Views.Controls.scaled16))).run result.2)
    | _ => none

theorem both_aliases : aliasRead .here=some (some (.ok (.fixed (-32768) (by decide)),expected)) ∧
    aliasRead (.there .here)=some (some (.ok (.fixed (-32768) (by decide)),expected)) := by
  first | solve | simp only [aliasRead]
        | unfold aliasRead
          rw [changed_source]
          exact ⟨rfl,rfl⟩

theorem dirty_rejected : writeback state placement placement .initial [entry]
    (mstore (fun _=>0) (placement.address 0) 65411)=none := rfl

theorem old_dispatch_gap : FixedNominalInventory.writeback state placement placement .initial [entry]
    (changed (fun _=>165))=none := rfl

theorem fallback_unchanged (m : ByteView) (base : Nat) : decode placement [entry] (.bytes .memory) m base=
    FixedNominalInventory.decode placement [entry] (.bytes .memory) m base := rfl

end Solidity.Yul.Views.MixedNominalInventory.Controls
