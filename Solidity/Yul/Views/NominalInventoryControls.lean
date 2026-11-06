import Solidity.Yul.Views.NominalInventoryLaws
import Solidity.Yul.Views.NominalMemoryControls
import Solidity.Yul.Views.InventoryUnchanged

/-! Actual allocated nominal-array inventory writes, two source aliases and
canonical-failure controls. Existing source and representation witnesses are
reused; no new Source.St or external-call constructor is introduced. -/
namespace Solidity.Yul.Views.NominalInventory.Controls
open Solidity.Yul.Views

def words : Fin 2 → Roadmap.Word := fun i => if i.val=0 then ⟨2^256-1,by decide⟩ else 32767

def entry : MixedHeapEntry NominalMemory.Controls.placement :=
  ⟨0,NominalMemory.Controls.arrayTy,NominalMemory.Controls.data,rfl,
    .words _ _ (.array 2 NominalMemory.Controls.lengthOK (by decide) NominalMemory.Controls.values words
      (fun i => .scalar _ _ ((show ∀ j, (NominalMemory.Controls.values j).word=some (words j) from by decide) i)))⟩

def observe (m : ByteView) : Bool :=
  match writeback NominalMemory.Controls.state NominalMemory.Controls.placement NominalMemory.Controls.placement .initial [entry] m with
  | some (.ok (),after) =>
    decide (NominalMemory.Controls.aliasRead after .here 0 = some ⟨2^256-32768,by decide⟩ ∧
      NominalMemory.Controls.aliasRead after (.there .here) 0 = some ⟨2^256-32768,by decide⟩ ∧
      NominalMemory.Controls.aliasRead after .here 1 = some 0 ∧ after.2.heap.next=1 ∧
      (m 212).toNat=165)
  | _ => false

/-- info: true -/
#guard_msgs in #eval observe NominalMemory.Controls.newRaw
/-- info: false -/
#guard_msgs in #eval observe NominalMemory.Controls.oldRaw
/-- info: false -/
#guard_msgs in #eval observe (mstore NominalMemory.Controls.newRaw 128 65535)
/-- info: false -/
#guard_msgs in #eval (snapshot NominalMemory.Controls.placement NominalMemory.Controls.missing (some 0) NominalMemory.Controls.oldRaw 128).isSome
/-- info: false -/
#guard_msgs in #eval (decodeInventoryObject NominalMemory.Controls.placement [entry] NominalMemory.Controls.arrayTy NominalMemory.Controls.newRaw 128).isSome
/-- info: true -/
#guard_msgs in #eval (decode NominalMemory.Controls.placement [entry] NominalMemory.Controls.arrayTy NominalMemory.Controls.newRaw 128).isSome

def reconstruction (m : ByteView) : Bool :=
  match updates NominalMemory.Controls.placement NominalMemory.Controls.placement [entry] [entry] m with
  | some us => decide (readBytes (reencodeInventory us m) 0 256=readBytes m 0 256)
  | none => false
/-- info: true -/
#guard_msgs in #eval reconstruction NominalMemory.Controls.newRaw
/-- info: false -/
#guard_msgs in #eval reconstruction (mstore NominalMemory.Controls.newRaw 128 65535)

/-- An actual changed whole-source result for the additive inventory dispatcher. -/
theorem changed_source :
    writeback NominalMemory.Controls.state NominalMemory.Controls.placement
      NominalMemory.Controls.placement .initial [entry] NominalMemory.Controls.newRaw =
      some (.ok (),NominalMemory.Controls.newState) := by
  obtain ⟨o,prepared,data⟩ := Option.map_eq_some_iff.mp
    (snapshot_encode NominalMemory.Controls.placement NominalMemory.Controls.small (some 2) 2
      NominalMemory.Controls.lengthOK (by decide) NominalMemory.Controls.newValues
      NominalMemory.Controls.newRaw 128 (by rfl) (by trivial) rfl (by decide))
  have shape : o.shape = .array false 2 :=
    memoryShape_unique o.shaped (data.symm ▸ HasMemoryShape.array 2 NominalMemory.Controls.lengthOK
      (fun i => Source.Data.val (NominalMemory.Controls.newValues i)))
  have capacity : o.shape.size ≤ (NominalMemory.Controls.placement.shape entry.id).size := by
    rw [shape]
    decide
  have decoded : decode NominalMemory.Controls.placement [entry] entry.ty
      NominalMemory.Controls.newRaw (NominalMemory.Controls.placement.address entry.id)=some o := prepared
  unfold writeback updates update
  rw [decoded]
  dsimp only [Bind.bind,Pure.pure,Option.bind,updates]
  rw [dif_pos capacity]
  dsimp only [Option.bind,Option.map]
  rw [runInventoryUpdates,Source.Hoare.run_bind]
  rw [data]
  dsimp only [entry,NominalMemory.Controls.arrayTy]
  rw [memberArrayHeapPut_run NominalMemory.Controls.state 0 (.udvt NominalMemory.Controls.small)
    (some 2) 2 NominalMemory.Controls.lengthOK NominalMemory.Controls.newValues (by rfl)]
  rfl

/-- The new complete source result inhabits the actual owner invariant. -/
theorem changed_MemOK : Source.MemOK NominalMemory.Controls.env NominalMemory.Controls.heap.ty
    NominalMemory.Controls.newState :=
  writeback_MemOK NominalMemory.Controls.heap.ty NominalMemory.Controls.state
    NominalMemory.Controls.placement NominalMemory.Controls.placement .initial [entry]
    NominalMemory.Controls.newRaw _ changed_source NominalMemory.Controls.actual_MemOK

end Solidity.Yul.Views.NominalInventory.Controls
