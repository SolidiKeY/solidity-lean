import Solidity.Yul.Views.FixedInventoryTransport
import Solidity.Yul.Views.FixedMemoryControls

/-! Changed actual fixed-array inventory writes construct their output view and
retained placement. Canonical aliases read the changed scaled value through real
Source operations. This fixture is not allocation or universal heap adequacy. -/
namespace Solidity.Yul.Views.FixedInventory.RealizationControls
open Solidity.Yul.Views

def words : Fin 2 → Roadmap.Word := fun i=>if i.val=0 then Source.intWord (-125) else 32767
def entry : MixedHeapEntry FixedMemory.Controls.placement :=
  ⟨0,FixedMemory.Controls.ty,FixedMemory.Controls.data,rfl,
    .words _ _ (.array 2 FixedMemory.Controls.lengthOK (by decide) FixedMemory.Controls.values words
      (fun i=>.scalar _ _ (by by_cases zero : i.val=0 <;>
        simp only [FixedMemory.Controls.values,words,zero,if_true,if_false,Source.Val.word] <;> rfl)))⟩

def expectedState := withSourceHeap FixedMemory.Controls.state
  (FixedMemory.Controls.heap.write 0 FixedMemory.Controls.changedData
    (heap_ty_of_get FixedMemory.Controls.heap 0 _ FixedMemory.Controls.data rfl))

theorem changed_source :
    writeback FixedMemory.Controls.state FixedMemory.Controls.placement
      FixedMemory.Controls.placement .initial [entry] FixedMemory.Controls.changedRaw =
      some (.ok (),expectedState) := by
  obtain ⟨o,prepared,data⟩ := Option.map_eq_some_iff.mp
    (snapshot_encode FixedMemory.Controls.placement FixedMemory.Controls.f (some 2) 2
      FixedMemory.Controls.lengthOK (by decide) FixedMemory.Controls.changedValues
      FixedMemory.Controls.changedRaw (FixedMemory.Controls.placement.address 0) rfl FixedMemory.Controls.changed_encoded)
  have shape : o.shape = .array false 2 :=
    memoryShape_unique o.shaped (data.symm ▸ HasMemoryShape.array 2 FixedMemory.Controls.lengthOK
      (fun i => Source.Data.val (FixedMemory.Controls.changedValues i)))
  have capacity : o.shape.size ≤ (FixedMemory.Controls.placement.shape entry.id).size := by
    rw [shape]
    decide
  have decoded : decode FixedMemory.Controls.placement [entry] entry.ty
      FixedMemory.Controls.changedRaw (FixedMemory.Controls.placement.address entry.id)=some o := prepared
  unfold writeback updates update
  rw [decoded]
  dsimp only [Bind.bind,Pure.pure,Option.bind,updates]
  rw [dif_pos capacity]
  dsimp only [Option.bind,Option.map]
  rw [runInventoryUpdates,Source.Hoare.run_bind]
  rw [data]
  dsimp only [entry,FixedMemory.Controls.ty]
  rw [memberArrayHeapPut_run FixedMemory.Controls.state 0 (.fixed FixedMemory.Controls.f)
    (some 2) 2 FixedMemory.Controls.lengthOK FixedMemory.Controls.changedValues (by rfl)]
  rfl


theorem coverage : CoversMixedHeap [entry] := by
  intro a present
  have bound := ComputedPlacement.occupied_lt FixedMemory.Controls.heap a present
  change a<1 at bound
  have zero : a=0 := by omega
  subst a
  exact ⟨entry,List.mem_cons_self,rfl⟩

theorem changed_view : ∃ realized : InventoryRealization FixedMemory.Controls.placement,
    withSourceHeap FixedMemory.Controls.state realized.heap=expectedState ∧
    CoversMixedHeap realized.entries ∧ (realized.entries.map MixedHeapEntry.id).Nodup ∧
    realized.heap.ty=FixedMemory.Controls.heap.ty ∧ realized.heap.next=1 ∧
    realized.placement.address=FixedMemory.Controls.placement.address ∧
    realized.placement.free=FixedMemory.Controls.placement.free ∧
    encodeMixedHeap realized.placement realized.entries FixedMemory.Controls.changedRaw=FixedMemory.Controls.changedRaw := by
  obtain ⟨realized,run,covered,distinct,types,next,addresses,free,raw⟩ :=
    writeback_view FixedMemory.Controls.state FixedMemory.Controls.placement FixedMemory.Controls.placement
      .initial [entry] coverage (by decide) FixedMemory.Controls.changedRaw _ changed_source
  exact ⟨realized,(congrArg Prod.snd run).symm,covered,distinct,types,next,addresses,free,raw⟩

def aliasRead (alias : Source.Idx [FixedMemory.Controls.ty,FixedMemory.Controls.ty] FixedMemory.Controls.ty) :=
  (writeback FixedMemory.Controls.state FixedMemory.Controls.placement FixedMemory.Controls.placement .initial [entry]
    FixedMemory.Controls.changedRaw).map fun after=>
      ((do let loc ← Source.indexLoc NominalMemory.Controls.readFrame (after.2.1.get alias) 0
           Source.readLoc NominalMemory.Controls.readFrame loc) :
        Source.EM FixedMemory.Controls.env _ (Source.Val FixedMemory.Controls.env.layout (.fixed FixedMemory.Controls.f))).run after.2

theorem changed_both_aliases : aliasRead .here=some (.ok (FixedMemory.Controls.changedValues 0),expectedState) ∧
    aliasRead (.there .here)=some (.ok (FixedMemory.Controls.changedValues 0),expectedState) := by
  -- Direct reduction exceeds the retained recursion limit; use the full run.
  unfold aliasRead
  rw [changed_source]
  exact ⟨rfl,rfl⟩

theorem changed_MemOK : Source.MemOK FixedMemory.Controls.env FixedMemory.Controls.heap.ty expectedState :=
  writeback_MemOK FixedMemory.Controls.heap.ty FixedMemory.Controls.state FixedMemory.Controls.placement
    FixedMemory.Controls.placement .initial [entry] FixedMemory.Controls.changedRaw _ changed_source FixedMemory.Controls.actual_MemOK
theorem stale_alias_rejected : aliasRead .here≠some (.ok (FixedMemory.Controls.values 0),expectedState) := by
  rw [changed_both_aliases.1]
  intro same
  have numeric := congrArg (fun result : Option
      (Except Source.Halt (Source.Val FixedMemory.Controls.env.layout (.fixed FixedMemory.Controls.f)) ×
        Source.EMState FixedMemory.Controls.env [FixedMemory.Controls.ty,FixedMemory.Controls.ty]) =>
    match result with | some (.ok (.fixed n _),_) => n | _ => 0) same
  exact (by decide : (-32768 : Int)≠ -125) numeric
end Solidity.Yul.Views.FixedInventory.RealizationControls
