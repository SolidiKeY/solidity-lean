import Solidity.Yul.Views.FixedNominalInventoryLaws
import Solidity.Yul.Views.InventoryUnchanged
import Solidity.Yul.Views.FixedNominalMemoryControls

/-! Actual fixed16x2 nominal inventory preparation and Source mutation retain
both aliases. Dirty and undeclared nominal inputs are unsupported preparation,
not Source errors, and fallback fixed-array decoding remains unchanged. -/
namespace Solidity.Yul.Views.FixedNominalInventory.Controls
open Solidity.Yul.Views

def words : Fin 2 → Roadmap.Word := fun i=>if i.val=0 then Source.intWord (-125) else 32767
def entry : MixedHeapEntry FixedNominalMemory.Controls.placement :=
  ⟨0,FixedNominalMemory.Controls.ty,FixedNominalMemory.Controls.data,rfl,
    .words _ _ (.array 2 FixedMemory.Controls.lengthOK (by decide) FixedNominalMemory.Controls.values words
      (fun i=>.scalar _ _ (by by_cases zero : i.val=0 <;>
        simp only [FixedNominalMemory.Controls.values,words,zero,if_true,if_false,Source.Val.word] <;> rfl)))⟩

def expectedState := withSourceHeap FixedNominalMemory.Controls.state
  (FixedNominalMemory.Controls.heap.write 0 FixedNominalMemory.Controls.newData
    (heap_ty_of_get FixedNominalMemory.Controls.heap 0 _ FixedNominalMemory.Controls.data rfl))

theorem changed_source :
    writeback FixedNominalMemory.Controls.state FixedNominalMemory.Controls.placement
      FixedNominalMemory.Controls.placement .initial [entry] FixedNominalMemory.Controls.changed =
      some (.ok (),expectedState) := by
  obtain ⟨o,prepared,data⟩ := Option.map_eq_some_iff.mp
    (snapshot_encode FixedNominalMemory.Controls.placement FixedNominalMemory.Controls.name (some 2) 2
      FixedMemory.Controls.lengthOK (by decide) FixedNominalMemory.Controls.newValues
      FixedNominalMemory.Controls.changed (FixedNominalMemory.Controls.placement.address 0) (by rfl) (by trivial) rfl FixedNominalMemory.Controls.changed_encoded)
  have shape : o.shape = .array false 2 :=
    memoryShape_unique o.shaped (data.symm ▸ HasMemoryShape.array 2 FixedMemory.Controls.lengthOK
      (fun i => Source.Data.val (FixedNominalMemory.Controls.newValues i)))
  have capacity : o.shape.size ≤ (FixedNominalMemory.Controls.placement.shape entry.id).size := by
    rw [shape]
    decide
  have decoded : decode FixedNominalMemory.Controls.placement [entry] entry.ty
      FixedNominalMemory.Controls.changed (FixedNominalMemory.Controls.placement.address entry.id)=some o := prepared
  unfold writeback updates update
  rw [decoded]
  dsimp only [Bind.bind,Pure.pure,Option.bind,updates]
  rw [dif_pos capacity]
  dsimp only [Option.bind,Option.map]
  rw [runInventoryUpdates,Source.Hoare.run_bind]
  rw [data]
  dsimp only [entry,FixedNominalMemory.Controls.ty]
  rw [memberArrayHeapPut_run FixedNominalMemory.Controls.state 0 (.udvt FixedNominalMemory.Controls.name)
    (some 2) 2 FixedMemory.Controls.lengthOK FixedNominalMemory.Controls.newValues (by rfl)]
  rfl


theorem actual_both_aliases :
    expectedState=FixedNominalMemory.Controls.expected ∧
    ((do let loc ← Source.indexLoc NominalMemory.Controls.readFrame (expectedState.1.get .here) 0
         Source.readLoc NominalMemory.Controls.readFrame loc) :
      Source.EM FixedNominalMemory.Controls.env [FixedNominalMemory.Controls.ty,FixedNominalMemory.Controls.ty]
        (Source.Val FixedNominalMemory.Controls.env.layout (.udvt FixedNominalMemory.Controls.name))).run expectedState=
      (.ok (FixedNominalMemory.Controls.newValues 0),expectedState) ∧
    ((do let loc ← Source.indexLoc NominalMemory.Controls.readFrame (expectedState.1.get (.there .here)) 0
         Source.readLoc NominalMemory.Controls.readFrame loc) :
      Source.EM FixedNominalMemory.Controls.env [FixedNominalMemory.Controls.ty,FixedNominalMemory.Controls.ty]
        (Source.Val FixedNominalMemory.Controls.env.layout (.udvt FixedNominalMemory.Controls.name))).run expectedState=
      (.ok (FixedNominalMemory.Controls.newValues 0),expectedState) := by
  first | solve | simp only
        | exact ⟨rfl,FixedNominalMemory.Controls.both_aliases.1,FixedNominalMemory.Controls.both_aliases.2⟩

theorem dirty_rejected : writeback FixedNominalMemory.Controls.state FixedNominalMemory.Controls.placement
    FixedNominalMemory.Controls.placement .initial [entry]
    (mstore FixedNominalMemory.Controls.raw (FixedNominalMemory.Controls.placement.address 0) 65411)=none := by
  first | solve | rfl
        | solve | decide

theorem missing_declaration : snapshot FixedNominalMemory.Controls.placement
    FixedNominalMemory.Controls.missing (some 0) (fun _=>0) 128=none := rfl

theorem fixed_fallback (es : List (MixedHeapEntry FixedMemory.Controls.placement)) (m : ByteView) (base : Nat) :
    decode FixedMemory.Controls.placement es FixedMemory.Controls.ty m base=
      FixedInventory.decode FixedMemory.Controls.placement es FixedMemory.Controls.ty m base := rfl

end Solidity.Yul.Views.FixedNominalInventory.Controls
