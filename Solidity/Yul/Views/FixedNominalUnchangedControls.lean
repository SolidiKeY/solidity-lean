import Solidity.Yul.Views.FixedNominalInventoryUnchanged
import Solidity.Yul.Views.FixedNominalInventoryControls

/-! Whole-state identity on a real fixed16x2 nominal heap for every residual
map. Both source aliases are read after the actual writeback; duplicate root
IDs and an empty inventory are explicitly distinct from a complete unique view. -/
namespace Solidity.Yul.Views.FixedNominalInventory.UnchangedControls
open Solidity.Yul.Views
open Solidity.Yul.Views.FixedNominalInventory.Controls

theorem coverage : CoversMixedHeap [entry] := by
  first | solve | simp only [CoversMixedHeap]
        | intro a present
          have bound := ComputedPlacement.occupied_lt FixedNominalMemory.Controls.heap a present
          change a<1 at bound
          have zero : a=0 := by omega
          subst a
          exact ⟨entry,List.mem_cons_self,rfl⟩

theorem supported : ∀ e∈[entry],TypeSupported FixedNominalMemory.Controls.env e.ty := by
  first | solve | simp only [List.mem_singleton]
        | intro e member
          cases List.mem_singleton.mp member
          exact ⟨rfl,trivial⟩

theorem entire_state (residual : ByteView) :
    writeback FixedNominalMemory.Controls.state FixedNominalMemory.Controls.placement
      FixedNominalMemory.Controls.placement .initial [entry]
      (encodeMixedHeap FixedNominalMemory.Controls.placement [entry] residual)=
      some (.ok (),FixedNominalMemory.Controls.state) := by
  first | solve | simp only
        | apply writeback_encoded
          · exact coverage
          · decide
          · exact supported

def afterRead (residual : ByteView)
    (alias : Source.Idx [FixedNominalMemory.Controls.ty,FixedNominalMemory.Controls.ty] FixedNominalMemory.Controls.ty) :=
  (writeback FixedNominalMemory.Controls.state FixedNominalMemory.Controls.placement
    FixedNominalMemory.Controls.placement .initial [entry]
    (encodeMixedHeap FixedNominalMemory.Controls.placement [entry] residual)).map fun after=>
    ((do let loc ← Source.indexLoc NominalMemory.Controls.readFrame (after.2.1.get alias) 0
         Source.readLoc NominalMemory.Controls.readFrame loc) :
      Source.EM FixedNominalMemory.Controls.env [FixedNominalMemory.Controls.ty,FixedNominalMemory.Controls.ty]
        (Source.Val FixedNominalMemory.Controls.env.layout (.udvt FixedNominalMemory.Controls.name))).run after.2

theorem both_aliases (residual : ByteView) :
    afterRead residual .here=some (.ok (FixedNominalMemory.Controls.values 0),FixedNominalMemory.Controls.state) ∧
    afterRead residual (.there .here)=some (.ok (FixedNominalMemory.Controls.values 0),FixedNominalMemory.Controls.state) := by
  first | solve | simp only [afterRead]
        | unfold afterRead
          rw [entire_state]
          exact ⟨rfl,rfl⟩

theorem empty_is_incomplete : ¬ CoversMixedHeap ([] : List (MixedHeapEntry FixedNominalMemory.Controls.placement)) := by
  first | solve | simp only [CoversMixedHeap]
        | intro covered
          obtain ⟨e,member,_⟩ := covered 0 (by rfl)
          cases member

theorem duplicate_ids : ¬ ([entry,entry].map MixedHeapEntry.id).Nodup := by decide

end Solidity.Yul.Views.FixedNominalInventory.UnchangedControls
