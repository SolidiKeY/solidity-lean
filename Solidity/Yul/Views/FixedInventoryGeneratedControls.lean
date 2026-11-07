import Solidity.Yul.Views.FixedInventoryPreparation
import Solidity.Yul.Views.FixedInventoryControls

/-! Actual heap-derived preparation for the fixed/byte combination. The images,
coverage and unique enumeration are computed, not manually supplied final laws.
Fresh alias reads occur after the exact unchanged whole-Source writeback. -/
namespace Solidity.Yul.Views.FixedInventory.GeneratedControls
open Solidity.Yul.Views Solidity.Yul.Views.FixedInventory.Controls

theorem actual_MemOK : Source.MemOK FixedMemory.Controls.env state.2.heap.ty state :=
  (objectAllocRef_MemOK FixedMemory.Controls.heap.ty FixedMemory.Controls.state payload rfl
    trivial trivial (.bytes _) FixedMemory.Controls.actual_MemOK).1.self

theorem heap_profile (a : Nat) (τ : Source.STy) (d : Source.Data FixedMemory.Controls.env.layout τ)
    (found : state.2.heap.get a=some ⟨τ,d⟩) : TypeSupported FixedMemory.Controls.env τ := by
  have present : (state.2.heap.get a).isSome := by rw [found]; rfl
  have bound := ComputedPlacement.occupied_lt state.2.heap a present
  change a<2 at bound
  have choices : a=0 ∨ a=1 := by omega
  rcases choices with zero | one
  · subst a
    change (some ⟨FixedMemory.Controls.ty,FixedMemory.Controls.data⟩ :
      Option (Σ t,Source.Data FixedMemory.Controls.env.layout t))=some ⟨τ,d⟩ at found
    cases found
    trivial
  · subst a
    change (some ⟨.bytes .memory,payload⟩ :
      Option (Σ t,Source.Data FixedMemory.Controls.env.layout t))=some ⟨τ,d⟩ at found
    cases found
    trivial

theorem generated_whole_state :
    prepareHeapInventory placement=.ok (generatedHeapEntries placement) ∧
    writeback state placement placement .initial (generatedHeapEntries placement)
      (encodeMixedHeap placement (generatedHeapEntries placement) residual)=some (.ok (),state) :=
  generated_roundtrip state.2.heap.ty state placement placement .initial actual_MemOK heap_profile residual

theorem generated_ids : (generatedHeapEntries placement).map MixedHeapEntry.id=[0,1] := rfl

theorem generated_coverage_unique : CoversMixedHeap (generatedHeapEntries placement) ∧
    ((generatedHeapEntries placement).map MixedHeapEntry.id).Nodup := by
  first | (simp only;done) | decide | omega | rfl | skip
  obtain ⟨_,coverage,unique⟩ := prepareHeapInventory_ok placement _ generated_whole_state.1
  exact ⟨coverage,unique⟩

def generatedAliasRead (alias : Source.Idx [FixedMemory.Controls.ty,FixedMemory.Controls.ty] FixedMemory.Controls.ty) :=
  (writeback state placement placement .initial (generatedHeapEntries placement)
    (encodeMixedHeap placement (generatedHeapEntries placement) residual)).map fun after=>
      ((do let loc ← Source.indexLoc NominalMemory.Controls.readFrame (after.2.1.get alias) 0
           Source.readLoc NominalMemory.Controls.readFrame loc) :
        Source.EM FixedMemory.Controls.env _ (Source.Val FixedMemory.Controls.env.layout (.fixed FixedMemory.Controls.f))).run after.2

theorem generated_both_alias_reads :
    generatedAliasRead .here=some (.ok (FixedMemory.Controls.values 0),state) ∧
    generatedAliasRead (.there .here)=some (.ok (FixedMemory.Controls.values 0),state) := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold generatedAliasRead
  rw [generated_whole_state.2]
  exact ⟨rfl,rfl⟩
theorem missing_byte_inventory : ¬ CoversMixedHeap [Controls.nominal] := by
  first | (simp only;done) | decide | omega | rfl | skip
  intro covers
  obtain ⟨entry,member,id⟩ := covers 1 (by rfl)
  have same := List.mem_singleton.mp member
  subst entry
  exact (by decide : (0:Nat)≠1) id

theorem no_duplicate_generated_ids : (generatedHeapEntries placement).map MixedHeapEntry.id≠[0,0] := by
  decide
end Solidity.Yul.Views.FixedInventory.GeneratedControls
