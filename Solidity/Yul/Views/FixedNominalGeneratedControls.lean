import Solidity.Yul.Views.FixedNominalInventoryPreparation
import Solidity.Yul.Views.FixedNominalInventoryControls

/-! Actual owner preparation computes the fixed-underlying nominal inventory,
its images, coverage and unique IDs. Whole Source identity and fresh aliases
follow real writeback; no caller-supplied complete inventory is assumed. -/
namespace Solidity.Yul.Views.FixedNominalInventory.GeneratedControls
open Solidity.Yul.Views
open Solidity.Yul.Views.FixedNominalMemory.Controls

theorem actual_MemOK : Source.MemOK env heap.ty state := by
  refine ⟨⟨⟨?_,Solidity.Source.HeapTy.Le.refl _⟩,?_⟩,?_,?_⟩
  · apply Solidity.Source.HeapOK.alloc Solidity.Source.HeapOK.empty
    exact .array (fun i => .val (by trivial))
  · exact ⟨⟨Solidity.Yul.Views.FixedNominalMemory.Controls.ty,rfl,rfl⟩,⟨⟨Solidity.Yul.Views.FixedNominalMemory.Controls.ty,rfl,rfl⟩,trivial⟩⟩
  · apply Solidity.Source.HeapShaped.alloc Solidity.Source.HeapShaped.empty
    trivial
  · apply Solidity.Source.HeapInner.alloc (fun a x found => by cases found)
    exact fun i => ⟨Solidity.Yul.Views.FixedNominalMemory.Controls.values i,rfl⟩


theorem heap_profile (a : Nat) (τ : Source.STy) (d : Source.Data env.layout τ)
    (found : heap.get a=some ⟨τ,d⟩) : TypeSupported env τ := by
  first | solve | simp only
        | have present : (heap.get a).isSome := by rw [found]; rfl
          have bound := ComputedPlacement.occupied_lt heap a present
          change a<1 at bound
          have zero : a=0 := by omega
          subst a
          change (some ⟨ty,data⟩ : Option (Σ t,Source.Data env.layout t))=some ⟨τ,d⟩ at found
          cases found
          exact ⟨rfl,trivial⟩

theorem generated_roundtrip (residual : ByteView) :
    prepareHeapInventory placement=.ok (generatedHeapEntries placement) ∧
    writeback state placement placement .initial (generatedHeapEntries placement)
      (encodeMixedHeap placement (generatedHeapEntries placement) residual)=some (.ok (),state) := by
  first | solve | simp only
        | exact FixedNominalInventory.generated_roundtrip heap.ty state placement placement .initial
            actual_MemOK heap_profile residual

theorem generated_ids : (generatedHeapEntries placement).map MixedHeapEntry.id=[0] := rfl

theorem generated_coverage_unique : CoversMixedHeap (generatedHeapEntries placement) ∧
    ((generatedHeapEntries placement).map MixedHeapEntry.id).Nodup := by
  first | solve | simp only
        | obtain ⟨_,coverage,distinct⟩ := prepareHeapInventory_ok placement _ (generated_roundtrip (fun _=>165)).1
          exact ⟨coverage,distinct⟩

def afterRead (residual : ByteView) (alias : Source.Idx [ty,ty] ty) :=
  (writeback state placement placement .initial (generatedHeapEntries placement)
    (encodeMixedHeap placement (generatedHeapEntries placement) residual)).map fun after=>
      ((do let loc ← Source.indexLoc NominalMemory.Controls.readFrame (after.2.1.get alias) 0
           Source.readLoc NominalMemory.Controls.readFrame loc) :
        Source.EM env [ty,ty] (Source.Val env.layout (.udvt name))).run after.2

theorem both_aliases (residual : ByteView) :
    afterRead residual .here=some (.ok (values 0),state) ∧
    afterRead residual (.there .here)=some (.ok (values 0),state) := by
  first | solve | simp only [afterRead]
        | unfold afterRead
          rw [(generated_roundtrip residual).2]
          exact ⟨rfl,rfl⟩

theorem not_duplicate : (generatedHeapEntries placement).map MixedHeapEntry.id≠[0,0] := by
  decide

end Solidity.Yul.Views.FixedNominalInventory.GeneratedControls
