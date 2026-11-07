import Solidity.Yul.Views.MixedNominalInventoryPreparation
import Solidity.Yul.Views.MixedNominalInventoryControls

/-! Actual mixed-struct owner invariants compute the complete inventory.
Generated images/coverage/unique IDs drive full Source roundtrip and two fresh
alias field reads; no supplied complete inventory or desired output law. -/
namespace Solidity.Yul.Views.MixedNominalInventory.GeneratedControls
open Solidity.Yul.Views
open Solidity.Yul.Views.FixedNominalMember.StructControls

theorem actual_MemOK : Source.MemOK env heap.ty state := by
  refine ⟨⟨⟨?_,Source.HeapTy.Le.refl _⟩,?_⟩,?_,?_⟩
  · apply Source.HeapOK.alloc Source.HeapOK.empty
    exact .struct (.cons (.val trivial) (.cons (.val trivial) (.cons (.val trivial) .nil)))
  · exact ⟨⟨ty,rfl,rfl⟩,⟨⟨ty,rfl,rfl⟩,trivial⟩⟩
  · apply Source.HeapShaped.alloc Source.HeapShaped.empty
    trivial
  · apply Source.HeapInner.alloc (fun a x found=>by cases found)
    exact ⟨⟨_,rfl⟩,⟨⟨_,rfl⟩,⟨⟨_,rfl⟩,trivial⟩⟩⟩

theorem heap_profile (a : Nat) (τ : Source.STy) (d : Source.Data env.layout τ)
    (found : heap.get a=some ⟨τ,d⟩) : TypeSupported env τ := by
  first | solve | simp only
        | have present : (heap.get a).isSome := by rw [found]; rfl
          have bound := ComputedPlacement.occupied_lt heap a present
          change a<1 at bound
          have zero : a=0 := by omega
          subst a
          change (some ⟨ty,Source.Data.struct oldFields⟩ : Option (Σ t,Source.Data env.layout t))=some ⟨τ,d⟩ at found
          cases found
          exact profile

theorem generated_whole_state (residual : ByteView) :
    prepareHeapInventory placement=.ok (generatedHeapEntries placement) ∧
    writeback state placement placement .initial (generatedHeapEntries placement)
      (encodeMixedHeap placement (generatedHeapEntries placement) residual)=some (.ok (),state) := by
  first | solve | simp only
        | exact generated_roundtrip heap.ty state placement placement .initial actual_MemOK heap_profile residual

theorem generated_ids : (generatedHeapEntries placement).map MixedHeapEntry.id=[0] := rfl

def afterRead (residual : ByteView) (alias : Source.Idx [ty,ty] ty) :=
  (writeback state placement placement .initial (generatedHeapEntries placement)
    (encodeMixedHeap placement (generatedHeapEntries placement) residual)).map fun result=>
      match result.2.1.get alias with
      | .memRef _ root=>some ((Source.readLoc NominalMemory.Controls.readFrame (.mem root 0) :
          Source.EM env [ty,ty] (Source.Val env.layout (.fixed Solidity.Yul.Views.Controls.scaled16))).run result.2)
      | _=>none

theorem both_aliases (residual : ByteView) :
    afterRead residual .here=some (some (.ok (.fixed (-125) (by decide)),state)) ∧
    afterRead residual (.there .here)=some (some (.ok (.fixed (-125) (by decide)),state)) := by
  first | solve | simp only [afterRead]
        | unfold afterRead
          rw [(generated_whole_state residual).2]
          exact ⟨rfl,rfl⟩

theorem no_duplicate : (generatedHeapEntries placement).map MixedHeapEntry.id≠[0,0] := by decide

end Solidity.Yul.Views.MixedNominalInventory.GeneratedControls
