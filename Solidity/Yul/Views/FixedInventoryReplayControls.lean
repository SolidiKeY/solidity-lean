import Solidity.Yul.Views.FixedInventoryReplay
import Solidity.Yul.Views.FixedInventoryRealizationControls

/-! The actual changed scaled-array write constructs an inhabited replay state.
Replay retains both source aliases and rejects the original stale observation;
it does not assert allocation provenance or universal decoder support. -/
namespace Solidity.Yul.Views.FixedInventory.ReplayControls
open Solidity.Yul.Views
open Solidity.Yul.Views.FixedInventory.RealizationControls

theorem heap_profile (a : Nat) (τ : Source.STy) (d : Source.Data FixedMemory.Controls.env.layout τ)
    (found : FixedMemory.Controls.heap.get a=some ⟨τ,d⟩) : TypeSupported FixedMemory.Controls.env τ := by
  first | solve | simp only [TypeSupported]
        | solve | rfl
        | have present : (FixedMemory.Controls.heap.get a).isSome := by rw [found]; rfl
          have bound := ComputedPlacement.occupied_lt FixedMemory.Controls.heap a present
          change a<1 at bound
          have zero : a=0 := by omega
          subst a
          change (some ⟨FixedMemory.Controls.ty,FixedMemory.Controls.data⟩ :
            Option (Σ t,Source.Data FixedMemory.Controls.env.layout t))=some ⟨τ,d⟩ at found
          cases found
          trivial

theorem changed_replay : ∃ r : InventoryRealization FixedMemory.Controls.placement,
    withSourceHeap FixedMemory.Controls.state r.heap=expectedState ∧
    writeback (withSourceHeap FixedMemory.Controls.state r.heap) FixedMemory.Controls.placement
      r.placement r.history r.entries FixedMemory.Controls.changedRaw =
      some (.ok (),expectedState) ∧
    Source.MemOK FixedMemory.Controls.env FixedMemory.Controls.heap.ty
      (withSourceHeap FixedMemory.Controls.state r.heap) := by
  first | solve | simp only
        | solve | rfl
        | obtain ⟨r,run,_,_,_,safe,replay⟩ := writeback_replay FixedMemory.Controls.state
            FixedMemory.Controls.placement FixedMemory.Controls.placement .initial [entry]
            coverage (by decide) heap_profile FixedMemory.Controls.changedRaw _ changed_source
          have same := (congrArg Prod.snd run).symm
          exact ⟨r,same,replay.trans (congrArg (fun s => some ((.ok () : Except Source.Halt Unit),s)) same),safe _ FixedMemory.Controls.actual_MemOK⟩

def freshRead (s : Source.EMState FixedMemory.Controls.env [FixedMemory.Controls.ty,FixedMemory.Controls.ty])
    (alias : Source.Idx [FixedMemory.Controls.ty,FixedMemory.Controls.ty] FixedMemory.Controls.ty) :=
  ((do let loc ← Source.indexLoc NominalMemory.Controls.readFrame (s.1.get alias) 0
       Source.readLoc NominalMemory.Controls.readFrame loc) :
    Source.EM FixedMemory.Controls.env _ (Source.Val FixedMemory.Controls.env.layout (.fixed FixedMemory.Controls.f))).run s

theorem replay_aliases : ∃ r : InventoryRealization FixedMemory.Controls.placement,
    writeback (withSourceHeap FixedMemory.Controls.state r.heap) FixedMemory.Controls.placement
      r.placement r.history r.entries FixedMemory.Controls.changedRaw=some (.ok (),expectedState) ∧
    freshRead (withSourceHeap FixedMemory.Controls.state r.heap) .here=
      (.ok (FixedMemory.Controls.changedValues 0),expectedState) ∧
    freshRead (withSourceHeap FixedMemory.Controls.state r.heap) (.there .here)=
      (.ok (FixedMemory.Controls.changedValues 0),expectedState) := by
  first | solve | simp only
        | solve | rfl
        | obtain ⟨r,same,replay,_⟩ := changed_replay
          refine ⟨r,replay,?_,?_⟩ <;> rw [same] <;> rfl

theorem replay_state_not_original : expectedState≠FixedMemory.Controls.state := by
  first | solve | decide
        | intro same
          have observed := congrArg (fun s =>
            match (freshRead s .here).1 with | .ok (.fixed n _) => n | _ => 0) same
          exact (by decide : (-32768 : Int) ≠ -125) observed

end Solidity.Yul.Views.FixedInventory.ReplayControls
