import Solidity.Yul.Views.MixedNominalInventoryHistory
import Solidity.Yul.Views.MixedNominalInventoryReplay

/-! Every reached fixed/nominal snapshot prefix has a replayable complete heap
view, even when preparation stops. Coverage, unique IDs and decoder support
follow from the initial inventory and actual preserved metadata; no output
support or inverse certificate is supplied. Allocation provenance remains open. -/
namespace Solidity.Yul.Views.MixedNominalInventory
open NominalInventory (SnapshotCursor)

/-- Arbitrary residual bytes are retained by encoding the reached view, whose
actual writeback is identity on the entire reached Source state. -/
theorem runSnapshots_replay {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (coverage : CoversMixedHeap c.entries) (distinct : (c.entries.map MixedHeapEntry.id).Nodup)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → TypeSupported E τ)
    (ms : List ByteView) (residual : ByteView) :
    let out := (runSnapshots allocated s c ms).current
    CoversMixedHeap out.2.entries ∧ (out.2.entries.map MixedHeapEntry.id).Nodup ∧
    writeback out.1 allocated out.2.placement out.2.history out.2.entries
      (encodeMixedHeap out.2.placement out.2.entries residual)=some (.ok (),out.1) := by
  first | solve | simp only
        | have preserved := runSnapshots_preserves allocated s c ms
          have covers := preserved.2.2.2.2.2.2 coverage
          have unique : ((runSnapshots allocated s c ms).current.2.entries.map MixedHeapEntry.id).Nodup := by
            rw [preserved.2.2.2.2.2.1]
            exact distinct
          have profile := profile_of_types s.2.heap (runSnapshots allocated s c ms).current.1.2.heap
            preserved.2.1 supported
          exact ⟨covers,unique,writeback_encoded _ allocated _ _ _ covers unique
            (fun e _=>profile e.id e.ty e.data e.found) residual⟩

end Solidity.Yul.Views.MixedNominalInventory
