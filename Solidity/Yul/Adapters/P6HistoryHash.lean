import Solidity.Yul.Adapters.P6CopyHistory
import Solidity.Yul.Views.SnapshotHashBinding
import Solidity.Backend.Environment.Crypto

/-! Actual hashes of reached P6 copy histories. Raw hashing also observes frames
whose canonical preparation failed; only completed synchronization supports the
Source-byte relation. Concrete Fixed agreement is same-input and explicit. -/
namespace Solidity.Yul.Adapters.P6HistoryHash
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6CopyHistory
variable {C : Contract} {Δ : Ctx}

/-- Actual KECCAK256 observes the live complete frame, without cleaning or
consulting the Source heap. No successful preparation premise is needed. -/
theorem live_hash (μ : FrameMem C Δ) (span : ByteSpan μ.capacity) (tail : List Environment.Word) :
    Environment.cryptoStep (.op .KECCAK256)
      ⟨span.offset::span.length::tail,frameBytes μ⟩=
      some ⟨Environment.digest (snapshot μ span)::tail,frameBytes μ⟩ := by
  rw [frame_snapshot_read]
  rfl

/-- Source and actual target hash the same payload after a completed history.
Inventory/byte agreement follows the concrete history, not an input final-view
law. Query facts describe actual poststate references and the selected span. -/
theorem completed_hash {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (allocated : Placement origin) (capacity : Nat) (s : Source.EMState E Γ)
    (c : SnapshotCursor allocated s) (μ : FrameMem C Δ) (bound : μ.capacity=capacity)
    (requests : List (SpanPair capacity))
    (initial : encodeMixedHeap c.placement c.entries (frameBytes μ)=frameBytes μ)
    (coverage : CoversMixedHeap c.entries) (distinct : (c.entries.map MixedHeapEntry.id).Nodup)
    (complete : (run allocated capacity s c μ bound requests).pending=[]) :
    let out := run allocated capacity s c μ bound requests
    ∀ (index : Source.Idx Γ (.bytes .memory)) (a : Nat) (bs : Roadmap.Bytes),
      out.current.1.1.get index=Source.Val.memRef rfl a →
      out.current.1.2.heap.get a=some ⟨.bytes .memory,Source.Data.bytes bs⟩ →
      ∀ (span : ByteSpan out.frame.capacity) (tail : List Environment.Word),
      span.offset.val.toNat=out.current.2.placement.address a+32 →
      span.length.val.toNat=bs.length →
      G.fixed.evm.keccak bs=Roadmap.Evm.keccakWord bs →
      let value:=Source.mkBytes (D:=E.layout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash bs))
      (Source.evalE G F (n+4) (sourceMemoryHashExpr index)).run out.current.1=
        (.ok (.val value),out.current.1) ∧
      Environment.cryptoStep (.op .KECCAK256)
        ⟨span.offset::span.length::tail,frameBytes out.frame⟩=
        some ⟨Environment.digest bs::tail,frameBytes out.frame⟩ ∧
      value.word=some (G.fixed.hash bs) ∧
      (Environment.digest bs).val.toNat=(G.fixed.hash bs).val := by
  dsimp only
  intro index a bs localValue found span tail offset length fixed
  have raw := run_reencode allocated capacity s c μ bound requests initial complete
  have stable := run_preserves allocated capacity s c μ bound requests
  have covers := stable.2.2 coverage
  have nodup : ((run allocated capacity s c μ bound requests).current.2.entries.map MixedHeapEntry.id).Nodup := by
    rw [stable.2.1]
    exact distinct
  have payload : Environment.readMemory (frameBytes (run allocated capacity s c μ bound requests).frame)
      span.offset.val.toNat span.length.val.toNat=bs := by
    change readBytes _ _ _=bs
    rw [offset,length,←raw]
    exact heapEntriesBytes _ _ covers nodup _ a bs found
  refine ⟨sourceMemoryHashExpr_run G F n _ index a bs localValue found,?_,hashWord_observe E.layout _,?_⟩
  · have target := live_hash (run allocated capacity s c μ bound requests).frame span tail
    rw [frame_snapshot_read,payload] at target
    exact target
  · rw [Environment.digest_fixed]
    exact fixed.symm

end Solidity.Yul.Adapters.P6HistoryHash
