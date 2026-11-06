import Solidity.Yul.Adapters.P6HistoryHash
import Solidity.Source.Horizon

/-! Hash a known typed byte object through the owner's actual local-context
operation after completed physical synchronization. Caller locals are restored;
this is not callInternal instrumentation or reference-formation provenance. -/
namespace Solidity.Yul.Adapters.P6HistoryHashRef
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6CopyHistory

def byteLocal (E : Source.Env) (a : Nat) : Source.Locals E.layout [.bytes .memory] :=
  .cons (.memRef rfl a) .nil

/-- Actual owner substitution/evaluation; no new evaluator or Source state. -/
def hashAt {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (n a : Nat) : Source.EM E Γ
      (Source.RVal E.layout Source.STy.bytes32 × Source.Locals E.layout [.bytes .memory]) :=
  Source.EM.sub (byteLocal E a) (Source.evalE G F (n+4) (sourceMemoryHashExpr .here))

/-- Hashing restores the caller's exact locals and passes its current store. -/
theorem hashAt_run {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (n : Nat) (s : Source.EMState E Γ) (a : Nat) (bs : Roadmap.Bytes)
    (found : s.2.heap.get a=some ⟨.bytes .memory,Source.Data.bytes bs⟩) :
    let value:=Source.mkBytes (D:=E.layout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash bs))
    (hashAt G F n a).run s=(.ok (.val value,byteLocal E a),s) := by
  rcases s with ⟨caller,store⟩
  have actual := sourceMemoryHashExpr_run G F n (byteLocal E a,store) .here a bs rfl found
  unfold hashAt
  rw [Source.run_sub,actual]

/-- The actual zero-horizon query halts before reading its reference. Owner
substitution restores the caller locals on this real error path as well. -/
theorem query_timeout {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (s : Source.EMState E Γ) (a : Nat) :
    (Source.EM.sub (byteLocal E a)
      (Source.evalE G F 0 (sourceMemoryHashExpr .here))).run s=(.error .timeout,s) := by
  rcases s with ⟨caller,store⟩
  rw [Source.run_sub]
  rfl

/-- Query an initially related current Source/frame view. Consumers derive
this input relation from actual preceding synchronization, not a final oracle. -/
theorem query_hash {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    {C : Contract} {Δ : Ctx} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (μ : FrameMem C Δ)
    (initial : encodeMixedHeap c.placement c.entries (frameBytes μ)=frameBytes μ)
    (coverage : CoversMixedHeap c.entries) (distinct : (c.entries.map MixedHeapEntry.id).Nodup)
    (a : Nat) (bs : Roadmap.Bytes)
    (found : s.2.heap.get a=some ⟨.bytes .memory,Source.Data.bytes bs⟩)
    (span : ByteSpan μ.capacity) (tail : List Environment.Word)
    (offset : span.offset.val.toNat=c.placement.address a+32) (length : span.length.val.toNat=bs.length)
    (fixed : G.fixed.evm.keccak bs=Roadmap.Evm.keccakWord bs) :
    let value:=Source.mkBytes (D:=E.layout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash bs))
    (hashAt G F n a).run s=(.ok (.val value,byteLocal E a),s) ∧
      Environment.cryptoStep (.op .KECCAK256) ⟨span.offset::span.length::tail,frameBytes μ⟩=
        some ⟨Environment.digest bs::tail,frameBytes μ⟩ ∧
      value.word=some (G.fixed.hash bs) ∧
      (Environment.digest bs).val.toNat=(G.fixed.hash bs).val := by
  have payload : Environment.readMemory (frameBytes μ) span.offset.val.toNat span.length.val.toNat=bs := by
    change readBytes _ _ _=bs
    rw [offset,length,←initial]
    exact heapEntriesBytes _ _ coverage distinct _ a bs found
  have target := P6HistoryHash.live_hash μ span tail
  rw [frame_snapshot_read,payload] at target
  refine ⟨hashAt_run G F n s a bs found,target,hashWord_observe E.layout _,?_⟩
  rw [Environment.digest_fixed]
  exact fixed.symm

/-- The byte-query context uses the view CONSTRUCTED by the completed history.
No final agreement or Source-run law is supplied as a producer premise. -/
theorem completed_hashAt {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    {C : Contract} {Δ : Ctx} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (allocated : Placement origin) (capacity : Nat) (s : Source.EMState E Γ)
    (c : SnapshotCursor allocated s) (μ : FrameMem C Δ) (bound : μ.capacity=capacity)
    (requests : List (SpanPair capacity))
    (initial : encodeMixedHeap c.placement c.entries (frameBytes μ)=frameBytes μ)
    (coverage : CoversMixedHeap c.entries) (distinct : (c.entries.map MixedHeapEntry.id).Nodup)
    (complete : (run allocated capacity s c μ bound requests).pending=[]) :
    let out := run allocated capacity s c μ bound requests
    ∀ (a : Nat) (bs : Roadmap.Bytes),
      out.current.1.2.heap.get a=some ⟨.bytes .memory,Source.Data.bytes bs⟩ →
      ∀ (span : ByteSpan out.frame.capacity) (tail : List Environment.Word),
      span.offset.val.toNat=out.current.2.placement.address a+32 →
      span.length.val.toNat=bs.length →
      G.fixed.evm.keccak bs=Roadmap.Evm.keccakWord bs →
      let value:=Source.mkBytes (D:=E.layout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash bs))
      (hashAt G F n a).run out.current.1=(.ok (.val value,byteLocal E a),out.current.1) ∧
      Environment.cryptoStep (.op .KECCAK256)
        ⟨span.offset::span.length::tail,frameBytes out.frame⟩=
        some ⟨Environment.digest bs::tail,frameBytes out.frame⟩ ∧
      value.word=some (G.fixed.hash bs) ∧
      (Environment.digest bs).val.toNat=(G.fixed.hash bs).val := by
  dsimp only
  intro a bs found span tail offset length fixed
  let out := run allocated capacity s c μ bound requests
  have raw := run_reencode allocated capacity s c μ bound requests initial complete
  have stable := run_preserves allocated capacity s c μ bound requests
  have nodup : (out.current.2.entries.map MixedHeapEntry.id).Nodup := by
    rw [stable.2.1]
    exact distinct
  exact query_hash G F n allocated out.current.1 out.current.2 out.frame raw
    (stable.2.2 coverage) nodup a bs found span tail offset length fixed

end Solidity.Yul.Adapters.P6HistoryHashRef
