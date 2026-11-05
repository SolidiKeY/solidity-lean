import Solidity.Yul.Views.MultiRootByteFrames
import Solidity.Yul.Views.SnapshotHashBinding

/-! The actual keccak expression reads the same reached bytes as the physical
companion after a finite multi-root write plan. Final heap bytes and locals are
derived, and a source error prevents the hash from running. -/
namespace Solidity.Yul.Views.BytePlanHash
open MultiRootByteWrites

def program {E Γ} (G : Source.Glob E) (F : Source.Fr) (writeHorizon hashHorizon : Nat)
    (requests : List Request) (index : Source.Idx Γ (.bytes .memory)) : Source.EM E Γ (Source.RVal E.layout Source.STy.bytes32) := do
  MultiRootByteWrites.program F writeHorizon requests
  Source.evalE G F (hashHorizon+4) (sourceMemoryHashExpr index)

theorem bytes_of_type (E : Source.Env) (heap : Source.Heap E.layout) (root : Nat)
    (shaped : Source.HeapShaped (E:=E) heap) (typed : heap.ty root=some (.bytes .memory)) :
    ∃ bytes,heap.get root=some ⟨.bytes .memory,Source.Data.bytes bytes⟩ := by
  first | (simp only;done) | decide | omega | rfl | skip
  change (heap.get root).map Sigma.fst=some (.bytes .memory) at typed
  obtain ⟨⟨τ,data⟩,found,same⟩ := Option.map_eq_some_iff.mp typed
  cases same
  cases data with
  | bytes bytes => exact ⟨bytes,found⟩
  | val value =>
    have shape := shaped root _ found
    change (some Source.DataLoc.memory : Option Source.DataLoc)=none at shape
    cases shape

/-- No final content or final view premise: actual type preservation and heap
shape produce the bytes; the constructed whole map supplies the exact preimage. -/
theorem transport {E Γ} {origin : Source.Heap E.layout} (G : Source.Glob E) (F : Source.Fr)
    (writeHorizon hashHorizon : Nat) (requests : List Request) (H : Source.HeapTy)
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (prior : RetainedAllocation allocated p) (ok : Source.MemOK E H s)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (memory : ByteView) (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free)
    (index : Source.Idx Γ (.bytes .memory)) (root : Nat) (old : Roadmap.Bytes)
    (localValue : s.1.get index=Source.Val.memRef rfl root)
    (found : s.2.heap.get root=some ⟨.bytes .memory,Source.Data.bytes old⟩) :
    let result := coupled F writeHorizon p.address requests s memory
    match result.1.1 with
    | .error reason => (program G F writeHorizon hashHorizon requests index).run s=(.error reason,result.1.2)
    | .ok _ => ∃ bytes,
        result.1.2.2.heap.get root=some ⟨.bytes .memory,Source.Data.bytes bytes⟩ ∧
        let value := Source.mkBytes (D:=E.layout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash bytes))
        (program G F writeHorizon hashHorizon requests index).run s=(.ok (.val value),result.1.2) ∧
        value.word=some (keccak256 G.fixed.evm result.2 (p.address root+32) bytes.length) := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  let result := coupled F writeHorizon p.address requests s memory
  obtain ⟨outcome,heap,run,types,support⟩ := MultiRootByteFrames.program_store F writeHorizon requests s supported
  have actual : result.1=(outcome,withSourceHeap s heap) :=
    (MultiRootByteWrites.source F writeHorizon p.address requests s memory).trans run
  have physical := sound H allocated F writeHorizon requests s p prior ok supported memory oldReads reserved
  change result.1=_ ∧ _ at physical
  rw [actual] at physical
  obtain ⟨q,safe,addresses,free,full,history,writeback,reservedAfter⟩ := physical.2
  change match result.1.1 with | .error reason => _ | .ok _ => _
  rw [actual]
  cases outcome with
  | error reason =>
    unfold program
    rw [Source.Hoare.run_bind,run]
  | ok unit =>
    have rootType : heap.ty root=some (.bytes .memory) := by
      rw [types]
      exact heap_ty_of_get s.2.heap root _ _ found
    obtain ⟨bytes,lookup⟩ := bytes_of_type E heap root safe.2.1 rootType
    refine ⟨bytes,lookup,?_,?_⟩
    · unfold program
      rw [Source.Hoare.run_bind,run]
      exact sourceMemoryHashExpr_run G F hashHorizon (withSourceHeap s heap) index root bytes localValue lookup
    · have ready := ownerMemOK_prepares_inventory H (withSourceHeap s heap) q safe support
      have facts := prepareHeapInventory_ok q _ ready
      have payload := heapEntriesBytes q _ facts.2.1 facts.2.2 result.2 root bytes lookup
      rw [full,addresses] at payload
      exact (hashWord_observe E.layout (G.fixed.hash bytes)).trans
        (congrArg some (fixedHash_physical G.fixed result.2 (p.address root+32) bytes.length bytes payload).symm)
end Solidity.Yul.Views.BytePlanHash
