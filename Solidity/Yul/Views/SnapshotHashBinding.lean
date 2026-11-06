import Solidity.Yul.Views.SourceHashBinding
import Solidity.Yul.Views.InventoryView

/-! Actual Source keccak after changed physical-snapshot writeback. The hash
input is the supplied raw payload, excluding its header/padding. Resulting
bytes and the view relation are derived from actual decoding and realization;
no hash injectivity, final agreement oracle or new source state is introduced. -/
namespace Solidity.Yul.Views

theorem heapEntriesBytes {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es)
    (distinct : (es.map MixedHeapEntry.id).Nodup) (m : ByteView) (a : Nat) (bs : Roadmap.Bytes)
    (found : h.get a=some ⟨.bytes .memory,Source.Data.bytes bs⟩) :
    readBytes (encodeMixedHeap p es m) (p.address a+32) bs.length=bs := by
  apply List.ext_getElem
  · simp only [readBytes,List.length_map,List.length_range]
  · intro i hi hj
    have byte := encodeMixedHeap_source_byte p es distinct coverage m a (.bytes .memory) (.bytes bs)
      found (32+i) bs[i] (ObjectByte.bytes bs ⟨i,hj⟩)
    simpa only [readBytes,List.getElem_map,List.getElem_range,Nat.add_assoc] using byte

/-- Successful complete changed writeback constructs the SAME raw bytes read
by the actual Source expression at every positive supported horizon. Caller
locals are the real unchanged locals; every original-H invariant is retained. -/
theorem sourceMemoryHash_snapshot {E : Source.Env} {Γ : Source.RCtx}
    {origin : Source.Heap E.layout} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (distinct : (es.map MixedHeapEntry.id).Nodup)
    (m : ByteView) (result : Except Source.Halt Unit × Source.EMState E Γ)
    (step : inventoryStateWriteback s allocated p history es m=some result) :
    ∃ realized : InventoryRealization allocated,
      result=(.ok (),withSourceHeap s realized.heap) ∧
      (∀ H : Source.HeapTy,Source.MemOK E H s → Source.MemOK E H (withSourceHeap s realized.heap)) ∧
      (∀ (index : Source.Idx Γ (.bytes .memory)) (a : Nat) (bs : Roadmap.Bytes),
        s.1.get index=Source.Val.memRef rfl a →
        realized.heap.get a=some ⟨.bytes .memory,Source.Data.bytes bs⟩ →
        let after:=withSourceHeap s realized.heap
        let value:=Source.mkBytes (D:=E.layout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash bs))
        (Source.evalE G F (n+4) (sourceMemoryHashExpr index)).run after=(.ok (.val value),after) ∧
        value.word=some (keccak256 G.fixed.evm m (realized.placement.address a+32) bs.length)) := by
  obtain ⟨realized,run,covers,nodup,raw⟩ := inventoryStateWriteback_view s allocated p history es coverage distinct m result step
  refine ⟨realized,run,?_,?_⟩
  · intro H ok
    have safe := inventoryStateWriteback_MemOK H s allocated p history es m result step ok
    rw [run] at safe
    exact safe
  · intro index a bs localValue found
    have payload : readBytes m (realized.placement.address a+32) bs.length=bs := by
      rw [← raw]
      exact heapEntriesBytes realized.placement realized.entries covers nodup m a bs found
    have hash := fixedHash_physical G.fixed m (realized.placement.address a+32) bs.length bs payload
    exact ⟨sourceMemoryHashExpr_run G F n (withSourceHeap s realized.heap) index a bs localValue found,
      (hashWord_observe E.layout (G.fixed.hash bs)).trans (congrArg some hash.symm)⟩
end Solidity.Yul.Views
