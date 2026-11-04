import Solidity.Yul.Views.BytePlanHash

/-! Source and physical keccak transport after actual multi-root writes through
bytes-typed aliases to byte or string objects. The reached contents come from
preserved typing and heap shape; the exact raw preimage comes from the complete
coupled map. No final content/view premise or new source state is introduced. -/
namespace Solidity.Yul.Views.BytePlanHashAlias
open MultiRootByteWrites BytePlanHash

theorem content_of_type (E : Source.Env) (heap : Source.Heap E.layout)
    (root : Nat) (string : Bool) (shaped : Source.HeapShaped (E:=E) heap)
    (typed : heap.ty root=some (heapByteType string)) :
    ∃ bytes,heap.get root=some ⟨heapByteType string,heapByteData E.layout string bytes⟩ := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases string with
  | false => exact bytes_of_type E heap root shaped typed
  | true =>
    change (heap.get root).map Sigma.fst=some (.string .memory) at typed
    obtain ⟨⟨τ,data⟩,found,same⟩ := Option.map_eq_some_iff.mp typed
    cases same
    cases data with
    | string bytes => exact ⟨bytes,found⟩
    | val value =>
      have shape := shaped root _ found
      change (some Source.DataLoc.memory : Option Source.DataLoc)=none at shape
      cases shape

theorem byte_lookup {E : Source.Env} {heap : Source.Heap E.layout} {root : Nat}
    {bytes : Roadmap.Bytes} (string : Bool)
    (found : heap.get root=some ⟨heapByteType string,heapByteData E.layout string bytes⟩) :
    heap.get root=some ⟨.string .memory,Source.Data.string bytes⟩ ∨
      heap.get root=some ⟨.bytes .memory,Source.Data.bytes bytes⟩ := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases string
  · exact Or.inr found
  · exact Or.inl found

/-- No final content or final view premise: actual type preservation and heap
shape produce the bytes; the constructed whole map supplies the exact preimage. -/
theorem transport {E Γ} {origin : Source.Heap E.layout} (G : Source.Glob E) (F : Source.Fr)
    (writeHorizon hashHorizon : Nat) (requests : List Request) (H : Source.HeapTy)
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (prior : RetainedAllocation allocated p) (ok : Source.MemOK E H s)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (memory : ByteView) (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free)
    (index : Source.Idx Γ (.bytes .memory)) (root : Nat) (string : Bool) (old : Roadmap.Bytes)
    (localValue : s.1.get index=Source.Val.memRef rfl root)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string old⟩) :
    let result := coupled F writeHorizon p.address requests s memory
    match result.1.1 with
    | .error reason => (BytePlanHash.program G F writeHorizon hashHorizon requests index).run s=(.error reason,result.1.2)
    | .ok _ => ∃ bytes,
        result.1.2.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bytes⟩ ∧
        let value := Source.mkBytes (D:=E.layout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash bytes))
        (BytePlanHash.program G F writeHorizon hashHorizon requests index).run s=(.ok (.val value),result.1.2) ∧
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
    unfold BytePlanHash.program
    rw [Source.Hoare.run_bind,run]
  | ok resultUnit =>
    have rootType : heap.ty root=some (heapByteType string) := by
      rw [types]
      exact heap_ty_of_get s.2.heap root _ _ found
    obtain ⟨bytes,lookup⟩ := content_of_type E heap root string safe.2.1 rootType
    refine ⟨bytes,lookup,?_,?_⟩
    · unfold BytePlanHash.program
      rw [Source.Hoare.run_bind,run]
      have actualHash := sourceKeccakMemory_alias_run G F hashHorizon
        (withSourceHeap s heap) index root bytes localValue (byte_lookup string lookup)
      exact actualHash
    · have ready := ownerMemOK_prepares_inventory H (withSourceHeap s heap) q safe support
      have facts := prepareHeapInventory_ok q _ ready
      have allReads := encodeMixedHeap_reads q _ facts.2.2 result.2
      rw [full] at allReads
      have bound := heapByte_length_bound heap q root string bytes lookup
      let image : MemoryImage q (heapByteData E.layout string bytes) := by
        cases string
        · exact .bytes bytes bound
        · exact .string bytes bound
      have selected := mixedImage_reads_of_coverage q _ facts.2.1 result.2 allReads
        (⟨root,_,_,lookup,image⟩ : MixedHeapEntry q)
      have payload : readBytes result.2 (q.address root+32) bytes.length=bytes := by
        cases string <;> exact selected.2
      rw [addresses] at payload
      exact (hashWord_observe E.layout (G.fixed.hash bytes)).trans
        (congrArg some (fixedHash_physical G.fixed result.2 (p.address root+32) bytes.length bytes payload).symm)
end Solidity.Yul.Views.BytePlanHashAlias
