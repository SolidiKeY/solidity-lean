import Solidity.Yul.Views.BytePlanHashAlias

/-! Actual callee byte writes followed by a source hash return their result
through EM.sub. Caller locals and the complete physical map/writeback use the
same reached callee store, on both success and halt. This is local substitution,
not an invented heap rollback or instrumentation of arbitrary internal calls. -/
namespace Solidity.Yul.Views.BytePlanHashFrames
open MultiRootByteWrites

/-- Arbitrary valid caller and child locals share one actual heap. No empty
locals or absence-of-alias premise is required, and no final view is supplied. -/
theorem transport {E Γ Δ} {origin : Source.Heap E.layout}
    (G : Source.Glob E) (F : Source.Fr) (writeHorizon hashHorizon : Nat)
    (requests : List Request) (H : Source.HeapTy) (s : Source.EMState E Γ)
    (child : Source.Locals E.layout Δ) (childOK : Source.LocalsOK E s.2.heap.ty child)
    (allocated : Placement origin) (p : Placement s.2.heap)
    (prior : RetainedAllocation allocated p) (ok : Source.MemOK E H s)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (memory : ByteView) (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free)
    (index : Source.Idx Δ (.bytes .memory)) (root : Nat) (string : Bool) (old : Roadmap.Bytes)
    (localValue : child.get index=Source.Val.memRef rfl root)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string old⟩) :
    let result := coupled F writeHorizon p.address requests (⟨child,s.2⟩ : Source.EMState E Δ) memory
    let caller : Source.EMState E Γ := (s.1,result.1.2.2)
    ((∃ heap,caller=withSourceHeap s heap ∧ heap.ty=s.2.heap.ty) ∧ Source.MemOK E H caller ∧
      ∃ q : Placement caller.2.heap,
        q.address=p.address ∧ q.free=p.free ∧ encodeMixedHeap q (generatedHeapEntries q) result.2=result.2 ∧
        ∃ history : RetainedAllocation allocated q,
          enumeratedMemoryWriteback caller allocated q history result.2=.ok (some (.ok (),caller)) ∧
          ReservedOK result.2 q.free) ∧
    match result.1.1 with
    | .error reason =>
      (Source.EM.sub child (BytePlanHash.program G F writeHorizon hashHorizon requests index)).run s=
        (.error reason,caller)
    | .ok _ => ∃ bytes,
      caller.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bytes⟩ ∧
      let value := Source.mkBytes (D:=E.layout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash bytes))
      (Source.EM.sub child (BytePlanHash.program G F writeHorizon hashHorizon requests index)).run s=
        (.ok (.val value,child),caller) ∧
      value.word=some (keccak256 G.fixed.evm result.2 (p.address root+32) bytes.length) := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  let initial : Source.EMState E Δ := (child,s.2)
  let result := coupled F writeHorizon p.address requests initial memory
  have childSafe : Source.MemOK E H initial := ⟨⟨ok.1.1,childOK⟩,ok.2⟩
  have physical := MultiRootByteFrames.sub_physical H allocated F writeHorizon requests s child childOK
    p prior ok supported memory oldReads reserved
  refine ⟨physical.2,?_⟩
  have hashed := BytePlanHashAlias.transport G F writeHorizon hashHorizon requests H initial allocated p prior
    childSafe supported memory oldReads reserved index root string old localValue found
  obtain ⟨outcome,heap,run,types,support⟩ := MultiRootByteFrames.program_store F writeHorizon requests initial supported
  have actual : result.1=(outcome,withSourceHeap initial heap) :=
    (source F writeHorizon p.address requests initial memory).trans run
  change match result.1.1 with | .error _ => _ | .ok _ => _
  change match result.1.1 with | .error _ => _ | .ok _ => _ at hashed
  rw [actual] at hashed ⊢
  cases outcome with
  | error reason =>
    have evaluated := hashed
    dsimp only [initial,withSourceHeap] at evaluated
    simp only [ExceptT.run] at evaluated
    unfold Source.EM.sub
    simp only [ExceptT.run,ExceptT.mk,evaluated]
    rfl
  | ok resultUnit =>
    obtain ⟨bytes,lookup,executed,word⟩ := hashed
    refine ⟨bytes,lookup,?_,word⟩
    have evaluated := executed
    dsimp only [initial,withSourceHeap] at evaluated
    simp only [ExceptT.run] at evaluated
    unfold Source.EM.sub
    simp only [ExceptT.run,ExceptT.mk,evaluated]
    rfl
end Solidity.Yul.Views.BytePlanHashFrames
