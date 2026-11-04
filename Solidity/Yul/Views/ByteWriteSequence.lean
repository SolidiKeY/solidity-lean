import Solidity.Yul.Views.RetainedByteHeader

/-! Finite byte-write plans execute the real Source operation at every step.
The physical companion patches only on that Source success; errors retain the
exact prefix. This is an adapter over actual runs, not a second interpreter. -/
namespace Solidity.Yul.Views.ByteWriteSequence

def action {E Γ} (F : Source.Fr) (horizon root : Nat) (request : Nat × UInt8) : Source.EM E Γ Unit :=
  Source.writeLoc F horizon (.memByte root request.1)
    (Source.Val.fixedBytes (n:=1) (h:=by decide) [request.2] rfl)

def program {E Γ} (F : Source.Fr) (horizon root : Nat) : List (Nat × UInt8) → Source.EM E Γ Unit
  | [] => pure ()
  | request::rest => do action F horizon root request;program F horizon root rest

/-- Source result/state is authoritative; a failed action does not patch raw
memory and does not run later actions. -/
def coupled {E Γ} (F : Source.Fr) (horizon root base : Nat) :
    List (Nat × UInt8) → Source.EMState E Γ → ByteView → (Source.R Unit × Source.EMState E Γ) × ByteView
  | [], s, memory => ((.ok (),s),memory)
  | request::rest, s, memory =>
    let result := (action F horizon root request).run s
    match result.1 with
    | .error _ => (result,memory)
    | .ok _ => coupled F horizon root base rest result.2 (saveByte memory (base+32+request.1) request.2)

theorem source {E Γ} (F : Source.Fr) (horizon root base : Nat) (requests : List (Nat × UInt8))
    (s : Source.EMState E Γ) (memory : ByteView) :
    (coupled F horizon root base requests s memory).1=(program F horizon root requests).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  induction requests generalizing s memory with
  | nil => rfl
  | cons request rest ih =>
    rw [program,Source.Hoare.run_bind]
    rcases run : (action F horizon root request).run s with ⟨result,after⟩
    cases result with
    | error reason => simp only [coupled,run]
    | ok value =>
      cases value
      simp only [coupled,run]
      exact ih after _

theorem bounds {E Γ} (s : Source.EMState E Γ) (F : Source.Fr) (horizon root : Nat)
    (string : Bool) (bytes : List UInt8)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bytes⟩)
    (request : Nat × UInt8) (outside : ¬request.1<bytes.length) :
    (action F horizon root request).run s=(.error (.revert (Source.panicData .index)),s) := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold action
  cases string <;> rw [Source.writeLoc,Source.Hoare.run_bind,heapObj_known s root _ found]
  all_goals
    dsimp only [heapByteType,heapByteData]
    rw [if_neg outside]
    rfl

/-- Every finite plan, including late out-of-bounds writes, has a complete
physical view of its exact reached Source store and original allocation history.
No successful-plan predicate or assumed final view is required. -/
theorem sound {E Γ} {origin : Source.Heap E.layout} (H : Source.HeapTy) (allocated : Placement origin)
    (F : Source.Fr) (horizon root : Nat) (requests : List (Nat × UInt8))
    (s : Source.EMState E Γ) (p : Placement s.2.heap) (prior : RetainedAllocation allocated p)
    (string : Bool) (bytes : List UInt8)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string bytes⟩)
    (ok : Source.MemOK E H s)
    (supported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (memory : ByteView) (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free) :
    let result := coupled F horizon root (p.address root) requests s memory
    result.1=(program F horizon root requests).run s ∧
    ∃ q : Placement result.1.2.2.heap,
      Source.MemOK E H result.1.2 ∧ q.address=p.address ∧ q.free=p.free ∧
      encodeMixedHeap q (generatedHeapEntries q) result.2=result.2 ∧
      ∃ history : RetainedAllocation allocated q,
        enumeratedMemoryWriteback result.1.2 allocated q history result.2=.ok (some (.ok (),result.1.2)) ∧
        ReservedOK result.2 q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  refine ⟨source F horizon root (p.address root) requests s memory,?_⟩
  induction requests generalizing s p bytes memory with
  | nil =>
    have ready := ownerMemOK_prepares_inventory H s p ok supported
    have full := encodeMixedHeap_unchanged p _ memory oldReads
    have wb := enumeratedMemory_unchanged s allocated p prior memory supported _ ready
    rw [full] at wb
    exact ⟨p,ok,rfl,rfl,full,prior,wb,reserved⟩
  | cons request rest ih =>
    by_cases inside : request.1<bytes.length
    · let data := heapByteData E.layout string (bytes.set request.1 request.2)
      let ht := heap_ty_of_get s.2.heap root _ _ found
      let after := withSourceHeap s (s.2.heap.write root data ht)
      let q := ByteElementStore.placement s.2.heap p root string bytes found ⟨request.1,inside⟩ request.2
      let raw := saveByte memory (p.address root+32+request.1) request.2
      obtain ⟨run,safe,full,lineage,wb,reservedAfter⟩ := ByteElementStore.whole H s allocated p prior ok supported F horizon root
        string bytes found ⟨request.1,inside⟩ request.2 memory oldReads reserved
      have sourceRun : (action F horizon root request).run s=(.ok (),after) := run
      have nextFound : after.2.heap.get root=some ⟨_,data⟩ := Source.Heap.write_get s.2.heap root _ ht
      have supportAfter := heapWrite_inventory_supported s.2.heap root data ht supported
      have ready := ownerMemOK_prepares_inventory H after q safe supportAfter
      have nextReads := encodeMixedHeap_reads q _ (prepareHeapInventory_ok q _ ready).2.2 raw
      rw [full] at nextReads
      have next := ih after q lineage (bytes.set request.1 request.2) nextFound safe supportAfter raw nextReads reservedAfter
      rw [coupled,sourceRun]
      exact next
    · have run := bounds s F horizon root string bytes found request inside
      rw [coupled,run]
      have ready := ownerMemOK_prepares_inventory H s p ok supported
      have full := encodeMixedHeap_unchanged p _ memory oldReads
      have wb := enumeratedMemory_unchanged s allocated p prior memory supported _ ready
      rw [full] at wb
      exact ⟨p,ok,rfl,rfl,full,prior,wb,reserved⟩
end Solidity.Yul.Views.ByteWriteSequence
