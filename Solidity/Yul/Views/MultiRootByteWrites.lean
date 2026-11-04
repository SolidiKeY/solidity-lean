import Solidity.Yul.Views.ByteWriteSequence

/-! Finite writes may select any actual heap root. Each operation delegates to
Source.writeLoc; heap lookup derives byte/string ownership or the exact owner
error. Missing/non-byte roots need no admission assumption or raw patch. -/
namespace Solidity.Yul.Views.MultiRootByteWrites

abbrev Request := Nat × Nat × UInt8

def action {E Γ} (F : Source.Fr) (horizon : Nat) (r : Request) : Source.EM E Γ Unit :=
  ByteWriteSequence.action F horizon r.1 r.2

def program {E Γ} (F : Source.Fr) (horizon : Nat) : List Request → Source.EM E Γ Unit
  | [] => pure ()
  | r::rest => do action F horizon r;program F horizon rest

def coupled {E Γ} (F : Source.Fr) (horizon : Nat) (addresses : Nat → Nat) :
    List Request → Source.EMState E Γ → ByteView → (Source.R Unit × Source.EMState E Γ) × ByteView
  | [], s, memory => ((.ok (),s),memory)
  | r::rest, s, memory =>
    let result := (action F horizon r).run s
    match result.1 with
    | .error _ => (result,memory)
    | .ok _ => coupled F horizon addresses rest result.2 (saveByte memory (addresses r.1+32+r.2.1) r.2.2)

theorem source {E Γ} (F : Source.Fr) (horizon : Nat) (addresses : Nat → Nat) (requests : List Request)
    (s : Source.EMState E Γ) (memory : ByteView) :
    (coupled F horizon addresses requests s memory).1=(program F horizon requests).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  induction requests generalizing s memory with
  | nil => rfl
  | cons r rest ih =>
    rw [program,Source.Hoare.run_bind]
    rcases run : (action F horizon r).run s with ⟨result,after⟩
    cases result with
    | error reason => simp only [coupled,run]
    | ok value => cases value;simp only [coupled,run];exact ih after _

theorem classify {E Γ} (s : Source.EMState E Γ) (F : Source.Fr) (horizon : Nat) (r : Request)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ) :
    (∃ string bytes,s.2.heap.get r.1=some ⟨heapByteType string,heapByteData E.layout string bytes⟩) ∨
    ∃ reason,(action F horizon r).run s=(.error reason,s) := by
  first | (simp only;done) | decide | omega | rfl | skip
  cases lookup : s.2.heap.get r.1 with
  | none =>
    right
    refine ⟨.stuck "dangling memory reference",?_⟩
    have missing : (Source.heapObj r.1 : Source.EM E Γ _).run s=(.error (.stuck "dangling memory reference"),s) := by
      have state : (Source.EM.st : Source.EM E Γ (Source.St E)).run s=(.ok s.2,s) := by cases s;rfl
      unfold Source.heapObj
      rw [Source.Hoare.run_bind,state]
      dsimp only
      rw [lookup]
      rfl
    unfold action ByteWriteSequence.action
    rw [Source.writeLoc,Source.Hoare.run_bind,missing]
  | some object =>
    rcases object with ⟨τ,data⟩
    cases data with
    | @bytes location bytes =>
      have profile := supported r.1 _ _ lookup
      cases location with
      | memory => exact Or.inl ⟨false,bytes,rfl⟩
      | storage => cases profile
      | calldata => cases profile
    | @string location bytes =>
      have profile := supported r.1 _ _ lookup
      cases location with
      | memory => exact Or.inl ⟨true,bytes,rfl⟩
      | storage => cases profile
      | calldata => cases profile
    | val value =>
      right;refine ⟨.stuck "not bytes",?_⟩
      unfold action ByteWriteSequence.action
      rw [Source.writeLoc,Source.Hoare.run_bind,heapObj_known s r.1 _ lookup]
      rfl
    | array n hl values =>
      right;refine ⟨.stuck "not bytes",?_⟩
      unfold action ByteWriteSequence.action
      rw [Source.writeLoc,Source.Hoare.run_bind,heapObj_known s r.1 _ lookup]
      rfl
    | struct fields =>
      right;refine ⟨.stuck "not bytes",?_⟩
      unfold action ByteWriteSequence.action
      rw [Source.writeLoc,Source.Hoare.run_bind,heapObj_known s r.1 _ lookup]
      rfl
    | mapping values =>
      right;refine ⟨.stuck "not bytes",?_⟩
      unfold action ByteWriteSequence.action
      rw [Source.writeLoc,Source.Hoare.run_bind,heapObj_known s r.1 _ lookup]
      rfl

/-- All finite multi-root plans preserve a complete physical view of the exact
reached Source prefix, including bounds, non-byte and dangling-root errors. -/
theorem sound {E Γ} {origin : Source.Heap E.layout} (H : Source.HeapTy) (allocated : Placement origin)
    (F : Source.Fr) (horizon : Nat) (requests : List Request)
    (s : Source.EMState E Γ) (p : Placement s.2.heap) (prior : RetainedAllocation allocated p)
    (ok : Source.MemOK E H s)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (memory : ByteView) (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free) :
    let result := coupled F horizon p.address requests s memory
    result.1=(program F horizon requests).run s ∧
    ∃ q : Placement result.1.2.2.heap,
      Source.MemOK E H result.1.2 ∧ q.address=p.address ∧ q.free=p.free ∧
      encodeMixedHeap q (generatedHeapEntries q) result.2=result.2 ∧
      ∃ history : RetainedAllocation allocated q,
        enumeratedMemoryWriteback result.1.2 allocated q history result.2=.ok (some (.ok (),result.1.2)) ∧ ReservedOK result.2 q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  refine ⟨source F horizon p.address requests s memory,?_⟩
  induction requests generalizing s p memory with
  | nil =>
    have ready := ownerMemOK_prepares_inventory H s p ok supported
    have full := encodeMixedHeap_unchanged p _ memory oldReads
    have wb := enumeratedMemory_unchanged s allocated p prior memory supported _ ready
    rw [full] at wb
    exact ⟨p,ok,rfl,rfl,full,prior,wb,reserved⟩
  | cons r rest ih =>
    rcases classify s F horizon r supported with ⟨string,bytes,found⟩ | ⟨reason,failure⟩
    · by_cases inside : r.2.1<bytes.length
      · let data := heapByteData E.layout string (bytes.set r.2.1 r.2.2)
        let ht := heap_ty_of_get s.2.heap r.1 _ _ found
        let after := withSourceHeap s (s.2.heap.write r.1 data ht)
        let q := ByteElementStore.placement s.2.heap p r.1 string bytes found ⟨r.2.1,inside⟩ r.2.2
        let raw := saveByte memory (p.address r.1+32+r.2.1) r.2.2
        obtain ⟨run,safe,full,lineage,wb,reservedAfter⟩ := ByteElementStore.whole H s allocated p prior ok supported F horizon r.1
          string bytes found ⟨r.2.1,inside⟩ r.2.2 memory oldReads reserved
        have sourceRun : (action F horizon r).run s=(.ok (),after) := run
        have supportAfter := heapWrite_inventory_supported s.2.heap r.1 data ht supported
        have ready := ownerMemOK_prepares_inventory H after q safe supportAfter
        have nextReads := encodeMixedHeap_reads q _ (prepareHeapInventory_ok q _ ready).2.2 raw
        rw [full] at nextReads
        have next := ih after q lineage safe supportAfter raw nextReads reservedAfter
        rw [coupled,sourceRun]
        exact next
      · have failure : (action F horizon r).run s=(.error (.revert (Source.panicData .index)),s) :=
          ByteWriteSequence.bounds s F horizon r.1 string bytes found r.2 inside
        rw [coupled,failure]
        have ready := ownerMemOK_prepares_inventory H s p ok supported
        have full := encodeMixedHeap_unchanged p _ memory oldReads
        have wb := enumeratedMemory_unchanged s allocated p prior memory supported _ ready
        rw [full] at wb
        exact ⟨p,ok,rfl,rfl,full,prior,wb,reserved⟩
    · rw [coupled,failure]
      have ready := ownerMemOK_prepares_inventory H s p ok supported
      have full := encodeMixedHeap_unchanged p _ memory oldReads
      have wb := enumeratedMemory_unchanged s allocated p prior memory supported _ ready
      rw [full] at wb
      exact ⟨p,ok,rfl,rfl,full,prior,wb,reserved⟩
end Solidity.Yul.Views.MultiRootByteWrites
