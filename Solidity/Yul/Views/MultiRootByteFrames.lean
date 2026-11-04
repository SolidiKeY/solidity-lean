import Solidity.Yul.Views.MultiRootByteWrites

/-! Multi-root byte plans change only the actual source heap, keeping its type
map and every administrative field. Actual local substitution restores caller
locals on success/halt; complete physical writeback applies to that caller store. -/
namespace Solidity.Yul.Views.MultiRootByteFrames
open MultiRootByteWrites

theorem action_store {E Γ} (s : Source.EMState E Γ) (F : Source.Fr) (horizon : Nat) (request : Request)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ) :
    ∃ result heap,(action F horizon request).run s=(result,withSourceHeap s heap) ∧ heap.ty=s.2.heap.ty ∧
      ∀ a τ d,heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ := by
  first | (simp only;done) | decide | omega | rfl | skip
  rcases classify s F horizon request supported with ⟨string,bytes,found⟩ | ⟨reason,failure⟩
  · by_cases inside : request.2.1<bytes.length
    · let data := heapByteData E.layout string (bytes.set request.2.1 request.2.2)
      let ht := heap_ty_of_get s.2.heap request.1 _ _ found
      refine ⟨.ok (),s.2.heap.write request.1 data ht,?_,?_,?_⟩
      · exact ByteElementStore.source_run s F horizon request.1 string bytes found ⟨request.2.1,inside⟩ request.2.2
      · exact funext (fun a => Source.Heap.write_ty s.2.heap request.1 a data ht)
      · exact heapWrite_inventory_supported s.2.heap request.1 data ht supported
    · refine ⟨.error (.revert (Source.panicData .index)),s.2.heap,?_,rfl,supported⟩
      rw [withSourceHeap_unchanged]
      exact ByteWriteSequence.bounds s F horizon request.1 string bytes found request.2 inside
  · refine ⟨.error reason,s.2.heap,?_,rfl,supported⟩
    rw [withSourceHeap_unchanged]
    exact failure

theorem program_store {E Γ} (F : Source.Fr) (horizon : Nat) (requests : List Request) (s : Source.EMState E Γ)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ) :
    ∃ result heap,(program F horizon requests).run s=(result,withSourceHeap s heap) ∧ heap.ty=s.2.heap.ty ∧
      ∀ a τ d,heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ := by
  first | (simp only;done) | decide | omega | rfl | skip
  induction requests generalizing s with
  | nil => exact ⟨.ok (),s.2.heap,by rw [withSourceHeap_unchanged];rfl,rfl,supported⟩
  | cons request rest ih =>
    obtain ⟨result,heap,run,types,support⟩ := action_store s F horizon request supported
    rw [program,Source.Hoare.run_bind,run]
    cases result with
    | error reason => exact ⟨.error reason,heap,rfl,types,support⟩
    | ok value =>
      obtain ⟨result,next,executed,nextTypes,nextSupport⟩ := ih (withSourceHeap s heap) support
      refine ⟨result,next,?_,nextTypes.trans types,nextSupport⟩
      exact executed

theorem sub_store {E Γ Δ} (F : Source.Fr) (horizon : Nat) (requests : List Request)
    (s : Source.EMState E Γ) (child : Source.Locals E.layout Δ)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ) :
    ∃ (result : Source.R Unit) (heap : Source.Heap E.layout),
      (Source.EM.sub child (program F horizon requests)).run s=
        (result.map (fun value => (value,child)),withSourceHeap s heap) ∧ heap.ty=s.2.heap.ty := by
  first | (simp only;done) | decide | omega | rfl | skip
  obtain ⟨result,heap,run,types,_⟩ := program_store F horizon requests (⟨child,s.2⟩ : Source.EMState E Δ) supported
  refine ⟨result,heap,?_,types⟩
  simp only [ExceptT.run] at run
  unfold Source.EM.sub
  simp only [ExceptT.run,ExceptT.mk,run]
  cases result <;> rfl

/-- Source local substitution and the physical companion share the same actual
callee run. Caller aliases are arbitrary valid locals, and halt retains its
real heap prefix; whole caller Source writeback preserves all administration. -/
theorem sub_physical {E Γ Δ} {origin : Source.Heap E.layout} (H : Source.HeapTy) (allocated : Placement origin)
    (F : Source.Fr) (horizon : Nat) (requests : List Request)
    (s : Source.EMState E Γ) (child : Source.Locals E.layout Δ)
    (childOK : Source.LocalsOK E s.2.heap.ty child)
    (p : Placement s.2.heap) (prior : RetainedAllocation allocated p) (ok : Source.MemOK E H s)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (memory : ByteView) (oldReads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free) :
    let result := coupled F horizon p.address requests (⟨child,s.2⟩ : Source.EMState E Δ) memory
    let caller : Source.EMState E Γ := (s.1,result.1.2.2)
    (Source.EM.sub child (program F horizon requests)).run s=
      (result.1.1.map (fun value => (value,child)),caller) ∧
    (∃ heap,caller=withSourceHeap s heap ∧ heap.ty=s.2.heap.ty) ∧ Source.MemOK E H caller ∧
    ∃ q : Placement caller.2.heap,
      q.address=p.address ∧ q.free=p.free ∧ encodeMixedHeap q (generatedHeapEntries q) result.2=result.2 ∧
      ∃ history : RetainedAllocation allocated q,
        enumeratedMemoryWriteback caller allocated q history result.2=.ok (some (.ok (),caller)) ∧ ReservedOK result.2 q.free := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  let initial : Source.EMState E Δ := (child,s.2)
  let result := coupled F horizon p.address requests initial memory
  have childSafe : Source.MemOK E H initial := ⟨⟨ok.1.1,childOK⟩,ok.2⟩
  obtain ⟨outcome,heap,run,types,support⟩ := program_store F horizon requests initial supported
  have actual : result.1=(outcome,withSourceHeap initial heap) := (source F horizon p.address requests initial memory).trans run
  have physical := sound H allocated F horizon requests initial p prior childSafe supported memory oldReads reserved
  change result.1=_ ∧ _ at physical
  rw [actual] at physical
  obtain ⟨q,safe,addresses,free,full,history,wb,reservedAfter⟩ := physical.2
  let caller := withSourceHeap s heap
  have callerSafe : Source.MemOK E H caller := by
    refine ⟨⟨safe.1.1,?_⟩,safe.2⟩
    change Source.LocalsOK E heap.ty s.1
    rw [types]
    exact ok.1.2
  have prepared := ownerMemOK_prepares_inventory H caller q callerSafe support
  have callerWriteback := enumeratedMemory_unchanged caller allocated q history result.2 support _ prepared
  rw [full] at callerWriteback
  have substituted : (Source.EM.sub child (program F horizon requests)).run s=
      (outcome.map (fun value => (value,child)),caller) := by
    have evaluated := run
    dsimp only [initial] at evaluated
    simp only [ExceptT.run] at evaluated
    unfold Source.EM.sub
    simp only [ExceptT.run,ExceptT.mk,evaluated]
    cases outcome <;> rfl
  change (Source.EM.sub child (program F horizon requests)).run s=(result.1.1.map _,(s.1,result.1.2.2)) ∧ _
  rw [actual]
  exact ⟨substituted,⟨heap,rfl,types⟩,callerSafe,q,addresses,free,full,history,callerWriteback,reservedAfter⟩
end Solidity.Yul.Views.MultiRootByteFrames
