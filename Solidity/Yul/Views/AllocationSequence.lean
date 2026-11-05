import Solidity.Yul.Views.AllocationRefresh

/-! Finite actual allocation producers with step-indexed owner validity and
computed geometric bounds. This proof-only relation is not Source admission:
uncertified inputs still have the actual Source outcomes. No final image,
inverse, writeback or source-run law is a certificate field. Runtime recursion
is only over the existing list, with results retaining their intrinsic types. -/
namespace Solidity.Yul.Views.AllocationSequence

abbrev Request (E : Source.Env) := Σ τ,Source.Data E.layout τ

def program {E Γ} : (requests : List (Request E)) →
    Source.EM E Γ (Source.Vals E.layout (requests.map Sigma.fst))
  | [] => pure .nil
  | ⟨τ,data⟩::rest => do
    let value ← Source.allocRef data
    let values ← program rest
    pure (.cons value values)

inductive Certified {E Γ} : (s : Source.EMState E Γ) → (p : Placement s.2.heap) →
    ComputedPlacement.prepare s.2.heap=.ok p → List (Request E) → Prop where
  | nil (s : Source.EMState E Γ) (p : Placement s.2.heap)
      (done : ComputedPlacement.prepare s.2.heap=.ok p) : Certified s p done []
  | cons {s : Source.EMState E Γ} {p : Placement s.2.heap}
      {done : ComputedPlacement.prepare s.2.heap=.ok p} {τ : Source.STy}
      (data : Source.Data E.layout τ) (shape : MemoryShape)
      (found : ComputedPlacement.objectShape data=some shape)
      (bound : p.free.val+max 1 shape.size<2^256)
      (inner : Source.Data.Inner (E:=E) data) (valid : Source.DataOK E s.2.heap.ty data)
      (supported : InventoryTypeSupported E τ) {rest : List (Request E)}
      (tail : Certified (objectAllocatedState s data)
        (AllocationRefresh.placement s.2.heap p done data shape found bound)
        (AllocationRefresh.prepared s.2.heap p done data shape found bound) rest) :
      Certified s p done (⟨τ,data⟩::rest)

/-- Arbitrary finite supported sequences derive every subsequent old read from
the preceding actual encoding, preserving typed results and complete Source
state. Reserved words are transported from the initial input, not assumed anew. -/
theorem realize {E Γ s p done requests} (trace : @Certified E Γ s p done requests)
    (H : Source.HeapTy) (ok : Source.MemOK E H s) (memory : ByteView)
    (supported : ∀ a τ d,s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (reads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free) :
    ∃ (after : Source.EMState E Γ) (values : Source.Vals E.layout (requests.map Sigma.fst))
      (q : Placement after.2.heap) (raw : ByteView),
      (program requests).run s=(.ok values,after) ∧
      ComputedPlacement.prepare after.2.heap=.ok q ∧ Source.MemOK E H after ∧
      encodeMixedHeap q (generatedHeapEntries q) raw=raw ∧
      enumeratedMemoryWriteback after q q (retainInitial _ _) raw=.ok (some (.ok (),after)) ∧
      ReservedOK raw q.free ∧ Source.RValsOK E after.2.heap.ty values.toR := by
  first | (simp only;done) | decide | omega | rfl | skip
  induction trace generalizing H memory with
  | nil initial placement ready =>
    have inventory := ownerMemOK_prepares_inventory H initial placement ok supported
    have whole := encodeMixedHeap_unchanged placement (generatedHeapEntries placement) memory reads
    have writeback := enumeratedMemory_unchanged initial placement placement (retainInitial _ _) memory supported _ inventory
    rw [whole] at writeback
    exact ⟨initial,.nil,placement,memory,rfl,ready,ok,whole,writeback,reserved,trivial⟩
  | @cons initial placement ready τ data shape found bound inner valid newSupported rest tail ih =>
    have inventory := ownerMemOK_prepares_inventory H initial placement ok supported
    obtain ⟨raw,step⟩ := Option.isSome_iff_exists.mp
      (ComputedAllocationWrite.complete initial.2.heap placement ready data shape found bound memory newSupported inner valid)
    have allocation := objectAllocRef_MemOK H initial data (ComputedPlacement.objectShape_memory data shape found)
      (ComputedPlacement.objectShape_top data shape found) inner valid ok
    have safe := allocation.1
    have nextSupported := heapAlloc_inventory_supported initial.2.heap data newSupported supported
    have nextReads : ∀ e∈generatedHeapEntries (AllocationRefresh.placement initial.2.heap placement ready data shape found bound),
        e.image.Reads raw ((AllocationRefresh.placement initial.2.heap placement ready data shape found bound).address e.id) := by
      intro e _
      exact AllocationRefresh.reads initial.2.heap placement ready data shape found bound _ inventory memory raw reads step e
    have nextReserved := ComputedAllocationWrite.reserved initial.2.heap placement ready data shape found bound memory raw step reserved
    rw [←AllocationRefresh.free initial.2.heap placement ready data shape found bound] at nextReserved
    obtain ⟨after,values,q,finalRaw,actual,computed,finalSafe,whole,writeback,finalReserved,returnedSafe⟩ :=
      ih (objectAllocatedState initial data).2.heap.ty safe.self raw nextSupported nextReads nextReserved
    refine ⟨after,.cons (.memRef (ComputedPlacement.objectShape_memory data shape found) initial.2.heap.next) values,
      q,finalRaw,?_,computed,finalSafe.weaken safe.le,whole,writeback,finalReserved,?_⟩
    · rw [program,Source.Hoare.run_bind,objectAllocRef_run initial data (ComputedPlacement.objectShape_memory data shape found)]
      dsimp only
      rw [Source.Hoare.run_bind,actual]
      rfl
    · exact ⟨Source.Val.RefOK.mono finalSafe.le allocation.2,returnedSafe⟩
end Solidity.Yul.Views.AllocationSequence
