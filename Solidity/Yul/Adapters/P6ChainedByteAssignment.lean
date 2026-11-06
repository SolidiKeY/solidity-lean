import Solidity.Yul.Adapters.P6ByteAssignment

/-! A concrete effectful RHS: nested existing Source byte assignments. The inner
write precedes outer location formation, and an outer bounds panic retains that
successful prefix. No arbitrary-expression profile or new evaluator is added. -/
namespace Solidity.Yul.Adapters.P6ChainedByteAssignment
open Solidity.Yul.Views Solidity.Backend Solidity.Backend.MemoryOps
open Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage

def expression {E : Source.Env} {Γ : Source.RCtx}
    (root : Source.Idx Γ (.bytes .memory)) (inner outer : Source.Idx Γ (.int .u256))
    (rhs : Source.Idx Γ (.fixedBytes 1 (by decide))) : Source.RExpr E Γ (.fixedBytes 1 (by decide)) :=
  .assign (P6ByteReferenceReads.byteLocation root outer) (P6ByteAssignment.expression root inner rhs)

abbrev after {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (a : Nat) (string : Bool) (old : Roadmap.Bytes)
    (found : s.2.heap.get a=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (i : Nat) (b : UInt8) :=
  withSourceHeap s (s.2.heap.write a (heapByteData E.layout string (old.set i b))
    (heap_ty_of_get s.2.heap a _ _ found))

theorem after_found {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (a : Nat) (string : Bool) (old : Roadmap.Bytes)
    (found : s.2.heap.get a=some ⟨heapByteType string,heapByteData E.layout string old⟩) (i : Nat) (b : UInt8) :
    (after s a string old found i b).2.heap.get a=some ⟨heapByteType string,heapByteData E.layout string (old.set i b)⟩ :=
  Source.Heap.write_get _ _ _ (heap_ty_of_get s.2.heap a _ _ found)

/-- Transport a real typed heap update with its dependent cell witness. -/
theorem after_congr {E : Source.Env} {Γ : Source.RCtx} (s t : Source.EMState E Γ)
    (a : Nat) (string : Bool) (old : Roadmap.Bytes)
    (hs : s.2.heap.get a=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (ht : t.2.heap.get a=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (i : Nat) (b : UInt8) (same : s=t) : after s a string old hs i b=after t a string old ht i b := by
  first | (simp only;done) | skip
  cases same
  rfl

/-- Exact two-write Source state, without a distinct-index or empty-state premise. -/
theorem run {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (root : Source.Idx Γ (.bytes .memory))
    (inner outer : Source.Idx Γ (.int .u256)) (rhs : Source.Idx Γ (.fixedBytes 1 (by decide)))
    (a : Nat) (i j : Roadmap.Word) (b : UInt8)
    (reference : s.1.get root=Source.Val.memRef rfl a)
    (innerIndex : s.1.get inner=uintValueOfWord E.layout i)
    (outerIndex : s.1.get outer=uintValueOfWord E.layout j)
    (value : s.1.get rhs=Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)
    (string : Bool) (old : Roadmap.Bytes)
    (found : s.2.heap.get a=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (inside : i.val<old.length) (outside : j.val<old.length) :
    (Source.evalE G F (n+4) (expression root inner outer rhs)).run s=
      (.ok (.val (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)),
        after (after s a string old found i.val b) a string (old.set i.val b)
          (after_found s a string old found i.val b) j.val b) := by
  first | (simp only;done) | skip
  have innerRun := P6ByteAssignment.run G F n s root inner rhs a i b reference innerIndex value string old found inside
  change (Source.evalE G F (n+3) (P6ByteAssignment.expression root inner rhs)).run s=
    (.ok (.val (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)),after s a string old found i.val b) at innerRun
  rw [expression,Source.evalE,Source.Hoare.run_bind,innerRun]
  dsimp only
  rw [Source.Hoare.run_bind,P6ByteReferenceReads.form_location G F (n+1)
    (after s a string old found i.val b) root outer a j reference outerIndex]
  have converted : (Source.getV (Source.RVal.val (Source.Val.fixedBytes (D:=E.layout) (n:=1) (h:=by decide) [b] rfl)) :
      Source.EM E Γ _).run (after s a string old found i.val b)=
      (.ok (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl),after s a string old found i.val b) := rfl
  dsimp only
  rw [Source.Hoare.run_bind,converted]
  dsimp only
  rw [Source.Hoare.run_bind,P6ByteReferenceReads.write_byte F (n+3)
    (after s a string old found i.val b) a string (old.set i.val b) (after_found s a string old found i.val b)
    j.val (by simpa only [List.length_set] using outside) b]
  rfl

/-- An outer bounds failure does NOT erase the already completed inner write. -/
theorem outer_error {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (root : Source.Idx Γ (.bytes .memory))
    (inner outer : Source.Idx Γ (.int .u256)) (rhs : Source.Idx Γ (.fixedBytes 1 (by decide)))
    (a : Nat) (i j : Roadmap.Word) (b : UInt8)
    (reference : s.1.get root=Source.Val.memRef rfl a)
    (innerIndex : s.1.get inner=uintValueOfWord E.layout i)
    (outerIndex : s.1.get outer=uintValueOfWord E.layout j)
    (value : s.1.get rhs=Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)
    (string : Bool) (old : Roadmap.Bytes)
    (found : s.2.heap.get a=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (inside : i.val<old.length) (out : old.length≤j.val) :
    (Source.evalE G F (n+4) (expression root inner outer rhs)).run s=
      (.error (.revert (Source.panicData .index)),after s a string old found i.val b) := by
  first | (simp only;done) | skip
  have innerRun := P6ByteAssignment.run G F n s root inner rhs a i b reference innerIndex value string old found inside
  change (Source.evalE G F (n+3) (P6ByteAssignment.expression root inner rhs)).run s=
    (.ok (.val (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)),after s a string old found i.val b) at innerRun
  rw [expression,Source.evalE,Source.Hoare.run_bind,innerRun]
  dsimp only
  rw [Source.Hoare.run_bind,P6ByteReferenceReads.form_location G F (n+1)
    (after s a string old found i.val b) root outer a j reference outerIndex]
  have converted : (Source.getV (Source.RVal.val (Source.Val.fixedBytes (D:=E.layout) (n:=1) (h:=by decide) [b] rfl)) :
      Source.EM E Γ _).run (after s a string old found i.val b)=
      (.ok (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl),after s a string old found i.val b) := rfl
  dsimp only
  rw [Source.Hoare.run_bind,converted]
  dsimp only
  rw [Source.Hoare.run_bind,P6ByteReferenceReads.write_outside F (n+3)
    (after s a string old found i.val b) a string (old.set i.val b) (after_found s a string old found i.val b)
    j.val (by simpa only [List.length_set] using out) b]

/-- Both physical writes use the actual sequential inventories; the nested
source result and complete maps are derived from those same states. -/
theorem inventory {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    {C : Contract} {Δ : Ctx} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (root : Source.Idx Γ (.bytes .memory))
    (inner outer : Source.Idx Γ (.int .u256)) (rhs : Source.Idx Γ (.fixedBytes 1 (by decide)))
    (a : Nat) (i j : Roadmap.Word) (b : UInt8)
    (reference : s.1.get root=Source.Val.memRef rfl a)
    (innerIndex : s.1.get inner=uintValueOfWord E.layout i)
    (outerIndex : s.1.get outer=uintValueOfWord E.layout j)
    (value : s.1.get rhs=Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)
    (allocated : Placement origin) (p : Placement s.2.heap) (history : RetainedAllocation allocated p)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (distinct : (es.map MixedHeapEntry.id).Nodup)
    (μ : FrameMem C Δ) (residual : ByteView) (initial : frameBytes μ=encodeMixedHeap p es residual)
    (string : Bool) (old : Roadmap.Bytes)
    (found : s.2.heap.get a=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (inside : i.val<old.length) (outside : j.val<old.length)
    (fits1 : p.address a+32+i.val+1≤μ.capacity) (fits2 : p.address a+32+j.val+1≤μ.capacity) :
    let firstFrame := P6ByteMemory.store8 μ (P6ByteReferenceWrite.payloadOffset p a string old found i.val inside)
      (P6ByteReferenceWrite.byteWord b) fits1
    ∃ r : InventoryRealization allocated,
    ∃ cell : r.heap.get a=some ⟨heapByteType string,heapByteData E.layout string (old.set i.val b)⟩,
    ∃ addresses : r.placement.address=p.address,
    let secondFrame := P6ByteMemory.store8 firstFrame
      (P6ByteReferenceWrite.payloadOffset r.placement a string (old.set i.val b) cell j.val
        (by simpa only [List.length_set] using outside)) (P6ByteReferenceWrite.byteWord b)
      (by change r.placement.address a+32+j.val+1≤firstFrame.capacity;rw [addresses];
          simpa only [P6ByteMemory.store8,P6ByteMemory.write_capacity] using fits2)
    ∃ next : InventoryRealization allocated,
      (Source.evalE G F (n+4) (expression root inner outer rhs)).run s=
        (.ok (.val (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)),withSourceHeap s next.heap) ∧
      encodeMixedHeap r.placement r.entries (frameBytes firstFrame)=frameBytes firstFrame ∧
      encodeMixedHeap next.placement next.entries (frameBytes secondFrame)=frameBytes secondFrame ∧
      CoversMixedHeap next.entries ∧ next.entries.map MixedHeapEntry.id=es.map MixedHeapEntry.id ∧
      (∀ H,Source.MemOK E H s → Source.MemOK E H (withSourceHeap s next.heap)) ∧
      (∀ q,q≠a → next.heap.get q=s.2.heap.get q) := by
  first | (simp only;done) | skip
  dsimp only
  let firstFrame := P6ByteMemory.store8 μ (P6ByteReferenceWrite.payloadOffset p a string old found i.val inside)
    (P6ByteReferenceWrite.byteWord b) fits1
  obtain ⟨r,run1,selected1,encoded1,covered1,ids1,other1,safe1,cell,types1,count1,addresses,free1⟩ :=
    P6ByteWriteInventory.write F (n+2) s allocated p history es coverage distinct μ residual initial a string old found i.val inside b fits1
  have distinct1 : (r.entries.map MixedHeapEntry.id).Nodup := by rw [ids1];exact distinct
  have capacity : firstFrame.capacity=μ.capacity := P6ByteMemory.write_capacity _ _ _ _
  have fitsNext : r.placement.address a+32+j.val+1≤firstFrame.capacity := by rw [addresses,capacity];exact fits2
  obtain ⟨next,run2,selected2,encoded2,covered2,ids2,other2,safe2,cell2,types2,count2,addresses2,free2⟩ :=
    P6ByteWriteInventory.write F (n+3) (withSourceHeap s r.heap) allocated r.placement r.history r.entries
      covered1 distinct1 firstFrame (frameBytes firstFrame) encoded1.symm a string (old.set i.val b) cell j.val
      (by simpa only [List.length_set] using outside) b fitsNext
  have direct1 := P6ByteReferenceReads.write_byte F (n+2) s a string old found i.val inside b
  have state1 := congrArg Prod.snd (direct1.symm.trans run1)
  dsimp only at state1
  have direct2 := P6ByteReferenceReads.write_byte F (n+3) (withSourceHeap s r.heap) a string
    (old.set i.val b) cell j.val (by simpa only [List.length_set] using outside) b
  have state2 := congrArg Prod.snd (direct2.symm.trans run2)
  dsimp only at state2
  have actual := run G F n s root inner outer rhs a i j b reference innerIndex outerIndex value string old found inside outside
  change after s a string old found i.val b=withSourceHeap s r.heap at state1
  have changed := after_congr (after s a string old found i.val b) (withSourceHeap s r.heap)
    a string (old.set i.val b) (after_found s a string old found i.val b) cell j.val b state1
  change after (withSourceHeap s r.heap) a string (old.set i.val b) cell j.val b=withSourceHeap s next.heap at state2
  rw [changed,state2] at actual
  refine ⟨r,cell,addresses,next,actual,encoded1,encoded2,covered2,ids2.trans ids1,?_,?_⟩
  · intro H ok
    exact safe2 H (safe1 H ok)
  · intro q different
    exact (other2 q different).trans (other1 q different)
end Solidity.Yul.Adapters.P6ChainedByteAssignment
