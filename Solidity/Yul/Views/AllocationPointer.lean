import Solidity.Yul.Views.NewMemoryOperand

/-! Newly allocated Source references and their actual physical pointer codec.
Coverage comes from successful old/new image preparation, not a supplied inverse
law. Consuming the new expression through a pointer-field write preserves the
actual owner outcome, including errors; decoding failure is only preparation.
A target sink-word store and full changed-memory reconstruction are not proved. -/
namespace Solidity.Yul.Views.AllocationPointer

theorem decode {E Γ} (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (done : ComputedPlacement.prepare s.2.heap=.ok p) {τ : Source.STy}
    (data : Source.Data E.layout τ) (shape : MemoryShape)
    (found : ComputedPlacement.objectShape data=some shape)
    (bound : p.free.val+max 1 shape.size<2^256) (es : List (MixedHeapEntry p))
    (ready : prepareHeapInventory p=.ok es) (memory raw : ByteView)
    (step : ComputedAllocationWrite.prepare s.2.heap p done data shape found bound memory=some raw) :
    let q := ComputedAllocationWrite.placement s.2.heap p done data shape found bound
    decodeMemoryPointer q (generatedHeapEntries q) τ (ComputedPlacement.objectShape_memory data shape found) p.free=
      some (Source.Val.memRef (ComputedPlacement.objectShape_memory data shape found) s.2.heap.next) := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  let q := ComputedAllocationWrite.placement s.2.heap p done data shape found bound
  have computed := objectAllocationView_prepares s.2.heap p data (ComputedPlacement.objectShape_memory data shape found)
    shape (ComputedPlacement.objectShape_sound data shape found) p.free.val (ComputedAllocationWrite.nextFree p shape bound)
    (Nat.le_refl _) (ComputedAllocationWrite.computed_fresh s.2.heap p done)
    (by dsimp [ComputedAllocationWrite.nextFree];omega) es ready memory raw step
  have coverage := (prepareHeapInventory_ok q (generatedHeapEntries q) computed).2.1
  have owned : (objectAllocatedState s data).2.heap.ty s.2.heap.next=some τ :=
    heap_ty_of_get _ _ τ data (Source.Heap.alloc_get s.2.heap _)
  have same : ownedPointerWord q s.2.heap.next τ owned=p.free := by
    apply Fin.ext
    change (if s.2.heap.next=s.2.heap.next then p.free.val else p.address s.2.heap.next)=p.free.val
    rw [if_pos rfl]
  rw [←same]
  exact decodeMemoryPointer_encode q _ coverage τ _ s.2.heap.next τ owned rfl

def writeNew {E : Source.Env} {Γ : Source.RCtx} {τ σ : Source.STy} (G : Source.Glob E) (F : Source.Fr) (n writerHorizon : Nat)
    (newable : τ.newable=true) (length : Source.RExpr E Γ σ) (indexable : σ.isIndex=true)
    (root index : Nat) : Source.EM E Γ Unit := do
  let value ← Source.getV (← Source.evalE G F (n+1) (.newArray newable length indexable))
  Source.writeLoc F writerHorizon (.mem root index) value

theorem write_new {E : Source.Env} {Γ : Source.RCtx} {τ σ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n writerHorizon : Nat) (s reached : Source.EMState E Γ)
    (newable : τ.newable=true) (length : Source.RExpr E Γ σ) (indexable : σ.isIndex=true)
    (value : Source.RVal E.layout σ) (actual : (Source.evalE G F n length).run s=(.ok value,reached))
    (k : Nat) (amount : value.amount=.ok k) (small : k<2^64)
    (data : Source.Data E.layout τ) (newData : Source.newData τ k=.ok data)
    (shape : MemoryShape) (found : ComputedPlacement.objectShape data=some shape)
    (p : Placement reached.2.heap) (done : ComputedPlacement.prepare reached.2.heap=.ok p)
    (bound : p.free.val+max 1 shape.size<2^256) (es : List (MixedHeapEntry p))
    (ready : prepareHeapInventory p=.ok es) (memory raw : ByteView)
    (step : ComputedAllocationWrite.prepare reached.2.heap p done data shape found bound memory=some raw)
    (root index : Nat) :
    let after := objectAllocatedState reached data
    let q := ComputedAllocationWrite.placement reached.2.heap p done data shape found bound
    pointerStateWriteback after q (generatedHeapEntries q) F writerHorizon root index τ
      (ComputedPlacement.objectShape_memory data shape found) p.free=
      some ((writeNew G F n writerHorizon newable length indexable root index).run s) := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  unfold pointerStateWriteback
  rw [decode reached p done data shape found bound es ready memory raw step]
  simp only [Option.map_some]
  unfold writeNew
  rw [Source.Hoare.run_bind,
    NewMemoryOperand.run G F n s reached newable length indexable value actual k amount small data newData
      (ComputedPlacement.objectShape_memory data shape found)]
  rfl
theorem source {E : Source.Env} {Γ : Source.RCtx} {τ σ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n writerHorizon : Nat) (s reached : Source.EMState E Γ)
    (newable : τ.newable=true) (length : Source.RExpr E Γ σ) (indexable : σ.isIndex=true)
    (value : Source.RVal E.layout σ) (actual : (Source.evalE G F n length).run s=(.ok value,reached))
    (k : Nat) (amount : value.amount=.ok k) (small : k<2^64)
    (data : Source.Data E.layout τ) (newData : Source.newData τ k=.ok data)
    (memory : τ.loc?=some .memory) (root index : Nat) :
    (writeNew G F n writerHorizon newable length indexable root index).run s=
      (Source.writeLoc F writerHorizon (.mem root index) (Source.Val.memRef memory reached.2.heap.next)).run
        (objectAllocatedState reached data) := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold writeNew
  rw [Source.Hoare.run_bind,NewMemoryOperand.run G F n s reached newable length indexable value actual
    k amount small data newData memory]
  rfl

/-- Owner safety holds on both successful and halting pointer-field writes.
The actual reached operand state, not an unchanged initial state, is required. -/
theorem MemOK {E : Source.Env} {Γ : Source.RCtx} {τ σ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n writerHorizon : Nat) (s reached : Source.EMState E Γ)
    (newable : τ.newable=true) (length : Source.RExpr E Γ σ) (indexable : σ.isIndex=true)
    (value : Source.RVal E.layout σ) (actual : (Source.evalE G F n length).run s=(.ok value,reached))
    (k : Nat) (amount : value.amount=.ok k) (small : k<2^64)
    (data : Source.Data E.layout τ) (newData : Source.newData τ k=.ok data)
    (memory : τ.loc?=some .memory) (top : Source.Data.Top (E:=E) data)
    (inner : Source.Data.Inner (E:=E) data) (valid : Source.DataOK E reached.2.heap.ty data)
    (H : Source.HeapTy) (ok : Source.MemOK E H reached) (root index : Nat) :
    Source.MemOK E H ((writeNew G F n writerHorizon newable length indexable root index).run s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [source G F n writerHorizon s reached newable length indexable value actual k amount small data newData memory root index]
  have allocation := objectAllocRef_MemOK H reached data memory top inner valid ok
  have keep := Source.writeLoc_memOK (E:=E) (Γ:=Γ) (H:=H) F writerHorizon (.mem root index)
    (Source.Val.memRef memory reached.2.heap.next) (objectAllocatedState reached data) ⟨allocation.1,allocation.2⟩
  cases run : (Source.writeLoc F writerHorizon (.mem root index) (Source.Val.memRef memory reached.2.heap.next)).run
      (objectAllocatedState reached data) with
  | mk result after => cases result <;> simpa only [run] using keep
end Solidity.Yul.Views.AllocationPointer
