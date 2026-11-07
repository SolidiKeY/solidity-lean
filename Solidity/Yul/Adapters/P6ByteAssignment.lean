import Solidity.Yul.Adapters.P6ByteWriteInventory

/-! Actual resolved Source assignment to a memory-byte lvalue. The RHS local is
evaluated before location formation; bounds are checked by the actual write.
This supported producer case is not arbitrary intermediate/call capture or
Source-to-Yul compiler adequacy. No source syntax or evaluator is duplicated. -/
namespace Solidity.Yul.Adapters.P6ByteAssignment
open Solidity.Yul.Views Solidity.Backend Solidity.Backend.MemoryOps
open Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage

def expression {E : Source.Env} {Γ : Source.RCtx}
    (root : Source.Idx Γ (.bytes .memory)) (index : Source.Idx Γ (.int .u256))
    (rhs : Source.Idx Γ (.fixedBytes 1 (by decide))) : Source.RExpr E Γ (.fixedBytes 1 (by decide)) :=
  .assign (P6ByteReferenceReads.byteLocation root index) (.local rhs)

/-- The existing evaluator returns the assigned value and exact Source update. -/
theorem run {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (root : Source.Idx Γ (.bytes .memory))
    (index : Source.Idx Γ (.int .u256)) (rhs : Source.Idx Γ (.fixedBytes 1 (by decide)))
    (a : Nat) (i : Roadmap.Word) (b : UInt8)
    (reference : s.1.get root=Source.Val.memRef rfl a)
    (indexed : s.1.get index=uintValueOfWord E.layout i)
    (value : s.1.get rhs=Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)
    (string : Bool) (old : Roadmap.Bytes)
    (found : s.2.heap.get a=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (inside : i.val<old.length) :
    (Source.evalE G F (n+3) (expression root index rhs)).run s=
      (.ok (.val (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)),
        withSourceHeap s (s.2.heap.write a (heapByteData E.layout string (old.set i.val b))
          (heap_ty_of_get s.2.heap a _ _ found))) := by
  first | (simp only;done) | skip
  rw [expression,Source.evalE,Source.Hoare.run_bind,source_local_value_run G F (n+1) s rhs _ value]
  dsimp only
  rw [Source.Hoare.run_bind,P6ByteReferenceReads.form_location G F n s root index a i reference indexed]
  have converted : (Source.getV (Source.RVal.val (Source.Val.fixedBytes (D:=E.layout) (n:=1) (h:=by decide) [b] rfl)) :
      Source.EM E Γ _).run s=(.ok (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl),s) := rfl
  dsimp only
  rw [Source.Hoare.run_bind,converted]
  dsimp only
  rw [Source.Hoare.run_bind,P6ByteReferenceReads.write_byte F (n+2) s a string old found i.val inside b]
  rfl

/-- Forming the location does not avoid the actual write's bounds panic. -/
theorem outside {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (root : Source.Idx Γ (.bytes .memory))
    (index : Source.Idx Γ (.int .u256)) (rhs : Source.Idx Γ (.fixedBytes 1 (by decide)))
    (a : Nat) (i : Roadmap.Word) (b : UInt8)
    (reference : s.1.get root=Source.Val.memRef rfl a)
    (indexed : s.1.get index=uintValueOfWord E.layout i)
    (value : s.1.get rhs=Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)
    (string : Bool) (old : Roadmap.Bytes)
    (found : s.2.heap.get a=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (out : old.length≤i.val) :
    (Source.evalE G F (n+3) (expression root index rhs)).run s=
      (.error (.revert (Source.panicData .index)),s) := by
  first | (simp only;done) | skip
  rw [expression,Source.evalE,Source.Hoare.run_bind,source_local_value_run G F (n+1) s rhs _ value]
  dsimp only
  rw [Source.Hoare.run_bind,P6ByteReferenceReads.form_location G F n s root index a i reference indexed]
  have converted : (Source.getV (Source.RVal.val (Source.Val.fixedBytes (D:=E.layout) (n:=1) (h:=by decide) [b] rfl)) :
      Source.EM E Γ _).run s=(.ok (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl),s) := rfl
  dsimp only
  rw [Source.Hoare.run_bind,converted]
  dsimp only
  rw [Source.Hoare.run_bind,P6ByteReferenceReads.write_outside F (n+2) s a string old found i.val out b]

/-- The RHS local itself times out at horizon zero; no location/write occurs. -/
theorem timeout_rhs {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (s : Source.EMState E Γ) (root : Source.Idx Γ (.bytes .memory))
    (index : Source.Idx Γ (.int .u256)) (rhs : Source.Idx Γ (.fixedBytes 1 (by decide))) :
    (Source.evalE G F 1 (expression root index rhs)).run s=(.error .timeout,s) := by
  first | rfl | simp only [expression,Source.evalE,Source.Hoare.run_bind]

/-- Actual assignment production, physical write and all refreshed images
share one constructed state; no final evaluator/view law is supplied. -/
theorem inventory {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    {C : Contract} {Δ : Ctx} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (root : Source.Idx Γ (.bytes .memory))
    (index : Source.Idx Γ (.int .u256)) (rhs : Source.Idx Γ (.fixedBytes 1 (by decide)))
    (a : Nat) (i : Roadmap.Word) (b : UInt8)
    (reference : s.1.get root=Source.Val.memRef rfl a)
    (indexed : s.1.get index=uintValueOfWord E.layout i)
    (value : s.1.get rhs=Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)
    (allocated : Placement origin) (p : Placement s.2.heap) (history : RetainedAllocation allocated p)
    (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (distinct : (es.map MixedHeapEntry.id).Nodup)
    (μ : FrameMem C Δ) (residual : ByteView) (initial : frameBytes μ=encodeMixedHeap p es residual)
    (string : Bool) (old : Roadmap.Bytes)
    (found : s.2.heap.get a=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (inside : i.val<old.length) (fits : p.address a+32+i.val+1≤μ.capacity) :
    let reached := P6ByteMemory.store8 μ (P6ByteReferenceWrite.payloadOffset p a string old found i.val inside)
      (P6ByteReferenceWrite.byteWord b) fits
    ∃ r : InventoryRealization allocated,
      (Source.evalE G F (n+3) (expression root index rhs)).run s=
        (.ok (.val (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)),withSourceHeap s r.heap) ∧
      encodeMixedHeap r.placement r.entries (frameBytes reached)=frameBytes reached ∧
      CoversMixedHeap r.entries ∧ r.entries.map MixedHeapEntry.id=es.map MixedHeapEntry.id ∧
      (∀ H,Source.MemOK E H s → Source.MemOK E H (withSourceHeap s r.heap)) ∧
      r.heap.get a=some ⟨heapByteType string,heapByteData E.layout string (old.set i.val b)⟩ := by
  first | (simp only;done) | skip
  dsimp only
  obtain ⟨r,write,selected,encoded,covered,ids,other,safe,cell,types,count,addresses,free⟩ :=
    P6ByteWriteInventory.write F (n+2) s allocated p history es coverage distinct μ residual initial a string old found i.val inside b fits
  have direct := P6ByteReferenceReads.write_byte F (n+2) s a string old found i.val inside b
  have state := congrArg Prod.snd (direct.symm.trans write)
  dsimp only at state
  refine ⟨r,?_,encoded,covered,ids,safe,cell⟩
  rw [←state]
  exact run G F n s root index rhs a i b reference indexed value string old found inside
end Solidity.Yul.Adapters.P6ByteAssignment
