import Solidity.Yul.Adapters.P6ByteWriteInventory
import Solidity.Source.Horizon

/-! Actual local-context transport for represented memory-byte writes. Source
substitution restores caller locals on success and halt, while passing the
reached store. This is not call instrumentation or transaction/frame rollback.
No child-local safety follows without that context's own typing premises. -/
namespace Solidity.Yul.Adapters.P6ByteWriteSub
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6ByteReferenceWrite

/-- Exact success projection through the existing Source substitution. -/
theorem success {E : Source.Env} {Γ Γ' : Source.RCtx} (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (locals : Source.Locals E.layout Γ')
    (root : Nat) (string : Bool) (old : Roadmap.Bytes)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (i : Nat) (inside : i<old.length) (b : UInt8) :
    (Source.EM.sub locals (Source.writeLoc F n (.memByte root i)
      (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl))).run s=
      (.ok ((),locals),withSourceHeap s (s.2.heap.write root
        (heapByteData E.layout string (old.set i b)) (heap_ty_of_get s.2.heap root _ _ found))) := by
  first | (simp only;done) | skip
  rcases s with ⟨caller,store⟩
  rw [Source.run_sub,P6ByteReferenceReads.write_byte F n (locals,store) root string old found i inside b]
  rfl

/-- A later real Source halt retains the successful write and caller prefix.
There is intentionally no physical or logical rollback asserted here. -/
theorem late_halt {E : Source.Env} {Γ Γ' : Source.RCtx} (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (locals : Source.Locals E.layout Γ')
    (root : Nat) (string : Bool) (old : Roadmap.Bytes)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (i : Nat) (inside : i<old.length) (b : UInt8) (halt : Source.Halt) :
    (Source.EM.sub locals ((Source.writeLoc F n (.memByte root i)
      (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)) >>= fun _ =>
        (Source.EM.halt halt : Source.EM E Γ' Unit))).run s=
      (.error halt,withSourceHeap s (s.2.heap.write root
        (heapByteData E.layout string (old.set i b)) (heap_ty_of_get s.2.heap root _ _ found))) := by
  first | (simp only;done) | skip
  rcases s with ⟨caller,store⟩
  rw [Source.run_sub,Source.Hoare.run_bind,
    P6ByteReferenceReads.write_byte F n (locals,store) root string old found i inside b]
  rfl

/-- An immediate out-of-bounds SOURCE write restores the complete original
Source state. No independently performed physical write is erased by this law. -/
theorem outside {E : Source.Env} {Γ Γ' : Source.RCtx} (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (locals : Source.Locals E.layout Γ')
    (root : Nat) (string : Bool) (old : Roadmap.Bytes)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (i : Nat) (out : old.length≤i) (b : UInt8) :
    (Source.EM.sub locals (Source.writeLoc F n (.memByte root i)
      (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl))).run s=
      (.error (.revert (Source.panicData .index)),s) := by
  first | (simp only;done) | skip
  rcases s with ⟨caller,store⟩
  rw [Source.run_sub,P6ByteReferenceReads.write_outside F n (locals,store) root string old found i out b]

/-- One realized heap simultaneously describes successful child completion,
late halt, restored caller locals and complete physical reconstruction. -/
theorem inventory {E : Source.Env} {Γ Γ' : Source.RCtx} {origin : Source.Heap E.layout}
    {C : Contract} {Δ : Ctx} (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (locals : Source.Locals E.layout Γ')
    (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (distinct : (es.map MixedHeapEntry.id).Nodup)
    (μ : FrameMem C Δ) (residual : ByteView) (initial : frameBytes μ=encodeMixedHeap p es residual)
    (root : Nat) (string : Bool) (old : Roadmap.Bytes)
    (found : s.2.heap.get root=some ⟨heapByteType string,heapByteData E.layout string old⟩)
    (i : Nat) (inside : i<old.length) (b : UInt8) (fits : p.address root+32+i+1≤μ.capacity) :
    let reached := P6ByteMemory.store8 μ (payloadOffset p root string old found i inside) (byteWord b) fits
    ∃ r : InventoryRealization allocated,
      (Source.EM.sub locals (Source.writeLoc F n (.memByte root i)
        (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl))).run s=
        (.ok ((),locals),withSourceHeap s r.heap) ∧
      (∀ halt : Source.Halt,
        (Source.EM.sub locals ((Source.writeLoc F n (.memByte root i)
          (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)) >>= fun _ =>
            (Source.EM.halt halt : Source.EM E Γ' Unit))).run s=
          (.error halt,withSourceHeap s r.heap)) ∧
      encodeMixedHeap r.placement r.entries (frameBytes reached)=frameBytes reached ∧
      CoversMixedHeap r.entries ∧ r.entries.map MixedHeapEntry.id=es.map MixedHeapEntry.id ∧
      r.heap.get root=some ⟨heapByteType string,heapByteData E.layout string (old.set i b)⟩ ∧
      (∀ H,Source.MemOK E H s → Source.MemOK E H (withSourceHeap s r.heap)) ∧
      (∀ a,a≠root → r.heap.get a=s.2.heap.get a) := by
  first | (simp only;done) | skip
  dsimp only
  obtain ⟨r,run,selected,encoded,covered,ids,other,safe,cell,types,count,addresses,free⟩ :=
    P6ByteWriteInventory.write F n s allocated p history es coverage distinct μ residual initial root string old found i inside b fits
  have direct := P6ByteReferenceReads.write_byte F n s root string old found i inside b
  have state := congrArg Prod.snd (direct.symm.trans run)
  dsimp only at state
  refine ⟨r,?_,?_,encoded,covered,ids,cell,safe,other⟩
  · rw [←state];exact success F n s locals root string old found i inside b
  · intro halt
    rw [←state];exact late_halt F n s locals root string old found i inside b halt
end Solidity.Yul.Adapters.P6ByteWriteSub
