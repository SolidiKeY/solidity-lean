import Solidity.Yul.Views.RetainedAllocationRegions

namespace Solidity.Yul.Views

/-- ACTUAL owner programs, including returned reference and COMPLETE state.
A genuine old typed target is necessary; missing/new targets do not commute. -/
theorem heapPut_allocRef_commute {E Γ} (s : Source.EMState E Γ) (a : Nat) {τ}
    (d : Source.Data E.layout τ) (typed : s.2.heap.ty a=some τ)
    (string : Bool) (bs : List UInt8) :
    ((do Source.heapPut a ⟨τ,d⟩; Source.allocRef (heapByteData E.layout string bs)) :
      Source.EM E Γ (Source.Val E.layout (heapByteType string))).run s=
    ((do let v ← Source.allocRef (heapByteData E.layout string bs); Source.heapPut a ⟨τ,d⟩; pure v) :
      Source.EM E Γ (Source.Val E.layout (heapByteType string))).run s := by
  rw [Source.Hoare.run_bind,heapPutConcrete_run s a d typed]
  simp only []
  rw [byteAllocRef_run,Source.Hoare.run_bind,byteAllocRef_run]
  simp only []
  rw [Source.Hoare.run_bind,heapPutConcrete_run _ a d (heap_alloc_old_type s.2.heap ⟨_,heapByteData E.layout string bs⟩ a τ typed)]
  change (Except.ok (Source.Val.memRef (heapByteType_memory string) s.2.heap.next),
    withSourceHeap s ((s.2.heap.write a d typed).alloc ⟨_,heapByteData E.layout string bs⟩).1)=
    (Except.ok (Source.Val.memRef (heapByteType_memory string) s.2.heap.next),
      withSourceHeap s ((s.2.heap.alloc ⟨_,heapByteData E.layout string bs⟩).1.write a d _))
  rw [heap_write_alloc]

/-- Whole raw-map commutation for an old header/word and the actual fresh
allocation encoder (including FMP). Its physical-window premises are real. -/
theorem byteAllocation_mstore_commute (bs : List UInt8) (base : Nat) (free : Roadmap.Word)
    (fits : base+(MemoryShape.bytes bs.length).size≤free.val) (m : ByteView)
    (wordBase : Nat) (w : Roadmap.Word) (start : 128≤wordBase) (before : wordBase+32≤base) :
    byteAllocationView bs base free fits (mstore m wordBase w)=
      mstore (byteAllocationView bs base free fits m) wordBase w := by
  funext i
  unfold byteAllocationView bytesObjectView copyBytes mstore
  by_cases old : wordBase≤i ∧ i<wordBase+32
  · have notHeader : ¬(base≤i ∧ i<base+32) := by omega
    have notPayload : ¬(base+32≤i ∧ i<base+32+bs.length) := by omega
    have notFree : ¬(64≤i ∧ i<64+32) := by omega
    simp only [if_neg notPayload,dif_neg notHeader,dif_neg notFree,dif_pos old]
  · simp only [dif_neg old]

end Solidity.Yul.Views
