import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingResume

/-! Actual saved-parent payload and protected words across allocating descent.
The running-prefix premise is supplied by the checked source-coupled producer;
no saved history or memory-preservation certificate is assumed. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHistory
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

/-- The private allocation's published writes preserve every other positive
word below the owned heap frontier. -/
theorem allocation_word {b frame : Nat} (before : Machine) (cursor : Fin W)
 (above : frame≤cursor.val) (x : Nat) (positive : 0<x) (below : x<frame) (privateCell : x≠cell (b+2)) :
 (writeMachine (allocateMachine before cursor AllocatingActivation.size) (cell (b+2)) (.val cursor)).mem x=before.mem x :=
 (upd_other _ _ privateCell).trans
   (Footprint.allocation_words (lo:=1) (by decide) cursor AllocatingActivation.size above x (by omega) below)

/-- Read the actual captured parent words in source-call order and derive the
complete exterior interval needed by subsequent paired unwind. -/
theorem history {C : Contract} {L b frame : Nat} {F : Frag (Parameters A)}
 (steps count : Nat) (reached : steps≤count) (bound : count<W)
 (σ : State C (Parameters A)) (ref : HRef σ.H A)
 (counter : TEnv.get (.here : Idx (Parameters A) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters A) (.mem A)) σ.env=some ref)
 (reads : count≤σ.heap.len ref .dyn)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (cursor : Fin W) (owner : StructAllocatorRepr σ.heap base frame cursor before)
 (positive : 0<b) (heapSpace : cursor.val+4*steps<W)
 (lo pointer start : Nat) (localBound : b+2<lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (payloadAbove : lo≤start) (pointerBefore : pointer<start)
 (capacity : start+2*steps≤frame) (fits : start+2*steps<W)
 (current : before.mem pointer=.val (wmod start)) (after : Machine)
 (actual : loopIterN (run (guardCompiled (C:=C) b F).code)
   (run (AllocatingActivation.code (C:=C) b F pointer)) steps before=.inl after) :
 (∀ j,j<steps → after.mem (start+2*j)=before.mem b ∧
   after.mem (start+2*j+1)=.val (wmod (count-j))) ∧
 (∀ x,0<x → x<frame → x≠b+1 → x≠b+2 → x≠pointer →
   (x<start ∨ start+2*steps≤x) → after.mem x=before.mem x) ∧
 after.mem b=before.mem b := by
 induction steps generalizing count σ base before cursor start with
 | zero =>
   have same : before=after := Sum.inl.inj actual
   subst after
   refine ⟨?_,?_,rfl⟩
   · intro j small;omega
   · intro x hp hf hc ht hx ho;rfl
 | succ steps ih =>
   cases count with
   | zero => omega
   | succ count =>
     let parent := AllocatingActivation.allocated σ
     let firstExtension := AllocatingActivation.extension σ
     let inherited := ref.wk firstExtension
     let child : State C (Parameters A) := parent.withEnv (countValue count (by omega),(some inherited,()))
     let allocationMachine := writeMachine (allocateMachine before cursor AllocatingActivation.size) (cell (b+2)) (.val cursor)
     have firstSpace : cursor.val+4<W := by omega
     obtain ⟨next,addresses,args,entered,executed,represented,stack,extended,growth,nextPointer,payload,firstExterior⟩ :=
       AllocatingActivation.activation σ count bound ref counter alias (by omega) base before repr cursor owner
         positive firstSpace lo pointer start localBound pointerAbove pointerBelow payloadAbove (by omega)
         pointerBefore (by omega) current
     have low : ∀ x,0<x → x<b+2 → allocationMachine.mem x=before.mem x := by
       intro x hp hx
       exact allocation_word before cursor owner.arrays.free.above x hp (by omega) (by change x≠b+2;omega)
     have nextReference : next.mem b=before.mem b :=
       (firstExterior b (by omega) (by omega) (.inl (by omega))).trans (low b positive (by omega))
     have nextExterior : ∀ x,0<x → x<frame → x≠b+1 → x≠b+2 → x≠pointer →
         (x<start ∨ start+2≤x) → next.mem x=before.mem x := by
       intro x hp hf hc ht hx ho
       exact (firstExterior x hx hc ho).trans
         (allocation_word before cursor owner.arrays.free.above x hp hf (by change x≠b+2;exact ht))
     let nextCursor : Fin W := ⟨cursor.val+4,firstSpace⟩
     have nextOwner : StructAllocatorRepr child.heap addresses frame nextCursor next := growth cursor positive owner firstSpace
     have kept : Heap.Keeps firstExtension σ.heap child.heap := Heap.keeps_alloc σ.heap (AllocatingActivation.object σ)
     have length : child.heap.len inherited .dyn=σ.heap.len ref .dyn := kept.len ref .dyn
     have childReads : count≤child.heap.len inherited .dyn := by rw [length];omega
     have remainingSpace : nextCursor.val+4*steps<W := by change cursor.val+4+4*steps<W;omega
     have guard := guard_run σ (count+1) bound counter base before repr
     have positiveGuard : run (guardCompiled (C:=C) b F).code before=.ok (before.push w[1]) 0 := by
       simpa only [show decide (0<count+1)=true from decide_eq_true (by omega),bword,ite_true] using guard
     have turn := successful_turn _ _ _ _ positiveGuard executed
     have rest : loopIterN (run (guardCompiled (C:=C) b F).code)
         (run (AllocatingActivation.code (C:=C) b F pointer)) steps next=.inl after := by
       simpa only [loopIterN,turn] using actual
     obtain ⟨saved,exterior,reference⟩ :=
       ih (count:=count) (reached:=by omega) (bound:=by omega) (σ:=child) (ref:=inherited)
         (counter:=rfl) (alias:=rfl) (reads:=childReads) (base:=addresses) (before:=next)
         (repr:=represented) (cursor:=nextCursor) (owner:=nextOwner) (heapSpace:=remainingSpace)
         (start:=start+2) (payloadAbove:=by omega) (pointerBefore:=by omega) (capacity:=by omega)
         (fits:=by omega) (current:=nextPointer) (actual:=rest)
     refine ⟨?_,?_,reference.trans nextReference⟩
     · intro j small
       cases j with
       | zero =>
         have savedRef := payload 0 (by decide)
         have savedCounter := payload 1 (by decide)
         have refAfter := exterior start (by omega) (by omega) (by omega) (by omega) (by omega) (.inl (by omega))
         have counterAfter := exterior (start+1) (by omega) (by omega) (by omega) (by omega) (by omega) (.inl (by omega))
         have word := RecursiveHistory.counter_word σ (count+1) bound counter base before repr
         constructor
         · simpa only [Nat.mul_zero,Nat.add_zero] using refAfter.trans (savedRef.trans (low b positive (by omega)))
         · simpa only [Nat.mul_zero,Nat.add_zero,Nat.sub_zero] using
             counterAfter.trans (savedCounter.trans ((low (b+1) (by omega) (by omega)).trans word))
       | succ j =>
         have words := saved j (by omega)
         have offset : start+2*(j+1)=start+2+2*j := by omega
         constructor
         · rw [offset]
           exact words.1.trans nextReference
         · rw [offset]
           simpa only [Nat.add_sub_add_right] using words.2
     · intro x hp hf hc ht hx ho
       exact (exterior x hp hf hc ht hx (by omega)).trans (nextExterior x hp hf hc ht hx (by omega))

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingHistory
