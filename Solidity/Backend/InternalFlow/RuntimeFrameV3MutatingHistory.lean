import Solidity.Backend.InternalFlow.RuntimeFrameV3MutatingResume

/-! Actual saved-parent payload and protected words across mutating descent.
The running-prefix premise is supplied by the checked source-coupled producer;
no saved history or memory-preservation certificate is assumed. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.MutatingHistory
open Evm Evm.Memory RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes

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
   (run (MutatingActivation.code (C:=C) b F pointer)) steps before=.inl after) :
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
     let mutated := MutatingActivation.changed σ ref count
     let parent := AllocatingActivation.allocated mutated
     let firstExtension := AllocatingActivation.extension mutated
     let inherited := ref.wk firstExtension
     let child : State C (Parameters A) := parent.withEnv (countValue count (by omega),(some inherited,()))
     have firstSpace : cursor.val+4<W := by omega
     obtain ⟨word,next,addresses,wordRepr,written,args,entered,executed,represented,stack,extended,growth,nextPointer,payload,firstExterior,rawExterior⟩ :=
       MutatingActivation.activation σ count bound ref counter alias (by omega) base before repr cursor owner
         positive firstSpace lo pointer start localBound pointerAbove pointerBelow payloadAbove (by omega)
         pointerBefore (by omega) current
     have nextReference : next.mem b=before.mem b :=
       firstExterior b positive (by have cells:=repr.locals;change b+2≤frame at cells;omega)
         (by omega) (by omega) (by omega) (.inl (by omega))
     have nextExterior : ∀ x,0<x → x<frame → x≠b+1 → x≠b+2 → x≠pointer →
         (x<start ∨ start+2≤x) → next.mem x=before.mem x := firstExterior
     let nextCursor : Fin W := ⟨cursor.val+4,firstSpace⟩
     have nextOwner : StructAllocatorRepr child.heap addresses frame nextCursor next := growth cursor positive owner firstSpace
     have kept : Heap.Keeps firstExtension mutated.heap child.heap := Heap.keeps_alloc mutated.heap (AllocatingActivation.object mutated)
     have length : child.heap.len inherited .dyn=σ.heap.len ref .dyn :=
       (kept.len ref .dyn).trans (MutatingActivation.lengths σ ref count (by omega) (by omega) ref .dyn)
     have childReads : count≤child.heap.len inherited .dyn := by rw [length];omega
     have remainingSpace : nextCursor.val+4*steps<W := by change cursor.val+4+4*steps<W;omega
     have guard := guard_run σ (count+1) bound counter base before repr
     have positiveGuard : run (guardCompiled (C:=C) b F).code before=.ok (before.push w[1]) 0 := by
       simpa only [show decide (0<count+1)=true from decide_eq_true (by omega)] using guard
     have turn := successful_turn _ _ _ _ positiveGuard executed
     have rest : loopIterN (run (guardCompiled (C:=C) b F).code)
         (run (MutatingActivation.code (C:=C) b F pointer)) steps next=.inl after := by
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
         · simpa only [Nat.mul_zero,Nat.add_zero] using refAfter.trans savedRef
         · simpa only [Nat.mul_zero,Nat.add_zero,Nat.sub_zero] using
             counterAfter.trans (savedCounter.trans word)
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

end Solidity.Backend.InternalFlow.RuntimeFrame.MutatingHistory
