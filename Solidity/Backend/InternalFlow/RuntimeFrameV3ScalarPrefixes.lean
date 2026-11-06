import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarUnwind
import Solidity.Backend.InternalFlow.RuntimeFrameV3PairedUnwind

/-! Typed scalar results at every running finite horizon of the existing
runtime loop iterator. Saved words and reached representation are explicit;
no new evaluator, recursive compiler selector or admission cutoff is added. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPrefixes
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

def sourceAt {C : Contract} {R : RefTy} (σ : State C (Frame R)) (n : Nat) (h : n<W) :=
 σ.withEnv (Δ:=Frame R) (countValue n h,(countValue n h,σ.env.2.2))

def image {C : Contract} {R : RefTy} (b pointer bottom : Nat) (F : Frag (Frame R)) : List Instr :=
 [.loop (PairedUnwind.condition pointer bottom) (ScalarUnwind.code (C:=C) b pointer F)]

theorem turn_more {C : Contract} {R : RefTy} (m next : Machine) (b pointer bottom start frames : Nat)
 (F : Frag (Frame R))
 (current : m.mem pointer=.val (wmod (start+2*(frames+1))))
 (bottomValue : m.mem bottom=.val (wmod start)) (fits : start+2*(frames+1)<W)
 (body : run (ScalarUnwind.code (C:=C) b pointer F) m=.ok next 0) :
 loopTurn (run (PairedUnwind.condition pointer bottom))
   (run (ScalarUnwind.code (C:=C) b pointer F)) m=.inl next := by
 have guard := RecursiveUnwind.condition_run m pointer bottom (wmod (start+2*(frames+1))) (wmod start) current bottomValue
 have different : (wmod (start+2*(frames+1))).val≠(wmod start).val := by
   change (start+2*(frames+1))%W≠start%W
   rw [Nat.mod_eq_of_lt fits,Nat.mod_eq_of_lt (show start<W by omega)]
   omega
 simp only [loopTurn,guard,decide_eq_true different,Machine.push,bword,if_true,if_false,Nat.one_ne_zero,body]

theorem turn_done {C : Contract} {R : RefTy} (m : Machine) (b pointer bottom start : Nat)
 (F : Frag (Frame R))
 (current : m.mem pointer=.val (wmod start)) (bottomValue : m.mem bottom=.val (wmod start)) :
 loopTurn (run (PairedUnwind.condition pointer bottom))
   (run (ScalarUnwind.code (C:=C) b pointer F)) m=.inr (.ok m 0) := by
 have guard := RecursiveUnwind.condition_run m pointer bottom (wmod start) (wmod start) current bottomValue
 simp only [loopTurn,guard,ne_eq,not_true_eq_false,decide_false,Machine.push,bword,
   Bool.false_eq_true,if_false,if_true]

/-- Every running horizon recovers the matching counter and computes its
live scalar result from the previous child result. No whole-loop frame or
simulation conclusion is supplied as a hypothesis. -/
theorem running_prefix {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Frame R)}
 (σ : State C (Frame R)) (base : Nat → Fin W) (total steps frames : Nat)
 (enough : steps≤frames) (bounded : frames≤total) (bound : total<W)
 (after : Machine)
 (repr : StateRepr L b frame F (sourceAt σ (total-frames) (by omega)) base after)
 (lo pointer bottom start : Nat) (locals : b+3≤lo) (above : lo≤pointer)
 (below : pointer<frame) (_payload : lo≤start) (separate : pointer<start)
 (bottomAbove : b+3≤bottom) (_bottomBefore : bottom<start) (bottomSeparate : bottom≠pointer)
 (fits : start+2*frames<W)
 (current : after.mem pointer=.val (wmod (start+2*frames)))
 (bottomValue : after.mem bottom=.val (wmod start))
 (saved : ∀ j,j<frames → after.mem (start+2*j)=after.mem b ∧
   after.mem (start+2*j+1)=.val (wmod (total-j))) :
 ∃ last,
 loopIterN (run (PairedUnwind.condition pointer bottom))
   (run (ScalarUnwind.code (C:=C) b pointer F)) steps after=.inl last ∧
 StateRepr L b frame F (sourceAt σ (total-frames+steps) (by omega)) base last ∧
 last.stack=after.stack ∧ last.mem pointer=.val (wmod (start+2*(frames-steps))) ∧
 last.mem b=after.mem b ∧
 GrowsAllocator b frame 0 (sourceAt σ (total-frames) (by omega)) base after
   (sourceAt σ (total-frames+steps) (by omega)) base last ∧
 (∀ x,x≠pointer → x≠b → x≠b+1 → x≠b+2 → last.mem x=after.mem x) := by
 induction steps generalizing frames after with
 | zero =>
   refine ⟨after,rfl,?_,rfl,?_,rfl,?_,?_⟩
   · simpa only [Nat.add_zero] using repr
   · simpa only [Nat.sub_zero] using current
   · intro cursor positive owner space
     simpa only [Nat.add_zero] using owner
   · intro x hp hr hc hv;rfl
 | succ steps ih =>
   cases frames with
   | zero => omega
   | succ frames =>
     have words := saved frames (by omega)
     obtain ⟨mid,executed,represented,stack,cursor,reference,counter,result,growth,outside⟩ :=
       ScalarUnwind.step (sourceAt σ (total-(frames+1)) (by omega)) base after repr
         (total-(frames+1)) (by omega) rfl lo pointer (start+2*frames)
         locals above below (by omega) (by omega) (by omega)
         (by simpa only [show start+2*frames+2=start+2*(frames+1) from by omega] using current)
         words.1 (by simpa only [show total-(frames+1)+1=total-frames from by omega] using words.2)
     have nextRepr : StateRepr L b frame F (sourceAt σ (total-frames) (by omega)) base mid := by
       simpa only [show total-(frames+1)+1=total-frames from by omega] using represented
     have nextSaved : ∀ j,j<frames → mid.mem (start+2*j)=mid.mem b ∧
         mid.mem (start+2*j+1)=.val (wmod (total-j)) := by
       intro j small
       exact ⟨(outside _ (by omega) (by omega) (by omega) (by omega)).trans
         ((saved j (by omega)).1.trans reference.symm),
         (outside _ (by omega) (by omega) (by omega) (by omega)).trans (saved j (by omega)).2⟩
     have nextBottom : mid.mem bottom=.val (wmod start) :=
       (outside bottom bottomSeparate (by omega) (by omega) (by omega)).trans bottomValue
     have turn := turn_more after mid b pointer bottom start frames F current bottomValue fits executed
     obtain ⟨last,running,finalRepr,finalStack,finalCursor,finalRef,finalGrowth,finalOutside⟩ :=
       ih frames (by omega) (by omega) mid nextRepr (by omega) cursor nextBottom nextSaved
     have arithmetic : total-(frames+1)+(steps+1)=total-frames+steps := by omega
     refine ⟨last,?_,?_,finalStack.trans stack,?_,finalRef.trans reference,?_,?_⟩
     · simpa only [loopIterN,turn] using running
     · simpa only [arithmetic] using finalRepr
     · simpa only [Nat.sub_zero,Nat.add_sub_add_right] using finalCursor
     · have compatible : GrowsAllocator b frame 0 (sourceAt σ (total-(frames+1)) (by omega)) base after
         (sourceAt σ (total-frames) (by omega)) base mid := by
         simpa only [show total-(frames+1)+1=total-frames from by omega] using growth
       simpa only [Nat.add_zero,arithmetic] using compatible.comp finalGrowth
     · intro x hp hr hc hv
       exact (finalOutside x hp hr hc hv).trans (outside x hp hr hc hv)

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPrefixes
