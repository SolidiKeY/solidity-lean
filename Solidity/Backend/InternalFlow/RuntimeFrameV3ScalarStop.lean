import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarPrefixes

/-! Completed scalar unwind and stable later horizons of the SAME existing
loop iterator and code image. Only actual successful states are represented;
no failure state, byte rollback or general recursive compiler is inferred. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPrefixes
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

theorem stop_after_running {C : Contract} {R : RefTy} {b pointer bottom start horizon : Nat}
 {F : Frag (Frame R)} {before last : Machine}
 (running : loopIterN (run (PairedUnwind.condition pointer bottom))
   (run (ScalarUnwind.code (C:=C) b pointer F)) horizon before=.inl last)
 (current : last.mem pointer=.val (wmod start)) (bottomValue : last.mem bottom=.val (wmod start)) :
 loopIterN (run (PairedUnwind.condition pointer bottom))
   (run (ScalarUnwind.code (C:=C) b pointer F)) (horizon+1) before=.inr (.ok last 0) := by
 induction horizon generalizing before with
 | zero =>
   have same : before=last := Sum.inl.inj running
   subst before
   simp only [loopIterN,turn_done last b pointer bottom start F current bottomValue]
 | succ horizon ih =>
   simp only [loopIterN] at running ⊢
   cases turn : loopTurn (run (PairedUnwind.condition pointer bottom))
       (run (ScalarUnwind.code (C:=C) b pointer F)) before with
   | inl next => rw [turn] at running;exact ih running
   | inr result => rw [turn] at running;cases running

theorem run_of_stopped {C : Contract} {R : RefTy} {b pointer bottom horizon : Nat}
 {F : Frag (Frame R)} {before after : Machine}
 (stopped : loopIterN (run (PairedUnwind.condition pointer bottom))
   (run (ScalarUnwind.code (C:=C) b pointer F)) horizon before=.inr (.ok after 0)) :
 run (image (C:=C) b pointer bottom F) before=.ok after 0 := by
 have done := loopRun_of_iterN stopped
 change loopRun (fun m => exec (PairedUnwind.condition pointer bottom) 0 m)
   (fun m => exec (ScalarUnwind.code (C:=C) b pointer F) 0 m) before=.ok after 0 at done
 simp only [image,run,exec_cons_zero,Instr.step,done,Out.ok_bind,exec_nil]

/-- Final false guard and ALL later observations return the same represented
scalar result. This quantifies every horizon, not a runtime/admission cutoff. -/
theorem complete {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Frame R)}
 (σ : State C (Frame R)) (base : Nat → Fin W) (total frames : Nat)
 (bounded : frames≤total) (bound : total<W) (after : Machine)
 (repr : StateRepr L b frame F (sourceAt σ (total-frames) (by omega)) base after)
 (lo pointer bottom start : Nat) (locals : b+3≤lo) (above : lo≤pointer)
 (below : pointer<frame) (payload : lo≤start) (separate : pointer<start)
 (bottomAbove : b+3≤bottom) (bottomBefore : bottom<start) (bottomSeparate : bottom≠pointer)
 (fits : start+2*frames<W)
 (current : after.mem pointer=.val (wmod (start+2*frames)))
 (bottomValue : after.mem bottom=.val (wmod start))
 (saved : ∀ j,j<frames → after.mem (start+2*j)=after.mem b ∧
   after.mem (start+2*j+1)=.val (wmod (total-j))) :
 ∃ last,
 run (image (C:=C) b pointer bottom F) after=.ok last 0 ∧
 (∀ n,frames+1≤n → loopIterN (run (PairedUnwind.condition pointer bottom))
   (run (ScalarUnwind.code (C:=C) b pointer F)) n after=.inr (.ok last 0)) ∧
 StateRepr L b frame F (sourceAt σ total bound) base last ∧
 last.stack=after.stack ∧ last.mem pointer=.val (wmod start) ∧ last.mem b=after.mem b ∧
 GrowsAllocator b frame 0 (sourceAt σ (total-frames) (by omega)) base after
   (sourceAt σ total bound) base last ∧
 (∀ x,x≠pointer → x≠b → x≠b+1 → x≠b+2 → last.mem x=after.mem x) := by
 obtain ⟨last,running,reached,stack,cursor,reference,growth,outside⟩ :=
   running_prefix σ base total frames frames (Nat.le_refl _) bounded bound after repr
     lo pointer bottom start locals above below payload separate bottomAbove bottomBefore
     bottomSeparate fits current bottomValue saved
 simp only [Nat.sub_self,Nat.mul_zero,Nat.add_zero,Nat.sub_add_cancel bounded] at reached cursor growth
 have bottomWord := (outside bottom bottomSeparate (by omega) (by omega) (by omega)).trans bottomValue
 have stopped := stop_after_running running cursor bottomWord
 exact ⟨last,run_of_stopped stopped,fun n hn => loopIterN_done_le hn stopped,
   reached,stack,cursor,reference,growth,outside⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarPrefixes
