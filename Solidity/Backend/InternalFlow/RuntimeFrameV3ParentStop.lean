import Solidity.Backend.InternalFlow.RuntimeFrameV3ParentPrefixes

/-! Final false guard and stable completed observations of the SAME typed
paired unwind. This consumes existing running prefixes and loop semantics;
no new evaluator, depth cutoff or failed output state is introduced. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ParentStop
open Evm Evm.Memory RecursiveSource ParentPrefixes

theorem stop_after_running {b pointer bottom start horizon : Nat} {R : RefTy} {before last : Machine}
 (running : loopIterN (run (PairedUnwind.condition pointer bottom))
   (run (Restore.restoreCells pointer (Restore.contextCells b (Parameters R)))) horizon before=.inl last)
 (current : last.mem pointer=.val (wmod start)) (bottomValue : last.mem bottom=.val (wmod start)) :
 loopIterN (run (PairedUnwind.condition pointer bottom))
   (run (Restore.restoreCells pointer (Restore.contextCells b (Parameters R)))) (horizon+1) before=.inr (.ok last 0) := by
 induction horizon generalizing before with
 | zero =>
   have same : before=last := Sum.inl.inj running
   subst before
   simp only [loopIterN,PairedUnwind.turn_done last b pointer bottom start R current bottomValue]
 | succ horizon ih =>
   simp only [loopIterN] at running ⊢
   cases turn : loopTurn (run (PairedUnwind.condition pointer bottom))
       (run (Restore.restoreCells pointer (Restore.contextCells b (Parameters R)))) before with
   | inl next =>
     rw [turn] at running
     exact ih running
   | inr result =>
     rw [turn] at running
     cases running

/-- The represented final parent is the SAME machine returned by the final
false guard and by every later observation horizon. -/
theorem complete {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (σ : State C (Parameters R)) (base : Nat → Fin W) (total frames : Nat)
 (bounded : frames≤total) (bound : total<W) (after : Machine)
 (repr : StateRepr L b frame F (sourceAt σ (total-frames) (by omega)) base after)
 (lo pointer bottom start : Nat) (locals : b+2≤lo) (above : lo≤pointer)
 (below : pointer<frame) (payload : lo≤start) (separate : pointer<start)
 (bottomAbove : b+2≤bottom) (bottomBefore : bottom<start) (bottomSeparate : bottom≠pointer)
 (fits : start+2*frames<W)
 (current : after.mem pointer=.val (wmod (start+2*frames)))
 (bottomValue : after.mem bottom=.val (wmod start))
 (saved : ∀ j, j<frames → after.mem (start+2*j)=after.mem b ∧
   after.mem (start+2*j+1)=.val (wmod (total-j))) :
 ∃ last,
 run (PairedUnwind.code b pointer bottom R) after=.ok last 0 ∧
 (∀ n, frames+1≤n → loopIterN (run (PairedUnwind.condition pointer bottom))
   (run (Restore.restoreCells pointer (Restore.contextCells b (Parameters R)))) n after=.inr (.ok last 0)) ∧
 StateRepr L b frame F (sourceAt σ total bound) base last ∧
 last.stack=after.stack ∧ last.mem pointer=.val (wmod start) ∧ last.mem b=after.mem b ∧
 GrowsAllocator b frame 0 (sourceAt σ (total-frames) (by omega)) base after
   (sourceAt σ total bound) base last ∧
 (∀ x, frame≤x → last.mem x=after.mem x) := by
 obtain ⟨last,running,reached,stack,cursor,reference,growth,high,outside⟩ :=
   running_prefix σ base total frames frames (Nat.le_refl _) bounded bound after repr
     lo pointer bottom start locals above below payload separate bottomAbove bottomBefore
     bottomSeparate fits current bottomValue saved
 simp only [Nat.sub_self,Nat.mul_zero,Nat.add_zero,Nat.sub_add_cancel bounded] at reached cursor growth
 have bottomWord := (outside bottom bottomSeparate (by omega) (by omega)).trans bottomValue
 have stopped := stop_after_running running cursor bottomWord
 exact ⟨last,PairedUnwind.run_of_stopped stopped,
   fun n hn => loopIterN_done_le hn stopped,reached,stack,cursor,reference,growth,high⟩

namespace Checks
open CountdownWitness RecursiveActivation

/-- Actual descent and completed unwind from the inhabited cursor-22 input;
ALL later observation horizons return this same represented parent. -/
theorem endpoint : ∃ down last addresses,
 run (descentCode (C:=P.C) 2 F 8 ++ PairedUnwind.code 2 8 7 A) ParentPrefixes.Checks.input=.ok last 0 ∧
 run (RecursiveReturn.entryCode (C:=P.C) 2 F 8 7) AllocatorReturn.Checks.input=.ok last 0 ∧
 (∀ n,3≤n → loopIterN (run (PairedUnwind.condition 8 7))
   (run (Restore.restoreCells 8 (Restore.contextCells 2 (Parameters A)))) n down=.inr (.ok last 0)) ∧
 StateRepr 1 2 16 F (sourceAt callee 2 (by decide)) addresses last ∧
 last.stack=[w[77]] ∧ last.mem 8=w[10] ∧ last.mem 2=w[16] ∧ last.mem 3=w[2] ∧
 StructAllocatorRepr callee.heap addresses 16 ⟨22,by decide⟩ last ∧
 [last.mem 16,last.mem 17,last.mem 18,last.mem 20,last.mem 21]=[w[2],w[7],w[9],w[1],w[4]] ∧
 [last.mem 0,last.mem 1,last.mem 7,last.mem 10,last.mem 11,last.mem 12,last.mem 13]=
 [w[22],w[16],w[10],w[16],w[2],w[16],w[1]] ∧
 loopIterN (run (PairedUnwind.condition 8 7))
   (run (Restore.restoreCells 8 (Restore.contextCells 2 (Parameters A)))) 2 down=.inl last ∧
 loopIterN (run (PairedUnwind.condition 8 7))
   (run (Restore.restoreCells 8 (Restore.contextCells 2 (Parameters A)))) 2 down≠.inr (.ok last 0) ∧
 run (RecursiveReturn.entryCode (C:=P.C) 2 F 8 7) AllocatorReturn.Checks.input≠.revert ∧
 run (RecursiveReturn.entryCode (C:=P.C) 2 F 8 7) AllocatorReturn.Checks.input≠.fault := by
 obtain ⟨down,last,addresses,descended,running,repr,stack,cursor,reference,counter,ownership,heap,words,negative⟩ :=
   ParentPrefixes.Checks.horizons 2 (Nat.le_refl _)
 have bottomWord : last.mem 7=w[10] := by
   have selected := congrArg (fun xs : List Word => xs[2]?) words
   change some (last.mem 7)=some w[10] at selected
   exact Option.some.inj selected
 have stopped := stop_after_running running cursor bottomWord
 have returned := PairedUnwind.run_of_stopped stopped
 have joined := (run_append_ok descended).trans returned
 have initialized : run (RecursiveReturn.initializeCode 8 7) AllocatorReturn.Checks.input=
     .ok ParentPrefixes.Checks.input 0 := by rfl
 have full : run (RecursiveReturn.entryCode (C:=P.C) 2 F 8 7) AllocatorReturn.Checks.input=.ok last 0 := by
   rw [RecursiveReturn.entryCode,RecursiveReturn.code,run_append_ok initialized]
   exact joined
 refine ⟨down,last,addresses,joined,full,
   fun n hn => loopIterN_done_le hn stopped,repr,stack,cursor,reference,counter,ownership,heap,words,running,?_,?_,?_⟩
 · rw [running];intro bad;cases bad
 · rw [full];intro bad;cases bad
 · rw [full];intro bad;cases bad

/-- Empty runtime history takes the false guard immediately, retaining the
same populated typed state and real allocator rather than performing a pop. -/
theorem zero_frames :
 run (PairedUnwind.code 2 8 7 A) ParentPrefixes.Checks.input=.ok ParentPrefixes.Checks.input 0 ∧
 (∀ n,1≤n → loopIterN (run (PairedUnwind.condition 8 7))
   (run (Restore.restoreCells 8 (Restore.contextCells 2 (Parameters A)))) n
     ParentPrefixes.Checks.input=.inr (.ok ParentPrefixes.Checks.input 0)) ∧
 StateRepr 1 2 16 F callee P.base ParentPrefixes.Checks.input ∧
 StructAllocatorRepr callee.heap P.base 16 ⟨22,by decide⟩ ParentPrefixes.Checks.input := by
 have turn := PairedUnwind.turn_done ParentPrefixes.Checks.input 2 8 7 10 A rfl rfl
 have stopped : loopIterN (run (PairedUnwind.condition 8 7))
     (run (Restore.restoreCells 8 (Restore.contextCells 2 (Parameters A)))) 1
     ParentPrefixes.Checks.input=.inr (.ok ParentPrefixes.Checks.input 0) := by
   simp only [loopIterN,turn]
 exact ⟨PairedUnwind.run_of_stopped stopped,fun n hn => loopIterN_done_le hn stopped,
   ParentPrefixes.Checks.initial,ParentPrefixes.Checks.ownership⟩

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.ParentStop

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ParentStop.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ParentStop.complete
