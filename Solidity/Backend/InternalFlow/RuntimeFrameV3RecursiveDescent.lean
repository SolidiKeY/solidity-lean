import Solidity.Backend.InternalFlow.RuntimeFrameV3RecursiveActivation

/-! Descent of the hand-written countdown image at every reached horizon,
from a reached `StateRepr` and the checked activation bridge. It reaches the
deepest child, not the returned caller. -/

namespace Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveDescent
open Evm Evm.Memory RecursiveSource RecursiveActivation

set_option backward.isDefEq.respectTransparency false in
/-- Every admitted countdown completes the same descent code. The index is
an observation horizon, not a compilation or recursion-admission cutoff.
Capacity is the actual two captured context cells per positive activation. -/
theorem complete {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (hm : (Ty.ref R).mapFree=true) (count : Nat) (bound : count<W)
 (σ : State C (Parameters R)) (ref : HRef σ.H R)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters R) (.mem R)) σ.env=some ref)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (lo pointer start : Nat) (localBound : b+2≤lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (payloadAbove : lo≤start) (pointerBefore : pointer<start)
 (capacity : start+2*count≤frame) (fits : start+2*count<W)
 (current : before.mem pointer=.val (wmod start)) :
 let finalSource : State C (Parameters R) := σ.withEnv (countValue 0 W_pos,(some ref,()))
 ∃ after addresses,
 loopIterN (run (guardCompiled (C:=C) b F).code) (run (activationCode (C:=C) b F pointer)) count before=.inl after ∧
 loopIterN (run (guardCompiled (C:=C) b F).code) (run (activationCode (C:=C) b F pointer)) (count+1) before=.inr (.ok after 0) ∧
 StateRepr L b frame F finalSource addresses after ∧ after.stack=before.stack ∧
 BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame 0 σ base before finalSource addresses after ∧
 after.mem pointer=.val (wmod (start+2*count)) := by
 induction count generalizing σ base before start with
 | zero =>
   have environment : σ.env=(countValue 0 W_pos,(some ref,())) :=
     Prod.ext counter (Prod.ext alias (by cases σ.env.2.2;rfl))
   have same : σ.withEnv (Δ:=Parameters R) (countValue 0 W_pos,(some ref,()))=σ := by
     rw [←environment]
     rfl
   have stopped := zero_turn σ counter base before repr pointer
   refine ⟨before,base,?_,?_,?_,rfl,BaseExtends.refl base,?_,?_⟩
   · rfl
   · simp only [loopIterN,stopped]
   · rw [same];exact repr
   · rw [same]
     intro cursor hb ha hs
     simpa only [Nat.add_zero] using ha
   · simpa only [Nat.mul_zero,Nat.add_zero] using current
 | succ count ih =>
   let child : State C (Parameters R) := σ.withEnv (countValue count (by omega),(some ref,()))
   obtain ⟨saved,next,addresses,args,entry,captured,updated,executed,represented,stack,extended,growth,cursor,payload⟩ :=
     activation hm σ count bound ref counter alias base before repr lo pointer start localBound
       pointerAbove pointerBelow payloadAbove (by omega) (.inl (by omega)) (by omega) current
   have turn := positive_turn σ count bound counter base before next repr pointer executed
   obtain ⟨after,finalAddresses,running,stopped,finalRepr,finalStack,finalExt,finalGrowth,finalCursor⟩ :=
     ih (by omega) child ref rfl rfl addresses next represented (start+2) (by omega)
       (by omega) (by omega) (by omega) cursor
   refine ⟨after,finalAddresses,?_,?_,?_,finalStack.trans stack,?_,?_,?_⟩
   · simpa only [loopIterN,turn] using running
   · simpa only [loopIterN,turn] using stopped
   · exact finalRepr
   · exact extended.trans (List.prefix_refl _) finalExt
   · exact growth.comp finalGrowth
   · have arithmetic : start+2+2*count=start+2*(count+1) := by omega
     simpa only [arithmetic] using finalCursor


set_option backward.isDefEq.respectTransparency false in
/-- Every reached finite prefix preserves the actual next native parameters,
not only the stopping endpoint. Neither a prefix run nor a reached StateRepr
is supplied: both follow from checked capture/update and the initial capacity. -/
theorem reached_prefix {C : Contract} {R : RefTy} {L b frame : Nat} {F : Frag (Parameters R)}
 (hm : (Ty.ref R).mapFree=true) (steps count : Nat) (reached : steps≤count) (bound : count<W)
 (σ : State C (Parameters R)) (ref : HRef σ.H R)
 (counter : TEnv.get (.here : Idx (Parameters R) (.val .uint)) σ.env=countValue count bound)
 (alias : TEnv.get (.there .here : Idx (Parameters R) (.mem R)) σ.env=some ref)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (lo pointer start : Nat) (localBound : b+2≤lo) (pointerAbove : lo≤pointer)
 (pointerBelow : pointer<frame) (payloadAbove : lo≤start) (pointerBefore : pointer<start)
 (capacity : start+2*count≤frame) (fits : start+2*count<W)
 (current : before.mem pointer=.val (wmod start)) :
 let source : State C (Parameters R) := σ.withEnv (countValue (count-steps) (by omega),(some ref,()))
 ∃ after addresses,
 loopIterN (run (guardCompiled (C:=C) b F).code) (run (activationCode (C:=C) b F pointer)) steps before=.inl after ∧
 StateRepr L b frame F source addresses after ∧ after.stack=before.stack ∧
 BaseExtends σ.H base addresses ∧
 GrowsAllocator b frame 0 σ base before source addresses after ∧
 after.mem pointer=.val (wmod (start+2*steps)) := by
 induction steps generalizing count σ base before start with
 | zero =>
   have environment : σ.env=(countValue count bound,(some ref,())) :=
     Prod.ext counter (Prod.ext alias (by cases σ.env.2.2;rfl))
   have same : σ.withEnv (Δ:=Parameters R) (countValue (count-0) (by omega),(some ref,()))=σ := by
     simp only [Nat.sub_zero]
     rw [←environment]
     rfl
   refine ⟨before,base,rfl,?_,rfl,BaseExtends.refl base,?_,?_⟩
   · rw [same];exact repr
   · rw [same]
     intro cursor hb ha hs
     simpa only [Nat.add_zero] using ha
   · simpa only [Nat.mul_zero,Nat.add_zero] using current
 | succ steps ih =>
   cases count with
   | zero => omega
   | succ count =>
     let child : State C (Parameters R) := σ.withEnv (countValue count (by omega),(some ref,()))
     obtain ⟨saved,next,addresses,args,entry,captured,updated,executed,represented,stack,extended,growth,cursor,payload⟩ :=
       activation hm σ count bound ref counter alias base before repr lo pointer start localBound
         pointerAbove pointerBelow payloadAbove (by omega) (.inl (by omega)) (by omega) current
     have turn := positive_turn σ count bound counter base before next repr pointer executed
     obtain ⟨after,finalAddresses,running,finalRepr,finalStack,finalExt,finalGrowth,finalCursor⟩ :=
       ih count (by omega) (by omega) child ref rfl rfl addresses next represented (start+2)
         (by omega) (by omega) (by omega) (by omega) cursor
     refine ⟨after,finalAddresses,?_,?_,finalStack.trans stack,?_,?_,?_⟩
     · simpa only [loopIterN,turn] using running
     · simpa only [child, State.withEnv, Nat.add_sub_add_right] using finalRepr
     · exact extended.trans (List.prefix_refl _) finalExt
     · exact growth.comp finalGrowth
     · have arithmetic : start+2+2*steps=start+2*(steps+1) := by omega
       simpa only [arithmetic] using finalCursor

/-- Connect the proved stopping horizon to execution of the SAME one-image
instruction list. The stopping premise is discharged by complete above. -/
theorem run_of_stopped {C : Contract} {R : RefTy} {b pointer horizon : Nat}
 {F : Frag (Parameters R)} {before after : Machine}
 (stopped : loopIterN (run (guardCompiled (C:=C) b F).code)
   (run (activationCode (C:=C) b F pointer)) horizon before=.inr (.ok after 0)) :
 run (descentCode (C:=C) b F pointer) before=.ok after 0 := by
 have done := loopRun_of_iterN stopped
 change loopRun (fun m => exec (guardCompiled (C:=C) b F).code 0 m)
   (fun m => exec (activationCode (C:=C) b F pointer) 0 m) before=.ok after 0 at done
 simp only [descentCode,run,exec_cons_zero,Instr.step,done,Out.ok_bind,exec_nil]

end Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveDescent
