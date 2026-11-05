import Solidity.Lowering.StorageOps.SourceStorageCopyPrefix

/-! Actual Source snapshot timeout before any destination operation.
The existing load/copy semantics and original fuel are unchanged. -/
namespace Solidity.Lowering.StorageOps.SourceStorageCopyBarrier
open Solidity

/-- Insufficient primitive capture fuel retains the entire original state. -/
theorem load_timeout {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (t : Source.IntTy) (path : Source.SPath)
 (fuel start count : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (initial : Source.Locals E.layout Γ × Source.St E)
 (short : fuel≤count)
 (reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (path.go (.index (start+j))) (.int t)).run initial=(.ok (payload (start+j)),initial)) :
 (Source.loadElems (E:=E) (Γ:=Γ) frame fuel (.int t) path start count).run initial=(.error .timeout,initial) := by
 induction fuel generalizing start count with
 | zero => cases count <;> rfl
 | succ fuel ih =>
   cases count with
   | zero => omega
   | succ count =>
     cases fuel with
     | zero => rfl
     | succ fuel =>
       change ((Source.readAt frame (path.go (.index start)) (.int t) >>= fun x =>
         Source.loadElems frame (fuel+1) (.int t) path (start+1) count >>= fun xs =>
         pure (Source.finCons (.val x) xs)).run initial)=_
       rw [Source.Hoare.run_bind]
       have first := reads 0 (by omega)
       simp only [Nat.add_zero] at first
       rw [first]
       dsimp only
       rw [Source.Hoare.run_bind]
       rw [ih (start+1) count (by omega) (by
         intro j member
         have found := reads (j+1) (by omega)
         simpa only [Nat.add_assoc,Nat.add_comm j 1] using found)]

/-- Actual array snapshot timeout includes the header-read phase. -/
theorem array_timeout {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (t : Source.IntTy) (path : Source.SPath)
 (fuel count : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (initial : Source.Locals E.layout Γ × Source.St E) (short : fuel≤count+1)
 (header : (Source.readLen (E:=E) (Γ:=Γ) frame path).run initial=(.ok count,initial))
 (reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (path.go (.index j)) (.int t)).run initial=(.ok (payload j),initial)) :
 (Source.loadMem (E:=E) (Γ:=Γ) frame fuel (.array .memory (.int t) none) path).run initial=(.error .timeout,initial) := by
 cases fuel with
 | zero => rfl
 | succ fuel =>
   change ((Source.readLen frame path >>= fun len =>
     Source.loadElems frame fuel (.int t) path 0 len >>= fun xs =>
     pure (Source.Data.array (l:=.memory) (n:=none) len (fun _ h => nomatch h) xs)).run initial)=_
   rw [Source.Hoare.run_bind,header]
   dsimp only
   rw [Source.Hoare.run_bind,load_timeout frame t path fuel 0 count payload initial (by omega) (by
     simpa only [Nat.zero_add] using reads)]

/-- A distinct-path copy cannot mutate the destination before capture finishes.
No writable, destination-type or destination-header premise is needed. Valid
source reads matter: a malformed source can fail before the timeout. -/
theorem copy_timeout {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (t : Source.IntTy) (src dst : Source.SPath)
 (fuel count : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (initial : Source.Locals E.layout Γ × Source.St E) (different : src≠dst)
 (short : fuel≤count+2)
 (header : (Source.readLen (E:=E) (Γ:=Γ) frame src).run initial=(.ok count,initial))
 (reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index j)) (.int t)).run initial=(.ok (payload j),initial)) :
 (Source.storeVal (E:=E) (Γ:=Γ) frame fuel (.array .storage (.int t) none) dst
   (Source.Val.storRef (τ:=.array .storage (.int t) none) rfl src)).run initial=(.error .timeout,initial) := by
 cases fuel with
 | zero => rfl
 | succ fuel =>
   simp only [Source.storeVal,if_neg different,Source.STy.withLoc]
   rw [Source.Hoare.run_bind,array_timeout frame t src fuel count payload initial (by omega) header reads]

/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyBarrier.load_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms load_timeout
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyBarrier.array_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms array_timeout
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyBarrier.copy_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms copy_timeout
end Solidity.Lowering.StorageOps.SourceStorageCopyBarrier
