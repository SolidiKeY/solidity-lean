import Solidity.Lowering.StorageOps.SourceStorageCopyBarrier

/-! Actual Source payload-phase failure at original copy fuel count+3.
The existing capture, payload, cleanup and journal semantics are unchanged. -/
namespace Solidity.Lowering.StorageOps.SourceStorageCopyPayload
open Solidity Solidity.Backend.StorageOps.SourceStorageCopy

/-- At the boundary fuel, all but the final captured element are written;
the final primitive leaf times out before its write. -/
theorem store_prefix {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (t : Source.IntTy) (path : Source.SPath)
 (start count : Nat) (payload : Nat → Source.Val E.layout (.int t))
 (typed : ∀ j, (.int t : Source.STy)=E.cellTy (path.go (.index j)))
 (locals : Source.Locals E.layout Γ) (state : Source.St E) :
 (Source.storeElems (E:=E) (Γ:=Γ) frame (count+2) (.int t) path start (count+1)
  (fun j : Fin (count+1) => Source.Data.val (payload (start+j.val)))).run (locals,state)=
 (.error .timeout,(locals,{state with ex:=state.ex.run (writes frame t path payload typed start count)})) := by
 induction count generalizing start state with
 | zero => rfl
 | succ count ih =>
   have budget : count+1+2=(count+2)+1 := by omega
   rw [budget]
   change ((Source.storeData frame (count+2) (.int t) (path.go (.index start)) (.val (payload (start+0))) >>= fun _ =>
    Source.storeElems frame (count+2) (.int t) path (start+1) (count+1)
     (fun j => .val (payload (start+(j.val+1))))).run (locals,state))=_
   simp only [Nat.add_zero]
   rw [Source.Hoare.run_bind,store_leaf frame writable t _ (payload start) (typed start) count locals state]
   dsimp only
   have vector : (fun j : Fin (count+1) => Source.Data.val (payload (start+(j.val+1))))=
     (fun j : Fin (count+1) => Source.Data.val (payload (start+1+j.val))) := by
     funext j
     congr 2
     omega
   rw [vector,ih]
   rfl

/-- Actual distinct-path storage copy with nonempty source, at original
fuel sourceLength+3. Cleanup and header commit are skipped after payload failure. -/
theorem copy_prefix {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (t : Source.IntTy)
 (src dst : Source.SPath) (different : src≠dst) (count oldLength : Nat)
 (payload : Nat → Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) none))
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (sourceHeader : (Source.readLen (E:=E) (Γ:=Γ) frame src).run (locals,state)=(.ok (count+1),(locals,state)))
 (reads : ∀ j<count+1,(Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index j)) (.int t)).run (locals,state)=(.ok (payload j),(locals,state)))
 (targetHeader : (Source.readLen (E:=E) (Γ:=Γ) frame dst).run (locals,state)=(.ok oldLength,(locals,state))) :
 (Source.storeVal (E:=E) (Γ:=Γ) frame (count+4) (.array .storage (.int t) none) dst
   (Source.Val.storRef (τ:=.array .storage (.int t) none) rfl src)).run (locals,state)=
 (.error .timeout,(locals,{state with ex:=state.ex.run (writes frame t dst payload (fun j => (element_type t dst typed j).symm) 0 count)})) := by
 have budget : count+4=(count+1)+0+3 := by omega
 rw [budget,captured_copy frame t src dst different (count+1) 0 payload (locals,state) sourceHeader reads]
 change ((Source.readLen frame dst >>= fun old =>
   Source.storeElems frame (count+2) (.int t) dst 0 (count+1)
     (fun j : Fin (count+1) => Source.Data.val (payload j.val)) >>= fun _ =>
   Source.deleteRange frame (count+2) (.int t) dst (count+1) (old-(count+1)) >>= fun _ =>
   Source.writeLen frame dst (count+1)).run (locals,state))=_
 rw [Source.Hoare.run_bind,targetHeader]
 dsimp only
 rw [Source.Hoare.run_bind]
 have writtenPrefix := store_prefix frame writable t dst 0 count payload
   (fun j => (element_type t dst typed j).symm) locals state
 simp only [Nat.zero_add] at writtenPrefix
 rw [writtenPrefix]

/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPayload.store_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms store_prefix
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPayload.copy_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms copy_prefix
end Solidity.Lowering.StorageOps.SourceStorageCopyPayload
