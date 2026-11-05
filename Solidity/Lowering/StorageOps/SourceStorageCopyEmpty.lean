import Solidity.Lowering.StorageOps.SourceStorageCopyPayload

/-! Actual Source empty-copy boundary at original fuel3. Header materialization
is a real journal operation; failure is not an implicit rollback. -/
namespace Solidity.Lowering.StorageOps.SourceStorageCopyEmpty
open Solidity Solidity.Backend.StorageOps.SourceStorageCopy

theorem copy_empty {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (t : Source.IntTy)
 (src dst : Source.SPath) (different : src≠dst) (oldLength : Nat)
 (typed : E.pathTy dst=some (.array .storage (.int t) none))
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (sourceHeader : (Source.readLen (E:=E) (Γ:=Γ) frame src).run (locals,state)=(.ok 0,(locals,state)))
 (targetHeader : (Source.readLen (E:=E) (Γ:=Γ) frame dst).run (locals,state)=(.ok oldLength,(locals,state))) :
 (Source.storeVal (E:=E) (Γ:=Γ) frame 3 (.array .storage (.int t) none) dst
   (Source.Val.storRef (τ:=.array .storage (.int t) none) rfl src)).run (locals,state)=
 if oldLength=0 then
   (.ok (),(locals,{state with ex:=state.ex.run (copyLog frame t dst 0 0 (fun _ => Source.intWrap t 0) typed)}))
 else (.error .timeout,(locals,state)) := by
 rw [captured_copy frame t src dst different 0 0 (fun _ => Source.intWrap t 0)
   (locals,state) sourceHeader (by intro j bound; omega)]
 change ((Source.readLen frame dst >>= fun old =>
   Source.storeElems frame 1 (.int t) dst 0 0
     (fun _ : Fin 0 => Source.Data.val (Source.intWrap t 0)) >>= fun _ =>
   Source.deleteRange frame 1 (.int t) dst 0 (old-0) >>= fun _ =>
   Source.writeLen frame dst 0).run (locals,state))=_
 rw [Source.Hoare.run_bind,targetHeader]
 dsimp only
 cases oldLength with
 | zero =>
   change (Source.writeLen frame dst 0).run (locals,state)=_
   simp only [Source.writeLen]
   rw [write_run (E:=E) (Γ:=Γ) frame writable dst (Source.intWrap Source.IntTy.u256 (0 : Nat)) (by
     simp only [Source.Env.cellTy,typed,Option.map_some,Source.STy.cell,Option.getD_some])]
   rfl
 | succ oldLength => rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyEmpty.copy_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms copy_empty
end Solidity.Lowering.StorageOps.SourceStorageCopyEmpty
