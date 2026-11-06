import Solidity.Lowering.StorageOps.SourceByteStorageCopy

/-! Actual byte-capture timeout with complete state preservation. Valid OLD
reads are material: malformed cells can fail earlier with a different error.
No destination, writable-frame or world rollback premise is introduced. -/
namespace Solidity.Lowering.StorageOps.SourceByteStorageBarrier
open Solidity

/-- The capture loop has no effects at any insufficient original runtime fuel. -/
theorem load_timeout {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (path : Source.SPath) (fuel start count : Nat) (payload : Nat → UInt8)
 (initial : Source.Locals E.layout Γ × Source.St E) (short : fuel≤count)
 (reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (path.go (.index (start+j))) (.fixedBytes 1 (by decide))).run initial=
  (.ok (Source.Val.fixedBytes (n:=1) (h:=by decide) [payload (start+j)] rfl),initial)) :
 (Source.loadBytes (E:=E) (Γ:=Γ) frame fuel path start count).run initial=(.error .timeout,initial) := by
 induction fuel generalizing start count with
 | zero => cases count <;> rfl
 | succ fuel ih =>
   cases count with
   | zero => omega
   | succ count =>
     change ((Source.readAt frame (path.go (.index start)) (.fixedBytes 1 (by decide)) >>= fun value =>
       match value with
       | .fixedBytes bs _ => do
         let rest ← Source.loadBytes frame fuel path (start+1) count
         pure (bs.headD 0 :: rest)).run initial)=_
     rw [Source.Hoare.run_bind]
     have first := reads 0 (by omega)
     simp only [Nat.add_zero] at first
     rw [first]
     dsimp only
     rw [Source.Hoare.run_bind,ih (start+1) count (by omega) (by
       intro j member
       have found := reads (j+1) (by omega)
       simpa only [Nat.add_assoc,Nat.add_comm j 1] using found)]

/-- info: 'Solidity.Lowering.StorageOps.SourceByteStorageBarrier.load_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms load_timeout
end Solidity.Lowering.StorageOps.SourceByteStorageBarrier
