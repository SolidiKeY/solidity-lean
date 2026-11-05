import Solidity.Lowering.StorageOps.SourceStorageCopyEmpty

/-! Actual Source storage-reference byte/string capture and copy operations.
No packed physical layout or memory-to-storage compiler is supplied here. -/
namespace Solidity.Lowering.StorageOps.SourceByteStorageCopy
open Solidity

/-- Runtime byte capture reads only OLD cells and retains the entire state. -/
theorem load_bytes {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (path : Source.SPath) (start count padding : Nat)
 (payload : Nat → UInt8) (initial : Source.Locals E.layout Γ × Source.St E)
 (reads : ∀ j<count,(Source.readAt (E:=E) (Γ:=Γ) frame (path.go (.index (start+j))) (.fixedBytes 1 (by decide))).run initial=
   (.ok (Source.Val.fixedBytes (n:=1) (h:=by decide) [payload (start+j)] rfl),initial)) :
 (Source.loadBytes (E:=E) (Γ:=Γ) frame (count+padding+1) path start count).run initial=
   (.ok ((List.range' start count).map payload),initial) := by
 induction count generalizing start with
 | zero => rfl
 | succ count ih =>
   have budget : count+1+padding+1=(count+padding+1)+1 := by omega
   rw [budget]
   change ((Source.readAt frame (path.go (.index start)) (.fixedBytes 1 (by decide)) >>= fun value =>
     match value with
     | .fixedBytes bs _ => do
       let rest ← Source.loadBytes frame (count+padding+1) path (start+1) count
       pure (bs.headD 0 :: rest)).run initial)=_
   rw [Source.Hoare.run_bind]
   have first := reads 0 (by omega)
   simp only [Nat.add_zero] at first
   rw [first]
   dsimp only
   rw [Source.Hoare.run_bind,ih (start+1) (by
     intro j member
     have found := reads (j+1) (by omega)
     simpa only [Nat.add_assoc,Nat.add_comm j 1] using found)]
   simp only [List.range'_succ,List.map_cons]
   rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceByteStorageCopy.load_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms load_bytes
/-- A footprint of existing Source.Op writes, not another command/value layer. -/
def byteWrites {E : Source.Env} (frame : Source.Fr) (path : Source.SPath)
 (typed : ∀ j, (.fixedBytes 1 (by decide) : Source.STy)=E.cellTy (path.go (.index j))) :
 Nat → List UInt8 → List (Source.Op E.layout E.lay E.lay)
 | _,[] => []
 | start,b::bs =>
   Solidity.Backend.StorageOps.SourceStorageCopy.cellOp E frame (path.go (.index start))
     (some ((typed start) ▸ Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl)) ::
   byteWrites frame path typed (start+1) bs

/-- Exact progress at every original fuel, including timeout after the final
byte write when the empty tail is reached at zero fuel. -/
theorem store_bytes_fuel {E : Source.Env} {Γ : Source.RCtx}
 (frame : Source.Fr) (writable : frame.static=false) (path : Source.SPath)
 (fuel start : Nat) (bs : List UInt8)
 (typed : ∀ j, (.fixedBytes 1 (by decide) : Source.STy)=E.cellTy (path.go (.index j)))
 (locals : Source.Locals E.layout Γ) (state : Source.St E) :
 (Source.storeBytes (E:=E) (Γ:=Γ) frame fuel path start bs).run (locals,state)=
 if bs.length<fuel then
   (.ok (),(locals,{state with ex:=state.ex.run (byteWrites frame path typed start bs)}))
 else
   (.error .timeout,(locals,{state with ex:=state.ex.run (byteWrites frame path typed start (bs.take fuel))})) := by
 induction bs generalizing fuel start state with
 | nil =>
   cases fuel with
   | zero => rfl
   | succ fuel =>
     simp only [List.length_nil,Nat.zero_lt_succ,if_true]
     rfl
 | cons b bs ih =>
   cases fuel with
   | zero => rfl
   | succ fuel =>
     change ((Source.writeAt frame (path.go (.index start))
       (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl) >>= fun _ =>
       Source.storeBytes frame fuel path (start+1) bs).run (locals,state))=_
     rw [Source.Hoare.run_bind,Solidity.Backend.StorageOps.SourceStorageCopy.write_run frame writable
       (path.go (.index start)) (Source.Val.fixedBytes (n:=1) (h:=by decide) [b] rfl) (typed start) locals state]
     dsimp only
     rw [ih]
     by_cases enough : bs.length<fuel
     · simp only [List.length_cons,Nat.succ_lt_succ_iff,if_pos enough]
       rfl
     · simp only [List.length_cons,Nat.succ_lt_succ_iff,if_neg enough,List.take_succ_cons]
       rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceByteStorageCopy.store_bytes_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms store_bytes_fuel
end Solidity.Lowering.StorageOps.SourceByteStorageCopy
