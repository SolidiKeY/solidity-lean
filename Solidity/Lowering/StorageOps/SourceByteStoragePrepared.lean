import Solidity.Lowering.StorageOps.SourceByteStorageClear

/-! Exact actual Source byte-copy phase journals. No packed storage or
Source-to-target address correspondence is asserted. -/
namespace Solidity.Lowering.StorageOps.SourceByteStoragePrepared
open Solidity Solidity.Backend.StorageOps

def phaseLog {E : Source.Env} (frame : Source.Fr) (dst : Source.SPath)
 (typed : ∀ j, (.fixedBytes 1 (by decide) : Source.STy)=E.cellTy (dst.go (.index j)))
 (headerTyped : (.int Source.IntTy.u256 : Source.STy)=E.cellTy dst)
 (bs : List UInt8) (oldLength padding : Nat) : List (Source.Op E.layout E.lay E.lay) :=
 SourceByteStorageCopy.byteWrites frame dst typed 0 bs ++
 (List.range' bs.length (min (oldLength-bs.length) (bs.length+padding))).map
   (fun j=>SourceScalarDeleteLog.clearOp E frame (dst.go (.index j))) ++
 if oldLength-bs.length≤bs.length+padding then
 [SourceStorageCopy.cellOp E frame dst (some (headerTyped ▸ Source.intWrap Source.IntTy.u256 bs.length))]
 else []

/-- Snapshot payload writes finish; cleanup uses its original reused phase
fuel, and the header is committed only after complete cleanup. -/
theorem store_prepared : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (_writable : frame.static=false) (dst : Solidity.Source.SPath)
 (typed : ∀ j, (.fixedBytes 1 (by decide) : Solidity.Source.STy)=E.cellTy (dst.go (.index j)))
 (headerTyped : (.int Solidity.Source.IntTy.u256 : Solidity.Source.STy)=E.cellTy dst)
 (bs : List UInt8) (oldLength padding : Nat)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_oldHeader : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame dst).run (locals,state)=(.ok oldLength,(locals,state))),
 (Solidity.Source.storeData (E:=E) (Γ:=Γ) frame (bs.length+padding+2) (.bytes .storage) dst
   (Solidity.Source.Data.bytes (l:=.memory) bs)).run (locals,state)=
 (if oldLength-bs.length≤bs.length+padding then .ok () else .error .timeout,
  (locals,{state with ex:=state.ex.run (Solidity.Lowering.StorageOps.SourceByteStoragePrepared.phaseLog frame dst typed headerTyped bs oldLength padding)})) := by
 intro E Γ frame writable dst typed headerTyped bs oldLength padding locals state oldHeader
 change ((Source.readLen frame dst >>= fun old =>
   Source.storeBytes frame (bs.length+padding+1) dst 0 bs >>= fun _ =>
   Source.deleteRange frame (bs.length+padding+1) (.fixedBytes 1 (by decide)) dst bs.length (old-bs.length) >>= fun _ =>
   Source.writeLen frame dst bs.length).run (locals,state))=_
 rw [Source.Hoare.run_bind,oldHeader]
 dsimp only
 rw [Source.Hoare.run_bind,SourceByteStorageCopy.store_bytes_fuel frame writable dst
   (bs.length+padding+1) 0 bs typed locals state]
 have enough : bs.length<bs.length+padding+1 := by omega
 simp only [if_pos enough]
 rw [Source.Hoare.run_bind,SourceByteStorageClear.range_eq_int,
   SourceScalarDeleteLog.scalar_range_prefix frame writable Source.IntTy.u256 dst bs.length
     (oldLength-bs.length) (bs.length+padding)]
 by_cases done : oldLength-bs.length≤bs.length+padding
 · simp only [if_pos done]
   simp only [Source.writeLen]
   rw [SourceStorageCopy.write_run frame writable dst (Source.intWrap Source.IntTy.u256 bs.length) headerTyped]
   simp only [phaseLog,if_pos done,Source.run_append,Source.ExecState.run]
 · simp only [if_neg done]
   simp only [phaseLog,if_neg done,List.append_nil,Source.run_append]

/-- info: 'Solidity.Lowering.StorageOps.SourceByteStoragePrepared.store_prepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms store_prepared
end Solidity.Lowering.StorageOps.SourceByteStoragePrepared
