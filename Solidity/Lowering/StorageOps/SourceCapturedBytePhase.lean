import Solidity.Lowering.StorageOps.SourceByteStoragePrepared

/-! Actual captured-reference child execution for storage-to-storage snapshots.
The existing heap and byte-copy semantics supply both success and cleanup
failure. This is not a memory-to-storage compiler or physical representation. -/
namespace Solidity.Lowering.StorageOps.SourceCapturedBytePhase
open Solidity Solidity.Backend.StorageOps

theorem run_phase : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (_writable : frame.static=false) (dst : Solidity.Source.SPath)
 (typed : ∀ j, (.fixedBytes 1 (by decide) : Solidity.Source.STy)=E.cellTy (dst.go (.index j)))
 (headerTyped : (.int Solidity.Source.IntTy.u256 : Solidity.Source.STy)=E.cellTy dst)
 (bs : List UInt8) (oldLength padding first : Nat)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_captured : state.heap.get first=some ⟨.bytes .memory,Solidity.Source.Data.bytes bs⟩)
 (_header : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame dst).run (locals,state)=(.ok oldLength,(locals,state))),
 (Solidity.Source.storeData (E:=E) (Γ:=Γ) frame (bs.length+padding+4) (.bytes .storage) dst
  (Solidity.Source.Data.val (Solidity.Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl first))).run (locals,state)=
 (if oldLength-bs.length≤bs.length+padding then .ok () else .error .timeout,
 (locals,{state with ex:=state.ex.run (Solidity.Lowering.StorageOps.SourceByteStoragePrepared.phaseLog frame dst typed headerTyped bs oldLength padding)})) := by
 intro E Γ frame writable dst typed headerTyped bs oldLength padding first locals state captured header
 have fetched : (Source.heapObj (E:=E) (Γ:=Γ) first).run (locals,state)=
   (.ok ⟨.bytes .memory,Source.Data.bytes bs⟩,(locals,state)) := by
   simp only [Source.heapObj,Source.Hoare.run_bind]
   have current : (Source.EM.st (E:=E) (Γ:=Γ)).run (locals,state)=(.ok state,(locals,state)) := rfl
   rw [current]
   dsimp only
   rw [captured]
   rfl
 change ((Source.heapObj first >>= fun x=>Source.storeData frame (bs.length+padding+2) (.bytes .storage) dst x.2).run (locals,state))=_
 rw [Source.Hoare.run_bind,fetched]
 exact SourceByteStoragePrepared.store_prepared frame writable dst typed headerTyped bs oldLength padding locals state header

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedBytePhase.run_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_phase

end Solidity.Lowering.StorageOps.SourceCapturedBytePhase
