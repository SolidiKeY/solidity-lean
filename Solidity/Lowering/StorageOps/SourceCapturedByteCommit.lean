import Solidity.Lowering.StorageOps.SourceByteStoragePrepared

/-! The nested commit phase of storage-to-storage snapshots, over existing
Source operations and captured heap references. Per-prefix destination reads
are explicit; no OLD-only frame, physical compiler or world rollback is assumed. -/
namespace Solidity.Lowering.StorageOps.SourceCapturedByteCommit
open Solidity Solidity.Backend.StorageOps

def plans {E : Source.Env} (frame : Source.Fr) (dst : Source.SPath)
 (typed : ∀ i j, (.fixedBytes 1 (by decide) : Source.STy)=E.cellTy ((dst.go (.index i)).go (.index j)))
 (headerTyped : ∀ i, (.int Source.IntTy.u256 : Source.STy)=E.cellTy (dst.go (.index i)))
 (payload : Nat → List UInt8) (oldLength : Nat → Nat) (budget : Nat) :
 Nat → Nat → List (List (Source.Op E.layout E.lay E.lay))
 | _,0 => []
 | start,count+1 =>
   SourceByteStoragePrepared.phaseLog frame (dst.go (.index start)) (typed start) (headerTyped start)
     (payload start) (oldLength start) (count+1+budget-(payload start).length) ::
   plans frame dst typed headerTyped payload oldLength budget (start+1) count


/-- Actual nested snapshot writes at the reached-prefix headers and original fuel. -/
theorem commit_all : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (_writable : frame.static=false) (dst : Solidity.Source.SPath)
 (typed : ∀ i j, (.fixedBytes 1 (by decide) : Solidity.Source.STy)=E.cellTy ((dst.go (.index i)).go (.index j)))
 (headerTyped : ∀ i, (.int Solidity.Source.IntTy.u256 : Solidity.Source.STy)=E.cellTy (dst.go (.index i)))
 (payload : Nat → List UInt8) (oldLength : Nat → Nat) (start count budget first : Nat)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_captured : ∀ j<count,state.heap.get (first+j)=some ⟨.bytes .memory,Solidity.Source.Data.bytes (payload (start+j))⟩)
 (_enough : ∀ j<count,(payload (start+j)).length≤count+budget-j)
 (_cleanup : ∀ j<count,oldLength (start+j)-(payload (start+j)).length≤count+budget-j)
 (_headers : ∀ j<count,(Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (dst.go (.index (start+j)))).run
  (locals,{state with ex:=state.ex.run ((Solidity.Lowering.StorageOps.SourceCapturedByteCommit.plans frame dst typed headerTyped payload oldLength budget start count).take j).flatten})=
  (.ok (oldLength (start+j)),(locals,{state with ex:=state.ex.run ((Solidity.Lowering.StorageOps.SourceCapturedByteCommit.plans frame dst typed headerTyped payload oldLength budget start count).take j).flatten}))),
 (Solidity.Source.storeElems (E:=E) (Γ:=Γ) frame (count+budget+5) (.bytes .storage) dst start count
  (fun j : Fin count=>Solidity.Source.Data.val (Solidity.Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl (first+j.val)))).run (locals,state)=
 (.ok (),(locals,{state with ex:=state.ex.run (Solidity.Lowering.StorageOps.SourceCapturedByteCommit.plans frame dst typed headerTyped payload oldLength budget start count).flatten})) := by
 intro E Γ frame writable dst typed headerTyped payload oldLength start count budget first locals state captured enough cleanup headers
 induction count generalizing start first state with
 | zero => rfl
 | succ count ih =>
   let head := SourceByteStoragePrepared.phaseLog frame (dst.go (.index start)) (typed start) (headerTyped start)
     (payload start) (oldLength start) (count+1+budget-(payload start).length)
   let next := {state with ex:=state.ex.run head}
   have found := captured 0 (by omega)
   simp only [Nat.add_zero] at found
   have fetched : (Source.heapObj (E:=E) (Γ:=Γ) first).run (locals,state)=
     (.ok ⟨.bytes .memory,Source.Data.bytes (payload start)⟩,(locals,state)) := by
     simp only [Source.heapObj,Source.Hoare.run_bind]
     have current : (Source.EM.st (E:=E) (Γ:=Γ)).run (locals,state)=(.ok state,(locals,state)) := rfl
     rw [current]
     dsimp only
     rw [found]
     rfl
   have header := headers 0 (by omega)
   change (Source.readLen (E:=E) (Γ:=Γ) frame (dst.go (.index start))).run (locals,state)=
     (.ok (oldLength start),(locals,state)) at header
   have bound := enough 0 (by omega)
   have clearBound := cleanup 0 (by omega)
   simp only [Nat.add_zero,Nat.sub_zero] at bound clearBound
   have padding : (payload start).length+(count+1+budget-(payload start).length)+2=count+budget+3 := by omega
   have phase := SourceByteStoragePrepared.store_prepared frame writable (dst.go (.index start))
     (typed start) (headerTyped start) (payload start) (oldLength start)
     (count+1+budget-(payload start).length) locals state header
   rw [padding] at phase
   have clears : oldLength start-(payload start).length≤
     (payload start).length+(count+1+budget-(payload start).length) := by omega
   simp only [if_pos clears] at phase
   have body : (Source.storeData (E:=E) (Γ:=Γ) frame (count+budget+5) (.bytes .storage)
     (dst.go (.index start)) (Source.Data.val (Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl first))).run
     (locals,state)=(.ok (),(locals,next)) := by
     change ((Source.heapObj first >>= fun x=>Source.storeData frame (count+budget+3) (.bytes .storage)
       (dst.go (.index start)) x.2).run (locals,state))=_
     rw [Source.Hoare.run_bind,fetched]
     exact phase
   have total : count+1+budget+5=(count+budget+5)+1 := by omega
   rw [total]
   change ((Source.storeData frame (count+budget+5) (.bytes .storage) (dst.go (.index start))
     (Source.Data.val (Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl first)) >>= fun _=>
     Source.storeElems frame (count+budget+5) (.bytes .storage) dst (start+1) count
       (fun j : Fin count=>Source.Data.val (Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl (first+(j.val+1))))).run (locals,state))=_
   rw [Source.Hoare.run_bind,body]
   dsimp only
   have refs : (fun j : Fin count=>Source.Data.val (Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl (first+(j.val+1))))=
     (fun j : Fin count=>Source.Data.val (Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl ((first+1)+j.val))) := by
     funext j
     have address : first+(j.val+1)=(first+1)+j.val := by omega
     rw [address]
   rw [refs,ih (start+1) (first+1) next (by
     intro j member
     have h := captured (j+1) (by omega)
     have address : first+(j+1)=(first+1)+j := by omega
     have index : start+(j+1)=(start+1)+j := by omega
     rw [address,index] at h
     exact h) (by
     intro j member
     have h := enough (j+1) (by omega)
     have index : start+(j+1)=(start+1)+j := by omega
     rw [index] at h
     omega) (by
     intro j member
     have h := cleanup (j+1) (by omega)
     have index : start+(j+1)=(start+1)+j := by omega
     rw [index] at h
     omega) (by
     intro j member
     have h := headers (j+1) (by omega)
     simp only [plans,List.take_succ_cons,List.flatten_cons,Source.run_append] at h
     have index : start+(j+1)=(start+1)+j := by omega
     rw [index] at h
     exact h)]
   simp only [plans,List.flatten_cons,Source.run_append]
   rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommit.commit_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms commit_all

end Solidity.Lowering.StorageOps.SourceCapturedByteCommit
