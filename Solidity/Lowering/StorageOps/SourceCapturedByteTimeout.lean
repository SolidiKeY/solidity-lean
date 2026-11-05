import Solidity.Lowering.StorageOps.SourceCapturedBytePhase
import Solidity.Lowering.StorageOps.SourceByteCommitFrames

/-! Actual nested snapshot commit: an arbitrary successful prefix followed by
partial child cleanup and timeout. OLD headers are transported by the checked
Source path frames. No automatic rollback or physical execution is asserted. -/
namespace Solidity.Lowering.StorageOps.SourceCapturedByteTimeout
open Solidity Solidity.Backend.StorageOps

/-- Exact failed commit after an arbitrary successful child prefix.
The last child writes its payload and only the available stale-tail prefix;
its old header and all later shadows survive. OLD header inputs are sufficient. -/
theorem cleanup_timeout : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (_writable : frame.static=false) (dst : Solidity.Source.SPath)
 (typed : ∀ i j, (.fixedBytes 1 (by decide) : Solidity.Source.STy)=E.cellTy ((dst.go (.index i)).go (.index j)))
 (headerTyped : ∀ i, (.int Solidity.Source.IntTy.u256 : Solidity.Source.STy)=E.cellTy (dst.go (.index i)))
 (payload : Nat → List UInt8) (oldLength : Nat → Nat) (start count budget first : Nat)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_captured : ∀ j<count+1,state.heap.get (first+j)=some ⟨.bytes .memory,Solidity.Source.Data.bytes (payload (start+j))⟩)
 (_enough : ∀ j<count+1,(payload (start+j)).length≤count+1+budget-j)
 (_cleanup : ∀ j<count,oldLength (start+j)-(payload (start+j)).length≤count+1+budget-j)
 (_short : budget+1<oldLength (start+count)-(payload (start+count)).length)
 (_headers : ∀ j<count+1,(Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (dst.go (.index (start+j)))).run (locals,state)=
  (.ok (oldLength (start+j)),(locals,state))),
 (Solidity.Source.storeElems (E:=E) (Γ:=Γ) frame (count+budget+6) (.bytes .storage) dst start (count+1)
  (fun j : Fin (count+1)=>Solidity.Source.Data.val (Solidity.Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl (first+j.val)))).run (locals,state)=
 (.error .timeout,(locals,{state with ex:=state.ex.run (Solidity.Lowering.StorageOps.SourceCapturedByteCommit.plans frame dst typed headerTyped payload oldLength budget start (count+1)).flatten})) := by
 intro E Γ frame writable dst typed headerTyped payload oldLength start count budget first locals state captured enough cleanup short headers
 induction count generalizing start first state with
 | zero =>
   have found := captured 0 (by omega)
   have header := headers 0 (by omega)
   have bound := enough 0 (by omega)
   simp only [Nat.add_zero,Nat.sub_zero] at found header bound short
   have phase := SourceCapturedBytePhase.run_phase frame writable (dst.go (.index start)) (typed start)
     (headerTyped start) (payload start) (oldLength start) (1+budget-(payload start).length)
     first locals state found header
   have fuel : (payload start).length+(1+budget-(payload start).length)+4=budget+5 := by omega
   rw [fuel] at phase
   have fails : ¬oldLength start-(payload start).length≤
     (payload start).length+(1+budget-(payload start).length) := by omega
   simp only [if_neg fails] at phase
   simp only [Nat.zero_add]
   change ((Source.storeData frame (budget+5) (.bytes .storage) (dst.go (.index start))
     (Source.Data.val (Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl first)) >>= fun _=>
     Source.storeElems frame (budget+5) (.bytes .storage) dst (start+1) 0
       (fun j : Fin 0=>Source.Data.val (Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl (first+(j.val+1))))).run (locals,state))=_
   rw [Source.Hoare.run_bind,phase]
   simp only [SourceCapturedByteCommit.plans,List.flatten_cons,List.flatten_nil,List.append_nil]
 | succ count ih =>
   let head := SourceByteStoragePrepared.phaseLog frame (dst.go (.index start)) (typed start) (headerTyped start)
     (payload start) (oldLength start) (count+2+budget-(payload start).length)
   let next := {state with ex:=state.ex.run head}
   have found := captured 0 (by omega)
   have header := headers 0 (by omega)
   have bound := enough 0 (by omega)
   have clearBound := cleanup 0 (by omega)
   simp only [Nat.add_zero,Nat.sub_zero] at found header bound clearBound
   have phase := SourceCapturedBytePhase.run_phase frame writable (dst.go (.index start)) (typed start)
     (headerTyped start) (payload start) (oldLength start) (count+2+budget-(payload start).length)
     first locals state found header
   have fuel : (payload start).length+(count+2+budget-(payload start).length)+4=count+budget+6 := by omega
   rw [fuel] at phase
   have clears : oldLength start-(payload start).length≤
     (payload start).length+(count+2+budget-(payload start).length) := by omega
   simp only [if_pos clears] at phase
   have total : count+1+budget+6=(count+budget+6)+1 := by omega
   rw [total]
   change ((Source.storeData frame (count+budget+6) (.bytes .storage) (dst.go (.index start))
     (Source.Data.val (Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl first)) >>= fun _=>
     Source.storeElems frame (count+budget+6) (.bytes .storage) dst (start+1) (count+1)
       (fun j : Fin (count+1)=>Source.Data.val (Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl (first+(j.val+1))))).run (locals,state))=_
   rw [Source.Hoare.run_bind,phase]
   dsimp only
   have refs : (fun j : Fin (count+1)=>Source.Data.val (Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl (first+(j.val+1))))=
     (fun j : Fin (count+1)=>Source.Data.val (Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl ((first+1)+j.val))) := by
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
     have index : start+(count+1)=(start+1)+count := by omega
     simpa only [index] using short) (by
     intro j member
     have untouched := SourceByteCommitFrames.phase_other frame (dst.go (.index start))
       (dst.go (.index ((start+1)+j))) (typed start) (headerTyped start)
       (payload start) (oldLength start) (count+2+budget-(payload start).length) state.ex (by
         exact SourceCopyReadbacks.index_ne_index dst (by omega)) (by
         intro k same
         have lengths := congrArg (fun p : Source.SPath=>p.steps.length) same
         simp only [Source.SPath.go,List.length_append,List.length_singleton] at lengths
         omega)
     have transported := SourceReadFrames.readLen_transport frame (dst.go (.index ((start+1)+j))) locals state next
       untouched.1 untouched.2
     have old := headers (j+1) (by omega)
     have index : start+(j+1)=(start+1)+j := by omega
     rw [index] at old
     rw [old] at transported
     exact transported)]
   simp only [SourceCapturedByteCommit.plans,List.flatten_cons,Source.run_append]
   rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteTimeout.cleanup_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cleanup_timeout

end Solidity.Lowering.StorageOps.SourceCapturedByteTimeout
