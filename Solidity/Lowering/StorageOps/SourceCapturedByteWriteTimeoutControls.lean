import Solidity.Lowering.StorageOps.SourceCapturedByteWriteTimeout
import Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls

/-! Actual storage-reference copy fails while writing its final captured
payload, including the empty-tail fuel boundary. Cleanup and headers are not
performed; explicit rollback is distinct from a skipped failed-bind continuation. -/
namespace Solidity.Lowering.StorageOps.SourceCapturedByteWriteTimeoutControls
open Solidity Solidity.Backend.StorageOps
open SourceNestedByteCaptureControls (env left right child address frame Γ locals)
open SourceVaryingByteCaptureControls (seed length)
open SourceByteCaptureSuccessControls (capturedPayload)
open SourceCapturedByteCommitControls (typed headerTyped refs captured oldLength)
def bytesPayload (j : Nat) : List UInt8 := (List.range' 0 (length j)).map (capturedPayload j)
def trace := (SourceCapturedByteCommit.plans frame right typed headerTyped bytesPayload oldLength 1 0 2).flatten ++
 SourceByteStorageCopy.byteWrites frame (child right 2) (typed 2) 0 ((bytesPayload 2).take 2)
def after : Source.St env := {captured with ex:=captured.ex.run trace}
def phase := (Source.storeElems (E:=env) (Γ:=Γ) frame 8 (.bytes .storage) right 0 3 (refs 1 3)).run (locals,captured)
def whole := (SourceVaryingByteCaptureControls.program 10 left right).run (locals,seed)
def mark := (seed.ex.journal.length,seed.logs.length,seed.heap)
def rolledBack := (Source.rollbackTo mark : Source.EM env Γ Unit).run whole.2
def naive := ((do
 SourceVaryingByteCaptureControls.program 10 left right
 Source.rollbackTo mark) : Source.EM env Γ Unit).run (locals,seed)
def timeout_client := SourceCapturedByteWriteTimeout.write_timeout frame rfl right typed headerTyped bytesPayload oldLength
 0 2 1 1 locals captured (by
   intro j member
   have cases : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases cases with rfl | rfl | rfl <;> rfl) (by
   intro j member
   have cases : j=0 ∨ j=1 := by omega
   rcases cases with rfl | rfl <;> decide) (by
   intro j member
   have cases : j=0 ∨ j=1 := by omega
   rcases cases with rfl | rfl <;> decide) (by decide) (by
   intro j member
   have cases : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases cases with rfl | rfl | rfl <;> rfl)
theorem phase_outcome : phase=(.error .timeout,(locals,after)) := timeout_client
def capture_for_whole := SourceByteCaptureSuccessControls.full_client
theorem snapshot_for_whole :
 (Source.loadMem (E:=env) (Γ:=Γ) frame 9 (.array .memory (.bytes .memory) none) left).run (locals,seed)=
 (.ok (Source.Data.array (l:=.memory) (τ:=.bytes .memory) (n:=none) 3 (fun _ h=>nomatch h) (refs 1 3)),(locals,captured)) := by
 change ((Source.readLen frame left >>= fun n=>Source.loadElems frame 8 (.bytes .memory) left 0 n >>= fun xs=>
   pure (Source.Data.array (l:=.memory) (τ:=.bytes .memory) (n:=none) n (fun _ h=>nomatch h) xs)).run (locals,seed))=_
 have sourceHeader : (Source.readLen (E:=env) (Γ:=Γ) frame left).run (locals,seed)=(.ok 3,(locals,seed)) := rfl
 rw [Source.Hoare.run_bind,sourceHeader]
 dsimp only
 rw [Source.Hoare.run_bind,capture_for_whole]
 rfl

theorem whole_outcome : whole=(.error .timeout,(locals,after)) := by
 change ((Source.loadMem frame 9 (.array .memory (.bytes .memory) none) left >>= fun x=>
   Source.storeData frame 9 (.array .storage (.bytes .storage) none) right x).run (locals,seed))=_
 rw [Source.Hoare.run_bind,snapshot_for_whole]
 dsimp only
 change ((Source.readLen frame right >>= fun old=>
   Source.storeElems frame 8 (.bytes .storage) right 0 3 (refs 1 3) >>= fun _=>
   Source.deleteRange frame 8 (.bytes .storage) right 3 (old-3) >>= fun _=>
   Source.writeLen frame right 3).run (locals,captured))=_
 have targetHeader : (Source.readLen (E:=env) (Γ:=Γ) frame right).run (locals,captured)=(.ok 1,(locals,captured)) := rfl
 rw [Source.Hoare.run_bind,targetHeader]
 dsimp only
 have phaseRun : (Source.storeElems (E:=env) (Γ:=Γ) frame 8 (.bytes .storage) right 0 3 (refs 1 3)).run
   (locals,captured)=(.error .timeout,(locals,after)) := timeout_client
 rw [Source.Hoare.run_bind,phaseRun]
def success := SourceCapturedByteCommitControls.commit 9 0 3 1
def successState := SourceCapturedByteCommitControls.after 0 3 1
def success_client := SourceCapturedByteCommit.commit_all frame rfl right typed headerTyped bytesPayload oldLength
 0 3 1 1 locals captured (by
   intro j member
   have cases : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases cases with rfl | rfl | rfl <;> rfl) (by
   intro j member
   have cases : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases cases with rfl | rfl | rfl <;> decide) (by
   intro j member
   have cases : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases cases with rfl | rfl | rfl <;> decide) (by
   intro j member
   have cases : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases cases with rfl | rfl | rfl <;> rfl)
theorem success_outcome : success=(.ok (),(locals,successState)) := success_client

theorem naive_outcome : naive=(.error .timeout,(locals,after)) := by
 change ((SourceVaryingByteCaptureControls.program 10 left right >>= fun _=>Source.rollbackTo mark).run (locals,seed))=_
 have failed : (SourceVaryingByteCaptureControls.program 10 left right).run (locals,seed)=
   (.error .timeout,(locals,after)) := whole_outcome
 rw [Source.Hoare.run_bind,failed]

theorem rollback_outcome : rolledBack=(.ok (),(locals,captured)) := by
 unfold rolledBack
 rw [whole_outcome]
 change ((Except.ok () : Except Source.Halt Unit),(locals,
   {captured with
     ex := Source.ExecState.undoN ((captured.ex.run trace).journal.length-captured.ex.journal.length) (captured.ex.run trace)
     logs := captured.logs.drop (captured.logs.length-captured.logs.length)}))=_
 rw [Source.ExecState.journal_run,Nat.add_sub_cancel_left,Nat.sub_self,List.drop_zero,Source.ExecState.undoN_run]

def runs := [phase,whole,naive,rolledBack,success]
def outcomes : Prop := runs=
 [(.error .timeout,(locals,after)),(.error .timeout,(locals,after)),(.error .timeout,(locals,after)),
  (.ok (),(locals,captured)),(.ok (),(locals,successState))]
theorem outcome_certificate : outcomes := by
 simp only [outcomes,runs,phase_outcome,whole_outcome,naive_outcome,rollback_outcome,success_outcome]
def ordered : Prop := runs.map (fun r=>
 (r.2.1,SourceVaryingByteCaptureControls.headerView r.2.2,
  (SourceVaryingByteCaptureControls.bytes r.2.2).take 8,
  SourceCapturedByteCommitControls.targetHeaders (r.2.2.ex.world.accounts address).storage,
  SourceCapturedByteCommitControls.targetBytes (r.2.2.ex.world.accounts address).storage,
  SourceVaryingByteCaptureControls.heapView r.2.2,r.2.2.ex.journal.length,SourceVaryingByteCaptureControls.context r.2.2))=
 [([some 1,some 1,some 2,some 0,some 0],[some [53],none,some [61],some [67],some [71],some [73],none],8),
  ([some 1,some 1,some 2,some 0,some 0],[some [53],none,some [61],some [67],some [71],some [73],none],8),
  ([some 1,some 1,some 2,some 0,some 0],[some [53],none,some [61],some [67],some [71],some [73],none],8),
  ([some 1,some 1,some 0,some 0,some 0],[some [17],none,none,none,none,none,none],1),
  ([some 1,some 1,some 2,some 2,some 0],[some [53],none,some [61],some [67],some [71],some [73],none],9)].map
 (fun (hs,vs,n)=>(locals,[some 3,some 1,some 1,some 2,some 2,some 1],
 [some [53],some [59],some [61],some [67],some [71],some [73],some [97],some [97]],hs,vs,
 (4,[some [9,8],some [53],some [61,67],some [71,73],none]),n,(19,3,some 0,0,[(7,[9,8])],[.bool])))
theorem observations : ordered := by
 simp only [ordered,runs,phase_outcome,whole_outcome,naive_outcome,rollback_outcome,success_outcome]
 rfl

def journals : Prop := runs.map (fun r=>SourceCapturedByteCommitControls.journalRows r.2.2)=
 [SourceCapturedByteCommitControls.phaseRows.drop 1,SourceCapturedByteCommitControls.phaseRows.drop 1,
  SourceCapturedByteCommitControls.phaseRows.drop 1,[SourceCapturedByteCommitControls.originalRow],SourceCapturedByteCommitControls.phaseRows].map
 (fun rows=>rows.map (fun (hs,vs)=>(7,[some 3,some 1,some 2,some 2,some 1],
 [some [53],some [59],some [61],some [67],some [71],some [73],some [97],some [97]],hs,vs,19,3,some 0)))
theorem journal_observations : journals := by
 simp only [journals,runs,phase_outcome,whole_outcome,naive_outcome,rollback_outcome,success_outcome]
 rfl

theorem exact_payload_boundary : ((bytesPayload 2).length=2) ∧
 SourceCapturedByteCommitControls.word (after.ex.world.accounts address).storage (child right 2)=some 0 ∧
 SourceCapturedByteCommitControls.raw (after.ex.world.accounts address).storage (child (child right 2) 1)=some [73] := by
 exact ⟨rfl,rfl,rfl⟩
theorem heap_not_rolled_back : rolledBack.2.2.heap.next=4 ∧ seed.heap.next=1 := by
 rw [rollback_outcome]
 exact ⟨rfl,rfl⟩

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteWriteTimeoutControls.timeout_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms timeout_client

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteWriteTimeoutControls.phase_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms phase_outcome

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteWriteTimeoutControls.capture_for_whole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capture_for_whole

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteWriteTimeoutControls.snapshot_for_whole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms snapshot_for_whole

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteWriteTimeoutControls.whole_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whole_outcome

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteWriteTimeoutControls.success_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms success_outcome

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteWriteTimeoutControls.naive_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms naive_outcome

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteWriteTimeoutControls.rollback_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rollback_outcome

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteWriteTimeoutControls.outcome_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outcome_certificate

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteWriteTimeoutControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observations

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteWriteTimeoutControls.journal_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms journal_observations

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteWriteTimeoutControls.exact_payload_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exact_payload_boundary

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteWriteTimeoutControls.heap_not_rolled_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms heap_not_rolled_back

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteWriteTimeoutControls.success_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms success_client

end Solidity.Lowering.StorageOps.SourceCapturedByteWriteTimeoutControls
