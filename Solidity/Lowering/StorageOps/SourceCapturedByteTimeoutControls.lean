import Solidity.Lowering.StorageOps.SourceCapturedByteTimeout
import Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls

/-! Actual storage-reference copy timeout after earlier children commit.
The last child clears a strict stale-tail prefix without its header; explicit
rollback restores journaled state but does not undo snapshot heap allocations. -/
namespace Solidity.Lowering.StorageOps.SourceCapturedByteTimeoutControls
open Solidity Solidity.Backend.StorageOps
open SourceNestedByteCaptureControls (env left right child address frame Γ locals)
open SourceVaryingByteCaptureControls (length)
open SourceByteCaptureSuccessControls (capturedPayload)
open SourceCapturedByteCommitControls (typed headerTyped refs)

def bytesPayload (j : Nat) : List UInt8 := (List.range' 0 (length j)).map (capturedPayload j)
def dirtyLog : List (Source.Op env.layout env.lay env.lay) :=
 SourceStorageCopy.cellOp env frame (child right 2) (some (.int 6 (by decide))) ::
 ([(0,5),(1,7),(2,11),(3,13),(4,17),(5,19),(8,97)] : List (Nat × UInt8)).map
 (fun (j,b)=>SourceStorageCopy.cellOp env frame (child (child right 2) j) (some (.fixedBytes [b] rfl)))
def initial : Source.St env := {SourceVaryingByteCaptureControls.seed with
 ex:=SourceVaryingByteCaptureControls.seed.ex.run dirtyLog}
def captured : Source.St env := (List.range' 0 3).foldl
 (fun s j=>SourceNestedByteValues.allocateAt (length j) capturedPayload s j) initial
def oldLength (j : Nat) := if j=0 then 1 else if j=2 then 6 else 0
def trace (budget : Nat) := (SourceCapturedByteCommit.plans frame right typed headerTyped bytesPayload oldLength budget 0 3).flatten
def after (budget : Nat) : Source.St env := {captured with ex:=captured.ex.run (trace budget)}
def phase := (Source.storeElems (E:=env) (Γ:=Γ) frame 10 (.bytes .storage) right 0 3 (refs 1 3)).run (locals,captured)
def whole := (SourceVaryingByteCaptureControls.program 12 left right).run (locals,initial)
def mark := (initial.ex.journal.length,initial.logs.length,initial.heap)
def rolledBack := (Source.rollbackTo mark : Source.EM env Γ Unit).run whole.2
def naive := ((do
 SourceVaryingByteCaptureControls.program 12 left right
 Source.rollbackTo mark) : Source.EM env Γ Unit).run (locals,initial)
def timeout_client := SourceCapturedByteTimeout.cleanup_timeout frame rfl right typed headerTyped bytesPayload oldLength
 0 2 2 1 locals captured (by
   intro j member
   have cases : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases cases with rfl | rfl | rfl <;> rfl) (by
   intro j member
   have cases : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases cases with rfl | rfl | rfl <;> decide) (by
   intro j member
   have cases : j=0 ∨ j=1 := by omega
   rcases cases with rfl | rfl <;> decide) (by decide) (by
   intro j member
   have cases : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases cases with rfl | rfl | rfl <;> rfl)
theorem phase_outcome : phase=(.error .timeout,(locals,after 2)) := timeout_client
def capture_for_whole := SourceByteCaptureSuccess.capture_all frame left 0 3 4 length capturedPayload locals initial (by
 intro j member
 have cases : j=0 ∨ j=1 ∨ j=2 := by omega
 rcases cases with rfl | rfl | rfl <;> decide) (by
 intro j member
 have cases : j=0 ∨ j=1 ∨ j=2 := by omega
 rcases cases with rfl | rfl | rfl <;> rfl) (by
 intro j member k bound
 have outer : j=0 ∨ j=1 ∨ j=2 := by omega
 have inner : k=0 ∨ k=1 := by unfold length at bound; split at bound <;> omega
 rcases outer with rfl | rfl | rfl <;> rcases inner with rfl | rfl <;> rfl)
theorem snapshot_for_whole :
 (Source.loadMem (E:=env) (Γ:=Γ) frame 11 (.array .memory (.bytes .memory) none) left).run (locals,initial)=
 (.ok (Source.Data.array (l:=.memory) (τ:=.bytes .memory) (n:=none) 3 (fun _ h=>nomatch h) (refs 1 3)),(locals,captured)) := by
 change ((Source.readLen frame left >>= fun n=>Source.loadElems frame 10 (.bytes .memory) left 0 n >>= fun xs=>
   pure (Source.Data.array (l:=.memory) (τ:=.bytes .memory) (n:=none) n (fun _ h=>nomatch h) xs)).run (locals,initial))=_
 have sourceHeader : (Source.readLen (E:=env) (Γ:=Γ) frame left).run (locals,initial)=(.ok 3,(locals,initial)) := rfl
 rw [Source.Hoare.run_bind,sourceHeader]
 dsimp only
 rw [Source.Hoare.run_bind,capture_for_whole]
 rfl

theorem whole_outcome : whole=(.error .timeout,(locals,after 2)) := by
 change ((Source.loadMem frame 11 (.array .memory (.bytes .memory) none) left >>= fun x=>
   Source.storeData frame 11 (.array .storage (.bytes .storage) none) right x).run (locals,initial))=_
 rw [Source.Hoare.run_bind,snapshot_for_whole]
 dsimp only
 change ((Source.readLen frame right >>= fun old=>
   Source.storeElems frame 10 (.bytes .storage) right 0 3 (refs 1 3) >>= fun _=>
   Source.deleteRange frame 10 (.bytes .storage) right 3 (old-3) >>= fun _=>
   Source.writeLen frame right 3).run (locals,captured))=_
 have targetHeader : (Source.readLen (E:=env) (Γ:=Γ) frame right).run (locals,captured)=(.ok 1,(locals,captured)) := rfl
 rw [Source.Hoare.run_bind,targetHeader]
 dsimp only
 have phaseRun : (Source.storeElems (E:=env) (Γ:=Γ) frame 10 (.bytes .storage) right 0 3 (refs 1 3)).run
   (locals,captured)=(.error .timeout,(locals,after 2)) := timeout_client
 rw [Source.Hoare.run_bind,phaseRun]
def success := (Source.storeElems (E:=env) (Γ:=Γ) frame 11 (.bytes .storage) right 0 3 (refs 1 3)).run (locals,captured)
def success_client := SourceCapturedByteCommit.commit_all frame rfl right typed headerTyped bytesPayload oldLength
 0 3 3 1 locals captured (by
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
theorem success_outcome : success=(.ok (),(locals,after 3)) := success_client

theorem naive_outcome : naive=(.error .timeout,(locals,after 2)) := by
 change ((SourceVaryingByteCaptureControls.program 12 left right >>= fun _=>Source.rollbackTo mark).run (locals,initial))=_
 have failed : (SourceVaryingByteCaptureControls.program 12 left right).run (locals,initial)=
   (.error .timeout,(locals,after 2)) := whole_outcome
 rw [Source.Hoare.run_bind,failed]

theorem rollback_outcome : rolledBack=(.ok (),(locals,captured)) := by
 unfold rolledBack
 rw [whole_outcome]
 change ((Except.ok () : Except Source.Halt Unit),(locals,
   {captured with
     ex := Source.ExecState.undoN ((captured.ex.run (trace 2)).journal.length-captured.ex.journal.length)
       (captured.ex.run (trace 2))
     logs := captured.logs.drop (captured.logs.length-captured.logs.length)}))=_
 rw [Source.ExecState.journal_run,Nat.add_sub_cancel_left,Nat.sub_self,List.drop_zero,Source.ExecState.undoN_run]

def tailRow (st : Source.Storage env.layout env.cellTy) :=
 (SourceCapturedByteCommitControls.targetHeaders st,
 [0,1,2,3,4,5,8].map (fun j=>SourceCapturedByteCommitControls.raw st (child (child right 2) j)))
def runs := [phase,whole,naive,rolledBack,success]
def outcomes : Prop := runs=
 [(.error .timeout,(locals,after 2)),(.error .timeout,(locals,after 2)),(.error .timeout,(locals,after 2)),
  (.ok (),(locals,captured)),(.ok (),(locals,after 3))]
theorem outcome_certificate : outcomes := by
 simp only [outcomes,runs,phase_outcome,whole_outcome,naive_outcome,rollback_outcome,success_outcome]
def ordered : Prop := runs.map (fun r=>
 (r.2.1,SourceVaryingByteCaptureControls.headerView r.2.2,
  (SourceVaryingByteCaptureControls.bytes r.2.2).take 8,
  tailRow (r.2.2.ex.world.accounts address).storage,
  SourceVaryingByteCaptureControls.heapView r.2.2,r.2.2.ex.journal.length,SourceVaryingByteCaptureControls.context r.2.2))=
 ([([some 1,some 1,some 2,some 6,some 0],[some [71],some [73],none,none,none,some [19],some [97]],19),
   ([some 1,some 1,some 2,some 6,some 0],[some [71],some [73],none,none,none,some [19],some [97]],19),
   ([some 1,some 1,some 2,some 6,some 0],[some [71],some [73],none,none,none,some [19],some [97]],19),
   ([some 1,some 1,some 0,some 6,some 0],[some [5],some [7],some [11],some [13],some [17],some [19],some [97]],9),
   ([some 1,some 1,some 2,some 2,some 0],[some [71],some [73],none,none,none,none,some [97]],21)]).map
 (fun (hs,vs,n)=>(locals,[some 3,some 1,some 1,some 2,some 2,some 1],
 [some [53],some [59],some [61],some [67],some [71],some [73],some [97],some [97]],(hs,vs),
 (4,[some [9,8],some [53],some [61,67],some [71,73],none]),n,(19,3,some 0,0,[(7,[9,8])],[.bool])))
theorem observations : ordered := by
 simp only [ordered,runs,phase_outcome,whole_outcome,naive_outcome,rollback_outcome,success_outcome]
 rfl

theorem heap_not_rolled_back : rolledBack.2.2.heap.next=4 ∧ initial.heap.next=1 := by
 rw [rollback_outcome]
 exact ⟨rfl,rfl⟩

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteTimeoutControls.timeout_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms timeout_client

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteTimeoutControls.phase_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms phase_outcome

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteTimeoutControls.capture_for_whole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capture_for_whole

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteTimeoutControls.snapshot_for_whole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms snapshot_for_whole

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteTimeoutControls.whole_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whole_outcome

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteTimeoutControls.success_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms success_client

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteTimeoutControls.success_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms success_outcome

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteTimeoutControls.naive_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms naive_outcome

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteTimeoutControls.rollback_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rollback_outcome

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteTimeoutControls.outcome_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outcome_certificate

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteTimeoutControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observations

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteTimeoutControls.heap_not_rolled_back' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms heap_not_rolled_back

def sourceCells (st : Source.Storage env.layout env.cellTy) :=
 ([left,child left 0,child left 1,child left 2,child left 3].map (SourceCapturedByteCommitControls.word st),
 [child (child left 0) 0,child (child left 0) 1,child (child left 1) 0,child (child left 1) 1,
  child (child left 2) 0,child (child left 2) 1,child (child left 0) 3,child (child left 3) 0].map (SourceCapturedByteCommitControls.raw st))
def frontCells (st : Source.Storage env.layout env.cellTy) :=
 [child (child right 0) 0,child (child right 1) 0,child (child right 1) 1].map (SourceCapturedByteCommitControls.raw st)
def journalRows (s : Source.St env) := s.ex.journal.map fun e=>
 match e with
 | .account a old => (a.val,sourceCells old.storage,tailRow old.storage,frontCells old.storage,old.balance.val,old.nonce,old.code)
 | .transient a _ => (a.val,([],[]),([],[]),[],0,0,none)
def setupRows : List (List (Option Nat) × List (Option (List Nat)) × List (Option (List Nat))) := [
 ([some 1,some 1,some 0,some 6,some 0],[some [5],some [7],some [11],some [13],some [17],some [19],none],[some [17],none,none]),
 ([some 1,some 1,some 0,some 6,some 0],[some [5],some [7],some [11],some [13],some [17],none,none],[some [17],none,none]),
 ([some 1,some 1,some 0,some 6,some 0],[some [5],some [7],some [11],some [13],none,none,none],[some [17],none,none]),
 ([some 1,some 1,some 0,some 6,some 0],[some [5],some [7],some [11],none,none,none,none],[some [17],none,none]),
 ([some 1,some 1,some 0,some 6,some 0],[some [5],some [7],none,none,none,none,none],[some [17],none,none]),
 ([some 1,some 1,some 0,some 6,some 0],[some [5],none,none,none,none,none,none],[some [17],none,none]),
 ([some 1,some 1,some 0,some 6,some 0],[none,none,none,none,none,none,none],[some [17],none,none]),
 ([some 1,some 1,some 0,some 0,some 0],[none,none,none,none,none,none,none],[some [17],none,none]),
 ([some 1,some 1,some 0,some 0,some 0],[none,none,none,none,none,none,none],[some [17],none,none])]
def commitFailureRows : List (List (Option Nat) × List (Option (List Nat)) × List (Option (List Nat))) := [
 ([some 1,some 1,some 2,some 6,some 0],[some [71],some [73],none,none,some [17],some [19],some [97]],[some [53],some [61],some [67]]),
 ([some 1,some 1,some 2,some 6,some 0],[some [71],some [73],none,some [13],some [17],some [19],some [97]],[some [53],some [61],some [67]]),
 ([some 1,some 1,some 2,some 6,some 0],[some [71],some [73],some [11],some [13],some [17],some [19],some [97]],[some [53],some [61],some [67]]),
 ([some 1,some 1,some 2,some 6,some 0],[some [71],some [7],some [11],some [13],some [17],some [19],some [97]],[some [53],some [61],some [67]]),
 ([some 1,some 1,some 2,some 6,some 0],[some [5],some [7],some [11],some [13],some [17],some [19],some [97]],[some [53],some [61],some [67]]),
 ([some 1,some 1,some 0,some 6,some 0],[some [5],some [7],some [11],some [13],some [17],some [19],some [97]],[some [53],some [61],some [67]]),
 ([some 1,some 1,some 0,some 6,some 0],[some [5],some [7],some [11],some [13],some [17],some [19],some [97]],[some [53],some [61],none]),
 ([some 1,some 1,some 0,some 6,some 0],[some [5],some [7],some [11],some [13],some [17],some [19],some [97]],[some [53],none,none]),
 ([some 1,some 1,some 0,some 6,some 0],[some [5],some [7],some [11],some [13],some [17],some [19],some [97]],[some [53],none,none]),
 ([some 1,some 1,some 0,some 6,some 0],[some [5],some [7],some [11],some [13],some [17],some [19],some [97]],[some [17],none,none])]
def extraSuccessRows : List (List (Option Nat) × List (Option (List Nat)) × List (Option (List Nat))) := [
 ([some 1,some 1,some 2,some 6,some 0],[some [71],some [73],none,none,none,none,some [97]],[some [53],some [61],some [67]]),
 ([some 1,some 1,some 2,some 6,some 0],[some [71],some [73],none,none,none,some [19],some [97]],[some [53],some [61],some [67]])]
def journals : Prop := runs.map (fun r=>journalRows r.2.2)=
 [commitFailureRows++setupRows,commitFailureRows++setupRows,commitFailureRows++setupRows,
  setupRows,extraSuccessRows++commitFailureRows++setupRows].map
 (fun rows=>rows.map (fun (hs,vs,front)=>(7,([some 3,some 1,some 2,some 2,some 1],
 [some [53],some [59],some [61],some [67],some [71],some [73],some [97],some [97]]),(hs,vs),front,19,3,some 0)))
theorem journal_observations : journals := by
 simp only [journals,runs,phase_outcome,whole_outcome,naive_outcome,rollback_outcome,success_outcome]
 rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteTimeoutControls.journal_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms journal_observations

end Solidity.Lowering.StorageOps.SourceCapturedByteTimeoutControls
