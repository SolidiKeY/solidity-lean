import Solidity.Lowering.StorageOps.SourceCapturedByteCommit
import Solidity.Lowering.StorageOps.SourceByteCaptureSuccessControls

/-! Actual nested storage-reference copy and its snapshot commit phase.
All reads/writes use existing Source operations; no memory-to-storage compiler
or physical representation claim is made. -/
namespace Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls
open Solidity Solidity.Backend.StorageOps
open SourceNestedByteCaptureControls (env left right child address frame Γ locals)
open SourceVaryingByteCaptureControls (seed length)
open SourceByteCaptureSuccessControls (capturedPayload)
open SourceCapturedByteCommit

def bs (j : Nat) : List UInt8 := (List.range' 0 (length j)).map (capturedPayload j)
def oldLength (j : Nat) : Nat := if j=0 then 1 else 0
def typed (i j : Nat) : (.fixedBytes 1 (by decide) : Source.STy)=env.cellTy ((right.go (.index i)).go (.index j)) := rfl
def headerTyped (i : Nat) : (.int Source.IntTy.u256 : Source.STy)=env.cellTy (right.go (.index i)) := rfl
def captured : Source.St env := SourceVaryingByteCaptureControls.after 3
def log (start count budget : Nat) := (plans frame right typed headerTyped bs oldLength budget start count).flatten
def after (start count budget : Nat) : Source.St env := {captured with ex:=captured.ex.run (log start count budget)}
def refs (first count : Nat) : Fin count → Source.Data env.layout (.bytes .memory) :=
 fun j=>Source.Data.val (Source.Val.memRef rfl (first+j.val))
def commit (fuel start count first : Nat) :=
 (Source.storeElems (E:=env) (Γ:=Γ) frame fuel (.bytes .storage) right start count (refs first count)).run (locals,captured)
def whole := (SourceVaryingByteCaptureControls.program 12 left right).run (locals,seed)
def finished : Source.St env := {after 0 3 2 with ex:=((after 0 3 2).ex.apply (SourceStorageCopy.cellOp env frame right (some (.int 3 (by decide)))))}
def oneByte : Source.St env := {captured with ex:=(captured.ex.apply (SourceStorageCopy.cellOp env frame (child (child right 0) 0) (some (.fixedBytes [53] rfl))))}
def client := commit_all frame rfl right typed headerTyped bs oldLength 0 3 2 1 locals captured
 (by
   intro j member
   have h : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases h with rfl | rfl | rfl <;> rfl)
 (by
   intro j member
   have h : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases h with rfl | rfl | rfl <;> decide)
 (by
   intro j member
   have h : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases h with rfl | rfl | rfl <;> decide)
 (by
   intro j member
   have h : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases h with rfl | rfl | rfl <;> rfl)
def runs := [commit 10 0 3 1,whole,commit 9 1 2 2,commit 5 42 0 99,commit 10 0 3 99,commit 5 0 3 1]
def outcomes : Prop := runs=
 [(.ok (),(locals,after 0 3 2)),(.ok (),(locals,finished)),(.ok (),(locals,after 1 2 2)),
  (.ok (),(locals,captured)),(.error (.stuck "dangling memory reference"),(locals,captured)),
  (.error .timeout,(locals,oneByte))]
def word (st : Source.Storage env.layout env.cellTy) (p : Source.SPath) := ((st.read p).bind Source.Val.word).map Fin.val
def raw (st : Source.Storage env.layout env.cellTy) (p : Source.SPath) := (st.cell p).bind SourceNestedByteCaptureControls.bytes
def targetHeaders (st : Source.Storage env.layout env.cellTy) := [right,child right 0,child right 1,child right 2,child right 3].map (word st)
def targetBytes (st : Source.Storage env.layout env.cellTy) :=
 [child (child right 0) 0,child (child right 0) 1,child (child right 1) 0,child (child right 1) 1,
  child (child right 2) 0,child (child right 2) 1,child (child right 3) 0].map (raw st)
def ordered : Prop := runs.map (fun r=>
 (r.2.1,SourceVaryingByteCaptureControls.headerView r.2.2,
  (SourceVaryingByteCaptureControls.bytes r.2.2).take 8,
  targetHeaders (r.2.2.ex.world.accounts address).storage,targetBytes (r.2.2.ex.world.accounts address).storage,
  SourceVaryingByteCaptureControls.heapView r.2.2,r.2.2.ex.journal.length,SourceVaryingByteCaptureControls.context r.2.2))=
 [(some 1,[some 1,some 1,some 2,some 2,some 0],[some [53],none,some [61],some [67],some [71],some [73],none],9),
  (some 3,[some 3,some 1,some 2,some 2,some 0],[some [53],none,some [61],some [67],some [71],some [73],none],10),
  (some 1,[some 1,some 1,some 2,some 2,some 0],[some [17],none,some [61],some [67],some [71],some [73],none],7),
  (some 1,[some 1,some 1,some 0,some 0,some 0],[some [17],none,none,none,none,none,none],1),
  (some 1,[some 1,some 1,some 0,some 0,some 0],[some [17],none,none,none,none,none,none],1),
  (some 1,[some 1,some 1,some 0,some 0,some 0],[some [53],none,none,none,none,none,none],2)].map (fun (outer,hs,vs,j)=>
 (locals,[some 3,outer,some 1,some 2,some 2,some 1],
  [some [53],some [59],some [61],some [67],some [71],some [73],some [97],some [97]],hs,vs,
  (4,[some [9,8],some [53],some [61,67],some [71,73],none]),j,(19,3,some 0,0,[(7,[9,8])],[.bool])))
theorem phase_outcome : commit 10 0 3 1=(.ok (),(locals,after 0 3 2)) := client
def capture_for_whole := SourceByteCaptureSuccess.capture_all frame left 0 3 4 length capturedPayload locals seed (by
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
 (Source.loadMem (E:=env) (Γ:=Γ) frame 11 (.array .memory (.bytes .memory) none) left).run (locals,seed)=
 (.ok (Source.Data.array (l:=.memory) (τ:=.bytes .memory) (n:=none) 3 (fun _ h=>nomatch h) (refs 1 3)),(locals,captured)) := by
 change ((Source.readLen frame left >>= fun n=>Source.loadElems frame 10 (.bytes .memory) left 0 n >>= fun xs=>
   pure (Source.Data.array (l:=.memory) (τ:=.bytes .memory) (n:=none) n (fun _ h=>nomatch h) xs)).run (locals,seed))=_
 have sourceHeader : (Source.readLen (E:=env) (Γ:=Γ) frame left).run (locals,seed)=(.ok 3,(locals,seed)) := rfl
 rw [Source.Hoare.run_bind,sourceHeader]
 dsimp only
 rw [Source.Hoare.run_bind,capture_for_whole]
 rfl

theorem whole_outcome : whole=(.ok (),(locals,finished)) := by
 change ((Source.loadMem frame 11 (.array .memory (.bytes .memory) none) left >>= fun x=>
   Source.storeData frame 11 (.array .storage (.bytes .storage) none) right x).run (locals,seed))=_
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
   (locals,captured)=(.ok (),(locals,after 0 3 2)) := client
 rw [Source.Hoare.run_bind,phaseRun]
 change (Source.writeLen (E:=env) (Γ:=Γ) frame right 3).run (locals,after 0 3 2)=_
 rfl
theorem shifted_outcome : commit 9 1 2 2=(.ok (),(locals,after 1 2 2)) := by rfl
theorem empty_outcome : commit 5 42 0 99=(.ok (),(locals,captured)) := by rfl
theorem dangling_outcome : commit 10 0 3 99=(.error (.stuck "dangling memory reference"),(locals,captured)) := by rfl
theorem timeout_outcome : commit 5 0 3 1=(.error .timeout,(locals,oneByte)) := by rfl
theorem outcome_certificate : outcomes := by
 simp only [outcomes,runs,phase_outcome,whole_outcome,shifted_outcome,empty_outcome,dangling_outcome,timeout_outcome]
theorem observations : ordered := by
 simp only [ordered,runs,phase_outcome,whole_outcome,shifted_outcome,empty_outcome,dangling_outcome,timeout_outcome]
 rfl

def journalRows (s : Source.St env) := s.ex.journal.map fun e=>
 match e with
 | .account a old =>
   (a.val,[left,child left 0,child left 1,child left 2,child left 3].map (word old.storage),
    [child (child left 0) 0,child (child left 0) 1,child (child left 1) 0,child (child left 1) 1,
     child (child left 2) 0,child (child left 2) 1,child (child left 0) 3,child (child left 3) 0].map (raw old.storage),
    targetHeaders old.storage,targetBytes old.storage,old.balance,old.nonce,old.code)
 | .transient a _ => (a.val,[],[],[],[],0,0,none)
def originalRow : List (Option Nat) × List (Option (List Nat)) :=
 ([some 1,some 1,some 0,some 0,some 0],[some [17],none,none,none,none,none,none])
def phaseRows : List (List (Option Nat) × List (Option (List Nat))) :=
 [([some 1,some 1,some 2,some 0,some 0],[some [53],none,some [61],some [67],some [71],some [73],none]),
  ([some 1,some 1,some 2,some 0,some 0],[some [53],none,some [61],some [67],some [71],none,none]),
  ([some 1,some 1,some 2,some 0,some 0],[some [53],none,some [61],some [67],none,none,none]),
  ([some 1,some 1,some 0,some 0,some 0],[some [53],none,some [61],some [67],none,none,none]),
  ([some 1,some 1,some 0,some 0,some 0],[some [53],none,some [61],none,none,none,none]),
  ([some 1,some 1,some 0,some 0,some 0],[some [53],none,none,none,none,none,none]),
  ([some 1,some 1,some 0,some 0,some 0],[some [53],none,none,none,none,none,none]),
  originalRow,originalRow]
def completeRow : List (Option Nat) × List (Option (List Nat)) :=
 ([some 1,some 1,some 2,some 2,some 0],[some [53],none,some [61],some [67],some [71],some [73],none])
def shiftedRows : List (List (Option Nat) × List (Option (List Nat))) :=
 [([some 1,some 1,some 2,some 0,some 0],[some [17],none,some [61],some [67],some [71],some [73],none]),
  ([some 1,some 1,some 2,some 0,some 0],[some [17],none,some [61],some [67],some [71],none,none]),
  ([some 1,some 1,some 2,some 0,some 0],[some [17],none,some [61],some [67],none,none,none]),
  ([some 1,some 1,some 0,some 0,some 0],[some [17],none,some [61],some [67],none,none,none]),
  ([some 1,some 1,some 0,some 0,some 0],[some [17],none,some [61],none,none,none,none]),
  originalRow,originalRow]
def journals : Prop := runs.map (fun r=>journalRows r.2.2)=
 [phaseRows,completeRow::phaseRows,shiftedRows,[originalRow],[originalRow],[originalRow,originalRow]].map
 (fun rows=>rows.map (fun (hs,vs)=>
 (7,[some 3,some 1,some 2,some 2,some 1],
 [some [53],some [59],some [61],some [67],some [71],some [73],some [97],some [97]],hs,vs,19,3,some 0)))
theorem journal_observations : journals := by
 simp only [journals,runs,phase_outcome,whole_outcome,shifted_outcome,empty_outcome,dangling_outcome,timeout_outcome]
 rfl

def fresh (s : Source.St env) := (Source.indexLoc (E:=env) (Γ:=Γ) frame
 (.storRef rfl right : Source.Val env.layout (.array .storage (.bytes .storage) none)) 2).run (locals,s)
def retained (s : Source.St env) := (Source.readLoc (E:=env) (Γ:=Γ) frame
 (τ:=.bytes .storage) (.stor (child right 2))).run (locals,s)
theorem alias_observations :
 (fresh (after 0 3 2),fresh finished,retained (after 0 3 2))=
 ((.error (.revert (Source.panicData .index)),(locals,after 0 3 2)),
  (.ok (.stor (child right 2)),(locals,finished)),
  (.ok (.storRef rfl (child right 2)),(locals,after 0 3 2))) := by rfl

theorem wrong_reference_control :
 raw ((commit 9 0 2 2).2.2.ex.world.accounts address).storage (child (child right 0) 0)=some [61] ∧
 raw ((commit 10 0 3 1).2.2.ex.world.accounts address).storage (child (child right 0) 0)=some [53] := by decide

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls.client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms client

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls.capture_for_whole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capture_for_whole

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls.snapshot_for_whole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms snapshot_for_whole

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls.phase_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms phase_outcome

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls.whole_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whole_outcome

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls.shifted_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms shifted_outcome

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls.empty_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_outcome

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls.dangling_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dangling_outcome

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls.timeout_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms timeout_outcome

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls.outcome_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outcome_certificate

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observations

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls.journal_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms journal_observations

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls.alias_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms alias_observations

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls.wrong_reference_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_reference_control

def dirtyCaptured : Source.St env := {captured with ex:=(captured.ex.run
  [SourceStorageCopy.cellOp env frame (child right 0) (some (.int 3 (by decide))),
  SourceStorageCopy.cellOp env frame (child (child right 0) 1) (some (.fixedBytes [23] rfl)),
  SourceStorageCopy.cellOp env frame (child (child right 0) 2) (some (.fixedBytes [29] rfl)),
  SourceStorageCopy.cellOp env frame (child (child right 0) 4) (some (.fixedBytes [97] rfl))])}
def dirtyOldLength (j : Nat) := if j=0 then 3 else 0
def dirtyAfter : Source.St env := {dirtyCaptured with ex:=(dirtyCaptured.ex.run
  (plans frame right typed headerTyped bs dirtyOldLength 2 0 3).flatten)}
def dirtyRun := (Source.storeElems (E:=env) (Γ:=Γ) frame 10 (.bytes .storage) right 0 3 (refs 1 3)).run (locals,dirtyCaptured)
def dirty_client := commit_all frame rfl right typed headerTyped bs dirtyOldLength 0 3 2 1 locals dirtyCaptured
 (by
   intro j member
   have h : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases h with rfl | rfl | rfl <;> rfl)
 (by
   intro j member
   have h : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases h with rfl | rfl | rfl <;> decide)
 (by
   intro j member
   have h : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases h with rfl | rfl | rfl <;> decide)
 (by
   intro j member
   have h : j=0 ∨ j=1 ∨ j=2 := by omega
   rcases h with rfl | rfl | rfl <;> rfl)
theorem dirty_outcome : dirtyRun=(.ok (),(locals,dirtyAfter)) := dirty_client
def tailRow (st : Source.Storage env.layout env.cellTy) :=
 (word st (child right 0),[0,1,2,4].map (fun j=>raw st (child (child right 0) j)))
theorem dirty_observations :
 (tailRow (dirtyRun.2.2.ex.world.accounts address).storage,
  targetHeaders (dirtyRun.2.2.ex.world.accounts address).storage,
  SourceVaryingByteCaptureControls.heapView dirtyRun.2.2,dirtyRun.2.2.ex.journal.length,
  SourceVaryingByteCaptureControls.context dirtyRun.2.2)=
 ((some 1,[some [53],none,none,some [97]]),[some 1,some 1,some 2,some 2,some 0],
  (4,[some [9,8],some [53],some [61,67],some [71,73],none]),15,(19,3,some 0,0,[(7,[9,8])],[.bool])) := by
 rw [dirty_outcome]
 rfl

theorem dirty_journal_observations : dirtyRun.2.2.ex.journal.map (fun e=>
 match e with
 | .account a old => (a.val,tailRow old.storage,old.balance,old.nonce,old.code)
 | .transient a _ => (a.val,(none,[]),0,0,none))=
 (List.replicate 6 (some 1,[some [53],none,none,some [97]]) ++
 [(some 3,[some [53],none,none,some [97]]),
  (some 3,[some [53],none,some [29],some [97]]),
  (some 3,[some [53],some [23],some [29],some [97]]),
  (some 3,[some [17],some [23],some [29],some [97]]),
  (some 3,[some [17],some [23],some [29],none]),
  (some 3,[some [17],some [23],none,none]),
  (some 3,[some [17],none,none,none]),
  (some 1,[some [17],none,none,none]),(some 1,[some [17],none,none,none])]).map
 (fun row=>(7,row,19,3,some 0)) := by
 rw [dirty_outcome]
 rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls.dirty_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_client

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls.dirty_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_outcome

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls.dirty_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_observations

/-- info: 'Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls.dirty_journal_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dirty_journal_observations

end Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls
