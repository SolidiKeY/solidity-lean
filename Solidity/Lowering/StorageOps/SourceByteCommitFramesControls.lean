import Solidity.Lowering.StorageOps.SourceByteCommitFrames
import Solidity.Lowering.StorageOps.SourceCapturedByteCommitControls

/-! OLD destination headers suffice for the concrete snapshot commit client
because all earlier sibling operations frame them. Ordered observations retain
raw/default and fresh/retained distinctions; same-target reads are a negative. -/
namespace Solidity.Lowering.StorageOps.SourceByteCommitFramesControls
open Solidity Solidity.Backend.StorageOps
open SourceNestedByteCaptureControls (env left right child address frame Γ locals)
open SourceCapturedByteCommitControls (typed headerTyped bs oldLength captured)
open SourceByteCommitFrames

def atPrefix (j : Nat) : Source.St env := {captured with ex:=(captured.ex.run
  ((SourceCapturedByteCommit.plans frame right typed headerTyped bs oldLength 2 0 3).take j).flatten)}
def header_client (j : Nat) (within : j≤3) :=
 prefix_header frame right typed headerTyped bs oldLength 2 0 3 j locals captured within
def oldHeaders : ∀ j<3,(Source.readLen (E:=env) (Γ:=Γ) frame (child right j)).run (locals,captured)=
 (.ok (oldLength j),(locals,captured)) := by
 intro j member
 have cases : j=0 ∨ j=1 ∨ j=2 := by omega
 rcases cases with rfl | rfl | rfl <;> rfl

def old_header_commit_client := SourceCapturedByteCommit.commit_all frame rfl right typed headerTyped bs oldLength
 0 3 2 1 locals captured (by
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
   have transported := header_client j (by omega)
   simp only [Nat.zero_add] at transported
   have input : (Source.readLen (E:=env) (Γ:=Γ) frame (right.go (.index j))).run (locals,captured)=
     (.ok (oldLength j),(locals,captured)) := oldHeaders j member
   rw [input] at transported
   simpa only [Nat.zero_add] using transported)

def reads := [0,1,2,3].map (fun j=>(Source.readLen (E:=env) (Γ:=Γ) frame (child right j)).run (locals,atPrefix j))
def outcomes : Prop := reads=
 [(.ok 1,(locals,atPrefix 0)),(.ok 0,(locals,atPrefix 1)),(.ok 0,(locals,atPrefix 2)),(.ok 0,(locals,atPrefix 3))]
def ordered : Prop := [0,1,2,3].map (fun j=>
 (SourceVaryingByteCaptureControls.headerView (atPrefix j),
  (SourceVaryingByteCaptureControls.bytes (atPrefix j)).take 8,
  SourceCapturedByteCommitControls.targetHeaders ((atPrefix j).ex.world.accounts address).storage,
  SourceCapturedByteCommitControls.targetBytes ((atPrefix j).ex.world.accounts address).storage,
  SourceVaryingByteCaptureControls.heapView (atPrefix j),(atPrefix j).ex.journal.length,
  SourceVaryingByteCaptureControls.context (atPrefix j)))=
 [([some 1,some 1,some 0,some 0,some 0],[some [17],none,none,none,none,none,none],1),
  ([some 1,some 1,some 0,some 0,some 0],[some [53],none,none,none,none,none,none],3),
  ([some 1,some 1,some 2,some 0,some 0],[some [53],none,some [61],some [67],none,none,none],6),
  ([some 1,some 1,some 2,some 2,some 0],[some [53],none,some [61],some [67],some [71],some [73],none],9)].map
 (fun (hs,vs,n)=>([some 3,some 1,some 1,some 2,some 2,some 1],
 [some [53],some [59],some [61],some [67],some [71],some [73],some [97],some [97]],hs,vs,
 (4,[some [9,8],some [53],some [61,67],some [71,73],none]),n,(19,3,some 0,0,[(7,[9,8])],[.bool])))
theorem outcome_certificate : outcomes := by rfl
theorem observations : ordered := by rfl

def journals : Prop := [0,1,2,3].map (fun j=>SourceCapturedByteCommitControls.journalRows (atPrefix j))=
 [SourceCapturedByteCommitControls.phaseRows.drop 8,SourceCapturedByteCommitControls.phaseRows.drop 6,
  SourceCapturedByteCommitControls.phaseRows.drop 3,SourceCapturedByteCommitControls.phaseRows].map
 (fun rows=>rows.map (fun (hs,vs)=>(7,[some 3,some 1,some 2,some 2,some 1],
 [some [53],some [59],some [61],some [67],some [71],some [73],some [97],some [97]],hs,vs,19,3,some 0)))
theorem journal_observations : journals := by rfl

def missing : Source.SPath := SourceVaryingByteCaptureControls.missing
def outside_client := plans_prefix_other frame right missing typed headerTyped bs oldLength 2 0 3 3 captured.ex (by decide)
 (by
   intro j member same
   have different : missing.root≠right.root := by decide
   have rooted := congrArg Source.SPath.root same
   exact different rooted) (by
   intro j member k same
   have different : missing.root≠right.root := by decide
   have rooted := congrArg Source.SPath.root same
   exact different rooted)
def outside_read_client := SourceReadFrames.readLen_transport frame missing locals captured (atPrefix 3) outside_client.1 outside_client.2
theorem outside_failure : (Source.readLen (E:=env) (Γ:=Γ) frame missing).run (locals,atPrefix 3)=
 (.error (.stuck "storage cell without a value"),(locals,atPrefix 3)) := by rfl

theorem changed_visited_header :
 ((Source.readLen (E:=env) (Γ:=Γ) frame (child right 1)).run (locals,captured)).1=.ok 0 ∧
 ((Source.readLen (E:=env) (Γ:=Γ) frame (child right 1)).run (locals,atPrefix 2)).1=.ok 2 := by
 exact ⟨rfl,rfl⟩

/-- info: 'Solidity.Lowering.StorageOps.SourceByteCommitFramesControls.header_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms header_client

/-- info: 'Solidity.Lowering.StorageOps.SourceByteCommitFramesControls.oldHeaders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms oldHeaders

/-- info: 'Solidity.Lowering.StorageOps.SourceByteCommitFramesControls.old_header_commit_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms old_header_commit_client

/-- info: 'Solidity.Lowering.StorageOps.SourceByteCommitFramesControls.outcome_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outcome_certificate

/-- info: 'Solidity.Lowering.StorageOps.SourceByteCommitFramesControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observations

/-- info: 'Solidity.Lowering.StorageOps.SourceByteCommitFramesControls.journal_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms journal_observations

/-- info: 'Solidity.Lowering.StorageOps.SourceByteCommitFramesControls.outside_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outside_client

/-- info: 'Solidity.Lowering.StorageOps.SourceByteCommitFramesControls.outside_read_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outside_read_client

/-- info: 'Solidity.Lowering.StorageOps.SourceByteCommitFramesControls.outside_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outside_failure

/-- info: 'Solidity.Lowering.StorageOps.SourceByteCommitFramesControls.changed_visited_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms changed_visited_header

end Solidity.Lowering.StorageOps.SourceByteCommitFramesControls
