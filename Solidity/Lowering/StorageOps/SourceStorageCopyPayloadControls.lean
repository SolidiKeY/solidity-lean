import Solidity.Lowering.StorageOps.SourceStorageCopyPayload
import Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls
import Solidity.Lowering.StorageOps.SourceArrayIndex

/-! Actual Source payload-failure clients with complete ordered observations.
A partially written retained slot can still fail fresh indexing. -/
namespace Solidity.Lowering.StorageOps.SourceStorageCopyPayloadControls
open Solidity
open SourceStorageCopyPrefixControls

def two := run 2 7 5
def three := run 3 7 6
def emptyDestination := run 2 0 5
def shortDestination := run 2 1 5
def snapshot := run 3 7 5
def staticRefusal := (program 5 left right {frame with static:=true}).run (locals,seed 2 7)
def wrongType := (program 5 left bad).run (locals,seed 2 7)
def selfCopy := (program 6 right right).run (locals,seed 2 7)
def prepared := run 3 7 7

def two_certificate := SourceStorageCopyPayload.copy_prefix frame rfl Source.IntTy.u256 left right (by decide)
  1 7 SourceStorageCopyPrefixControls.payload rfl locals (seed 2 7) rfl (reads_two 7) rfl
def three_certificate := SourceStorageCopyPayload.copy_prefix frame rfl Source.IntTy.u256 left right (by decide)
  2 7 SourceStorageCopyPrefixControls.payload rfl locals (seed 3 7) rfl reads_three rfl
def empty_destination_certificate := SourceStorageCopyPayload.copy_prefix frame rfl Source.IntTy.u256 left right (by decide)
  1 0 SourceStorageCopyPrefixControls.payload rfl locals (seed 2 0) rfl (reads_two 0) rfl
def short_destination_certificate := SourceStorageCopyPayload.copy_prefix frame rfl Source.IntTy.u256 left right (by decide)
  1 1 SourceStorageCopyPrefixControls.payload rfl locals (seed 2 1) rfl (reads_two 1) rfl

def outcomes : Prop :=
 (two,three,emptyDestination,shortDestination,snapshot,staticRefusal,wrongType,selfCopy,prepared)=
 ((.error .timeout,(locals,prefixState 2 7 1)),(.error .timeout,(locals,prefixState 3 7 2)),
  (.error .timeout,(locals,prefixState 2 0 1)),(.error .timeout,(locals,prefixState 2 1 1)),
  (.error .timeout,(locals,seed 3 7)),(.error (.revert []),(locals,seed 2 7)),
  (.error (.stuck "storage cell type"),(locals,seed 2 7)),(.ok (),(locals,seed 2 7)),
  (.ok (),(locals,after 3 7)))
def ordered : Prop :=
 [two,three,emptyDestination,shortDestination,snapshot,staticRefusal,wrongType,selfCopy,prepared].map
   (fun r => (r.2.1,view r.2.2,rawView r.2.2,context r.2.2)) =
 [([some 2,some 53,some 59,some 61,some 7,some 53,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 2,some 53,some 59,some 61,some 7,some 53,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],2),([some 3,some 53,some 59,some 61,some 7,some 53,some 59,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 3,some 53,some 59,some 61,some 7,some 53,some 59,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],3),([some 2,some 53,some 59,some 61,some 0,some 53,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 2,some 53,some 59,some 61,some 0,some 53,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],2),([some 2,some 53,some 59,some 61,some 1,some 53,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 2,some 53,some 59,some 61,some 1,some 53,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],2),([some 3,some 53,some 59,some 61,some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 3,some 53,some 59,some 61,some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],1),([some 2,some 53,some 59,some 61,some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 2,some 53,some 59,some 61,some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],1),([some 2,some 53,some 59,some 61,some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 2,some 53,some 59,some 61,some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],1),([some 2,some 53,some 59,some 61,some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 2,some 53,some 59,some 61,some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],1),([some 3,some 53,some 59,some 61,some 3,some 53,some 59,some 61,some 0,some 0,some 0,some 0,some 97,some 1,some 101,none],[some 3,some 53,some 59,some 61,some 3,some 53,some 59,some 61,none,none,none,none,some 97,some 1,some 101,none],9)].map (fun (normal,raw,journalLength) =>
  (locals,normal,raw,(some 41,journalLength,19,3,some 0,0,true,0,[(7,[9,8]),(13,[7])],[.bool])))
def journals : Prop :=
 [two,three,emptyDestination,shortDestination,snapshot,staticRefusal,wrongType,selfCopy,prepared].map
   (fun r => (journalRows r.2.2,rawJournalRows r.2.2)) =
 [([[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]]),([[some 7,some 53,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[some 7,some 53,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]]),([[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]]),([[some 1,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 1,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[some 1,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 1,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]]),([[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]]),([[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]]),([[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]]),([[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]]),([[some 7,some 53,some 59,some 61,some 0,some 0,some 0,some 0,some 97,some 101],[some 7,some 53,some 59,some 61,some 0,some 0,some 0,some 83,some 97,some 101],[some 7,some 53,some 59,some 61,some 0,some 0,some 79,some 83,some 97,some 101],[some 7,some 53,some 59,some 61,some 0,some 73,some 79,some 83,some 97,some 101],[some 7,some 53,some 59,some 61,some 71,some 73,some 79,some 83,some 97,some 101],[some 7,some 53,some 59,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 7,some 53,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[some 7,some 53,some 59,some 61,none,none,none,none,some 97,some 101],[some 7,some 53,some 59,some 61,none,none,none,some 83,some 97,some 101],[some 7,some 53,some 59,some 61,none,none,some 79,some 83,some 97,some 101],[some 7,some 53,some 59,some 61,none,some 73,some 79,some 83,some 97,some 101],[some 7,some 53,some 59,some 61,some 71,some 73,some 79,some 83,some 97,some 101],[some 7,some 53,some 59,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 7,some 53,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]])].map (fun (normal,raw) =>
   (normal.map (fun row => (7,row,19,3,some 0)),raw.map (fun row => (7,row,19,3,some 0))))
def fresh (s : Source.St env) (i : Nat) :=
 (SourceArrayIndex.read (E:=env) (Γ:=Γ) frame right (.int Source.IntTy.u256) i).run (locals,s)
def retained (s : Source.St env) (i : Nat) :=
 (Source.readLoc (E:=env) (Γ:=Γ) frame (.stor (elem right i) : Source.Loc env.layout Γ (.int Source.IntTy.u256))).run (locals,s)
def aliases : Prop :=
 (fresh emptyDestination.2.2 0,retained emptyDestination.2.2 0,
  fresh shortDestination.2.2 0,fresh shortDestination.2.2 1,retained shortDestination.2.2 1,
  fresh prepared.2.2 2,fresh prepared.2.2 3,retained prepared.2.2 3)=
 ((.error (.revert (Source.panicData .index)),(locals,emptyDestination.2.2)),
  (.ok (.int 53 (by decide)),(locals,emptyDestination.2.2)),
  (.ok (.int 53 (by decide)),(locals,shortDestination.2.2)),
  (.error (.revert (Source.panicData .index)),(locals,shortDestination.2.2)),
  (.ok (.int 17 (by decide)),(locals,shortDestination.2.2)),
  (.ok (.int 61 (by decide)),(locals,prepared.2.2)),
  (.error (.revert (Source.panicData .index)),(locals,prepared.2.2)),
  (.ok (.int 0 (by decide)),(locals,prepared.2.2)))
theorem outcome_certificate : outcomes := by
 unfold outcomes
 rw [show two=(.error .timeout,(locals,prefixState 2 7 1)) from two_certificate,
   show three=(.error .timeout,(locals,prefixState 3 7 2)) from three_certificate,
   show emptyDestination=(.error .timeout,(locals,prefixState 2 0 1)) from empty_destination_certificate,
   show shortDestination=(.error .timeout,(locals,prefixState 2 1 1)) from short_destination_certificate,
   show prepared=(.ok (),(locals,after 3 7)) from SourceStorageCopyPrefixControls.varied_certificate]
 rfl

theorem observations : ordered := by rfl
theorem journal_observations : journals := by rfl
theorem alias_observations : aliases := by rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPayloadControls.two_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms two_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPayloadControls.three_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms three_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPayloadControls.empty_destination_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_destination_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPayloadControls.short_destination_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_destination_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPayloadControls.outcome_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outcome_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPayloadControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observations
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPayloadControls.journal_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms journal_observations
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPayloadControls.alias_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms alias_observations
end Solidity.Lowering.StorageOps.SourceStorageCopyPayloadControls
