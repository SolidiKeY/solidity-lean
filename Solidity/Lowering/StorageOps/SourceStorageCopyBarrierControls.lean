import Solidity.Lowering.StorageOps.SourceStorageCopyBarrier
import Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls

/-! Populated Source capture-barrier clients. All earlier fixture observations
remain unchanged; full results distinguish timeout, malformed source and self-copy. -/
namespace Solidity.Lowering.StorageOps.SourceStorageCopyBarrierControls
open Solidity
open SourceStorageCopyPrefixControls

def uniform : Prop := ∀ fuel, fuel≤4 → run 2 7 fuel=(.error .timeout,(locals,seed 2 7))
def malformedDestination := (program 4 left bad).run (locals,seed 2 7)
def emptyShort := run 0 0 2
def emptySuccess := run 0 0 3
def outcomes : Prop :=
 (run 2 7 0,run 2 7 4,boundary,self,sourceFailure,malformedDestination,emptyShort,emptySuccess)=
 ((.error .timeout,(locals,seed 2 7)),(.error .timeout,(locals,seed 2 7)),
  (.error .timeout,(locals,prefixState 2 7 1)),(.ok (),(locals,seed 2 7)),
  (.error (.stuck "storage cell without a value"),(locals,seed 2 7)),
  (.error .timeout,(locals,seed 2 7)),(.error .timeout,(locals,seed 0 0)),
  (.ok (),(locals,after 0 0)))
def ordered : Prop :=
 [run 2 7 0,run 2 7 4,boundary,self,sourceFailure,malformedDestination,emptyShort,emptySuccess].map
   (fun r => (view r.2.2,rawView r.2.2,context r.2.2)) =
 [([some 2,some 53,some 59,some 61,some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],1),
  ([some 2,some 53,some 59,some 61,some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],1),
  ([some 2,some 53,some 59,some 61,some 7,some 53,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],2),
  ([some 2,some 53,some 59,some 61,some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],1),
  ([some 2,some 53,some 59,some 61,some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],1),
  ([some 2,some 53,some 59,some 61,some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],1),
  ([some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],1),
  ([some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],2)].map
  (fun (row,journalLength) => (row,row,(some 41,journalLength,19,3,some 0,0,true,0,[(7,[9,8]),(13,[7])],[.bool])))
def journals : Prop :=
 (journalRows (run 2 7 4).2.2,rawJournalRows (run 2 7 4).2.2,
  journalRows boundary.2.2,rawJournalRows boundary.2.2)=
 (([(7,[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99],19,3,some 0)]),
  ([(7,[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99],19,3,some 0)]),
  ([[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],
    [some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]].map (fun row => (7,row,19,3,some 0))),
  ([[some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],
    [some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]].map (fun row => (7,row,19,3,some 0))))
theorem uniform_certificate : uniform := by
 intro fuel short
 exact SourceStorageCopyBarrier.copy_timeout frame Source.IntTy.u256 left right fuel 2 SourceStorageCopyPrefixControls.payload
   (locals,seed 2 7) (by decide) short rfl (reads_two 7)

theorem outcome_certificate : outcomes := by rfl
theorem observations : ordered := by rfl
theorem journal_observations : journals := by rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyBarrierControls.uniform_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uniform_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyBarrierControls.outcome_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outcome_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyBarrierControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observations
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyBarrierControls.journal_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms journal_observations
end Solidity.Lowering.StorageOps.SourceStorageCopyBarrierControls
