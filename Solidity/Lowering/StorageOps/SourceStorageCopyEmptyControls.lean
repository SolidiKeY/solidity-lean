import Solidity.Lowering.StorageOps.SourceStorageCopyEmpty
import Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls
import Solidity.Lowering.StorageOps.SourceArrayIndex

/-! Empty-copy boundary, header materialization and exact failure ordering.
Every result/observation row is retained, including raw absent versus default0. -/
namespace Solidity.Lowering.StorageOps.SourceStorageCopyEmptyControls
open Solidity
open SourceStorageCopyPrefixControls

def bothEmpty := run 0 0 3
def liveTail := run 0 3 3
def tooShort := run 0 0 2
def firstClear := run 0 3 4
def samePath := (program 3 right right).run (locals,seed 0 0)
def staticEmpty := (program 3 left right {frame with static:=true}).run (locals,seed 0 0)
def staticTail := (program 3 left right {frame with static:=true}).run (locals,seed 0 3)
def badTarget := (program 3 left bad).run (locals,seed 0 0)
def missingSource := (program 3 missing right).run (locals,seed 0 0)
def absentState : Source.St env :=
 {seed 0 0 with ex:=(seed 0 0).ex.apply (Solidity.Backend.StorageOps.SourceStorageCopy.cellOp env frame right none)}
def materialized := (program 3 left right).run (locals,absentState)
def afterAbsent : Source.St env :=
 {absentState with ex:=absentState.ex.run (Solidity.Backend.StorageOps.SourceStorageCopy.copyLog frame Source.IntTy.u256 right 0 0 (fun _ => Source.intWrap Source.IntTy.u256 0) rfl)}

def empty_certificate := SourceStorageCopyEmpty.copy_empty frame rfl Source.IntTy.u256 left right (by decide)
  0 rfl locals (seed 0 0) rfl rfl
def tail_certificate := SourceStorageCopyEmpty.copy_empty frame rfl Source.IntTy.u256 left right (by decide)
  3 rfl locals (seed 0 3) rfl rfl
def absent_certificate := SourceStorageCopyEmpty.copy_empty frame rfl Source.IntTy.u256 left right (by decide)
  0 rfl locals absentState rfl rfl

def outcomes : Prop :=
 (bothEmpty,liveTail,tooShort,firstClear,samePath,staticEmpty,staticTail,badTarget,missingSource,materialized)=
 ((.ok (),(locals,after 0 0)),(.error .timeout,(locals,seed 0 3)),
  (.error .timeout,(locals,seed 0 0)),(.error .timeout,(locals,prefixState 0 3 1)),
  (.ok (),(locals,seed 0 0)),(.error (.revert []),(locals,seed 0 0)),
  (.error .timeout,(locals,seed 0 3)),(.error (.stuck "storage cell type"),(locals,seed 0 0)),
  (.error (.stuck "storage cell without a value"),(locals,seed 0 0)),(.ok (),(locals,afterAbsent)))
def ordered : Prop :=
 [bothEmpty,liveTail,tooShort,firstClear,samePath,staticEmpty,staticTail,badTarget,missingSource,materialized].map
   (fun r => (r.2.1,view r.2.2,rawView r.2.2,context r.2.2)) =
 [([some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],2),([some 0,some 53,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 0,some 53,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],1),([some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],1),([some 0,some 53,some 59,some 61,some 3,some 0,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 0,some 53,some 59,some 61,some 3,none,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],2),([some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],1),([some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],1),([some 0,some 53,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 0,some 53,some 59,some 61,some 3,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],1),([some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],1),([some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],1),([some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],3)].map (fun (normal,raw,journalLength) =>
   (locals,normal,raw,(some 41,journalLength,19,3,some 0,0,true,0,[(7,[9,8]),(13,[7])],[.bool])))
def journals : Prop :=
 [bothEmpty,liveTail,tooShort,firstClear,samePath,staticEmpty,staticTail,badTarget,missingSource,materialized].map
   (fun r => (journalRows r.2.2,rawJournalRows r.2.2)) =
 [([[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]]),([[some 3,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[some 3,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]]),([[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]]),([[some 3,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 3,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[some 3,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 3,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]]),([[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]]),([[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]]),([[some 3,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[some 3,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]]),([[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]]),([[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]]),([[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]],[[none,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],[some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]])].map (fun (normal,raw) =>
   (normal.map (fun row => (7,row,19,3,some 0)),raw.map (fun row => (7,row,19,3,some 0))))
def fresh (s : Source.St env) (i : Nat) :=
 (SourceArrayIndex.read (E:=env) (Γ:=Γ) frame right (.int Source.IntTy.u256) i).run (locals,s)
def retained (s : Source.St env) (i : Nat) :=
 (Source.readLoc (E:=env) (Γ:=Γ) frame (.stor (elem right i) : Source.Loc env.layout Γ (.int Source.IntTy.u256))).run (locals,s)
def aliases : Prop :=
 (fresh materialized.2.2 0,retained materialized.2.2 0,
  fresh firstClear.2.2 0,retained firstClear.2.2 0,fresh liveTail.2.2 0)=
 ((.error (.revert (Source.panicData .index)),(locals,materialized.2.2)),
  (.ok (.int 7 (by decide)),(locals,materialized.2.2)),
  (.ok (.int 0 (by decide)),(locals,firstClear.2.2)),
  (.ok (.int 0 (by decide)),(locals,firstClear.2.2)),
  (.ok (.int 7 (by decide)),(locals,liveTail.2.2)))
def materialization : Prop :=
 (view absentState,rawView absentState,view materialized.2.2,rawView materialized.2.2,
  absentState.ex.journal.length,materialized.2.2.ex.journal.length,(seed 0 0).ex.journal.length,bothEmpty.2.2.ex.journal.length)=
 ([some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 0,some 53,some 59,some 61,none,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],[some 0,some 53,some 59,some 61,some 0,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],2,3,1,2)
theorem outcome_certificate : outcomes := by rfl
theorem observations : ordered := by rfl
theorem journal_observations : journals := by rfl
theorem alias_observations : aliases := by rfl
theorem materialization_observations : materialization := by rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyEmptyControls.empty_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyEmptyControls.tail_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tail_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyEmptyControls.absent_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms absent_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyEmptyControls.outcome_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outcome_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyEmptyControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observations
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyEmptyControls.journal_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms journal_observations
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyEmptyControls.alias_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms alias_observations
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyEmptyControls.materialization_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms materialization_observations
end Solidity.Lowering.StorageOps.SourceStorageCopyEmptyControls
