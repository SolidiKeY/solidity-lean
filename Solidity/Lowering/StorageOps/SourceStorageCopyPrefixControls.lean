import Solidity.Lowering.StorageOps.SourceStorageCopyPrefix
import Solidity.Lowering.StorageOps.SourceWordWrite

/-! Populated actual storRef-copy traces. Runtime cleanup reuses its fuel,
retains unvisited tail and older shadows on timeout, and commits the header
only on success. Boundary observations below do not prove the remaining
all-fuel theorem. No implicit rollback, memory-to-storage or compiler claim. -/
namespace Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls
open Solidity Solidity.Backend.StorageOps

def uintSyntax : Source.Syn .typeName := .elem (.int false 256 (by decide))
def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
  (.cons (.stateVar (.array uintSyntax .none) none none none false "left" .none)
   (.cons (.stateVar (.array uintSyntax .none) none none none false "right" .none)
    (.cons (.stateVar (.elem .bool) none none none false "bad" .none)
     (.cons (.stateVar uintSyntax none none none true "scratch" .none)
      (.cons (.stateVar uintSyntax none none none false "sentinel" .none) .nil)))))) .nil)
def env : Source.Env := unit.env
def left : Source.SPath := ⟨⟨some "C","left"⟩,[]⟩
def right : Source.SPath := ⟨⟨some "C","right"⟩,[]⟩
def bad : Source.SPath := ⟨⟨some "C","bad"⟩,[]⟩
def scratch : Source.SPath := ⟨⟨some "C","scratch"⟩,[]⟩
def sentinel : Source.SPath := ⟨⟨some "C","sentinel"⟩,[]⟩
def missing : Source.SPath := ⟨⟨some "C","missing"⟩,[]⟩
def elem (p : Source.SPath) (i : Nat) := p.go (.index i)
def address : Roadmap.Address := ⟨7,by decide⟩
def frame : Source.Fr := {this:=address,sender:=⟨13,by decide⟩,value:=⟨0,by decide⟩,static:=false,contract:="C"}
def storage (srcLength dstLength : Nat) : Source.Storage env.layout env.cellTy :=
  let s := (Source.Storage.empty : Source.Storage env.layout env.cellTy).write left (Source.intWrap Source.IntTy.u256 srcLength)
  let s := s.write right (Source.intWrap Source.IntTy.u256 dstLength)
  let s := s.write (elem left 0) (.int 53 (by decide))
  let s := s.write (elem left 1) (.int 59 (by decide))
  let s := s.write (elem left 2) (.int 61 (by decide))
  let s := s.write (elem right 0) (.int 7 (by decide))
  let s := s.write (elem right 1) (.int 17 (by decide))
  let s := s.write (elem right 2) (.int 23 (by decide))
  let s := s.write (elem right 3) (.int 71 (by decide))
  let s := s.write (elem right 4) (.int 73 (by decide))
  let s := s.write (elem right 5) (.int 79 (by decide))
  let s := s.write (elem right 6) (.int 83 (by decide))
  let s := s.write (elem right 8) (.int 97 (by decide))
  (s.write bad (.bool true)).write sentinel (.int 99 (by decide))
def state (srcLength dstLength : Nat) : Source.St env :=
  { ex :=
      { world := ⟨fun a => if a=address then
          {balance := 19,nonce:=3,code:=some 0,storage:=storage srcLength dstLength}
          else Source.Account.empty _⟩
        transient := Source.Transient.empty.set address
          ((Source.Storage.empty : Source.Storage env.layout env.cellTy).write scratch (.int 41 (by decide)))
        journal := [] }
    heap := Source.Heap.empty
    events := []
    logs := [(address,[9,8]),(frame.sender,[7])]
    fnLocals := ⟨[.bool],.cons (.bool false) .nil⟩ }
def seed (srcLength dstLength : Nat) := SourceWordWrite.after frame sentinel (.int 101 (by decide)) (state srcLength dstLength)
def Γ : Source.RCtx := [.bool,.int Source.IntTy.u256]
def locals : Source.Locals env.layout Γ := .cons (.bool true) (.cons (.int 73 (by decide)) .nil)
def ty : Source.STy := .array .storage (.int Source.IntTy.u256) none
def program (fuel : Nat) (src dst : Source.SPath) (F : Source.Fr := frame) : Source.EM env Γ Unit :=
  Source.storeVal F fuel ty dst (Source.Val.storRef (τ:=ty) rfl src)
def run (srcLength dstLength fuel : Nat) := (program fuel left right).run (locals,seed srcLength dstLength)
def payload (i : Nat) : Source.Val env.layout (.int Source.IntTy.u256) :=
  if i=0 then .int 53 (by decide) else if i=1 then .int 59 (by decide) else .int 61 (by decide)
def paths := [left,elem left 0,elem left 1,elem left 2,right,
  elem right 0,elem right 1,elem right 2,elem right 3,elem right 4,elem right 5,elem right 6,elem right 8,bad,sentinel,missing]
def wordAt (s : Source.St env) (p : Source.SPath) :=
  (((s.ex.world.accounts address).storage.read p).bind Source.Val.word).map Fin.val
def rawWordAt (s : Source.St env) (p : Source.SPath) :=
  (((s.ex.world.accounts address).storage.cell p).bind Source.Val.word).map Fin.val
def rawView (s : Source.St env) := paths.map (rawWordAt s)
def view (s : Source.St env) := paths.map (wordAt s)
def context (s : Source.St env) :=
  ((((s.ex.transient.cells address).read scratch).bind Source.Val.word).map Fin.val,
   s.ex.journal.length,(s.ex.world.accounts address).balance,(s.ex.world.accounts address).nonce,
   (s.ex.world.accounts address).code,s.heap.next,(s.heap.cells 0).isNone,s.events.length,
   s.logs.map (fun (a,b) => (a.val,b.map UInt8.toNat)),s.fnLocals.1)
def short := run 2 7 6
def longer := run 2 7 7
def complete := run 2 7 8
def ample := run 2 7 11
def emptySource := run 0 3 4
def emptyDestination := run 2 0 6
def varied := run 3 7 7
def boundary := run 2 7 5
def snapshotFailure := run 2 7 4
def self := (program 8 right right).run (locals,seed 2 7)
def staticFailure := (program 8 left right {frame with static:=true}).run (locals,seed 2 7)
def sourceFailure := (program 8 missing right).run (locals,seed 2 7)
def destinationFailure := (program 8 left bad).run (locals,seed 2 7)

def trace (srcLength dstLength : Nat) := SourceStorageCopy.copyLog frame Source.IntTy.u256 right srcLength dstLength payload rfl
def after (srcLength dstLength : Nat) : Source.St env :=
  {seed srcLength dstLength with ex := (seed srcLength dstLength).ex.run (trace srcLength dstLength)}
def prefixState (srcLength dstLength takeCount : Nat) : Source.St env :=
  {seed srcLength dstLength with ex := (seed srcLength dstLength).ex.run ((trace srcLength dstLength).take takeCount)}
def readsTwo : Prop := ∀ j<2,
  (Source.readAt (E:=env) (Γ:=Γ) frame (elem left j) (.int Source.IntTy.u256)).run (locals,seed 2 7)=
    (.ok (payload j),(locals,seed 2 7))
def uniform : Prop := ∀ padding : Nat,
  run 2 7 (2+padding+4) = if 5≤2+padding+1 then (.ok (),(locals,after 2 7))
    else (.error .timeout,(locals,prefixState 2 7 (2+min 5 (2+padding+1))))
def outcomes : Prop :=
  (short,longer,complete,ample,emptySource,emptyDestination,varied,boundary,snapshotFailure,self,
    staticFailure,sourceFailure,destinationFailure) =
  ((.error .timeout,(locals,prefixState 2 7 5)),(.error .timeout,(locals,prefixState 2 7 6)),
   (.ok (),(locals,after 2 7)),(.ok (),(locals,after 2 7)),
   (.error .timeout,(locals,prefixState 0 3 1)),(.ok (),(locals,after 2 0)),
   (.ok (),(locals,after 3 7)),(.error .timeout,(locals,prefixState 2 7 1)),
   (.error .timeout,(locals,seed 2 7)),(.ok (),(locals,seed 2 7)),
   (.error (.revert []),(locals,seed 2 7)),
   (.error (.stuck "storage cell without a value"),(locals,seed 2 7)),
   (.error (.stuck "storage cell type"),(locals,seed 2 7)))
def ordered : Prop :=
  (view (seed 2 7),view short.2.2,view longer.2.2,view complete.2.2,view ample.2.2,
    view emptySource.2.2,view emptyDestination.2.2,view varied.2.2,view boundary.2.2) =
  ([some 2,some 53,some 59,some 61,some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],
   [some 2,some 53,some 59,some 61,some 7,some 53,some 59,some 0,some 0,some 0,some 79,some 83,some 97,some 1,some 101,none],
   [some 2,some 53,some 59,some 61,some 7,some 53,some 59,some 0,some 0,some 0,some 0,some 83,some 97,some 1,some 101,none],
   [some 2,some 53,some 59,some 61,some 2,some 53,some 59,some 0,some 0,some 0,some 0,some 0,some 97,some 1,some 101,none],
   [some 2,some 53,some 59,some 61,some 2,some 53,some 59,some 0,some 0,some 0,some 0,some 0,some 97,some 1,some 101,none],
   [some 0,some 53,some 59,some 61,some 3,some 0,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],
   [some 2,some 53,some 59,some 61,some 2,some 53,some 59,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],
   [some 3,some 53,some 59,some 61,some 3,some 53,some 59,some 61,some 0,some 0,some 0,some 0,some 97,some 1,some 101,none],
   [some 2,some 53,some 59,some 61,some 7,some 53,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none])
def rawOrdered : Prop :=
  (rawView (seed 2 7),rawView short.2.2,rawView longer.2.2,rawView complete.2.2,rawView ample.2.2,
    rawView emptySource.2.2,rawView emptyDestination.2.2,rawView varied.2.2,rawView boundary.2.2) =
  ([some 2,some 53,some 59,some 61,some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],
   [some 2,some 53,some 59,some 61,some 7,some 53,some 59,none,none,none,some 79,some 83,some 97,some 1,some 101,none],
   [some 2,some 53,some 59,some 61,some 7,some 53,some 59,none,none,none,none,some 83,some 97,some 1,some 101,none],
   [some 2,some 53,some 59,some 61,some 2,some 53,some 59,none,none,none,none,none,some 97,some 1,some 101,none],
   [some 2,some 53,some 59,some 61,some 2,some 53,some 59,none,none,none,none,none,some 97,some 1,some 101,none],
   [some 0,some 53,some 59,some 61,some 3,none,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],
   [some 2,some 53,some 59,some 61,some 2,some 53,some 59,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none],
   [some 3,some 53,some 59,some 61,some 3,some 53,some 59,some 61,none,none,none,none,some 97,some 1,some 101,none],
   [some 2,some 53,some 59,some 61,some 7,some 53,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 1,some 101,none])
def contexts : Prop :=
  ([short,longer,complete,ample,emptySource,emptyDestination,varied,boundary,snapshotFailure,self,
    staticFailure,sourceFailure,destinationFailure].map fun r => (r.2.1,context r.2.2)) =
  [6,7,9,9,2,4,9,2,1,1,1,1,1].map (fun journalLength =>
    (locals,(some 41,journalLength,19,3,some 0,0,true,0,[(7,[9,8]),(13,[7])],[.bool])))
def journalRows (s : Source.St env) := s.ex.journal.map fun e =>
  match e with
  | .account a old => (a.val,([right,elem right 0,elem right 1,elem right 2,elem right 3,
      elem right 4,elem right 5,elem right 6,elem right 8,sentinel].map fun p =>
        ((old.storage.read p).bind Source.Val.word).map Fin.val),old.balance,old.nonce,old.code)
  | .transient a _ => (a.val,[],0,0,none)
def rawJournalRows (s : Source.St env) := s.ex.journal.map fun e =>
  match e with
  | .account a old => (a.val,([right,elem right 0,elem right 1,elem right 2,elem right 3,
      elem right 4,elem right 5,elem right 6,elem right 8,sentinel].map fun p =>
        ((old.storage.cell p).bind Source.Val.word).map Fin.val),old.balance,old.nonce,old.code)
  | .transient a _ => (a.val,[],0,0,none)
def journalOrder : Prop :=
  (journalRows short.2.2,journalRows complete.2.2) =
  (([[some 7,some 53,some 59,some 0,some 0,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 53,some 59,some 0,some 71,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 53,some 59,some 23,some 71,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 53,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]].map
       fun row => (7,row,19,3,some 0)),
   ([[some 7,some 53,some 59,some 0,some 0,some 0,some 0,some 0,some 97,some 101],
     [some 7,some 53,some 59,some 0,some 0,some 0,some 0,some 83,some 97,some 101],
     [some 7,some 53,some 59,some 0,some 0,some 0,some 79,some 83,some 97,some 101],
     [some 7,some 53,some 59,some 0,some 0,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 53,some 59,some 0,some 71,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 53,some 59,some 23,some 71,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 53,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]].map
       fun row => (7,row,19,3,some 0)))

def rawJournalOrder : Prop :=
  (rawJournalRows short.2.2,rawJournalRows complete.2.2) =
  (([[some 7,some 53,some 59,none,none,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 53,some 59,none,some 71,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 53,some 59,some 23,some 71,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 53,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]].map
       fun row => (7,row,19,3,some 0)),
   ([[some 7,some 53,some 59,none,none,none,none,none,some 97,some 101],
     [some 7,some 53,some 59,none,none,none,none,some 83,some 97,some 101],
     [some 7,some 53,some 59,none,none,none,some 79,some 83,some 97,some 101],
     [some 7,some 53,some 59,none,none,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 53,some 59,none,some 71,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 53,some 59,some 23,some 71,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 53,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 101],
     [some 7,some 7,some 17,some 23,some 71,some 73,some 79,some 83,some 97,some 99]].map
       fun row => (7,row,19,3,some 0)))

theorem reads_two (dstLength : Nat) : ∀ j<2,
  (Source.readAt (E:=env) (Γ:=Γ) frame (elem left j) (.int Source.IntTy.u256)).run (locals,seed 2 dstLength)=
    (.ok (payload j),(locals,seed 2 dstLength)) := by
  intro j bound
  have cases : j=0 ∨ j=1 := by omega
  rcases cases with rfl|rfl <;> rfl

theorem reads_three : ∀ j<3,
  (Source.readAt (E:=env) (Γ:=Γ) frame (elem left j) (.int Source.IntTy.u256)).run (locals,seed 3 7)=
    (.ok (payload j),(locals,seed 3 7)) := by
  intro j bound
  have cases : j=0 ∨ j=1 ∨ j=2 := by omega
  rcases cases with rfl|rfl|rfl <;> rfl

theorem uniform_certificate : uniform := by
  intro padding
  exact SourceStorageCopyPrefix.prepared frame rfl Source.IntTy.u256 left right (by decide)
    2 7 padding payload rfl locals (seed 2 7) rfl (reads_two 7) rfl

def short_certificate := uniform_certificate 0
def longer_certificate := uniform_certificate 1
def complete_certificate := uniform_certificate 2
def ample_certificate := uniform_certificate 5

def empty_source_certificate := SourceStorageCopyPrefix.prepared frame rfl Source.IntTy.u256 left right (by decide)
  0 3 0 payload rfl locals (seed 0 3) rfl (by intro j bound; omega) rfl
def empty_destination_certificate := SourceStorageCopyPrefix.prepared frame rfl Source.IntTy.u256 left right (by decide)
  2 0 0 payload rfl locals (seed 2 0) rfl (reads_two 0) rfl
def varied_certificate := SourceStorageCopyPrefix.prepared frame rfl Source.IntTy.u256 left right (by decide)
  3 7 0 payload rfl locals (seed 3 7) rfl reads_three rfl

theorem outcome_certificate : outcomes := by
  unfold outcomes
  rw [show short=(.error .timeout,(locals,prefixState 2 7 5)) from short_certificate,
    show longer=(.error .timeout,(locals,prefixState 2 7 6)) from longer_certificate,
    show complete=(.ok (),(locals,after 2 7)) from complete_certificate,
    show ample=(.ok (),(locals,after 2 7)) from ample_certificate,
    show emptySource=(.error .timeout,(locals,prefixState 0 3 1)) from empty_source_certificate,
    show emptyDestination=(.ok (),(locals,after 2 0)) from empty_destination_certificate,
    show varied=(.ok (),(locals,after 3 7)) from varied_certificate]
  rfl

theorem observations : ordered := by rfl

theorem raw_observations : rawOrdered := by rfl

theorem context_observations : contexts := by rfl

theorem journal_observations : journalOrder := by rfl

theorem raw_journal_observations : rawJournalOrder := by rfl

/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls.reads_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reads_two
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls.reads_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reads_three
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls.uniform_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uniform_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls.short_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls.longer_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms longer_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls.complete_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls.ample_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ample_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls.empty_source_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_source_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls.empty_destination_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_destination_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls.varied_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms varied_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls.outcome_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outcome_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observations
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls.raw_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_observations
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls.context_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms context_observations
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls.journal_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms journal_observations
/-- info: 'Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls.raw_journal_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_journal_observations

end Solidity.Lowering.StorageOps.SourceStorageCopyPrefixControls
