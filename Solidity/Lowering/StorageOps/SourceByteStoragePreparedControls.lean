import Solidity.Lowering.StorageOps.SourceByteStoragePrepared
import Solidity.Lowering.StorageOps.SourceArrayIndex

/-! Populated actual storage-reference byte copies: OLD capture, cleanup
prefix, header-last commit and older shadow preservation. No packed/EVM claim. -/
namespace Solidity.Lowering.StorageOps.SourceByteStoragePreparedControls
open Solidity Solidity.Backend.StorageOps
open SourceByteStoragePrepared

def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
 (.cons (.stateVar (.elem .bytes) none none none false "left" .none)
  (.cons (.stateVar (.elem .bytes) none none none false "right" .none) .nil))) .nil)
def env : Source.Env := unit.env
def left : Source.SPath := ⟨⟨some "C","left"⟩,[]⟩
def right : Source.SPath := ⟨⟨some "C","right"⟩,[]⟩
def child (p : Source.SPath) (i : Nat) := p.go (.index i)
def address : Roadmap.Address := ⟨7,by decide⟩
def frame : Source.Fr := {this:=address,sender:=⟨13,by decide⟩,value:=⟨0,by decide⟩,static:=false,contract:="C"}
def byte (n : UInt8) : Source.Val env.layout (.fixedBytes 1 (by decide)) := .fixedBytes [n] rfl
def storage (n old : Nat) : Source.Storage env.layout env.cellTy :=
 let s := (Source.Storage.empty : Source.Storage env.layout env.cellTy).write left (Source.intWrap Source.IntTy.u256 n)
 let s := s.write right (Source.intWrap Source.IntTy.u256 old)
 let s := s.write (child left 0) (byte 53)
 let s := s.write (child left 1) (byte 59)
 let s := s.write (child left 2) (byte 61)
 let s := s.write (child right 0) (byte 7)
 let s := s.write (child right 1) (byte 17)
 let s := s.write (child right 2) (byte 23)
 let s := s.write (child right 3) (byte 71)
 let s := s.write (child right 4) (byte 73)
 s.write (child right 6) (byte 97)
def state (n old : Nat) : Source.St env :=
 {ex:={world:=⟨fun a=>if a=address then
   {balance:=⟨19,by decide⟩,nonce:=3,code:=some 0,storage:=storage n old}
   else Source.Account.empty _⟩,transient:=Source.Transient.empty,journal:=[]}
  heap:=Source.Heap.empty,events:=[],logs:=[(address,[9,8])],fnLocals:=⟨[.bool],.cons (.bool false) .nil⟩}
def seed (n old : Nat) : Source.St env :=
 {state n old with ex:=(state n old).ex.apply (SourceStorageCopy.cellOp env frame left (some (Source.intWrap Source.IntTy.u256 n)))}
def Γ : Source.RCtx := [.bool]
def locals : Source.Locals env.layout Γ := .cons (.bool true) .nil
def program (fuel : Nat) (src dst : Source.SPath) (F : Source.Fr:=frame) : Source.EM env Γ Unit :=
 Source.storeVal F fuel (.bytes .storage) dst (Source.Val.storRef (τ:=.bytes .storage) rfl src)
def run (n old fuel : Nat) := (program fuel left right).run (locals,seed n old)
def typed (j : Nat) : (.fixedBytes 1 (by decide) : Source.STy)=env.cellTy (child right j) := rfl
def after (n old padding : Nat) (bs : List UInt8) : Source.St env :=
 {seed n old with ex:=(seed n old).ex.run (phaseLog frame right typed rfl bs old padding)}
def phase_client (padding : Nat) := store_prepared frame rfl right typed rfl [53,59] 5 padding
 locals (seed 2 5) rfl

def outcomes : Prop :=
 (run 2 5 4,run 2 5 5,run 2 5 6,run 2 1 5,run 0 0 3,run 0 2 3,
  (program 1 right right).run (locals,seed 2 5),
  (program 6 left right {frame with static:=true}).run (locals,seed 2 5))=
 ((.error .timeout,(locals,seed 2 5)),(.error .timeout,(locals,after 2 5 0 [53,59])),
  (.ok (),(locals,after 2 5 1 [53,59])),(.ok (),(locals,after 2 1 0 [53,59])),
  (.ok (),(locals,after 0 0 0 [])),(.error .timeout,(locals,seed 0 2)),
  (.ok (),(locals,seed 2 5)),(.error (.revert []),(locals,seed 2 5)))
def byteView {τ : Source.STy} : Source.Val env.layout τ → Option (List Nat)
 | .fixedBytes bs _ => some (bs.map UInt8.toNat)
 | _ => none
def raw (s : Source.Storage env.layout env.cellTy) (p : Source.SPath) :=
 (s.cell p).bind byteView
def word (s : Source.Storage env.layout env.cellTy) (p : Source.SPath) :=
 ((s.read p).bind Source.Val.word).map Fin.val
def row (s : Source.Storage env.layout env.cellTy) :=
 (word s left,word s right,[0,1,2,3,4,6].map (fun j=>raw s (child right j)),
  [0,1,2].map (fun j=>raw s (child left j)))
def observations : Prop :=
 [run 2 5 4,run 2 5 5,run 2 5 6,run 2 1 5,run 0 0 3,run 0 2 3,
  (program 1 right right).run (locals,seed 2 5),
  (program 6 left right {frame with static:=true}).run (locals,seed 2 5)].map
 (fun r=>(r.2.1,row (r.2.2.ex.world.accounts address).storage,r.2.2.ex.journal.length))=
 [(locals,(some 2,some 5,[some [7],some [17],some [23],some [71],some [73],some [97]],[some [53],some [59],some [61]]),1),
  (locals,(some 2,some 5,[some [53],some [59],none,none,some [73],some [97]],[some [53],some [59],some [61]]),5),
  (locals,(some 2,some 2,[some [53],some [59],none,none,none,some [97]],[some [53],some [59],some [61]]),7),
  (locals,(some 2,some 2,[some [53],some [59],some [23],some [71],some [73],some [97]],[some [53],some [59],some [61]]),4),
  (locals,(some 0,some 0,[some [7],some [17],some [23],some [71],some [73],some [97]],[some [53],some [59],some [61]]),2),
  (locals,(some 0,some 2,[some [7],some [17],some [23],some [71],some [73],some [97]],[some [53],some [59],some [61]]),1),
  (locals,(some 2,some 5,[some [7],some [17],some [23],some [71],some [73],some [97]],[some [53],some [59],some [61]]),1),
  (locals,(some 2,some 5,[some [7],some [17],some [23],some [71],some [73],some [97]],[some [53],some [59],some [61]]),1)]
def journalRows (s : Source.St env) := s.ex.journal.map fun e=>
 match e with
 | .account a old => (a.val,row old.storage,old.balance.val,old.nonce,old.code)
 | .transient a _ => (a.val,(none,none,[],[]),0,0,none)
def journals := journalRows (run 2 5 6).2.2
def journal_order : Prop := journals=
 [(some 5,[some [53],some [59],none,none,none,some [97]]),
  (some 5,[some [53],some [59],none,none,some [73],some [97]]),
  (some 5,[some [53],some [59],none,some [71],some [73],some [97]]),
  (some 5,[some [53],some [59],some [23],some [71],some [73],some [97]]),
  (some 5,[some [53],some [17],some [23],some [71],some [73],some [97]]),
  (some 5,[some [7],some [17],some [23],some [71],some [73],some [97]]),
  (some 5,[some [7],some [17],some [23],some [71],some [73],some [97]])].map
 (fun (header,bs)=>(7,(some 2,header,bs,[some [53],some [59],some [61]]),19,3,some 0))
def retained (s : Source.St env) (j : Nat) :=
 (Source.readLoc (E:=env) (Γ:=Γ) frame
  (.stor (child right j) : Source.Loc env.layout Γ (.fixedBytes 1 (by decide)))).run (locals,s)
def fresh (s : Source.St env) (j : Nat) :=
 (SourceArrayIndex.read (E:=env) (Γ:=Γ) frame right (.fixedBytes 1 (by decide)) j).run (locals,s)
def aliases : Prop :=
 (retained (after 2 5 1 [53,59]) 2,fresh (after 2 5 1 [53,59]) 2,
  retained (after 2 1 0 [53,59]) 2,fresh (after 2 1 0 [53,59]) 2,
  fresh (after 2 5 0 [53,59]) 2,retained (after 2 5 1 [53,59]) 6)=
 ((.ok (byte 0),(locals,after 2 5 1 [53,59])),
  (.error (.revert (Source.panicData .index)),(locals,after 2 5 1 [53,59])),
  (.ok (byte 23),(locals,after 2 1 0 [53,59])),
  (.error (.revert (Source.panicData .index)),(locals,after 2 1 0 [53,59])),
  (.ok (byte 0),(locals,after 2 5 0 [53,59])),
  (.ok (byte 97),(locals,after 2 5 1 [53,59])))
def context (s : Source.St env) :=
 ((s.ex.world.accounts address).balance.val,(s.ex.world.accounts address).nonce,
  (s.ex.world.accounts address).code,s.heap.next,(s.heap.cells 0).isNone,
  s.events.length,s.logs.map (fun (a,bs)=>(a.val,bs.map UInt8.toNat)),s.fnLocals.1)
def contexts : Prop :=
 [run 2 5 4,run 2 5 5,run 2 5 6,run 2 1 5,run 0 0 3,run 0 2 3,
  (program 1 right right).run (locals,seed 2 5),
  (program 6 left right {frame with static:=true}).run (locals,seed 2 5)].map
  (fun r=>(r.2.1,context r.2.2)) =
 List.replicate 8 (locals,(19,3,some 0,0,true,0,[(7,[9,8])],[.bool]))
theorem timeout_journal : journalRows (run 2 5 5).2.2=journals.drop 2 := by rfl
theorem alias_observations : aliases := by rfl
theorem context_observations : contexts := by rfl
theorem outcome_certificate : outcomes := by rfl
theorem ordered_observations : observations := by rfl
theorem journal_observations : journal_order := by rfl
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStoragePreparedControls.phase_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms phase_client
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStoragePreparedControls.outcome_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outcome_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStoragePreparedControls.ordered_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ordered_observations
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStoragePreparedControls.journal_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms journal_observations
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStoragePreparedControls.timeout_journal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms timeout_journal
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStoragePreparedControls.alias_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms alias_observations
/-- info: 'Solidity.Lowering.StorageOps.SourceByteStoragePreparedControls.context_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms context_observations
end Solidity.Lowering.StorageOps.SourceByteStoragePreparedControls
