import Solidity.Lowering.StorageOps.SourceNestedByteCapture
import Solidity.Lowering.StorageOps.SourceStorageCopy

/-! Nested Source snapshots can allocate before failure. These controls
separate unchanged storage/journal from changed heap and preserve old objects.
They concern storage-to-storage capture, not memory-to-storage compilation. -/
namespace Solidity.Lowering.StorageOps.SourceNestedByteCaptureControls
open Solidity Solidity.Backend.StorageOps
open SourceNestedByteCapture

def unit : Source.Syn .unit := .unit (.cons (.contract false "C" .none .nil
 (.cons (.stateVar (.array (.elem .bytes) .none) none none none false "left" .none)
  (.cons (.stateVar (.array (.elem .bytes) .none) none none none false "right" .none) .nil))) .nil)
def env : Source.Env := unit.env
def left : Source.SPath := ⟨⟨some "C","left"⟩,[]⟩
def right : Source.SPath := ⟨⟨some "C","right"⟩,[]⟩
def child (p : Source.SPath) (j : Nat) := p.go (.index j)
def address : Roadmap.Address := ⟨7,by decide⟩
def frame : Source.Fr := {this:=address,sender:=⟨13,by decide⟩,value:=⟨0,by decide⟩,static:=false,contract:="C"}
def storage : Source.Storage env.layout env.cellTy :=
 let s := (Source.Storage.empty : Source.Storage env.layout env.cellTy).write left (.int 2 (by decide))
 let s := s.write right (.int 1 (by decide))
 let s := s.write (child left 0) (.int 0 (by decide))
 let s := s.write (child left 1) (.int 0 (by decide))
 let s := s.write (child left 3) (.int 1 (by decide))
 let s := s.write (child right 0) (.int 1 (by decide))
 let s := s.write (child (child left 0) 0) (.fixedBytes [53] rfl)
 let s := s.write (child (child left 1) 0) (.fixedBytes [59] rfl)
 let s := s.write (child (child left 3) 0) (.fixedBytes [97] rfl)
 s.write (child (child right 0) 0) (.fixedBytes [17] rfl)
def state : Source.St env :=
 {ex:={world:=⟨fun a=>if a=address then
   {balance:=19,nonce:=3,code:=some 0,storage:=storage}
   else Source.Account.empty _⟩,transient:=Source.Transient.empty,journal:=[]}
  heap:=(Source.Heap.empty.alloc ⟨.bytes .memory,Source.Data.bytes [9,8]⟩).1,
  events:=[],logs:=[(address,[9,8])],fnLocals:=⟨[.bool],.cons (.bool false) .nil⟩}
def seed : Source.St env :=
 {state with ex:=state.ex.apply (SourceStorageCopy.cellOp env frame left (some (.int 2 (by decide))))}
def Γ : Source.RCtx := [.bool]
def locals : Source.Locals env.layout Γ := .cons (.bool true) .nil
def ty : Source.STy := .array .storage (.bytes .storage) none
def program (fuel : Nat) (src dst : Source.SPath) (F : Source.Fr:=frame) : Source.EM env Γ Unit :=
 Source.storeVal F fuel ty dst (Source.Val.storRef (τ:=ty) rfl src)
def run (fuel : Nat) := (program fuel left right).run (locals,seed)
def after (count : Nat) := Nat.repeatTR captureStep count seed
def success : Source.St env :=
 {after 2 with ex:=seed.ex.run (
  [SourceStorageCopy.cellOp env frame (child (child right 0) 0) none,
   SourceStorageCopy.cellOp env frame (child right 0) (some (.int 0 (by decide))),
   SourceStorageCopy.cellOp env frame (child right 1) (some (.int 0 (by decide))),
   SourceStorageCopy.cellOp env frame right (some (.int 2 (by decide)))])}
def prefix_client := timeout_prefix frame left 0 1 locals seed (by
 intro j member
 have cases : j=0 ∨ j=1 := by omega
 rcases cases with rfl | rfl <;> rfl)
def runs := [run 5,run 6,run 7,(program 8 left right {frame with static:=true}).run (locals,seed),
 run 8,(program 1 left left).run (locals,seed)]
def outcomes : Prop := runs=
 [(.error .timeout,(locals,seed)),(.error .timeout,(locals,after 1)),
  (.error .timeout,(locals,after 2)),(.error (.revert []),(locals,after 2)),
  (.ok (),(locals,success)),(.ok (),(locals,seed))]
def dataBytes {τ : Source.STy} : Source.Data env.layout τ → Option (List Nat)
 | .bytes bs => some (bs.map UInt8.toNat)
 | _ => none
def heapView (s : Source.St env) :=
 (s.heap.next,[0,1,2,3].map (fun a=>(s.heap.get a).bind (fun x=>dataBytes x.2)))
def word (s : Source.St env) (p : Source.SPath) :=
 (((s.ex.world.accounts address).storage.read p).bind Source.Val.word).map Fin.val
def bytes {τ : Source.STy} : Source.Val env.layout τ → Option (List Nat)
 | .fixedBytes bs _ => some (bs.map UInt8.toNat)
 | _ => none
def raw (s : Source.St env) (p : Source.SPath) :=
 ((s.ex.world.accounts address).storage.cell p).bind bytes
def row (s : Source.St env) :=
 ([left,right,child left 0,child left 1,child left 3,child right 0,child right 1].map (word s),
  [child (child left 0) 0,child (child left 1) 0,child (child left 3) 0,child (child right 0) 0].map (raw s))
def context (s : Source.St env) :=
 ((s.ex.world.accounts address).balance,(s.ex.world.accounts address).nonce,
  (s.ex.world.accounts address).code,s.events.length,
  s.logs.map (fun (a,bs)=>(a.val,bs.map UInt8.toNat)),s.fnLocals.1)
def ordered : Prop := runs.map (fun r=>(r.2.1,row r.2.2,heapView r.2.2,r.2.2.ex.journal.length,context r.2.2))=
 [([some 2,some 1,some 0,some 0,some 1,some 1,some 0],[some [53],some [59],some [97],some [17]],(1,[some [9,8],none,none,none]),1),
  ([some 2,some 1,some 0,some 0,some 1,some 1,some 0],[some [53],some [59],some [97],some [17]],(2,[some [9,8],some [],none,none]),1),
  ([some 2,some 1,some 0,some 0,some 1,some 1,some 0],[some [53],some [59],some [97],some [17]],(3,[some [9,8],some [],some [],none]),1),
  ([some 2,some 1,some 0,some 0,some 1,some 1,some 0],[some [53],some [59],some [97],some [17]],(3,[some [9,8],some [],some [],none]),1),
  ([some 2,some 2,some 0,some 0,some 1,some 0,some 0],[some [53],some [59],some [97],none],(3,[some [9,8],some [],some [],none]),5),
  ([some 2,some 1,some 0,some 0,some 1,some 1,some 0],[some [53],some [59],some [97],some [17]],(1,[some [9,8],none,none,none]),1)].map
 (fun (ws,bs,h,j)=>(locals,(ws,bs),h,j,(19,3,some 0,0,[(7,[9,8])],[.bool])))
def journalRows (s : Source.St env) := s.ex.journal.map fun e=>
 match e with
 | .account a old =>
   (a.val,[right,child right 0,child right 1].map (fun p=>((old.storage.cell p).bind Source.Val.word).map Fin.val),
    (old.storage.cell (child (child right 0) 0)).bind bytes,old.balance,old.nonce,old.code)
 | .transient a _ => (a.val,[],none,0,0,none)
def oldJournal := [(7,[some 1,some 1,none],some [17],19,3,some 0)]
def successJournal :=
 [(7,[some 1,some 0,some 0],none,19,3,some 0),
  (7,[some 1,some 0,none],none,19,3,some 0),
  (7,[some 1,some 1,none],none,19,3,some 0),
  (7,[some 1,some 1,none],some [17],19,3,some 0),
  (7,[some 1,some 1,none],some [17],19,3,some 0)]
theorem journal_observations : runs.map (fun r=>journalRows r.2.2)=
 [oldJournal,oldJournal,oldJournal,oldJournal,successJournal,oldJournal] := by rfl
theorem outcome_certificate : outcomes := by rfl
theorem observations : ordered := by rfl
theorem timeout_storage_unchanged : (run 6).2.2.ex=seed.ex := by rfl
theorem timeout_heap_changed : (run 6).2.2.heap.next≠seed.heap.next := by decide
/-- info: 'Solidity.Lowering.StorageOps.SourceNestedByteCaptureControls.prefix_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_client
/-- info: 'Solidity.Lowering.StorageOps.SourceNestedByteCaptureControls.outcome_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outcome_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceNestedByteCaptureControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observations
/-- info: 'Solidity.Lowering.StorageOps.SourceNestedByteCaptureControls.timeout_storage_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms timeout_storage_unchanged
/-- info: 'Solidity.Lowering.StorageOps.SourceNestedByteCaptureControls.timeout_heap_changed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms timeout_heap_changed
/-- info: 'Solidity.Lowering.StorageOps.SourceNestedByteCaptureControls.journal_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms journal_observations
end Solidity.Lowering.StorageOps.SourceNestedByteCaptureControls
