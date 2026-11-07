import Solidity.Lowering.StorageOps.SourceNestedByteValues
import Solidity.Lowering.StorageOps.SourceNestedByteCaptureControls

/-! Nonempty captured payloads retain source tails and existing heap objects.
Capture order is observable in distinct allocated payloads; failures retain
those allocations without storage or journal mutation. -/
namespace Solidity.Lowering.StorageOps.SourceNestedByteValuesControls
open Solidity Solidity.Backend.StorageOps
open SourceNestedByteCaptureControls (env left right child address frame Γ locals)
open SourceNestedByteValues

def storage : Source.Storage env.layout env.cellTy :=
 let s := SourceNestedByteCaptureControls.storage.write left (.int 3 (by decide))
 let s := s.write (child left 0) (.int 2 (by decide))
 let s := s.write (child left 1) (.int 2 (by decide))
 let s := s.write (child left 2) (.int 2 (by decide))
 let s := s.write (child (child left 0) 1) (.fixedBytes [59] rfl)
 let s := s.write (child (child left 0) 3) (.fixedBytes [97] rfl)
 let s := s.write (child (child left 1) 0) (.fixedBytes [61] rfl)
 let s := s.write (child (child left 1) 1) (.fixedBytes [67] rfl)
 let s := s.write (child (child left 2) 0) (.fixedBytes [71] rfl)
 s.write (child (child left 2) 1) (.fixedBytes [73] rfl)
def state : Source.St env :=
 {SourceNestedByteCaptureControls.state with ex:=
   {SourceNestedByteCaptureControls.state.ex with world:=⟨fun a=>
    if a=address then {SourceNestedByteCaptureControls.state.ex.world.accounts a with storage:=storage}
    else SourceNestedByteCaptureControls.state.ex.world.accounts a⟩}}
def seed : Source.St env :=
 {state with ex:=state.ex.apply (SourceStorageCopy.cellOp env frame left (some (.int 3 (by decide))))}
def payload (j k : Nat) : UInt8 :=
 if j=0 then if k=0 then 53 else 59
 else if j=1 then if k=0 then 61 else 67
 else if k=0 then 71 else 73
def after (count : Nat) := (List.range' 0 count).foldl (allocateAt 2 payload) seed
def missing : Source.SPath := ⟨⟨some "C","missing"⟩,[]⟩
def program (fuel : Nat) (src dst : Source.SPath) (F : Source.Fr:=frame) : Source.EM env Γ Unit :=
 SourceNestedByteCaptureControls.program fuel src dst F
def runs :=
 [(program 8 left right).run (locals,seed),
  (program 9 left right).run (locals,seed),
  (program 9 left right {frame with static:=true}).run (locals,seed),
  (program 10 left missing).run (locals,seed),
  (program 10 left right {frame with static:=true}).run (locals,seed),
  (program 1 left left).run (locals,seed)]
def prefix_client := timeout_prefix frame left 0 2 2 payload locals seed (by
 intro j member
 have cases : j=0 ∨ j=1 ∨ j=2 := by omega
 rcases cases with rfl | rfl | rfl <;> rfl) (by
 intro j member k bound
 have outer : j=0 ∨ j=1 ∨ j=2 := by omega
 have inner : k=0 ∨ k=1 := by omega
 rcases outer with rfl | rfl | rfl <;> rcases inner with rfl | rfl <;> rfl)
def capture_client (padding : Nat) := capture frame (child left 0) 2 padding (payload 0)
 locals seed rfl (by
 intro k bound
 have cases : k=0 ∨ k=1 := by omega
 rcases cases with rfl | rfl <;> rfl)
def outcomes : Prop := runs=
 [(.error .timeout,(locals,after 1)),(.error .timeout,(locals,after 2)),
  (.error .timeout,(locals,after 2)),(.error (.stuck "storage cell without a value"),(locals,after 3)),
  (.error (.revert []),(locals,after 3)),(.ok (),(locals,seed))]
def heapView (s : Source.St env) :=
 (s.heap.next,[0,1,2,3,4].map (fun a=>(s.heap.get a).bind (fun x=>SourceNestedByteCaptureControls.dataBytes x.2)))
def bytes (s : Source.St env) :=
 [child (child left 0) 0,child (child left 0) 1,child (child left 1) 0,child (child left 1) 1,
  child (child left 2) 0,child (child left 2) 1,child (child left 0) 3,child (child left 3) 0,
  child (child right 0) 0].map (SourceNestedByteCaptureControls.raw s)
def context := SourceNestedByteCaptureControls.context
def headerView (s : Source.St env) :=
 [left,right,child left 0,child left 1,child left 2,child left 3].map (SourceNestedByteCaptureControls.word s)
def ordered : Prop := runs.map (fun r=>(r.2.1,headerView r.2.2,bytes r.2.2,heapView r.2.2,r.2.2.ex.journal.length,context r.2.2))=
 [(2,[some [9,8],some [53,59],none,none,none]),
  (3,[some [9,8],some [53,59],some [61,67],none,none]),
  (3,[some [9,8],some [53,59],some [61,67],none,none]),
  (4,[some [9,8],some [53,59],some [61,67],some [71,73],none]),
  (4,[some [9,8],some [53,59],some [61,67],some [71,73],none]),
  (1,[some [9,8],none,none,none,none])].map
 (fun h=>(locals,[some 3,some 1,some 2,some 2,some 2,some 1],[some [53],some [59],some [61],some [67],some [71],some [73],some [97],some [97],some [17]],
 h,1,(19,3,some 0,0,[(7,[9,8])],[.bool])))
def reversed := allocateAt 2 payload (allocateAt 2 payload seed 1) 0

def journalRows (s : Source.St env) := s.ex.journal.map fun e=>
 match e with
 | .account a old =>
   (a.val,[left,right,child left 0,child left 1,child left 2,child left 3].map
     (fun p=>((old.storage.read p).bind Source.Val.word).map Fin.val),
    [child (child left 0) 0,child (child left 0) 1,child (child left 1) 0,child (child left 1) 1,
     child (child left 2) 0,child (child left 2) 1,child (child left 0) 3,child (child left 3) 0,
     child (child right 0) 0].map (fun p=>(old.storage.cell p).bind SourceNestedByteCaptureControls.bytes),
    old.balance,old.nonce,old.code)
 | .transient a _ => (a.val,[],[],0,0,none)
theorem journal_observations : runs.map (fun r=>journalRows r.2.2)=List.replicate 6
 [(7,[some 3,some 1,some 2,some 2,some 2,some 1],
 [some [53],some [59],some [61],some [67],some [71],some [73],some [97],some [97],some [17]],19,3,some 0)] := by rfl
theorem outcome_certificate : outcomes := by rfl
theorem observations : ordered := by rfl
theorem execution_unchanged : runs.map (fun r=>r.2.2.ex)=List.replicate 6 seed.ex := by rfl
theorem wrong_order : (heapView (after 2)).2≠(heapView reversed).2 := by decide
/-- info: 'Solidity.Lowering.StorageOps.SourceNestedByteValuesControls.prefix_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_client
/-- info: 'Solidity.Lowering.StorageOps.SourceNestedByteValuesControls.capture_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capture_client
/-- info: 'Solidity.Lowering.StorageOps.SourceNestedByteValuesControls.outcome_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outcome_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceNestedByteValuesControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observations
/-- info: 'Solidity.Lowering.StorageOps.SourceNestedByteValuesControls.execution_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms execution_unchanged
/-- info: 'Solidity.Lowering.StorageOps.SourceNestedByteValuesControls.wrong_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_order
/-- info: 'Solidity.Lowering.StorageOps.SourceNestedByteValuesControls.journal_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms journal_observations
end Solidity.Lowering.StorageOps.SourceNestedByteValuesControls
