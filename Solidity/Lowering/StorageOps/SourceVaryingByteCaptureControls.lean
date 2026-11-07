import Solidity.Lowering.StorageOps.SourceVaryingByteCapture
import Solidity.Lowering.StorageOps.SourceNestedByteValuesControls

/-! Independently varying lengths: first child has one live byte, later
children two. A retained second byte in the first child is not captured.
Dropping the earlier-child fuel condition yields a concrete wrong prefix. -/
namespace Solidity.Lowering.StorageOps.SourceVaryingByteCaptureControls
open Solidity Solidity.Backend.StorageOps
open SourceNestedByteCaptureControls (env left right child address frame Γ locals)
open SourceVaryingByteCapture

def length (j : Nat) : Nat := if j=0 then 1 else 2
def payload := SourceNestedByteValuesControls.payload
def storage := SourceNestedByteValuesControls.storage.write (child left 0) (.int 1 (by decide))
def state : Source.St env :=
 {SourceNestedByteValuesControls.state with ex:=
  {SourceNestedByteValuesControls.state.ex with world:=⟨fun a=>
   if a=address then {SourceNestedByteValuesControls.state.ex.world.accounts a with storage:=storage}
   else SourceNestedByteValuesControls.state.ex.world.accounts a⟩}}
def seed : Source.St env :=
 {state with ex:=state.ex.apply (SourceStorageCopy.cellOp env frame left (some (.int 3 (by decide))))}
def after (count : Nat) := (List.range' 0 count).foldl
 (fun s j=>SourceNestedByteValues.allocateAt (length j) payload s j) seed
def program (fuel : Nat) (src dst : Source.SPath) (F : Source.Fr:=frame) : Source.EM env Γ Unit :=
 SourceNestedByteCaptureControls.program fuel src dst F
def missing := SourceNestedByteValuesControls.missing
def runs :=
 [(program 7 left right).run (locals,seed),
  (program 8 left right).run (locals,seed),
  (program 9 left right).run (locals,seed),
  (program 9 left right {frame with static:=true}).run (locals,seed),
  (program 10 left missing).run (locals,seed),
  (program 10 left right {frame with static:=true}).run (locals,seed),
  (program 1 left left).run (locals,seed)]
def prefix_client := timeout_prefix frame left 0 2 2 length payload locals seed (by
 intro j member
 have cases : j=0 ∨ j=1 := by omega
 rcases cases with rfl | rfl <;> decide) (by decide) (by
 intro j member
 have cases : j=0 ∨ j=1 ∨ j=2 := by omega
 rcases cases with rfl | rfl | rfl <;> rfl) (by
 intro j member k bound
 have outer : j=0 ∨ j=1 ∨ j=2 := by omega
 have inner : k=0 ∨ k=1 := by unfold length at bound; split at bound <;> omega
 rcases outer with rfl | rfl | rfl <;> rcases inner with rfl | rfl <;> rfl)
def capture_client (padding : Nat) := SourceNestedByteValues.capture frame (child left 0) 1 padding
 (payload 0) locals seed rfl (by
 intro k bound
 have index : k=0 := by omega
 cases index
 rfl)
def outcomes : Prop := runs=
 [(.error .timeout,(locals,after 1)),(.error .timeout,(locals,after 1)),
  (.error .timeout,(locals,after 2)),(.error .timeout,(locals,after 2)),
  (.error (.stuck "storage cell without a value"),(locals,after 3)),
  (.error (.revert []),(locals,after 3)),(.ok (),(locals,seed))]
def heapView := SourceNestedByteValuesControls.heapView
def headerView := SourceNestedByteValuesControls.headerView
def bytes := SourceNestedByteValuesControls.bytes
def context := SourceNestedByteValuesControls.context
def ordered : Prop := runs.map (fun r=>(r.2.1,headerView r.2.2,bytes r.2.2,heapView r.2.2,r.2.2.ex.journal.length,context r.2.2))=
 [(2,[some [9,8],some [53],none,none,none]),
  (2,[some [9,8],some [53],none,none,none]),
  (3,[some [9,8],some [53],some [61,67],none,none]),
  (3,[some [9,8],some [53],some [61,67],none,none]),
  (4,[some [9,8],some [53],some [61,67],some [71,73],none]),
  (4,[some [9,8],some [53],some [61,67],some [71,73],none]),
  (1,[some [9,8],none,none,none,none])].map (fun h=>
 (locals,[some 3,some 1,some 1,some 2,some 2,some 1],
 [some [53],some [59],some [61],some [67],some [71],some [73],some [97],some [97],some [17]],
 h,1,(19,3,some 0,0,[(7,[9,8])],[.bool])))
def journalRows := SourceNestedByteValuesControls.journalRows

theorem outcome_certificate : outcomes := by rfl
theorem observations : ordered := by rfl
theorem execution_unchanged : runs.map (fun r=>r.2.2.ex)=List.replicate 7 seed.ex := by rfl
theorem journal_observations : runs.map (fun r=>journalRows r.2.2)=List.replicate 7
 [(7,[some 3,some 1,some 1,some 2,some 2,some 1],
 [some [53],some [59],some [61],some [67],some [71],some [73],some [97],some [97],some [17]],19,3,some 0)] := by rfl
theorem fuel_guard_needed : ((program 7 left right).run (locals,seed)).2.2.heap.next≠(after 2).heap.next := by decide
/-- info: 'Solidity.Lowering.StorageOps.SourceVaryingByteCaptureControls.prefix_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_client
/-- info: 'Solidity.Lowering.StorageOps.SourceVaryingByteCaptureControls.capture_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capture_client
/-- info: 'Solidity.Lowering.StorageOps.SourceVaryingByteCaptureControls.outcome_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outcome_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceVaryingByteCaptureControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observations
/-- info: 'Solidity.Lowering.StorageOps.SourceVaryingByteCaptureControls.execution_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms execution_unchanged
/-- info: 'Solidity.Lowering.StorageOps.SourceVaryingByteCaptureControls.journal_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms journal_observations
/-- info: 'Solidity.Lowering.StorageOps.SourceVaryingByteCaptureControls.fuel_guard_needed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fuel_guard_needed
end Solidity.Lowering.StorageOps.SourceVaryingByteCaptureControls
