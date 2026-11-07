import Solidity.Lowering.StorageOps.SourceByteCaptureSuccess
import Solidity.Lowering.StorageOps.SourceVaryingByteCaptureControls

/-! Actual successful full/shifted/static captures return distinct fresh typed
references. Returned identities are checked against actual heap byte reads;
physical pointer compilation and general rollback remain separate. -/
namespace Solidity.Lowering.StorageOps.SourceByteCaptureSuccessControls
open Solidity
open SourceNestedByteCaptureControls (env left right child frame Γ locals)
open SourceVaryingByteCaptureControls (seed length after)
open SourceByteCaptureSuccess

def capturedPayload : Nat → Nat → UInt8 := SourceVaryingByteCaptureControls.payload

def initial : Source.Locals env.layout Γ × Source.St env := (locals,seed)
def full := (Source.loadElems (E:=env) (Γ:=Γ) frame 8 (.bytes .memory) left 0 3).run initial
def slice := (Source.loadElems (E:=env) (Γ:=Γ) frame 7 (.bytes .memory) left 1 2).run initial
def readonly := (Source.loadElems (E:=env) (Γ:=Γ) {frame with static:=true} 8 (.bytes .memory) left 0 3).run initial
def empty := (Source.loadElems (E:=env) (Γ:=Γ) frame 3 (.bytes .memory) left 42 0).run initial
def insufficient := (Source.loadElems (E:=env) (Γ:=Γ) frame 7 (.bytes .memory) left 0 3).run initial
def snapshot := (Source.loadMem (E:=env) (Γ:=Γ) frame 9 (.array .memory (.bytes .memory) none) left).run initial
def afterSlice := (List.range' 1 2).foldl
 (fun s j=>SourceNestedByteValues.allocateAt (length j) capturedPayload s j) seed

def full_client := capture_all frame left 0 3 2 length capturedPayload locals seed (by
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
def slice_client := capture_all frame left 1 2 2 length capturedPayload locals seed (by
 intro j member
 have cases : j=0 ∨ j=1 := by omega
 rcases cases with rfl | rfl <;> decide) (by
 intro j member
 have cases : j=0 ∨ j=1 := by omega
 rcases cases with rfl | rfl <;> rfl) (by
 intro j member k bound
 have outer : j=0 ∨ j=1 := by omega
 have inner : k=0 ∨ k=1 := by unfold length at bound; split at bound <;> omega
 rcases outer with rfl | rfl <;> rcases inner with rfl | rfl <;> rfl)

def valRef {τ : Source.STy} : Source.Val env.layout τ → Option Nat
 | .memRef _ a => some a
 | _ => none
def reference {τ : Source.STy} : Source.Data env.layout τ → Option Nat
 | .val v => valRef v
 | _ => none
def arrayRefs {τ : Source.STy} : Source.Data env.layout τ → Option (List (Option Nat))
 | .array _ _ xs => some (List.ofFn (fun j=>reference (xs j)))
 | _ => none
def view {count : Nat} (r : Except Source.Halt (Fin count → Source.Data env.layout (.bytes .memory)) × (Source.Locals env.layout Γ × Source.St env)) :=
 (r.1.map (fun xs=>List.ofFn (fun j=>reference (xs j))),r.2)
def outcomes : Prop :=
 (view full,view slice,view readonly,view empty,view insufficient,snapshot.1.map arrayRefs,snapshot.2)=
 ((.ok [some 1,some 2,some 3],(locals,after 3)),
  (.ok [some 1,some 2],(locals,afterSlice)),
  (.ok [some 1,some 2,some 3],(locals,after 3)),
  (.ok [],initial),(.error .timeout,(locals,after 2)),
  .ok (some [some 1,some 2,some 3]),(locals,after 3))
def states := [full.2,slice.2,readonly.2,empty.2,insufficient.2,snapshot.2]
def ordered : Prop := states.map (fun r=>
 (r.1,SourceVaryingByteCaptureControls.headerView r.2,SourceVaryingByteCaptureControls.bytes r.2,
  SourceVaryingByteCaptureControls.heapView r.2,r.2.ex.journal.length,SourceVaryingByteCaptureControls.context r.2))=
 [(4,[some [9,8],some [53],some [61,67],some [71,73],none]),
  (3,[some [9,8],some [61,67],some [71,73],none,none]),
  (4,[some [9,8],some [53],some [61,67],some [71,73],none]),
  (1,[some [9,8],none,none,none,none]),
  (3,[some [9,8],some [53],some [61,67],none,none]),
  (4,[some [9,8],some [53],some [61,67],some [71,73],none])].map (fun h=>
 (locals,[some 3,some 1,some 1,some 2,some 2,some 1],
 [some [53],some [59],some [61],some [67],some [71],some [73],some [97],some [97],some [17]],
 h,1,(19,3,some 0,0,[(7,[9,8])],[.bool])))
def reads := [0,1,2,3,4].map (fun a=>
 (Source.heapBytes (E:=env) (Γ:=Γ) a).run (locals,full.2.2))
def readbacks : Prop := reads=
 [(.ok [9,8],(locals,after 3)),(.ok [53],(locals,after 3)),
  (.ok [61,67],(locals,after 3)),(.ok [71,73],(locals,after 3)),
  (.error (.stuck "dangling memory reference"),(locals,after 3))]
theorem outcome_certificate : outcomes := by rfl
theorem observations : ordered := by rfl
theorem heap_readbacks : readbacks := by rfl
theorem journals : states.map (fun r=>SourceVaryingByteCaptureControls.journalRows r.2)=List.replicate 6
 [(7,[some 3,some 1,some 1,some 2,some 2,some 1],
 [some [53],some [59],some [61],some [67],some [71],some [73],some [97],some [97],some [17]],19,3,some 0)] := by rfl
theorem shifted_not_absolute : (view slice).1≠.ok [some 2,some 3] := by
 change (Except.ok ([some 1,some 2] : List (Option Nat)) : Except Source.Halt (List (Option Nat)))≠.ok [some 2,some 3]
 intro h
 cases h
/-- info: 'Solidity.Lowering.StorageOps.SourceByteCaptureSuccessControls.full_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms full_client
/-- info: 'Solidity.Lowering.StorageOps.SourceByteCaptureSuccessControls.slice_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms slice_client
/-- info: 'Solidity.Lowering.StorageOps.SourceByteCaptureSuccessControls.outcome_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outcome_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceByteCaptureSuccessControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observations
/-- info: 'Solidity.Lowering.StorageOps.SourceByteCaptureSuccessControls.heap_readbacks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms heap_readbacks
/-- info: 'Solidity.Lowering.StorageOps.SourceByteCaptureSuccessControls.journals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms journals
/-- info: 'Solidity.Lowering.StorageOps.SourceByteCaptureSuccessControls.shifted_not_absolute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms shifted_not_absolute
end Solidity.Lowering.StorageOps.SourceByteCaptureSuccessControls
