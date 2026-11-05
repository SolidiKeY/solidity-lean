import Solidity.Lowering.StorageOps.SourceCaptureReadback
import Solidity.Lowering.StorageOps.SourceByteCaptureSuccessControls

/-! Generic allocation observations instantiated against actual Source capture
and typed heap reads. Wrong types and wrong shifted offsets remain failures;
older objects, storage, contexts and journals are retained. -/
namespace Solidity.Lowering.StorageOps.SourceCaptureReadbackControls
open Solidity
open SourceNestedByteCaptureControls (env left right child frame Γ locals)
open SourceVaryingByteCaptureControls (seed length)
open SourceByteCaptureSuccessControls (capturedPayload full slice afterSlice)
open SourceCaptureReadback

def full_client := allocation_observations seed 0 3 length capturedPayload
def slice_client := allocation_observations seed 1 2 length capturedPayload
def typed (s : Source.St env) (a : Nat) :=
 (Source.heapAt (E:=env) (Γ:=Γ) a (.bytes .memory)).run (locals,s)
def fullReads := [0,1,2,3,4].map (typed full.2.2)
def sliceReads := [0,1,2,3].map (typed slice.2.2)
def afterFull := SourceVaryingByteCaptureControls.after 3
def outcomes : Prop :=
 (fullReads,sliceReads,
  (Source.heapAt (E:=env) (Γ:=Γ) 1 .bool).run (locals,full.2.2))=
 ([ (.ok (.bytes [9,8]),(locals,afterFull)),(.ok (.bytes [53]),(locals,afterFull)),
    (.ok (.bytes [61,67]),(locals,afterFull)),(.ok (.bytes [71,73]),(locals,afterFull)),
    (.error (.stuck "dangling memory reference"),(locals,afterFull)) ],
  [ (.ok (.bytes [9,8]),(locals,afterSlice)),(.ok (.bytes [61,67]),(locals,afterSlice)),
    (.ok (.bytes [71,73]),(locals,afterSlice)),
    (.error (.stuck "dangling memory reference"),(locals,afterSlice)) ],
  (.error (.stuck "memory object type"),(locals,afterFull)))
def states := fullReads.map Prod.snd ++ sliceReads.map Prod.snd ++
 [(Source.heapAt (E:=env) (Γ:=Γ) 1 .bool).run (locals,full.2.2) |>.2]
def ordered : Prop := states.map (fun r=>
 (r.1,SourceVaryingByteCaptureControls.headerView r.2,SourceVaryingByteCaptureControls.bytes r.2,
  SourceVaryingByteCaptureControls.heapView r.2,r.2.ex.journal.length,SourceVaryingByteCaptureControls.context r.2))=
 (List.replicate 5 (4,[some [9,8],some [53],some [61,67],some [71,73],none]) ++
  List.replicate 4 (3,[some [9,8],some [61,67],some [71,73],none,none]) ++
  [(4,[some [9,8],some [53],some [61,67],some [71,73],none])]).map (fun h=>
 (locals,[some 3,some 1,some 1,some 2,some 2,some 1],
 [some [53],some [59],some [61],some [67],some [71],some [73],some [97],some [97],some [17]],
 h,1,(19,3,some 0,0,[(7,[9,8])],[.bool])))
theorem outcome_certificate : outcomes := by rfl
theorem observations : ordered := by rfl
theorem journal_observations : states.map (fun r=>SourceVaryingByteCaptureControls.journalRows r.2)=List.replicate 10
 [(7,[some 3,some 1,some 1,some 2,some 2,some 1],
 [some [53],some [59],some [61],some [67],some [71],some [73],some [97],some [97],some [17]],19,3,some 0)] := by rfl
/-- info: 'Solidity.Lowering.StorageOps.SourceCaptureReadbackControls.full_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms full_client
/-- info: 'Solidity.Lowering.StorageOps.SourceCaptureReadbackControls.slice_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms slice_client
/-- info: 'Solidity.Lowering.StorageOps.SourceCaptureReadbackControls.outcome_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outcome_certificate
/-- info: 'Solidity.Lowering.StorageOps.SourceCaptureReadbackControls.observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observations
/-- info: 'Solidity.Lowering.StorageOps.SourceCaptureReadbackControls.journal_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms journal_observations
end Solidity.Lowering.StorageOps.SourceCaptureReadbackControls
