import Solidity.Lowering.StorageOps.SourceReadFrames
import Solidity.Lowering.StorageOps.SourceArrayReadback
import Solidity.Source.Eval
import Solidity.Backend.StorageOps.TargetArrayDeleteSequence

/-! Actual captured two-array Source deletion and actual evolving-header target
code. Source/target address lowering, whole compiler and world closure remain
separate; OLD access/capture premises are never postcondition substitutes. -/
namespace Solidity.Backend.StorageOps.SourceTwoArrayDeletes
open SourceScalarDeleteLog SourceArrayDeleteTarget SourceReadFrames

/-- A composition of the existing actual Source operators, not an evaluator. -/
def program {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (leftTy rightTy : Source.IntTy) (left right : Source.SPath) (leftCount rightCount : Nat) :
    Source.EM E Γ Unit := do
  Source.deleteStor frame (leftCount + 2) (.array .storage (.int leftTy) none) left
  Source.deleteStor frame (rightCount + 2) (.array .storage (.int rightTy) none) right

/-- Derive the next actual read, preserving all success/failure outcomes. -/
theorem array_readLen_other {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (intTy : Source.IntTy)
    (path query : Source.SPath) (count : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (input : (Source.readLen (E := E) (Γ := Γ) frame path).run (locals,state) =
      (.ok count,(locals,state)))
    (headerApart : query ≠ path)
    (dataApart : ∀ i ∈ List.range' 0 count, query ≠ path.go (.index i)) :
    let first := (Source.deleteStor (E := E) (Γ := Γ) frame (count + 2)
      (.array .storage (.int intTy) none) path).run (locals,state)
    (Source.readLen frame query).run first.2 =
      (((Source.readLen (E := E) (Γ := Γ) frame query).run (locals,state)).1,first.2) := by
  dsimp only
  rw [source_array_run frame writable intTy path count locals state input,Source.run_append]
  simp only [Source.ExecState.run]
  rw [readLen_clearOp_other frame path query locals
    {state with ex := state.ex.run ((List.range' 0 count).map (fun i => clearOp E frame (path.go (.index i))))} headerApart]
  rw [readLen_log_other frame path query (List.range' 0 count) locals state dataApart]

/-- Both ORIGINAL header reads and the first generated access exclusion derive
actual two-operation success, exact locals/state and the ordered existing log. -/
theorem source_run {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (leftTy rightTy : Source.IntTy)
    (left right : Source.SPath) (leftCount rightCount : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (leftInput : (Source.readLen (E := E) (Γ := Γ) frame left).run (locals,state) =
      (.ok leftCount,(locals,state)))
    (rightInput : (Source.readLen (E := E) (Γ := Γ) frame right).run (locals,state) =
      (.ok rightCount,(locals,state)))
    (headerApart : right ≠ left)
    (dataApart : ∀ i ∈ List.range' 0 leftCount, right ≠ left.go (.index i)) :
    let leftOps := (List.range' 0 leftCount).map (fun i => clearOp E frame (left.go (.index i))) ++ [clearOp E frame left]
    let rightOps := (List.range' 0 rightCount).map (fun i => clearOp E frame (right.go (.index i))) ++ [clearOp E frame right]
    (program frame leftTy rightTy left right leftCount rightCount).run (locals,state) =
      (.ok (), (locals,{state with ex := state.ex.run (leftOps ++ rightOps)})) := by
  dsimp only
  unfold program
  rw [Source.Hoare.run_bind,source_array_run frame writable leftTy left leftCount locals state leftInput]
  simp only []
  have middleRead := array_readLen_other frame writable leftTy left right leftCount locals state leftInput headerApart dataApart
  rw [source_array_run frame writable leftTy left leftCount locals state leftInput,rightInput] at middleRead
  rw [source_array_run frame writable rightTy right rightCount _ _ middleRead]
  simp only [Source.run_append]

/-- Expose the ACTUAL second operation, including its possible halt. -/
theorem second_stage {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (leftTy rightTy : Source.IntTy)
    (left right : Source.SPath) (leftCount rightCount : Nat)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (leftInput : (Source.readLen (E := E) (Γ := Γ) frame left).run (locals,state) =
      (.ok leftCount,(locals,state))) :
    (program frame leftTy rightTy left right leftCount rightCount).run (locals,state) =
      (Source.deleteStor frame (rightCount + 2) (.array .storage (.int rightTy) none) right).run
        (locals,{state with ex := state.ex.run ((List.range' 0 leftCount).map (fun i => clearOp E frame (left.go (.index i))) ++ [clearOp E frame left])}) := by
  unfold program
  rw [Source.Hoare.run_bind,source_array_run frame writable leftTy left leftCount locals state leftInput]

/-- First selected data after both Source operations, with exact second frames. -/
theorem source_first_data {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (left right : Source.SPath)
    (leftCount rightCount j : Nat) (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (typed : E.pathTy left = some (.array .storage (.int Source.IntTy.u256) none))
    (ordinary : E.transientRoot left = false)
    (leftInput : (Source.readLen (E := E) (Γ := Γ) frame left).run (locals,state) = (.ok leftCount,(locals,state)))
    (rightInput : (Source.readLen (E := E) (Γ := Γ) frame right).run (locals,state) = (.ok rightCount,(locals,state)))
    (headerApart : right ≠ left)
    (dataApart : ∀ i ∈ List.range' 0 leftCount, right ≠ left.go (.index i))
    (observerHeaderApart : left.go (.index j) ≠ right)
    (observerDataApart : ∀ k ∈ List.range' 0 rightCount, left.go (.index j) ≠ right.go (.index k)) :
    wordAt frame ((program frame Source.IntTy.u256 Source.IntTy.u256 left right leftCount rightCount).run (locals,state)).2.2.ex (left.go (.index j)) =
      if j < leftCount then some 0 else wordAt frame state.ex (left.go (.index j)) := by
  have middleRead := array_readLen_other frame writable Source.IntTy.u256 left right leftCount locals state leftInput headerApart dataApart
  rw [source_array_run frame writable Source.IntTy.u256 left leftCount locals state leftInput,rightInput] at middleRead
  rw [second_stage frame writable Source.IntTy.u256 Source.IntTy.u256 left right leftCount rightCount locals state leftInput]
  rw [source_array_other frame writable Source.IntTy.u256 right (left.go (.index j)) rightCount locals _ middleRead observerHeaderApart observerDataApart]
  have original := source_array_data frame writable left leftCount j locals state typed ordinary leftInput
  rw [source_array_run frame writable Source.IntTy.u256 left leftCount locals state leftInput] at original
  exact original

/-- Second data uses OLD first-operation frames only on unvisited retained words. -/
theorem source_second_data {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (left right : Source.SPath)
    (leftCount rightCount j : Nat) (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (typed : E.pathTy right = some (.array .storage (.int Source.IntTy.u256) none))
    (ordinary : E.transientRoot right = false)
    (leftInput : (Source.readLen (E := E) (Γ := Γ) frame left).run (locals,state) = (.ok leftCount,(locals,state)))
    (rightInput : (Source.readLen (E := E) (Γ := Γ) frame right).run (locals,state) = (.ok rightCount,(locals,state)))
    (headerApart : right ≠ left)
    (dataApart : ∀ i ∈ List.range' 0 leftCount, right ≠ left.go (.index i))
    (unvisited : rightCount ≤ j → right.go (.index j) ≠ left ∧
      ∀ i ∈ List.range' 0 leftCount, right.go (.index j) ≠ left.go (.index i)) :
    wordAt frame ((program frame Source.IntTy.u256 Source.IntTy.u256 left right leftCount rightCount).run (locals,state)).2.2.ex (right.go (.index j)) =
      if j < rightCount then some 0 else wordAt frame state.ex (right.go (.index j)) := by
  have middleRead := array_readLen_other frame writable Source.IntTy.u256 left right leftCount locals state leftInput headerApart dataApart
  rw [source_array_run frame writable Source.IntTy.u256 left leftCount locals state leftInput,rightInput] at middleRead
  rw [second_stage frame writable Source.IntTy.u256 Source.IntTy.u256 left right leftCount rightCount locals state leftInput]
  rw [source_array_data frame writable right rightCount j locals _ typed ordinary middleRead]
  by_cases live : j < rightCount
  · simp only [if_pos live]
  · simp only [if_neg live]
    have original := source_array_other frame writable Source.IntTy.u256 left (right.go (.index j)) leftCount locals state leftInput
      (unvisited (by omega)).1 (unvisited (by omega)).2
    rw [source_array_run frame writable Source.IntTy.u256 left leftCount locals state leftInput] at original
    exact original

/-- Both logical headers, with reverse exclusion preserving the first header. -/
theorem source_headers {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (left right : Source.SPath)
    (leftCount rightCount : Nat) (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (leftTyped : E.pathTy left = some (.array .storage (.int Source.IntTy.u256) none))
    (rightTyped : E.pathTy right = some (.array .storage (.int Source.IntTy.u256) none))
    (leftOrdinary : E.transientRoot left = false) (rightOrdinary : E.transientRoot right = false)
    (leftInput : (Source.readLen (E := E) (Γ := Γ) frame left).run (locals,state) = (.ok leftCount,(locals,state)))
    (rightInput : (Source.readLen (E := E) (Γ := Γ) frame right).run (locals,state) = (.ok rightCount,(locals,state)))
    (headerApart : right ≠ left)
    (leftDataApart : ∀ i ∈ List.range' 0 leftCount, right ≠ left.go (.index i))
    (rightDataApart : ∀ i ∈ List.range' 0 rightCount, left ≠ right.go (.index i)) :
    let result := (program frame Source.IntTy.u256 Source.IntTy.u256 left right leftCount rightCount).run (locals,state)
    wordAt frame result.2.2.ex left = some 0 ∧ wordAt frame result.2.2.ex right = some 0 := by
  dsimp only
  have middleRead := array_readLen_other frame writable Source.IntTy.u256 left right leftCount locals state leftInput headerApart leftDataApart
  rw [source_array_run frame writable Source.IntTy.u256 left leftCount locals state leftInput,rightInput] at middleRead
  simp only [second_stage frame writable Source.IntTy.u256 Source.IntTy.u256 left right leftCount rightCount locals state leftInput]
  constructor
  · rw [source_array_other frame writable Source.IntTy.u256 right left rightCount locals _ middleRead (Ne.symm headerApart) rightDataApart]
    have original := source_array_header frame writable left leftCount locals state leftTyped leftOrdinary leftInput
    rw [source_array_run frame writable Source.IntTy.u256 left leftCount locals state leftInput] at original
    exact original
  · exact source_array_header frame writable right rightCount locals _ rightTyped rightOrdinary middleRead

/-- First selected Source/target word. OLD word agreement is required only
for an unvisited retained word, never as a desired middle/post relation. -/
theorem first_correspondence {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (left right : Source.SPath)
    (leftCount rightCount j : Nat) (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (typed : E.pathTy left = some (.array .storage (.int Source.IntTy.u256) none))
    (ordinary : E.transientRoot left = false)
    (leftInput : (Source.readLen (E := E) (Γ := Γ) frame left).run (locals,state) = (.ok leftCount,(locals,state)))
    (rightInput : (Source.readLen (E := E) (Γ := Γ) frame right).run (locals,state) = (.ok rightCount,(locals,state)))
    (headerApart : right ≠ left)
    (dataApart : ∀ i ∈ List.range' 0 leftCount, right ≠ left.go (.index i))
    (observerHeaderApart : left.go (.index j) ≠ right)
    (observerDataApart : ∀ k ∈ List.range' 0 rightCount, left.go (.index j) ≠ right.go (.index k))
    (target : Evm.Machine) (tail : List Evm.Word) (first second : Evm.Slot)
    (firstHeader : target.store first = leftCount)
    (targetHeaderApart : second ≠ first)
    (targetHeaderDataApart : ∀ k, k < target.store first → second ≠ .data first k)
    (targetObserverHeaderApart : Evm.Slot.data first j ≠ second)
    (targetObserverDataApart : ∀ k, k < target.store second → Evm.Slot.data first j ≠ .data second k)
    (old : leftCount ≤ j → wordAt frame state.ex (left.go (.index j)) = some (target.store (.data first j))) :
    wordAt frame ((program frame Source.IntTy.u256 Source.IntTy.u256 left right leftCount rightCount).run (locals,state)).2.2.ex (left.go (.index j)) =
      some ((TargetArrayDeleteSequence.after target tail first second).store (.data first j)) := by
  rw [source_first_data frame writable left right leftCount rightCount j locals state typed ordinary leftInput rightInput headerApart dataApart observerHeaderApart observerDataApart]
  rw [TargetArrayDeleteSequence.first_data target tail first second j targetHeaderApart targetHeaderDataApart targetObserverHeaderApart targetObserverDataApart,firstHeader]
  by_cases live : j < leftCount
  · simp only [if_pos live]
  · simp only [if_neg live]
    exact old (by omega)

/-- Selected second Source/target word; OLD tail and both unvisited frames
remain explicit and are not replaced by desired postconditions. -/
theorem second_correspondence {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (left right : Source.SPath)
    (leftCount rightCount j : Nat) (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (typed : E.pathTy right = some (.array .storage (.int Source.IntTy.u256) none))
    (ordinary : E.transientRoot right = false)
    (leftInput : (Source.readLen (E := E) (Γ := Γ) frame left).run (locals,state) = (.ok leftCount,(locals,state)))
    (rightInput : (Source.readLen (E := E) (Γ := Γ) frame right).run (locals,state) = (.ok rightCount,(locals,state)))
    (headerApart : right ≠ left)
    (dataApart : ∀ i ∈ List.range' 0 leftCount, right ≠ left.go (.index i))
    (unvisited : rightCount ≤ j → right.go (.index j) ≠ left ∧
      ∀ i ∈ List.range' 0 leftCount, right.go (.index j) ≠ left.go (.index i))
    (target : Evm.Machine) (tail : List Evm.Word) (first second : Evm.Slot)
    (secondHeader : target.store second = rightCount)
    (targetHeaderApart : second ≠ first)
    (targetHeaderDataApart : ∀ k, k < target.store first → second ≠ .data first k)
    (targetUnvisited : target.store second ≤ j → Evm.Slot.data second j ≠ first ∧
      ∀ k, k < target.store first → Evm.Slot.data second j ≠ .data first k)
    (old : rightCount ≤ j → wordAt frame state.ex (right.go (.index j)) = some (target.store (.data second j))) :
    wordAt frame ((program frame Source.IntTy.u256 Source.IntTy.u256 left right leftCount rightCount).run (locals,state)).2.2.ex (right.go (.index j)) =
      some ((TargetArrayDeleteSequence.after target tail first second).store (.data second j)) := by
  rw [source_second_data frame writable left right leftCount rightCount j locals state typed ordinary leftInput rightInput headerApart dataApart unvisited]
  rw [TargetArrayDeleteSequence.second_data target tail first second j targetHeaderApart targetHeaderDataApart targetUnvisited,secondHeader]
  by_cases live : j < rightCount
  · simp only [if_pos live]
  · simp only [if_neg live]
    exact old (by omega)

/-- Both ACTUAL post-operation header reads are derived, including exact
read-only states. Neither desired zero read is supplied as a premise. -/
theorem source_reads {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (left right : Source.SPath)
    (leftCount rightCount : Nat) (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (leftTyped : E.pathTy left = some (.array .storage (.int Source.IntTy.u256) none))
    (rightTyped : E.pathTy right = some (.array .storage (.int Source.IntTy.u256) none))
    (leftOrdinary : E.transientRoot left = false) (rightOrdinary : E.transientRoot right = false)
    (leftInput : (Source.readLen (E := E) (Γ := Γ) frame left).run (locals,state) = (.ok leftCount,(locals,state)))
    (rightInput : (Source.readLen (E := E) (Γ := Γ) frame right).run (locals,state) = (.ok rightCount,(locals,state)))
    (headerApart : right ≠ left)
    (leftDataApart : ∀ i ∈ List.range' 0 leftCount, right ≠ left.go (.index i))
    (rightDataApart : ∀ i ∈ List.range' 0 rightCount, left ≠ right.go (.index i)) :
    let result := (program frame Source.IntTy.u256 Source.IntTy.u256 left right leftCount rightCount).run (locals,state)
    (Source.readLen frame left).run result.2 = (.ok 0,result.2) ∧
    (Source.readLen frame right).run result.2 = (.ok 0,result.2) := by
  dsimp only
  let middle : Source.St E := {state with ex := state.ex.run ((List.range' 0 leftCount).map (fun i => clearOp E frame (left.go (.index i))) ++ [clearOp E frame left])}
  have middleRead : (Source.readLen (E := E) (Γ := Γ) frame right).run (locals,middle) = (.ok rightCount,(locals,middle)) := by
    have stable := array_readLen_other frame writable Source.IntTy.u256 left right leftCount locals state leftInput headerApart leftDataApart
    rw [source_array_run frame writable Source.IntTy.u256 left leftCount locals state leftInput,rightInput] at stable
    exact stable
  have leftZero : (Source.readLen (E := E) (Γ := Γ) frame left).run (locals,middle) = (.ok 0,(locals,middle)) := by
    have zero := SourceArrayReadback.source_array_readback frame writable left leftCount locals state leftOrdinary (array_header_type left leftTyped) leftInput
    rw [source_array_run frame writable Source.IntTy.u256 left leftCount locals state leftInput] at zero
    exact zero
  have leftStable := array_readLen_other frame writable Source.IntTy.u256 right left rightCount locals middle middleRead (Ne.symm headerApart) rightDataApart
  rw [leftZero] at leftStable
  have rightZero := SourceArrayReadback.source_array_readback frame writable right rightCount locals middle rightOrdinary (array_header_type right rightTyped) middleRead
  simp only [second_stage frame writable Source.IntTy.u256 Source.IntTy.u256 left right leftCount rightCount locals state leftInput]
  exact ⟨leftStable,rightZero⟩

/-- Actual fresh Source indexing after the two deletions refuses EVERY natural
index with its existing exact panic, preserving the post-operation state. -/
theorem source_index_refusal {E : Source.Env} {Γ : Source.RCtx}
    (frame : Source.Fr) (writable : frame.static = false) (left right : Source.SPath)
    (leftCount rightCount j : Nat) (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (leftTyped : E.pathTy left = some (.array .storage (.int Source.IntTy.u256) none))
    (rightTyped : E.pathTy right = some (.array .storage (.int Source.IntTy.u256) none))
    (leftOrdinary : E.transientRoot left = false) (rightOrdinary : E.transientRoot right = false)
    (leftInput : (Source.readLen (E := E) (Γ := Γ) frame left).run (locals,state) = (.ok leftCount,(locals,state)))
    (rightInput : (Source.readLen (E := E) (Γ := Γ) frame right).run (locals,state) = (.ok rightCount,(locals,state)))
    (headerApart : right ≠ left)
    (leftDataApart : ∀ i ∈ List.range' 0 leftCount, right ≠ left.go (.index i))
    (rightDataApart : ∀ i ∈ List.range' 0 rightCount, left ≠ right.go (.index i)) :
    let reference : Source.Val E.layout (.array .storage (.int Source.IntTy.u256) none) := .storRef rfl left
    let result := (program frame Source.IntTy.u256 Source.IntTy.u256 left right leftCount rightCount).run (locals,state)
    (Source.indexLoc frame reference j).run result.2 = (.error (.revert (Source.panicData .index)),result.2) := by
  dsimp only
  have zero := (source_reads frame writable left right leftCount rightCount locals state leftTyped rightTyped leftOrdinary rightOrdinary leftInput rightInput headerApart leftDataApart rightDataApart).1
  change (((Source.readLen frame left >>= fun length =>
    if j < length then pure (.stor (left.go (.index j))) else Source.EM.lift (Source.panic .index)) :
      Source.EM E Γ (Source.Loc E.layout Γ (.int Source.IntTy.u256))).run _) = _
  rw [Source.Hoare.run_bind,zero]
  simp only [Nat.not_lt_zero,if_false]
  rfl

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeletes.array_readLen_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms array_readLen_other

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeletes.source_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_run

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeletes.second_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms second_stage

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeletes.source_first_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_first_data

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeletes.source_second_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_second_data

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeletes.source_headers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_headers

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeletes.first_correspondence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms first_correspondence

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeletes.second_correspondence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms second_correspondence

/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeletes.source_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_reads
/-- info: 'Solidity.Backend.StorageOps.SourceTwoArrayDeletes.source_index_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_index_refusal
end Solidity.Backend.StorageOps.SourceTwoArrayDeletes
