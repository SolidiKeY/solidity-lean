import Solidity.Backend.InternalFlow.RuntimeFrameV3DistinctParentRestore
import Solidity.Backend.InternalFlow.RuntimeFrameV3CountdownWitness

/-! Actual save, different-reference entry and restore over the published
populated two-object heap. Native local stores correspond to typed local
updates; no general recursive compiler or source-call selection is claimed. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource CountdownWitness
abbrev F := CountdownWitness.F.push (.val .uint) .ok
def parent := (CountdownWitness.callee.setLocal (.there .here) (some CompileExamples.r1)).push
  (t:=.val .uint) (countValue 7 (by decide))
def before := writeMachine (writeMachine CountdownWitness.machine 2 w[20]) 4 w[7]
theorem parent_repr : StateRepr 1 2 16 F parent P.base before :=
 (CountdownWitness.callee_repr.setMem (.there .here) CompileExamples.r1).consVal
  (countValue 7 (by decide)) w[7] (ReprV.uint_of rfl) (by decide)

theorem capture_exists : ∃ m,
 run (Restore.saveCells 8 [2,3]) before=.ok m 0 ∧
 Context.Captured before m [2,3] 5 8 10 ∧
 StateRepr 1 2 16 F parent P.base m ∧
 GrowsAllocator 2 16 0 parent P.base before parent P.base m :=
 Context.capture_many [2,3] before 5 8 10 parent_repr (by decide)
  (by intro x hx; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; rcases hx with rfl|rfl <;> decide)
  (by decide) (by decide) (by decide) (by decide) (.inl (by decide)) (by decide) rfl

noncomputable def captured := capture_exists.choose

theorem capture_spec : run (Restore.saveCells 8 [2,3]) before=.ok captured 0 ∧
 Context.Captured before captured [2,3] 5 8 10 ∧
 StateRepr 1 2 16 F parent P.base captured ∧
 GrowsAllocator 2 16 0 parent P.base before parent P.base captured := capture_exists.choose_spec

def child := (parent.setLocal (.there (.there .here)) (some P.r0)).setLocal
  (.there .here) (countValue 0 W_pos)
noncomputable def after := writeMachine (writeMachine captured 2 w[16]) 3 w[0]
def captureCode := Restore.saveCells 8 (Restore.contextCells 2 (Parameters A))
def entryCode : List Instr := [.push w[16],.mstore 2,.push w[0],.mstore 3]
def restoreCode := Restore.restoreCells 8 (Restore.contextCells 2 (Parameters A))

theorem capture_run : run captureCode before=.ok captured 0 := capture_spec.1

theorem captured_repr : StateRepr 1 2 16 F parent P.base captured := capture_spec.2.2.1

theorem entry_run : run entryCode captured=.ok after 0 := by rfl

theorem after_repr : StateRepr 1 2 16 F child P.base after :=
 (captured_repr.setMem (.there (.there .here)) P.r0).setVal (.there .here)
  (countValue 0 W_pos) w[0] (ReprV.uint_of rfl)

theorem payload : after.mem 10=w[20] ∧ after.mem 11=w[2] ∧ after.mem 8=w[12] := by
 have first := capture_spec.2.1.payload 0 (by decide)
 have second := capture_spec.2.1.payload 1 (by decide)
 have pointer := capture_spec.2.1.cursor
 change captured.mem 10=w[20] at first
 change captured.mem 11=w[2] at second
 change captured.mem 8=w[12] at pointer
 simpa only [after,writeMachine,upd] using And.intro first (And.intro second pointer)

theorem actual_different : after.mem 2≠after.mem 10 := by
 rw [payload.1]
 change w[16]≠w[20]
 decide +kernel

theorem endpoint : ∃ last,
 run (captureCode++entryCode++restoreCode) before=.ok last 0 ∧
 StateRepr 1 2 16 F
  ((child.setLocal (.there (.there .here)) (some CompileExamples.r1)).setLocal
   (.there .here) (countValue 2 (by decide))) P.base last ∧
 last.stack=[w[77]] ∧ last.mem 2=w[20] ∧ last.mem 3=w[2] ∧ last.mem 4=w[7] ∧
 last.mem 8=w[10] ∧
 (∀ x, x≠8 → x≠2 → x≠3 → last.mem x=after.mem x) := by
 obtain ⟨last,executed,represented,stack,cursor,reference,counter,result,growth,outside⟩ :=
  restore child P.base after after_repr CompileExamples.r1 2 (by decide) 5 8 10
   (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) payload.2.2 payload.1 payload.2.1
 have savedStack : after.stack=[w[77]] := capture_spec.2.1.stack
 refine ⟨last,?_,represented,stack.trans savedStack,reference,counter,?_,cursor,outside⟩
 · rw [run_append_ok (by rw [run_append_ok capture_run]; exact entry_run)]
   exact executed
 · change last.mem 4=w[7]
   rw [result]
   change captured.mem 4=w[7]
   exact capture_spec.2.1.locals 4 (by decide)

theorem wrong_active : ∀ last,
 run restoreCode after=.ok last 0 → last.mem 2≠w[16] := by
 intro last actual
 obtain ⟨known,executed,represented,stack,cursor,reference,counter,result,growth,outside⟩ :=
  restore child P.base after after_repr CompileExamples.r1 2 (by decide) 5 8 10
   (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) payload.2.2 payload.1 payload.2.1
 have same : last=known := (Out.ok.inj (actual.symm.trans executed)).1
 rw [same,reference]
 decide +kernel

noncomputable def last := endpoint.choose

theorem completed :
 run (captureCode++entryCode++restoreCode) before=.ok last 0 ∧
 StateRepr 1 2 16 F
  ((child.setLocal (.there (.there .here)) (some CompileExamples.r1)).setLocal
   (.there .here) (countValue 2 (by decide))) P.base last ∧
 last.stack=[w[77]] ∧ last.mem 2=w[20] ∧ last.mem 3=w[2] ∧ last.mem 4=w[7] ∧
 last.mem 8=w[10] ∧
 (∀ x, x≠8 → x≠2 → x≠3 → last.mem x=after.mem x) := endpoint.choose_spec

theorem wrong_result : last.mem 4≠w[0] := by
 rw [completed.2.2.2.2.2.1]
 decide +kernel

theorem wrong_counter : last.mem 3≠w[0] := by
 rw [completed.2.2.2.2.1]
 decide +kernel

theorem wrong_cursor : last.mem 8≠w[12] := by
 rw [completed.2.2.2.2.2.2.1]
 decide +kernel

theorem not_revert : run (captureCode++entryCode++restoreCode) before≠.revert := by
 rw [completed.1]
 intro wrong
 cases wrong

end Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.parent_repr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.parent_repr

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.capture_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.capture_exists

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.capture_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.capture_spec

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.capture_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.capture_run

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.captured_repr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.captured_repr

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.entry_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.entry_run

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.after_repr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.after_repr

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.payload

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.actual_different' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.actual_different

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.endpoint

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.wrong_active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.wrong_active

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.completed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.completed

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.wrong_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.wrong_result

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.wrong_counter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.wrong_counter

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.wrong_cursor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.wrong_cursor

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.not_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.DistinctParentRestore.Controls.not_revert
