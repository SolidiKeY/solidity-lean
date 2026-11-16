import Solidity.Yul.Compilation.SwitchSequenceCompletion
import Solidity.Yul.Compilation.SwitchSequenceControls
/-! Reverse controls reuse actual compiled target execution, not an assumed
exchange or desired source run. These are kernel-model normal-success laws;
caller height remains uncapped and proves no native 1024-word capacity. -/
namespace Solidity.Yul.Compilation.SwitchSequenceCompletion.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SwitchSequence.Controls (artifact second)

theorem success_iff (locals out : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro (.seq MultiSwitchCompilation.Controls.source second)
   artifact.profile (sourceLocals locals) = some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 :=
 completion_iff artifact locals out m caller

theorem source_recovered (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro (.seq MultiSwitchCompilation.Controls.source second)
   artifact.profile (sourceLocals #v[0,0]) = some ⟨sourceLocals #v[0,6],.normal⟩ :=
 (success_iff #v[0,0] #v[0,6] m caller).mpr (SwitchSequence.Controls.target_done m caller)

/-- The intermediate source frame and executed boundary are recovered from
actual whole-sequence execution; neither is a premise of this witness. -/
theorem boundary_recovered (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ (ha hb : Nat) (mid out : Vector Scalar.Word 2),
 evalStmt ha .nil True.intro MultiSwitchCompilation.Controls.source artifact.left.compiled.profile (sourceLocals #v[0,0]) =
   some ⟨sourceLocals mid,.normal⟩ ∧
 evalStmt hb .nil True.intro second artifact.right.compiled.profile (sourceLocals mid) = some ⟨sourceLocals out,.normal⟩ ∧
 Evm.run artifact.left.code {m with stack := coreWord 0::coreWord 0::caller} =
   .ok {m with stack := mid.toList.map coreWord++caller} 0 := by
 obtain ⟨ha,hb,mid,out,first,last,boundary,_,_,_⟩ := model_to_source artifact #v[0,0] m
   {m with stack := coreWord 0::coreWord 6::caller} caller 0 (SwitchSequence.Controls.target_done m caller)
 exact ⟨ha,hb,mid,out,first,last,boundary⟩

theorem final_height (locals : Vector Scalar.Word 2) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 skip = 0 ∧ final.stack.length = 2+caller.length := by
 obtain ⟨_,_,_,out,_,_,_,_,done,frame⟩ := model_to_source artifact locals m final caller skip ran
 refine ⟨done,?_⟩
 exact CompletionControls.frame_height #v[] out m final caller frame

theorem stale_output_refused (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord 0::coreWord 0::caller} ≠
 .ok {m with stack := coreWord 0::coreWord 3::caller} 0 := by
 intro bad
 have same := (SwitchSequence.Controls.target_done m caller).symm.trans bad
 have frames := (Evm.Out.ok.inj same).1
 have stacks := congrArg Evm.Machine.stack frames
 have different : coreWord (6 : Scalar.Word) ≠ coreWord (3 : Scalar.Word) := by decide
 exact different (List.cons.inj (List.cons.inj stacks).2).1

/-- An oversized host stack is still admitted by this uncapped executor.
This successful model run is explicitly not native capacity evidence. -/
theorem oversized_success (m : Evm.Machine) :
 Evm.run artifact.code {m with stack := coreWord 0::coreWord 0::List.replicate 1025 (coreWord SourceLoop.Controls.dirty)} =
 .ok {m with stack := coreWord 0::coreWord 6::List.replicate 1025 (coreWord SourceLoop.Controls.dirty)} 0 :=
 SwitchSequence.Controls.target_done m _

/-- info: 'Solidity.Yul.Compilation.SwitchSequenceCompletion.Controls.success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_iff
/-- info: 'Solidity.Yul.Compilation.SwitchSequenceCompletion.Controls.source_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_recovered
/-- info: 'Solidity.Yul.Compilation.SwitchSequenceCompletion.Controls.boundary_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms boundary_recovered
/-- info: 'Solidity.Yul.Compilation.SwitchSequenceCompletion.Controls.final_height' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms final_height
/-- info: 'Solidity.Yul.Compilation.SwitchSequenceCompletion.Controls.stale_output_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stale_output_refused
/-- info: 'Solidity.Yul.Compilation.SwitchSequenceCompletion.Controls.oversized_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms oversized_success
end Solidity.Yul.Compilation.SwitchSequenceCompletion.Controls
