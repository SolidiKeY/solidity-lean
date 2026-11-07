import Solidity.Yul.Compilation.CompletionControls
import Solidity.Yul.Compilation.SwitchSequence
import Solidity.Yul.Compilation.MultiSwitchCompletion
/-! Reverse normal-success transport for two actual finite switch artifacts.
The executor boundary is inverted first, and each existing switch reflection
law derives its own source run, pending skip and raw frame. No desired middle
run/frame is assumed. Native capacity and failure/divergence remain separate. -/
namespace Solidity.Yul.Compilation.SwitchSequenceCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SwitchSequence

theorem model_to_source {c n f g} {a b : Stmt [] [] c n}
 (artifact : Artifact f g a b) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (ha hb : Nat) (mid out : Vector Scalar.Word n),
 evalStmt ha .nil True.intro a artifact.left.compiled.profile (sourceLocals locals) = some ⟨sourceLocals mid,.normal⟩ ∧
 evalStmt hb .nil True.intro b artifact.right.compiled.profile (sourceLocals mid) = some ⟨sourceLocals out,.normal⟩ ∧
 Evm.run artifact.left.code {m with stack := locals.toList.map coreWord++caller} =
   .ok {m with stack := mid.toList.map coreWord++caller} 0 ∧
 evalStmt (max ha hb+1) .nil True.intro (.seq a b) artifact.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩ ∧
 skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 have whole : (Evm.run artifact.left.code {m with stack := locals.toList.map coreWord++caller}).bind
   (fun intermediate pending => Evm.exec artifact.right.code pending intermediate) = .ok final skip := by
   simpa only [Artifact.code,Evm.run,Evm.exec_append] using ran
 cases actual : Evm.run artifact.left.code {m with stack := locals.toList.map coreWord++caller} with
 | revert => rw [actual] at whole; cases whole
 | fault => rw [actual] at whole; cases whole
 | ok intermediate pending =>
   obtain ⟨ha,mid,leftSource,retired,frame⟩ := MultiSwitchCompletion.model_to_source artifact.left locals m
     intermediate caller pending actual
   have boundary : Evm.run artifact.left.code {m with stack := locals.toList.map coreWord++caller} =
     .ok {m with stack := mid.toList.map coreWord++caller} 0 := by
     rw [actual,retired,frame]
   rw [actual,retired,frame] at whole
   change Evm.run artifact.right.code {m with stack := mid.toList.map coreWord++caller} = .ok final skip at whole
   obtain ⟨hb,out,rightSource,done,finalFrame⟩ := MultiSwitchCompletion.model_to_source artifact.right mid m final caller skip whole
   exact ⟨ha,hb,mid,out,leftSource,rightSource,(by simpa only [actual] using boundary),
     artifact.join_source ha hb locals mid out leftSource rightSource,done,finalFrame⟩

theorem completion_iff {c n f g} {a b : Stmt [] [] c n}
 (artifact : Artifact f g a b) (locals out : Vector Scalar.Word n)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro (.seq a b) artifact.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 apply CompletionControls.completion_iff_zero (.seq a b) artifact.profile artifact.code
   artifact.normal_to_model ?_ locals out m caller
 intro locals m final caller skip ran
 obtain ⟨ha,hb,mid,actual,_,_,_,source,done,frame⟩ := model_to_source artifact locals m
   final caller skip ran
 exact ⟨max ha hb+1,actual,source,done,frame⟩

/-- info: 'Solidity.Yul.Compilation.SwitchSequenceCompletion.model_to_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
/-- info: 'Solidity.Yul.Compilation.SwitchSequenceCompletion.completion_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms completion_iff
end Solidity.Yul.Compilation.SwitchSequenceCompletion
