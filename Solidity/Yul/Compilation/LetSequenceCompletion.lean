import Solidity.Yul.Compilation.CompletionControls
import Solidity.Yul.Compilation.LetSequenceCompilation
import Solidity.Yul.Compilation.LetScopeCompletion
/-! Actual sequence success reflection. Intermediate target frames and source
completions derive from whole execution, not supplied child-run assumptions.
This closes normal source/model correspondence only for the existing compiler. -/
namespace Solidity.Yul.Compilation.LetSequenceCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

/-- Actual whole success determines both source completions and their shared
intermediate locals, normal flow and exact caller/nonstack frame. -/
theorem model_to_source {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (compiled : LetSequenceCompilation.Compiled fuel stmt) (code : List Evm.Instr)
 (lowered : compiled.code = some code) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 induction compiled generalizing code locals m final skip with
 | scope artifact =>
   change some artifact.code = some code at lowered
   cases Option.some.inj lowered
   exact LetScopeCompletion.model_to_source artifact locals m final caller skip ran
 | seq left right ihLeft ihRight =>
   change (left.code).bind (fun a => (right.code).bind (fun b => some (a++b))) = some code at lowered
   obtain ⟨a,ha,rest⟩ := Option.bind_eq_some_iff.mp lowered
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   have whole : (Evm.run a {m with stack := locals.toList.map coreWord++caller}).bind
     (fun middle pending => Evm.exec b pending middle) = .ok final skip := by
     simpa only [Evm.run,Evm.exec_append] using ran
   cases actual : Evm.run a {m with stack := locals.toList.map coreWord++caller} with
   | revert => rw [actual] at whole; cases whole
   | fault => rw [actual] at whole; cases whole
   | ok middle pending =>
     obtain ⟨lo,mid,sourceLeft,done,frame⟩ := ihLeft a ha locals m middle pending actual
     rw [actual,done,frame] at whole
     change Evm.run b {m with stack := mid.toList.map coreWord++caller} = .ok final skip at whole
     obtain ⟨hi,out,sourceRight,done,frame⟩ := ihRight b hb mid m final skip whole
     have first := evalStmt_stable (Nat.le_max_left lo hi) .nil True.intro _ left.profile
       (sourceLocals locals) sourceLeft
     have last := evalStmt_stable (Nat.le_max_right lo hi) .nil True.intro _ right.profile
       (sourceLocals mid) sourceRight
     have source := LoopControlCompilation.sequence_source _ _ left.profile right.profile (max lo hi)
       (sourceLocals locals) (sourceLocals mid) (sourceLocals out) first last
     exact ⟨max lo hi+1,out,source,done,frame⟩

/-- Actual compiler artifact projection; no simulation law is stored. -/
theorem artifact_reflected {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : LetSequenceCompilation.Artifact fuel stmt) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} :=
 model_to_source artifact.compiled artifact.code artifact.lowered locals m final caller skip ran

/-- Normal-success equivalence at an existential original source horizon.
No capacity/native/G24/admission or failure/divergence equivalence follows. -/
theorem completion_iff {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : LetSequenceCompilation.Artifact fuel stmt) (locals out : Vector Scalar.Word n)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 exact CompletionControls.completion_iff_zero stmt artifact.compiled.profile artifact.code
   artifact.normal_to_model (artifact_reflected artifact) locals out m caller

/-- info: 'Solidity.Yul.Compilation.LetSequenceCompletion.model_to_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
/-- info: 'Solidity.Yul.Compilation.LetSequenceCompletion.artifact_reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms artifact_reflected
/-- info: 'Solidity.Yul.Compilation.LetSequenceCompletion.completion_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms completion_iff
end Solidity.Yul.Compilation.LetSequenceCompletion
