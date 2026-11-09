import Solidity.Yul.Compilation.SequenceCompletion
import Solidity.Yul.Compilation.SequenceCompilationControls
/-! Normal-success reflection of actual recursive compiler outputs. Original
source runs are recovered from prior kernel target witnesses; they are not
premises of recovery. Entry capacity controls remain distinct from model runs. -/
namespace Solidity.Yul.Compilation.SequenceCompletion.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SequenceCompilation.Controls (source artifact mixed mixedArtifact)

theorem success_iff (locals out : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 :=
 completion_iff artifact locals out m caller

theorem source_recovered (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals #v[0,0]) =
   some ⟨sourceLocals #v[0,9],.normal⟩ :=
 (success_iff #v[0,0] #v[0,9] m caller).mpr (SequenceCompilation.Controls.target_done m caller)

theorem mixed_iff (locals out : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro mixed mixedArtifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run mixedArtifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 :=
 completion_iff mixedArtifact locals out m caller

theorem mixed_recovered (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro mixed mixedArtifact.compiled.profile (sourceLocals #v[0,0]) =
   some ⟨sourceLocals #v[0,9],.normal⟩ :=
 (mixed_iff #v[0,0] #v[0,9] m caller).mpr (SequenceCompilation.Controls.mixed_target m caller)

theorem final_height (locals : Vector Scalar.Word 2) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 skip = 0 ∧ final.stack.length = 2+caller.length := by
 obtain ⟨_,out,_,done,frame⟩ := artifact_reflected artifact locals m final caller skip ran
 refine ⟨done,?_⟩
 exact CompletionControls.frame_height #v[] out m final caller frame

/-- Omitting the third original switch would leave 6. Actual compiled execution
cannot yield that truncated result, for any nonstack state or caller tail. -/
theorem truncated_output_refused (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord 0::coreWord 0::caller} ≠
 .ok {m with stack := coreWord 0::coreWord 6::caller} 0 := by
 intro bad
 have same := (SequenceCompilation.Controls.target_done m caller).symm.trans bad
 have frames := (Evm.Out.ok.inj same).1
 have stacks := congrArg Evm.Machine.stack frames
 have different : coreWord (9 : Scalar.Word) ≠ coreWord (6 : Scalar.Word) := by decide
 exact different (List.cons.inj (List.cons.inj stacks).2).1

theorem oversized_success (m : Evm.Machine) :
 Evm.run artifact.code {m with stack := coreWord 0::coreWord 0::List.replicate 1025 (coreWord SourceLoop.Controls.dirty)} =
 .ok {m with stack := coreWord 0::coreWord 9::List.replicate 1025 (coreWord SourceLoop.Controls.dirty)} 0 :=
 SequenceCompilation.Controls.target_done m _

/-- The actual scalar capacity checker rejects the same numerical entry
height even for empty code. This does not identify scalar/native target code. -/
example : Scalar.stackBound [] 1027 = false := by decide
example : Scalar.stackBound [] 1024 = true := by decide

/-- info: 'Solidity.Yul.Compilation.SequenceCompletion.Controls.success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_iff
/-- info: 'Solidity.Yul.Compilation.SequenceCompletion.Controls.source_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_recovered
/-- info: 'Solidity.Yul.Compilation.SequenceCompletion.Controls.mixed_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mixed_iff
/-- info: 'Solidity.Yul.Compilation.SequenceCompletion.Controls.mixed_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mixed_recovered
/-- info: 'Solidity.Yul.Compilation.SequenceCompletion.Controls.final_height' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms final_height
/-- info: 'Solidity.Yul.Compilation.SequenceCompletion.Controls.truncated_output_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms truncated_output_refused
/-- info: 'Solidity.Yul.Compilation.SequenceCompletion.Controls.oversized_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms oversized_success
end Solidity.Yul.Compilation.SequenceCompletion.Controls
