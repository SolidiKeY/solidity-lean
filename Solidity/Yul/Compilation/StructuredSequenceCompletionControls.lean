import Solidity.Yul.Compilation.StructuredSequenceCompletion
import Solidity.Yul.Compilation.StructuredSequenceCompilationControls
/-! Reverse controls for actual nested zero/let/if/switch compiler outputs.
Source completions are recovered from kernel target witnesses, not assumed.
Relative pending skips and uncapped model success are not native PC/capacity. -/
namespace Solidity.Yul.Compilation.StructuredSequenceCompletion.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open StructuredSequenceCompilation.Controls (source artifact inner innerArtifact falseInner falseArtifact)

theorem inner_iff (locals out : Vector Scalar.Word 1) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro inner innerArtifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run innerArtifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 :=
 completion_iff innerArtifact locals out m caller

theorem inner_source_recovered (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro inner innerArtifact.compiled.profile (sourceLocals #v[0]) =
 some ⟨sourceLocals #v[9],.normal⟩ :=
 (inner_iff #v[0] #v[9] m caller).mpr (StructuredSequenceCompilation.Controls.inner_target m caller)

theorem outer_source_recovered (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals #v[]) =
 some ⟨sourceLocals #v[],.normal⟩ :=
 (completion_iff artifact #v[] #v[] m caller).mpr (StructuredSequenceCompilation.Controls.target_done m caller)

theorem false_source_recovered (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro falseInner falseArtifact.compiled.profile (sourceLocals #v[0]) =
 some ⟨sourceLocals #v[0],.normal⟩ :=
 (completion_iff falseArtifact #v[0] #v[0] m caller).mpr (StructuredSequenceCompilation.Controls.false_target m caller)

theorem final_height (locals : Vector Scalar.Word 1) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run innerArtifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 skip = 0 ∧ final.stack.length = 1+caller.length := by
 obtain ⟨_,out,_,done,frame⟩ := artifact_reflected innerArtifact locals m final caller skip ran
 refine ⟨done,?_⟩
 exact CompletionControls.frame_height #v[] out m final caller frame

/-- Completed actual selected code cannot leave a forward jump into caller
code; this concerns the model's relative skip, not a native byte PC. -/
theorem pending_skip_refused (locals : Vector Scalar.Word 1) (m final : Evm.Machine)
 (caller : List Evm.Word) (pending : Nat) :
 Evm.run innerArtifact.code {m with stack := locals.toList.map coreWord++caller} ≠ .ok final (pending+1) := by
 exact CompletionControls.pending_refused (code := innerArtifact.code)
   (initial := {m with stack := locals.toList.map coreWord++caller})
   (fun actual pending ran => by
     obtain ⟨_,_,_,done,_⟩ := artifact_reflected innerArtifact locals m actual caller pending ran
     exact done) final pending

/-- The true artifact cannot return the false artifact's observed result. -/
theorem false_output_refused (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run innerArtifact.code {m with stack := coreWord 0::caller} ≠ .ok {m with stack := coreWord 0::caller} 0 := by
 intro bad
 have same := (StructuredSequenceCompilation.Controls.inner_target m caller).symm.trans bad
 have frames := (Evm.Out.ok.inj same).1
 have stacks := congrArg Evm.Machine.stack frames
 have different : coreWord (9 : Scalar.Word) ≠ coreWord (0 : Scalar.Word) := by decide
 exact different (List.cons.inj stacks).1

/-- Oversized dirty caller data is preserved by the uncapped model. No native
capacity follows: the actual first scalar scope-entry trace already refuses. -/
theorem oversized_success (m : Evm.Machine) :
 Evm.run artifact.code {m with stack := List.replicate 1025 (coreWord SourceLoop.Controls.dirty)} =
 .ok {m with stack := List.replicate 1025 (coreWord SourceLoop.Controls.dirty)} 0 :=
 StructuredSequenceCompilation.Controls.target_done m _
example : Scalar.stackBound (ZeroLoopScope.entry 1) 1025 = false := by decide

/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompletion.Controls.inner_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms inner_iff
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompletion.Controls.inner_source_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms inner_source_recovered
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompletion.Controls.outer_source_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms outer_source_recovered
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompletion.Controls.false_source_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms false_source_recovered
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompletion.Controls.final_height' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms final_height
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompletion.Controls.pending_skip_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pending_skip_refused
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompletion.Controls.false_output_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms false_output_refused
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompletion.Controls.oversized_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms oversized_success
end Solidity.Yul.Compilation.StructuredSequenceCompletion.Controls
