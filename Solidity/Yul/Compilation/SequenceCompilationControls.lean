import Solidity.Yul.Compilation.SequenceCompilation
import Solidity.Yul.Compilation.SwitchSequenceControls
/-! Nested original sequences of real switches, plus a real scoped skip leaf.
The actual visitor compiles all nodes. Ordered updates 0→3→6→9 observe the
intermediate frame; no host list execution stands for native stack capacity. -/
namespace Solidity.Yul.Compilation.SequenceCompilation.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root)

def tail : Solidity.Yul.Stmt [] [] root 2 :=
 .seq SwitchSequence.Controls.second MultiSwitchCompilation.Controls.source
def source : Solidity.Yul.Stmt [] [] root 2 := .seq MultiSwitchCompilation.Controls.source tail
def artifact := (lower 14 source).get (by rfl)
def tailArtifact := (lower 13 tail).get (by rfl)
def mixed : Solidity.Yul.Stmt [] [] root 2 := .seq .skip source
def mixedArtifact := (lower 15 mixed).get (by rfl)

theorem tail_source :
 evalStmt 6 .nil True.intro tail tailArtifact.compiled.profile (sourceLocals #v[0,3]) =
 some ⟨sourceLocals #v[0,9],.normal⟩ :=
 LoopControlCompilation.sequence_source _ _ _ _ 5 (sourceLocals #v[0,3]) (sourceLocals #v[0,6])
   (sourceLocals #v[0,9]) SwitchSequence.Controls.second_source (MultiSwitchCompilation.Controls.first_source 6)

theorem source_done :
 evalStmt 7 .nil True.intro source artifact.compiled.profile (sourceLocals #v[0,0]) =
 some ⟨sourceLocals #v[0,9],.normal⟩ := by
 have first := evalStmt_stable (by omega : 5 ≤ 6) .nil True.intro MultiSwitchCompilation.Controls.source
   MultiSwitchCompilation.Controls.artifact.compiled.profile (sourceLocals #v[0,0]) (MultiSwitchCompilation.Controls.first_source 0)
 exact LoopControlCompilation.sequence_source _ _ _ _ 6 (sourceLocals #v[0,0]) (sourceLocals #v[0,3])
   (sourceLocals #v[0,9]) first tail_source

theorem target_done (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord 0::coreWord 0::caller} =
 .ok {m with stack := coreWord 0::coreWord 9::caller} 0 :=
 artifact.normal_to_model 7 #v[0,0] #v[0,9] source_done m caller

theorem mixed_source :
 evalStmt 8 .nil True.intro mixed mixedArtifact.compiled.profile (sourceLocals #v[0,0]) =
 some ⟨sourceLocals #v[0,9],.normal⟩ :=
 LoopControlCompilation.sequence_source .skip source True.intro artifact.compiled.profile 7 (sourceLocals #v[0,0]) (sourceLocals #v[0,0])
   (sourceLocals #v[0,9]) rfl source_done

theorem mixed_target (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run mixedArtifact.code {m with stack := coreWord 0::coreWord 0::caller} =
 .ok {m with stack := coreWord 0::coreWord 9::caller} 0 :=
 mixedArtifact.normal_to_model 8 #v[0,0] #v[0,9] mixed_source m caller

theorem lowered : lower 14 source = some artifact := by rfl
theorem mixed_lowered : lower 15 mixed = some mixedArtifact := by rfl
theorem budget_refusal : lower 1 source = none := by rfl
/-- Existing root-only and scoped visitors cannot compile this nested switch
sequence; success above therefore uses the new original sequence recursion. -/
theorem old_root_refusal : MultiSwitchCompilation.lower 14 source = none := by rfl
theorem old_scoped_refusal : ScopedControlCompilation.lower 14 source = none := by rfl
example : evalStmt 0 .nil True.intro source artifact.compiled.profile (sourceLocals #v[0,0]) = none := by rfl

/-- info: 'Solidity.Yul.Compilation.SequenceCompilation.Controls.tail_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms tail_source
/-- info: 'Solidity.Yul.Compilation.SequenceCompilation.Controls.source_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_done
/-- info: 'Solidity.Yul.Compilation.SequenceCompilation.Controls.target_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_done
/-- info: 'Solidity.Yul.Compilation.SequenceCompilation.Controls.mixed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mixed_source
/-- info: 'Solidity.Yul.Compilation.SequenceCompilation.Controls.mixed_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mixed_target
/-- info: 'Solidity.Yul.Compilation.SequenceCompilation.Controls.lowered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lowered
/-- info: 'Solidity.Yul.Compilation.SequenceCompilation.Controls.mixed_lowered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mixed_lowered
/-- info: 'Solidity.Yul.Compilation.SequenceCompilation.Controls.budget_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms budget_refusal
/-- info: 'Solidity.Yul.Compilation.SequenceCompilation.Controls.old_root_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms old_root_refusal
/-- info: 'Solidity.Yul.Compilation.SequenceCompilation.Controls.old_scoped_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms old_scoped_refusal
end Solidity.Yul.Compilation.SequenceCompilation.Controls
