import Solidity.Yul.Compilation.SwitchCompletion
import Solidity.Yul.Compilation.SwitchCompilationControls
/-! Actual switch artifacts support exact success equivalence and genuine
source recovery. Derived heights show guard/selector retirement but do not
establish charged/native capacity or independent EVM validation. -/
namespace Solidity.Yul.Compilation.SwitchCompletion.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SwitchCompilation.Controls (switchSource artifact lowOnly armArtifact comparisonProgram)
open ScopedControlCompilation.Controls (update)
open SourceLoop.Controls (dirty)

theorem success_iff (locals out : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro switchSource artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := completion_iff artifact locals out m caller

theorem reflected (locals : Vector Scalar.Word 2) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word 2),
 evalStmt horizon .nil True.intro switchSource artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} :=
 model_to_source artifact locals m final caller skip ran

theorem matching_recovered (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro switchSource artifact.compiled.profile (sourceLocals #v[dirty,c]) =
 some ⟨sourceLocals #v[update dirty,c],.normal⟩ :=
 (success_iff #v[dirty,c] #v[update dirty,c] m caller).mpr (SwitchCompilation.Controls.matching_target c m caller)

theorem default_recovered (b c : Scalar.Word) (different : b.toFin ≠ dirty.toFin)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro switchSource artifact.compiled.profile (sourceLocals #v[b,c]) =
 some ⟨sourceLocals #v[b,c],.normal⟩ :=
 (success_iff #v[b,c] #v[b,c] m caller).mpr (SwitchCompilation.Controls.default_target b c different m caller)

theorem alias_recovered (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro switchSource artifact.compiled.profile (sourceLocals #v[lowOnly,c]) =
 some ⟨sourceLocals #v[lowOnly,c],.normal⟩ :=
 (success_iff #v[lowOnly,c] #v[lowOnly,c] m caller).mpr (SwitchCompilation.Controls.low_alias_target c m caller)

/-- Actual successful execution leaves neither the comparison guard nor the
retained selector. This length may exceed1024 in the uncapped model. -/
theorem final_height (locals : Vector Scalar.Word 2) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 skip = 0 ∧ final.stack.length = 2+caller.length := by
 obtain ⟨horizon,out,source,done,frame⟩ := reflected locals m final caller skip ran
 refine ⟨done,?_⟩
 exact CompletionControls.frame_height #v[] out m final caller frame

#guard (dirty &&& 255) = (lowOnly &&& 255)
#guard dirty ≠ lowOnly
#guard (evalStmt 1 .nil True.intro ScopedControlCompilation.Controls.source armArtifact.compiled.profile
 (sourceLocals #v[lowOnly,dirty])).isNone
#guard (evalStmt 0 .nil True.intro switchSource artifact.compiled.profile (sourceLocals #v[dirty,dirty])).isNone
-- The comparison-only capacity checks do not discharge whole-artifact capacity.
#guard Scalar.stackBound comparisonProgram (1022 : Int) = true
#guard Scalar.stackBound comparisonProgram (1023 : Int) = false
#guard (Scalar.run comparisonProgram []).isNone

/-- info: 'Solidity.Yul.Compilation.SwitchCompletion.Controls.success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_iff
/-- info: 'Solidity.Yul.Compilation.SwitchCompletion.Controls.reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reflected
/-- info: 'Solidity.Yul.Compilation.SwitchCompletion.Controls.matching_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms matching_recovered
/-- info: 'Solidity.Yul.Compilation.SwitchCompletion.Controls.default_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms default_recovered
/-- info: 'Solidity.Yul.Compilation.SwitchCompletion.Controls.alias_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms alias_recovered
/-- info: 'Solidity.Yul.Compilation.SwitchCompletion.Controls.final_height' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms final_height
end Solidity.Yul.Compilation.SwitchCompletion.Controls
