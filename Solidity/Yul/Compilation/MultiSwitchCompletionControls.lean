import Solidity.Yul.Compilation.MultiSwitchCompletion
import Solidity.Yul.Compilation.MultiSwitchCompilationControls
/-! Genuine finite-case compiler outputs instantiate exact normal-success
correspondence. Recovery uses actual prior kernel targets, not an independent
native oracle; exact final heights do not establish charged capacity. -/
namespace Solidity.Yul.Compilation.MultiSwitchCompletion.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open MultiSwitchCompilation.Controls (source artifact emptySource emptyArtifact)
open ScopedControlCompilation.Controls (update)
open SourceLoop.Controls (dirty)

theorem success_iff (locals out : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := completion_iff artifact locals out m caller

theorem reflected (locals : Vector Scalar.Word 2) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word 2),
 evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} :=
 model_to_source artifact locals m final caller skip ran

theorem first_recovered (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals #v[0,c]) =
 some ⟨sourceLocals #v[0,c+3],.normal⟩ :=
 (success_iff #v[0,c] #v[0,c+3] m caller).mpr (MultiSwitchCompilation.Controls.first_target c m caller)

theorem later_recovered (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals #v[dirty,c]) =
 some ⟨sourceLocals #v[update dirty,c],.normal⟩ :=
 (success_iff #v[dirty,c] #v[update dirty,c] m caller).mpr (MultiSwitchCompilation.Controls.later_target c m caller)

theorem default_recovered (b c : Scalar.Word) (nonzero : b.toFin ≠ 0) (different : b.toFin ≠ dirty.toFin)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals #v[b,c]) =
 some ⟨sourceLocals #v[b,c],.normal⟩ :=
 (success_iff #v[b,c] #v[b,c] m caller).mpr (MultiSwitchCompilation.Controls.default_target b c nonzero different m caller)

theorem alias_recovered (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile
   (sourceLocals #v[SwitchCompilation.Controls.lowOnly,c]) =
 some ⟨sourceLocals #v[SwitchCompilation.Controls.lowOnly,c],.normal⟩ :=
 (success_iff #v[SwitchCompilation.Controls.lowOnly,c] #v[SwitchCompilation.Controls.lowOnly,c] m caller).mpr
   (MultiSwitchCompilation.Controls.alias_target c m caller)

theorem empty_iff (locals out : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro emptySource emptyArtifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run emptyArtifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := completion_iff emptyArtifact locals out m caller

/-- Guard and retained selector are absent after every successful run. The
uncapped model still permits caller heights exceeding native capacity. -/
theorem final_height (locals : Vector Scalar.Word 2) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 skip = 0 ∧ final.stack.length = 2+caller.length := by
 obtain ⟨horizon,out,source,done,frame⟩ := reflected locals m final caller skip ran
 refine ⟨done,?_⟩
 exact CompletionControls.frame_height #v[] out m final caller frame

#guard (dirty &&& 255) = (SwitchCompilation.Controls.lowOnly &&& 255)
#guard dirty ≠ SwitchCompilation.Controls.lowOnly
#guard (evalStmt 1 .nil True.intro MultiSwitchCompilation.Controls.nested MultiSwitchCompilation.Controls.nestedArtifact.compiled.profile
 (sourceLocals #v[SwitchCompilation.Controls.lowOnly,dirty])).isNone
#guard (evalStmt 0 .nil True.intro source artifact.compiled.profile (sourceLocals #v[dirty,dirty])).isNone
-- Only the comparison slice is checked here, not whole-dispatch/native validity.
#guard Scalar.stackBound SwitchCompilation.Controls.comparisonProgram (1022 : Int) = true
#guard Scalar.stackBound SwitchCompilation.Controls.comparisonProgram (1023 : Int) = false
#guard (Scalar.run SwitchCompilation.Controls.comparisonProgram []).isNone

/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompletion.Controls.success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_iff
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompletion.Controls.reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reflected
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompletion.Controls.first_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms first_recovered
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompletion.Controls.later_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms later_recovered
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompletion.Controls.default_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms default_recovered
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompletion.Controls.alias_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms alias_recovered
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompletion.Controls.empty_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_iff
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompletion.Controls.final_height' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms final_height
end Solidity.Yul.Compilation.MultiSwitchCompletion.Controls
