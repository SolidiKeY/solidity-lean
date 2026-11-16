import Solidity.Yul.Compilation.Artifact
import Solidity.Yul.Compilation.ScopedControlCompletion
import Solidity.Yul.Compilation.ScopedControlCompilationControls
/-! Exact success reflection for real nested compiler outputs. Source recovery
is kernel correspondence, not an independent native EVM oracle. -/
namespace Solidity.Yul.Compilation.ScopedControlCompletion.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open ScopedControlCompilation.Controls (source artifact update branchSource branchArtifact lastSource lastArtifact)
open SourceLoop.Controls (dirty)

theorem success_iff (locals out : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 simpa only [Vector.toList_empty,List.nil_append] using
   (Solidity.Yul.Compilation.Artifact.ofZero (stmt := source)
     artifact.compiled.profile artifact.code artifact.source_to_model
     (artifact_reflected artifact)).completion_iff locals out #v[] m caller

theorem recovered (b c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals #v[b,c]) =
 some ⟨sourceLocals #v[update b,c],.normal⟩ :=
 (success_iff #v[b,c] #v[update b,c] m caller).mpr (ScopedControlCompilation.Controls.target_done b c m caller)

theorem reflected (locals : Vector Scalar.Word 2) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word 2),
 evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} :=
 artifact_reflected artifact locals m final caller skip ran

theorem branch_iff (locals out : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro branchSource branchArtifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run branchArtifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := completion_iff branchArtifact locals out m caller

theorem skipped_recovered (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro branchSource branchArtifact.compiled.profile (sourceLocals #v[b,0]) =
 some ⟨sourceLocals #v[b,0],.normal⟩ :=
 (branch_iff #v[b,0] #v[b,0] m caller).mpr (ScopedControlCompilation.Controls.branch_target_false b m caller)

theorem last_iff (locals out : Vector Scalar.Word 1) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro lastSource lastArtifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run lastArtifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := completion_iff lastArtifact locals out m caller

-- These refusals are separate from normal-success equivalence.
#guard (ScopedControlCompilation.lower 5 ScopedControlCompilation.Controls.beyondSource).isNone
#guard (evalStmt 0 .nil True.intro source artifact.compiled.profile (sourceLocals #v[dirty,dirty])).isNone
#guard Scalar.stackBound (ZeroLoopScope.entry 14) (1024 : Int) = false
#guard Scalar.run (popPrefix 1) [] = none
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompletion.Controls.success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_iff
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompletion.Controls.recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recovered
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompletion.Controls.reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reflected
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompletion.Controls.branch_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms branch_iff
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompletion.Controls.skipped_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms skipped_recovered
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompletion.Controls.last_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms last_iff
end Solidity.Yul.Compilation.ScopedControlCompletion.Controls
