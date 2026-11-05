import Solidity.Yul.Compilation.ZeroScopeCompilation
import Solidity.Yul.Compilation.ZeroScopeCompletionControls
/-! Actual zero-binder visitor controls: structured body, changed outer word,
changed fresh dirty word retired at exit, and honest local refusals. Kernel
source/model witnesses, not external solc or native capacity evidence. -/
namespace Solidity.Yul.Compilation.ZeroScopeCompilation.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)

/-- This value comes from the actual new source visitor, not manual assembly. -/
def artifact := (lower 10 ZeroScopeCompletion.Controls.retiringSource).get (by rfl)
theorem selected : artifact.code = ZeroScopeCompletion.Controls.retiringCode := by rfl

theorem success_iff (locals out : Vector Scalar.Word 1) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro ZeroScopeCompletion.Controls.retiringSource
   artifact.compiled.profile (sourceLocals locals) = some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 :=
 artifact.completion_iff locals out m caller

theorem target (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord b::caller} =
 .ok {m with stack := coreWord ((~~~(~~~b+3)+3)+3)::caller} 0 := by
 rw [selected]
 exact ZeroScopeCompletion.Controls.dirty_retired b m caller

theorem recovered (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro ZeroScopeCompletion.Controls.retiringSource
 artifact.compiled.profile (sourceLocals #v[b]) = some ⟨sourceLocals #v[(~~~(~~~b+3)+3)+3],.normal⟩ :=
 (success_iff #v[b] #v[(~~~(~~~b+3)+3)+3] m caller).mpr (target b m caller)

theorem reflected (locals : Vector Scalar.Word 1) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word 1),
 evalStmt horizon .nil True.intro ZeroScopeCompletion.Controls.retiringSource artifact.compiled.profile
   (sourceLocals locals) = some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧
 final = {m with stack := out.toList.map coreWord++caller} :=
 artifact.reflected locals m final caller skip ran

def emptySource : Solidity.Yul.Stmt [] [] root 2 := .zero 0 LoopControlCompilation.Controls.source
def emptyArtifact := (lower 8 emptySource).get (by rfl)
theorem empty_selected : emptyArtifact.code = ZeroScopeCompletion.Controls.noFreshCode := by rfl

theorem empty_iff (locals out : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro emptySource emptyArtifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run emptyArtifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 :=
 emptyArtifact.completion_iff locals out m caller

#guard (lower 0 ZeroScopeCompletion.Controls.retiringSource).isNone
#guard (lower 10 (Solidity.Yul.Stmt.skip (F := []) (X := []) (c := root) (n := 1))).isNone
-- Existing body visitor does not yet accept another lexical binder.
def nestedSource : Solidity.Yul.Stmt [] [] root 1 := .zero 1 (.zero 0 ZeroScopeCompletion.Controls.retiringBody)
#guard (lower 10 nestedSource).isNone
#guard dirty ≠ 0
#guard (~~~(~~~dirty+3)+3)+3 ≠ dirty
#guard (evalStmt 0 .nil True.intro ZeroScopeCompletion.Controls.retiringSource
 artifact.compiled.profile (sourceLocals #v[dirty])).isNone
-- Capacity and missing operands remain distinct from compiler/model success.
#guard Scalar.stackBound (ZeroLoopScope.entry 1) (1024 : Int) = false
#guard Scalar.run (popPrefix 1) [] = none

/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompilation.Controls.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms selected
/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompilation.Controls.success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_iff
/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompilation.Controls.target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target
/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompilation.Controls.recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recovered
/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompilation.Controls.reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reflected
/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompilation.Controls.empty_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_selected
/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompilation.Controls.empty_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_iff
end Solidity.Yul.Compilation.ZeroScopeCompilation.Controls
