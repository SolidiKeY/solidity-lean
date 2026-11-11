import Solidity.Yul.Compilation.ZeroScopeCompletion
import Solidity.Yul.Compilation.ZeroLoopScopeControls
/-! Actual scope artifact reflection; a final dirty write proves retirement
of a fresh value that is no longer zero. These are kernel witnesses only. -/
namespace Solidity.Yul.Compilation.ZeroScopeCompletion.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)
open ZeroLoopScope.Controls

theorem success_iff (locals out : Vector Scalar.Word 1) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro mutatingSource mutatingArtifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run mutatingCode {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 :=
 completion_iff (n := 1) (fresh := 1) mutatingArtifact mutatingCode (Option.some_get (by rfl)).symm locals out m caller

theorem recovered (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro mutatingSource mutatingArtifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[(~~~(~~~b+3)+3)+3],.normal⟩ :=
 (success_iff #v[b] #v[(~~~(~~~b+3)+3)+3] m caller).mpr (mutating_target b m caller)

theorem reflected (locals : Vector Scalar.Word 1) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run mutatingCode {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word 1),
 evalStmt horizon .nil True.intro mutatingSource mutatingArtifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} :=
 model_to_source (n := 1) (fresh := 1) mutatingArtifact mutatingCode (Option.some_get (by rfl)).symm
   locals m final caller skip ran

def noFreshCode := (ZeroLoopScope.lower 0 (n := 2) bodyArtifact).get (by rfl)
theorem no_fresh_iff (locals out : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro (.zero (n := 2) 0 LoopControlCompilation.Controls.source)
   bodyArtifact.compiled.profile (sourceLocals locals) = some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run noFreshCode {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 :=
 completion_iff (n := 2) (fresh := 0) bodyArtifact noFreshCode (Option.some_get (by rfl)).symm locals out m caller

/-- This source changes the fresh counter AFTER the loop and visible update. -/
def stamp : Solidity.Yul.Stmt [] [] root 2 := .assign (fun _ : Fin 1 => .local 0) (.literal dirty.toFin)
def stampCompiled := (PureStatements.compile 2 stamp).get (by rfl)
def retiringBody : Solidity.Yul.Stmt [] [] root 2 := .seq mutatingBody stamp
def retiringArtifact : LoopControlCompilation.Artifact 10 retiringBody 0 :=
 (LoopControlCompilation.lower 10 retiringBody 0).get (by rfl)
def retiringSource : Solidity.Yul.Stmt [] [] root 1 := .zero 1 retiringBody
def retiringCode := (ZeroLoopScope.lower 1 (n := 1) retiringArtifact).get (by rfl)

theorem dirty_body (b : Scalar.Word) :
 evalStmt 14 .nil True.intro retiringBody retiringArtifact.compiled.profile (sourceLocals #v[0,b]) =
 some ⟨sourceLocals #v[dirty,(~~~(~~~b+3)+3)+3],.normal⟩ := by
 have last := CompletionControls.completed_horizon
   (fun fuel => evalStmt fuel .nil True.intro stamp stampCompiled.profile
     (sourceLocals #v[0,(~~~(~~~b+3)+3)+3]))
   (fun fuel extra => evalStmt_refines_add fuel extra .nil True.intro stamp stampCompiled.profile
     (sourceLocals #v[0,(~~~(~~~b+3)+3)+3]))
   (show 2 ≤ 13 by omega) (stampCompiled.source #v[0,(~~~(~~~b+3)+3)+3])
 exact LoopControlCompilation.sequence_source mutatingBody stamp mutatingArtifact.compiled.profile stampCompiled.profile
   13 (sourceLocals #v[0,b]) (sourceLocals #v[0,(~~~(~~~b+3)+3)+3])
   (sourceLocals #v[dirty,(~~~(~~~b+3)+3)+3]) (mutating_body_source 0 b) last

theorem dirty_source (b : Scalar.Word) :
 evalStmt 15 .nil True.intro retiringSource retiringArtifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[(~~~(~~~b+3)+3)+3],.normal⟩ :=
 ZeroLoopScope.source_scope retiringArtifact 14 #v[b] #v[dirty,(~~~(~~~b+3)+3)+3] (dirty_body b)

theorem dirty_retired (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run retiringCode {m with stack := coreWord b::caller} =
 .ok {m with stack := coreWord ((~~~(~~~b+3)+3)+3)::caller} 0 :=
 (completion_iff (n := 1) (fresh := 1) retiringArtifact retiringCode (Option.some_get (by rfl)).symm
   #v[b] #v[(~~~(~~~b+3)+3)+3] m caller).mp ⟨15,dirty_source b⟩

#guard dirty ≠ 0
#guard Scalar.stackBound (ZeroLoopScope.entry 1) (1024 : Int) = false
#guard Scalar.run (popPrefix 1) [] = none
#guard (evalStmt 0 .nil True.intro retiringSource retiringArtifact.compiled.profile (sourceLocals #v[dirty])).isNone
/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompletion.Controls.success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_iff
/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompletion.Controls.recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recovered
/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompletion.Controls.reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reflected
/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompletion.Controls.no_fresh_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms no_fresh_iff
/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompletion.Controls.dirty_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dirty_body
/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompletion.Controls.dirty_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dirty_source
/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompletion.Controls.dirty_retired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dirty_retired
end Solidity.Yul.Compilation.ZeroScopeCompletion.Controls
