import Solidity.Yul.Compilation.LetControlCompletion
import Solidity.Yul.Compilation.LetControlCompilationControls
/-! Actual recursive-control reflection plus contrasting outer ISZERO and
inner word guards. Updated locals and the unconditional final scope are
observable on both paths. Kernel source/model witnesses only. -/
namespace Solidity.Yul.Compilation.LetControlCompletion.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open LetControlCompilation.Controls (artifact source update scopeUpdate)
open SourceLoop.Controls (root dirty)
open LetBranchCompilation.Controls (highOnly)

theorem success_iff (locals out : Vector Scalar.Word 1) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := completion_iff artifact locals out m caller

theorem recovered (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[update b],.normal⟩ :=
 (success_iff #v[b] #v[update b] m caller).mpr (LetControlCompilation.Controls.target_done b m caller)

theorem reflected (locals : Vector Scalar.Word 1) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word 1),
 evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} :=
 artifact_reflected artifact locals m final caller skip ran

def test : Expr [] [] 1 1 := .builtin (.pure .iszero) (fun _ => .local 0)
def condition := (PureExpressions.compile 15 test).get (by rfl)
def mixedIfSource : Solidity.Yul.Stmt [] [] root 1 := .if_ test source
def mixedSource : Solidity.Yul.Stmt [] [] root 1 := .seq mixedIfSource LetScopeCompilation.Controls.source
def mixedArtifact := (LetControlCompilation.lower 17 mixedSource).get (by rfl)

theorem mixed_high_source :
 evalStmt 17 .nil True.intro mixedSource mixedArtifact.compiled.profile (sourceLocals #v[highOnly]) =
 some ⟨sourceLocals #v[scopeUpdate highOnly],.normal⟩ := by
 have first := source_false condition artifact.compiled.profile #v[highOnly] (by decide)
 have last := CompletionControls.completed_horizon
   (fun fuel => evalStmt fuel .nil True.intro LetScopeCompilation.Controls.source
     LetScopeCompilation.Controls.artifact.compiled.profile (sourceLocals #v[highOnly]))
   (fun fuel extra => evalStmt_refines_add fuel extra .nil True.intro LetScopeCompilation.Controls.source
     LetScopeCompilation.Controls.artifact.compiled.profile (sourceLocals #v[highOnly]))
   (show 15 ≤ 16 by omega) (LetScopeCompilation.Controls.source_done highOnly)
 exact LoopControlCompilation.sequence_source mixedIfSource LetScopeCompilation.Controls.source
   ⟨condition.profile,artifact.compiled.profile⟩ LetScopeCompilation.Controls.artifact.compiled.profile 16
   (sourceLocals #v[highOnly]) (sourceLocals #v[highOnly]) (sourceLocals #v[scopeUpdate highOnly]) first last

theorem mixed_high_target (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run mixedArtifact.code {m with stack := coreWord highOnly::caller} =
 .ok {m with stack := coreWord (scopeUpdate highOnly)::caller} 0 :=
 mixedArtifact.normal_to_model 17 #v[highOnly] #v[scopeUpdate highOnly] mixed_high_source m caller

theorem mixed_zero_source :
 evalStmt 22 .nil True.intro mixedSource mixedArtifact.compiled.profile (sourceLocals #v[0]) =
 some ⟨sourceLocals #v[scopeUpdate (update 0)],.normal⟩ := by
 have first := source_true condition artifact.compiled.profile 20 #v[0] #v[update 0] (by decide)
   (LetControlCompilation.Controls.source_done 0)
 have last := CompletionControls.completed_horizon
   (fun fuel => evalStmt fuel .nil True.intro LetScopeCompilation.Controls.source
     LetScopeCompilation.Controls.artifact.compiled.profile (sourceLocals #v[update 0]))
   (fun fuel extra => evalStmt_refines_add fuel extra .nil True.intro LetScopeCompilation.Controls.source
     LetScopeCompilation.Controls.artifact.compiled.profile (sourceLocals #v[update 0]))
   (show 15 ≤ 21 by omega) (LetScopeCompilation.Controls.source_done (update 0))
 exact LoopControlCompilation.sequence_source mixedIfSource LetScopeCompilation.Controls.source
   ⟨condition.profile,artifact.compiled.profile⟩ LetScopeCompilation.Controls.artifact.compiled.profile 21
   (sourceLocals #v[0]) (sourceLocals #v[update 0]) (sourceLocals #v[scopeUpdate (update 0)]) first last

theorem mixed_zero_target (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run mixedArtifact.code {m with stack := coreWord 0::caller} =
 .ok {m with stack := coreWord (scopeUpdate (update 0))::caller} 0 :=
 mixedArtifact.normal_to_model 22 #v[0] #v[scopeUpdate (update 0)] mixed_zero_source m caller

theorem mixed_iff (locals out : Vector Scalar.Word 1) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro mixedSource mixedArtifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run mixedArtifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := completion_iff mixedArtifact locals out m caller

#guard condition.value #v[highOnly] = 0
#guard condition.value #v[0] = 1
#guard scopeUpdate highOnly ≠ highOnly
#guard scopeUpdate (update 0) = BitVec.ofNat 256 (2*(2^200+257)+6)
#guard (LetControlCompilation.lower 0 mixedSource).isNone
#guard (evalStmt 0 .nil True.intro mixedSource mixedArtifact.compiled.profile (sourceLocals #v[dirty])).isNone
-- Separate actual operation checks, not whole-artifact capacity/failure laws.
#guard Scalar.stackBound [Backend.Instr.op (.DUP 0)] (1024 : Int) = false
#guard Scalar.run (popPrefix 1) [] = none

/-- info: 'Solidity.Yul.Compilation.LetControlCompletion.Controls.success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_iff
/-- info: 'Solidity.Yul.Compilation.LetControlCompletion.Controls.recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recovered
/-- info: 'Solidity.Yul.Compilation.LetControlCompletion.Controls.reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reflected
/-- info: 'Solidity.Yul.Compilation.LetControlCompletion.Controls.mixed_high_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mixed_high_source
/-- info: 'Solidity.Yul.Compilation.LetControlCompletion.Controls.mixed_high_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mixed_high_target
/-- info: 'Solidity.Yul.Compilation.LetControlCompletion.Controls.mixed_zero_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mixed_zero_source
/-- info: 'Solidity.Yul.Compilation.LetControlCompletion.Controls.mixed_zero_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mixed_zero_target
/-- info: 'Solidity.Yul.Compilation.LetControlCompletion.Controls.mixed_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mixed_iff
end Solidity.Yul.Compilation.LetControlCompletion.Controls
