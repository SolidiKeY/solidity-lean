import Solidity.Yul.Compilation.LetBranchCompletion
import Solidity.Yul.Compilation.LetBranchCompilationControls
/-! Exact branch reflection and actual computed ISZERO guards. Both outcomes
reuse real let-sequence compilation, with raw high words and exact frames.
These are kernel source/model witnesses, not external/native evidence. -/
namespace Solidity.Yul.Compilation.LetBranchCompletion.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open LetBranchCompilation.Controls (artifact source highOnly)
open SourceLoop.Controls (root dirty)

theorem success_iff (locals out : Vector Scalar.Word 1) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := completion_iff artifact locals out m caller

theorem recovered (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[LetBranchCompilation.Controls.update b],.normal⟩ :=
 (success_iff #v[b] #v[LetBranchCompilation.Controls.update b] m caller).mpr
   (LetBranchCompilation.Controls.target_done b m caller)

theorem reflected (locals : Vector Scalar.Word 1) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word 1),
 evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} :=
 model_to_source artifact locals m final caller skip ran

def invertedTest : Expr [] [] 1 1 := .builtin (.pure .iszero) (fun _ => .local 0)
def invertedCondition := (PureExpressions.compile 11 invertedTest).get (by rfl)
def invertedSource : Solidity.Yul.Stmt [] [] root 1 := .if_ invertedTest LetSequenceCompilation.Controls.source
def invertedArtifact := (LetBranchCompilation.lower 11 invertedSource).get (by rfl)

theorem inverted_high_source :
 evalStmt 12 .nil True.intro invertedSource invertedArtifact.compiled.profile (sourceLocals #v[highOnly]) =
 some ⟨sourceLocals #v[highOnly],.normal⟩ :=
 source_false invertedCondition LetSequenceCompilation.Controls.artifact #v[highOnly] (by decide)

theorem inverted_high_target (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run invertedArtifact.code {m with stack := coreWord highOnly::caller} =
 .ok {m with stack := coreWord highOnly::caller} 0 :=
 invertedArtifact.normal_to_model 12 #v[highOnly] #v[highOnly] inverted_high_source m caller

theorem inverted_zero_source :
 evalStmt 17 .nil True.intro invertedSource invertedArtifact.compiled.profile (sourceLocals #v[0]) =
 some ⟨sourceLocals #v[LetSequenceCompilation.Controls.update (LetSequenceCompilation.Controls.update 0)],.normal⟩ :=
 source_true invertedCondition LetSequenceCompilation.Controls.artifact 16 #v[0]
   #v[LetSequenceCompilation.Controls.update (LetSequenceCompilation.Controls.update 0)] (by decide)
   (LetSequenceCompilation.Controls.source_done 0)

theorem inverted_zero_target (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run invertedArtifact.code {m with stack := coreWord 0::caller} =
 .ok {m with stack := coreWord (LetSequenceCompilation.Controls.update
   (LetSequenceCompilation.Controls.update 0))::caller} 0 :=
 invertedArtifact.normal_to_model 17 #v[0]
   #v[LetSequenceCompilation.Controls.update (LetSequenceCompilation.Controls.update 0)] inverted_zero_source m caller

#guard invertedCondition.value #v[highOnly] = 0
#guard invertedCondition.value #v[0] = 1
#guard LetSequenceCompilation.Controls.update (LetSequenceCompilation.Controls.update 0) ≠ 0
#guard (LetBranchCompilation.lower 0 invertedSource).isNone
#guard (evalStmt 0 .nil True.intro invertedSource invertedArtifact.compiled.profile (sourceLocals #v[dirty])).isNone
-- Separate actual-operation checks, not whole-artifact capacity/failure laws.
#guard Scalar.stackBound [Backend.Instr.op (.DUP 0)] (1024 : Int) = false
#guard Scalar.run (popPrefix 1) [] = none

/-- info: 'Solidity.Yul.Compilation.LetBranchCompletion.Controls.success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_iff
/-- info: 'Solidity.Yul.Compilation.LetBranchCompletion.Controls.recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recovered
/-- info: 'Solidity.Yul.Compilation.LetBranchCompletion.Controls.reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reflected
/-- info: 'Solidity.Yul.Compilation.LetBranchCompletion.Controls.inverted_high_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms inverted_high_source
/-- info: 'Solidity.Yul.Compilation.LetBranchCompletion.Controls.inverted_high_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms inverted_high_target
/-- info: 'Solidity.Yul.Compilation.LetBranchCompletion.Controls.inverted_zero_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms inverted_zero_source
/-- info: 'Solidity.Yul.Compilation.LetBranchCompletion.Controls.inverted_zero_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms inverted_zero_target
end Solidity.Yul.Compilation.LetBranchCompletion.Controls
