import Solidity.Yul.Compilation.LetSequenceCompletion
import Solidity.Yul.Compilation.LetSequenceCompilationControls
/-! Reflection over actual sequence visitor outputs. Three scopes witness
nested sequence composition and successive dirty initializers. Kernel
source/model evidence only, not an independent compiler/native oracle. -/
namespace Solidity.Yul.Compilation.LetSequenceCompletion.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open LetSequenceCompilation.Controls (artifact source update)
open SourceLoop.Controls (root dirty)

theorem success_iff (locals out : Vector Scalar.Word 1) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := completion_iff artifact locals out m caller

theorem recovered (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[update (update b)],.normal⟩ :=
 (success_iff #v[b] #v[update (update b)] m caller).mpr
   (LetSequenceCompilation.Controls.target_done b m caller)

theorem reflected (locals : Vector Scalar.Word 1) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word 1),
 evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} :=
 artifact_reflected artifact locals m final caller skip ran

def tripleSource : Solidity.Yul.Stmt [] [] root 1 := .seq source LetScopeCompilation.Controls.source
def tripleArtifact := (LetSequenceCompilation.lower 12 tripleSource).get (by rfl)

theorem triple_source (b : Scalar.Word) :
 evalStmt 17 .nil True.intro tripleSource tripleArtifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[update (update (update b))],.normal⟩ := by
 have last := evalStmt_stable (show 15 ≤ 16 by omega) .nil True.intro LetScopeCompilation.Controls.source
   LetScopeCompilation.Controls.artifact.compiled.profile (sourceLocals #v[update (update b)])
   (LetScopeCompilation.Controls.source_done (update (update b)))
 exact LoopControlCompilation.sequence_source source LetScopeCompilation.Controls.source artifact.compiled.profile
   LetScopeCompilation.Controls.artifact.compiled.profile 16 (sourceLocals #v[b])
   (sourceLocals #v[update (update b)]) (sourceLocals #v[update (update (update b))])
   (LetSequenceCompilation.Controls.source_done b) last

theorem triple_target (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run tripleArtifact.code {m with stack := coreWord b::caller} =
 .ok {m with stack := coreWord (update (update (update b)))::caller} 0 :=
 tripleArtifact.normal_to_model 17 #v[b] #v[update (update (update b))] (triple_source b) m caller

theorem triple_iff (locals out : Vector Scalar.Word 1) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro tripleSource tripleArtifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run tripleArtifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := completion_iff tripleArtifact locals out m caller

#guard update (update (update 0)) ≠ update (update 0)
#guard update (update (update 0)) = BitVec.ofNat 256 (3*(2^200+257)+9)
#guard (LetSequenceCompilation.lower 0 tripleSource).isNone
#guard (LetSequenceCompilation.lower 12 LetSequenceCompilation.Controls.unsupported).isNone
#guard (evalStmt 0 .nil True.intro tripleSource tripleArtifact.compiled.profile (sourceLocals #v[dirty])).isNone
-- Actual operation checks remain separate from whole model execution.
#guard Scalar.stackBound [Backend.Instr.op (.DUP 0)] (1024 : Int) = false
#guard Scalar.run (popPrefix 1) [] = none

/-- info: 'Solidity.Yul.Compilation.LetSequenceCompletion.Controls.success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_iff
/-- info: 'Solidity.Yul.Compilation.LetSequenceCompletion.Controls.recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recovered
/-- info: 'Solidity.Yul.Compilation.LetSequenceCompletion.Controls.reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reflected
/-- info: 'Solidity.Yul.Compilation.LetSequenceCompletion.Controls.triple_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms triple_source
/-- info: 'Solidity.Yul.Compilation.LetSequenceCompletion.Controls.triple_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms triple_target
/-- info: 'Solidity.Yul.Compilation.LetSequenceCompletion.Controls.triple_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms triple_iff
end Solidity.Yul.Compilation.LetSequenceCompletion.Controls
