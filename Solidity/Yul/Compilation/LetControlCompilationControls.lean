import Solidity.Yul.Compilation.LetControlCompilation
import Solidity.Yul.Compilation.LetBranchCompilationControls
/-! Actual nested if/seq lowering around real let/loop artifacts. The final
scope executes after either conditional path; all witnesses retain exact raw
words/caller/machine fields. Kernel source/model evidence only. -/
namespace Solidity.Yul.Compilation.LetControlCompilation.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)
open LetBranchCompilation.Controls (highOnly)

def scopeUpdate := LetSequenceCompilation.Controls.update
def bodySource : Solidity.Yul.Stmt [] [] root 1 :=
 .seq LetBranchCompilation.Controls.source LetScopeCompilation.Controls.source
def bodyArtifact := (lower 13 bodySource).get (by rfl)
def bodyUpdate (b : Scalar.Word) := scopeUpdate (LetBranchCompilation.Controls.update b)
def middleSource : Solidity.Yul.Stmt [] [] root 1 := .if_ (.local 0) bodySource
def middleArtifact := (lower 14 middleSource).get (by rfl)
def middleUpdate (b : Scalar.Word) := if b = 0 then b else bodyUpdate b
def source : Solidity.Yul.Stmt [] [] root 1 := .seq middleSource LetScopeCompilation.Controls.source
def artifact := (lower 15 source).get (by rfl)
def update (b : Scalar.Word) := scopeUpdate (middleUpdate b)

theorem body_source (b : Scalar.Word) :
 evalStmt 18 .nil True.intro bodySource bodyArtifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[bodyUpdate b],.normal⟩ := by
 have last := evalStmt_stable (show 15 ≤ 17 by omega) .nil True.intro LetScopeCompilation.Controls.source
   LetScopeCompilation.Controls.artifact.compiled.profile (sourceLocals #v[LetBranchCompilation.Controls.update b])
   (LetScopeCompilation.Controls.source_done (LetBranchCompilation.Controls.update b))
 exact LoopControlCompilation.sequence_source LetBranchCompilation.Controls.source LetScopeCompilation.Controls.source
   LetBranchCompilation.Controls.artifact.compiled.profile LetScopeCompilation.Controls.artifact.compiled.profile
   17 (sourceLocals #v[b]) (sourceLocals #v[LetBranchCompilation.Controls.update b])
   (sourceLocals #v[bodyUpdate b]) (LetBranchCompilation.Controls.source_done b) last

theorem middle_source (b : Scalar.Word) :
 evalStmt 19 .nil True.intro middleSource middleArtifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[middleUpdate b],.normal⟩ := by
 change (if b.toNat = 0 then some (⟨sourceLocals #v[b],.normal⟩ : Outcome root 1)
   else evalStmt 18 .nil True.intro bodySource bodyArtifact.compiled.profile (sourceLocals #v[b])) = _
 by_cases zero : b = 0
 · have zn : b.toNat = 0 := congrArg BitVec.toNat zero
   rw [if_pos zn,middleUpdate,if_pos zero]
 · have nz : b.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
   rw [if_neg nz,middleUpdate,if_neg zero]
   exact body_source b

theorem source_done (b : Scalar.Word) :
 evalStmt 20 .nil True.intro source artifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[update b],.normal⟩ := by
 have last := evalStmt_stable (show 15 ≤ 19 by omega) .nil True.intro LetScopeCompilation.Controls.source
   LetScopeCompilation.Controls.artifact.compiled.profile (sourceLocals #v[middleUpdate b])
   (LetScopeCompilation.Controls.source_done (middleUpdate b))
 exact LoopControlCompilation.sequence_source middleSource LetScopeCompilation.Controls.source middleArtifact.compiled.profile
   LetScopeCompilation.Controls.artifact.compiled.profile 19 (sourceLocals #v[b]) (sourceLocals #v[middleUpdate b])
   (sourceLocals #v[update b]) (middle_source b) last

theorem target_done (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord b::caller} =
 .ok {m with stack := coreWord (update b)::caller} 0 :=
 artifact.normal_to_model 20 #v[b] #v[update b] (source_done b) m caller

/-- The outer zero branch completes early without the inner sequence. -/
theorem middle_zero_early :
 evalStmt 2 .nil True.intro middleSource middleArtifact.compiled.profile (sourceLocals #v[0]) =
 some ⟨sourceLocals #v[0],.normal⟩ := by rfl

#guard update 0 = scopeUpdate 0
#guard update 0 ≠ 0
#guard update highOnly = scopeUpdate (scopeUpdate (scopeUpdate (scopeUpdate highOnly)))
#guard update highOnly = BitVec.ofNat 256 (5*2^200+4*257+12)
#guard update highOnly ≠ scopeUpdate highOnly
#guard (evalStmt 1 .nil True.intro bodySource bodyArtifact.compiled.profile (sourceLocals #v[0])).isNone
#guard (lower 0 source).isNone
#guard (LetSequenceCompilation.lower 15 source).isNone
#guard (LetBranchCompilation.lower 15 source).isNone
#guard (evalStmt 0 .nil True.intro source artifact.compiled.profile (sourceLocals #v[dirty])).isNone
def unsupported : Solidity.Yul.Stmt [] [] root 1 := .seq source .skip
#guard (lower 15 unsupported).isNone
-- Separate operation checks do not establish whole-artifact capacity.
#guard Scalar.stackBound [Backend.Instr.op (.DUP 0)] (1024 : Int) = false
#guard Scalar.run (popPrefix 1) [] = none

/-- info: 'Solidity.Yul.Compilation.LetControlCompilation.Controls.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms body_source
/-- info: 'Solidity.Yul.Compilation.LetControlCompilation.Controls.middle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms middle_source
/-- info: 'Solidity.Yul.Compilation.LetControlCompilation.Controls.source_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_done
/-- info: 'Solidity.Yul.Compilation.LetControlCompilation.Controls.target_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_done
/-- info: 'Solidity.Yul.Compilation.LetControlCompilation.Controls.middle_zero_early' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms middle_zero_early
end Solidity.Yul.Compilation.LetControlCompilation.Controls
