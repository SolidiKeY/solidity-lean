import Solidity.Yul.Compilation.LetScopeCompilation
import Solidity.Yul.Compilation.ZeroLoopScopeControls
/-! Actual let visitor combines a dirty computed initializer, a read of the
new local into an outer local, structured loop work and exact caller framing.
All witnesses are kernel source/model proofs, not solc/native adequacy. -/
namespace Solidity.Yul.Compilation.LetScopeCompilation.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)

def rhs : Expr [] [] 1 1 := .builtin (.pure .add) (Fin.cases (.local 0) (fun _ => .literal dirty.toFin))
def initializer := (PureExpressions.compile 10 rhs).get (by rfl)
def copy : Solidity.Yul.Stmt [] [] root 2 := .assign (fun _ : Fin 1 => .local 1) (.local 0)
def copyCompiled := (PureStatements.compile 2 copy).get (by rfl)
def body : Solidity.Yul.Stmt [] [] root 2 := .seq copy ZeroLoopScope.Controls.mutatingBody
def bodyArtifact := (LoopControlCompilation.lower 10 body 0).get (by rfl)
def source : Solidity.Yul.Stmt [] [] root 1 := .let_ 1 rhs body
def artifact := (lower 10 source).get (by rfl)

theorem initial (b : Scalar.Word) : initializer.value #v[b] = b+dirty := by rfl

theorem body_source (a b : Scalar.Word) :
 evalStmt 14 .nil True.intro body bodyArtifact.compiled.profile (sourceLocals #v[a,b]) =
 some ⟨sourceLocals #v[0,(~~~(~~~a+3)+3)+3],.normal⟩ := by
 have first := evalStmt_stable (show 2 ≤ 13 by omega) .nil True.intro copy copyCompiled.profile
   (sourceLocals #v[a,b]) (copyCompiled.source #v[a,b])
 exact LoopControlCompilation.sequence_source copy ZeroLoopScope.Controls.mutatingBody copyCompiled.profile
   ZeroLoopScope.Controls.mutatingArtifact.compiled.profile 13 (sourceLocals #v[a,b])
   (sourceLocals #v[a,a]) (sourceLocals #v[0,(~~~(~~~a+3)+3)+3]) first
   (ZeroLoopScope.Controls.mutating_body_source a a)

theorem source_done (b : Scalar.Word) :
 evalStmt 15 .nil True.intro source artifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[(~~~(~~~(b+dirty)+3)+3)+3],.normal⟩ :=
 scope_source initializer bodyArtifact 14 #v[b] #v[0,(~~~(~~~(b+dirty)+3)+3)+3] (body_source (b+dirty) b)

theorem target_done (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord b::caller} =
 .ok {m with stack := coreWord ((~~~(~~~(b+dirty)+3)+3)+3)::caller} 0 :=
 artifact.normal_to_model 15 #v[b] #v[(~~~(~~~(b+dirty)+3)+3)+3] (source_done b) m caller

-- The initial local really keeps the dirty high bits before the loop body.
#guard initializer.value #v[0] = dirty
#guard initializer.value #v[0] ≠ BitVec.ofNat 256 257
#guard (~~~(~~~dirty+3)+3)+3 ≠ 0
#guard (lower 0 source).isNone
#guard (evalStmt 0 .nil True.intro source artifact.compiled.profile (sourceLocals #v[dirty])).isNone
#guard (lower 10 (Solidity.Yul.Stmt.zero (c := root) (n := 1) 1 body)).isNone
-- Actual DUP accessibility: last accepted local15, local16 refuses even
-- though both source variables are intrinsically in range.
def lastSource : Solidity.Yul.Stmt [] [] root 16 := .let_ 1 (.local 15) .skip
def beyondSource : Solidity.Yul.Stmt [] [] root 17 := .let_ 1 (.local 16) .skip
#guard (lower 2 lastSource).isSome
#guard (lower 2 beyondSource).isNone
#guard Scalar.run (popPrefix 1) [] = none
#guard Scalar.stackBound [Backend.Instr.op (.DUP 0)] (1024 : Int) = false

/-- info: 'Solidity.Yul.Compilation.LetScopeCompilation.Controls.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms initial
/-- info: 'Solidity.Yul.Compilation.LetScopeCompilation.Controls.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms body_source
/-- info: 'Solidity.Yul.Compilation.LetScopeCompilation.Controls.source_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_done
/-- info: 'Solidity.Yul.Compilation.LetScopeCompilation.Controls.target_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_done
end Solidity.Yul.Compilation.LetScopeCompilation.Controls
