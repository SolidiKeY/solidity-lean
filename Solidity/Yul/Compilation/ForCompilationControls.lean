import Solidity.Yul.Compilation.ForCompilation
import Solidity.Yul.Compilation.SourceLoopInitializerControls
/-! Actual original-source visitor success and refusals. Emitted artifact is
constructed, not manually supplied component/emission/selection assumptions. -/
namespace Solidity.Yul.Compilation.ForCompilation.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root test step work body post dirty)
open SourceLoopInitializer.Controls

def artifact : Artifact 5 source 0 := (lower 5 source 0).get (by rfl)
theorem code_eq : artifact.code = code := rfl

theorem source_iff (locals out : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ fuel, evalStmt fuel .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
   .ok {m with stack := out.toList.map coreWord++caller} 0 :=
 artifact.completion_iff locals out #v[] m caller

/-- This real visitor artifact executes nontrivially from any old counter,
with raw second word and arbitrary caller fields, rather than always reverting. -/
theorem target_success (a b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := [coreWord a,coreWord b]++caller} =
   .ok {m with stack := [coreWord 0,coreWord (~~~(~~~b+3)+3)]++caller} 0 := by
 rw [code_eq]
 exact target_done a b m caller

/-- Accepted code generation is not a termination certificate. No divergence
adequacy is inferred from this constant nonzero guard's successful lowering. -/
def constantGuard : Solidity.Yul.Stmt [] [] root 2 := .for_ .skip (.literal 1) .skip .skip
#guard (lower 5 constantGuard 0).isSome
#guard (lower 5 source 0).isSome
#guard (lower 0 source 0).isNone
#guard (lower 5 source 15).isNone
#guard (lower 5 (Solidity.Yul.Stmt.skip (c := root) (n := 2)) 0).isNone
#guard (lower 5 (Solidity.Yul.Stmt.for_ (c := root) pre test step .break_) 0).isNone
#guard (evalStmt 0 .nil True.intro source artifact.compiled.profile (sourceLocals #v[99,dirty])).isNone
/-- info: 'Solidity.Yul.Compilation.ForCompilation.Controls.artifact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms artifact
/-- info: 'Solidity.Yul.Compilation.ForCompilation.Controls.code_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms code_eq
/-- info: 'Solidity.Yul.Compilation.ForCompilation.Controls.source_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_iff
/-- info: 'Solidity.Yul.Compilation.ForCompilation.Controls.target_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_success
end Solidity.Yul.Compilation.ForCompilation.Controls
