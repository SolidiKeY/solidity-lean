import Solidity.Yul.Compilation.GuardedFor
import Solidity.Yul.Compilation.ForCompilationControls
/-! An actual false guard skips a selected constant-nonzero loop without any
body execution premise. Taken guard transports an actual initialized loop. -/
namespace Solidity.Yul.Compilation.GuardedFor.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)

def zeroExpr : Solidity.Yul.Expr [] [] 2 1 := .literal 0
def zeroGuard := (PureExpressions.compile 1 zeroExpr).get (by rfl)
def endless : ForCompilation.Artifact 5 ForCompilation.Controls.constantGuard 0 :=
 (ForCompilation.lower 5 ForCompilation.Controls.constantGuard 0).get (by rfl)
def zeroProgram := (zeroGuard.lowered.code 0).get (by rfl)
def zeroCode := (WordMachine.selectCode zeroProgram).get (by rfl)
def skippedCode := (lower zeroGuard endless).get (by rfl)

/-- No target or source execution of the untaken constant-true loop is an
input. The exact entire caller frame is preserved. -/
theorem skipped (locals : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run skippedCode {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := locals.toList.map coreWord++caller} 0 :=
 machine zeroGuard endless zeroProgram zeroCode (Option.some_get (by rfl)).symm
   (Option.some_get (by rfl)).symm locals #v[] m caller

theorem source_skipped (locals : Vector Scalar.Word 2) :
 evalStmt 2 .nil True.intro (.if_ zeroExpr ForCompilation.Controls.constantGuard)
   ⟨zeroGuard.profile,endless.compiled.profile⟩ (sourceLocals locals) =
 some ⟨sourceLocals locals,.normal⟩ := rfl

def oneExpr : Solidity.Yul.Expr [] [] 2 1 := .literal 1
def oneGuard := (PureExpressions.compile 1 oneExpr).get (by rfl)
def takenCode := (lower oneGuard ForCompilation.Controls.artifact).get (by rfl)

theorem source_taken (a b : Scalar.Word) :
 evalStmt 10 .nil True.intro (.if_ oneExpr SourceLoopInitializer.Controls.source)
   ⟨oneGuard.profile,ForCompilation.Controls.artifact.compiled.profile⟩ (sourceLocals #v[a,b]) =
 some ⟨sourceLocals #v[0,~~~(~~~b+3)+3],.normal⟩ :=
 source_nonzero oneGuard ForCompilation.Controls.artifact 9 (by omega) #v[a,b] _
   (by change (1 : Scalar.Word) ≠ 0; decide) (SourceLoopInitializer.Controls.source_done a b)

/-- Actual original conditional completion produces a nontrivial whole
conditional/initialized-loop run, raw dirty data and arbitrary caller intact. -/
theorem target_taken (a b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run takenCode {m with stack := [coreWord a,coreWord b]++caller} =
 .ok {m with stack := [coreWord 0,coreWord (~~~(~~~b+3)+3)]++caller} 0 := by
 obtain ⟨out,same,ran⟩ := source_to_model oneGuard ForCompilation.Controls.artifact takenCode
   (Option.some_get (by rfl)).symm 10 #v[a,b] _ (source_taken a b) #v[] m caller
 have equal : #v[0,~~~(~~~b+3)+3] = out :=
   SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
 subst out
 exact ran

#guard (evalStmt 0 .nil True.intro (.if_ zeroExpr ForCompilation.Controls.constantGuard)
 ⟨zeroGuard.profile,endless.compiled.profile⟩ (sourceLocals #v[99,dirty])).isNone
#guard (evalStmt 1 .nil True.intro (.if_ zeroExpr ForCompilation.Controls.constantGuard)
 ⟨zeroGuard.profile,endless.compiled.profile⟩ (sourceLocals #v[99,dirty])).isNone
#guard (lower zeroGuard endless).isSome
#guard (PureExpressions.compile 0 zeroExpr).isNone
/-- info: 'Solidity.Yul.Compilation.GuardedFor.Controls.skipped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms skipped
/-- info: 'Solidity.Yul.Compilation.GuardedFor.Controls.source_skipped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_skipped
/-- info: 'Solidity.Yul.Compilation.GuardedFor.Controls.source_taken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_taken
/-- info: 'Solidity.Yul.Compilation.GuardedFor.Controls.target_taken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_taken
end Solidity.Yul.Compilation.GuardedFor.Controls
