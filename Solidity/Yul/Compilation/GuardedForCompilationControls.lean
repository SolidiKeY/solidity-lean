import Solidity.Yul.Compilation.GuardedForCompilation
import Solidity.Yul.Compilation.GuardedForControls
/-! Real source visitor artifacts and refusals, including a high-only local
guard. Pure Yul truth here is not a Solidity per-pipeline readback theorem. -/
namespace Solidity.Yul.Compilation.GuardedForCompilation.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root)

def skippedSource : Solidity.Yul.Stmt [] [] root 2 :=
 .if_ GuardedFor.Controls.zeroExpr ForCompilation.Controls.constantGuard
def skippedArtifact : Artifact 5 0 skippedSource := (lower 5 0 skippedSource).get (by rfl)
theorem skipped_code_eq : skippedArtifact.code = GuardedFor.Controls.skippedCode := rfl

theorem skipped_success (locals : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run skippedArtifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := locals.toList.map coreWord++caller} 0 := by
 rw [skipped_code_eq]
 exact GuardedFor.Controls.skipped locals m caller

def takenSource : Solidity.Yul.Stmt [] [] root 2 :=
 .if_ GuardedFor.Controls.oneExpr SourceLoopInitializer.Controls.source
def takenArtifact : Artifact 5 0 takenSource := (lower 5 0 takenSource).get (by rfl)
theorem taken_code_eq : takenArtifact.code = GuardedFor.Controls.takenCode := rfl

theorem taken_success (a b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run takenArtifact.code {m with stack := [coreWord a,coreWord b]++caller} =
 .ok {m with stack := [coreWord 0,coreWord (~~~(~~~b+3)+3)]++caller} 0 := by
 rw [taken_code_eq]
 exact GuardedFor.Controls.target_taken a b m caller

def localExpr : Solidity.Yul.Expr [] [] 2 1 := .local 0
def localGuard := (PureExpressions.compile 5 localExpr).get (by rfl)
def localSource : Solidity.Yul.Stmt [] [] root 2 := .if_ localExpr SourceLoopInitializer.Controls.source
def localArtifact : Artifact 5 0 localSource := (lower 5 0 localSource).get (by rfl)
def localProgram := (localGuard.lowered.code 0).get (by rfl)
def localCode := (WordMachine.selectCode localProgram).get (by rfl)
def highOnly : Scalar.Word := BitVec.ofNat 256 (2^200)

/-- Full-word Yul truth takes the actual compiled branch even when all low
8bits are zero. No cleaning or Solidity-readback convention is inserted. -/
theorem high_only_taken (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run localArtifact.code {m with stack := [coreWord highOnly,coreWord b]++caller} =
 .ok {m with stack := [coreWord 0,coreWord (~~~(~~~b+3)+3)]++caller} 0 := by
 have driver := GuardedFor.machine localGuard ForCompilation.Controls.artifact localProgram localCode
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm #v[highOnly,b] #v[] m caller
 have nz : localGuard.value #v[highOnly,b] ≠ 0 := by change highOnly ≠ 0; decide
 rw [if_neg nz] at driver
 exact driver.trans (ForCompilation.Controls.target_success highOnly b m caller)

#guard highOnly.toNat % 256 = 0
#guard highOnly ≠ 0
#guard (lower 5 0 takenSource).isSome
#guard (lower 0 0 takenSource).isNone
#guard (lower 5 15 takenSource).isNone
#guard (lower 5 0 SourceLoopInitializer.Controls.source).isNone
#guard (lower 5 0 (Solidity.Yul.Stmt.if_ (c := root) GuardedFor.Controls.zeroExpr .skip)).isNone
/-- info: 'Solidity.Yul.Compilation.GuardedForCompilation.Controls.skippedArtifact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms skippedArtifact
/-- info: 'Solidity.Yul.Compilation.GuardedForCompilation.Controls.skipped_code_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms skipped_code_eq
/-- info: 'Solidity.Yul.Compilation.GuardedForCompilation.Controls.skipped_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms skipped_success
/-- info: 'Solidity.Yul.Compilation.GuardedForCompilation.Controls.takenArtifact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms takenArtifact
/-- info: 'Solidity.Yul.Compilation.GuardedForCompilation.Controls.taken_code_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms taken_code_eq
/-- info: 'Solidity.Yul.Compilation.GuardedForCompilation.Controls.taken_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms taken_success
/-- info: 'Solidity.Yul.Compilation.GuardedForCompilation.Controls.high_only_taken' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms high_only_taken
end Solidity.Yul.Compilation.GuardedForCompilation.Controls
