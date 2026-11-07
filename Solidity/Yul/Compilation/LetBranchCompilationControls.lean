import Solidity.Yul.Compilation.LetBranchCompilation
import Solidity.Yul.Compilation.LetSequenceCompilationControls
/-! Actual conditional let-sequence lowering, with raw high-only conditions
and short-horizon untaken arms. These are kernel source/model controls, not
Solidity narrow-type readback or external compiler/native evidence. -/
namespace Solidity.Yul.Compilation.LetBranchCompilation.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)

def test : Expr [] [] 1 1 := .local 0
def condition := (PureExpressions.compile 11 test).get (by rfl)
def source : Solidity.Yul.Stmt [] [] root 1 := .if_ test LetSequenceCompilation.Controls.source
def artifact := (lower 11 source).get (by rfl)
def update (b : Scalar.Word) : Scalar.Word :=
 if b = 0 then b else LetSequenceCompilation.Controls.update (LetSequenceCompilation.Controls.update b)

theorem source_done (b : Scalar.Word) :
 evalStmt 17 .nil True.intro source artifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[update b],.normal⟩ := by
 change (if b.toNat = 0 then some (⟨sourceLocals #v[b],.normal⟩ : Outcome root 1)
   else evalStmt 16 .nil True.intro LetSequenceCompilation.Controls.source
     LetSequenceCompilation.Controls.artifact.compiled.profile (sourceLocals #v[b])) = _
 by_cases zero : b = 0
 · have zn : b.toNat = 0 := congrArg BitVec.toNat zero
   rw [if_pos zn,update,if_pos zero]
 · have nz : b.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
   rw [if_neg nz,update,if_neg zero]
   exact LetSequenceCompilation.Controls.source_done b

theorem target_done (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord b::caller} =
 .ok {m with stack := coreWord (update b)::caller} 0 :=
 artifact.normal_to_model 17 #v[b] #v[update b] (source_done b) m caller

/-- The zero guard completes without requiring a body completion at horizon1. -/
theorem zero_early_source :
 evalStmt 2 .nil True.intro source artifact.compiled.profile (sourceLocals #v[0]) =
 some ⟨sourceLocals #v[0],.normal⟩ := by rfl

theorem zero_target (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord 0::caller} =
 .ok {m with stack := coreWord 0::caller} 0 :=
 artifact.normal_to_model 2 #v[0] #v[0] zero_early_source m caller

def highOnly : Scalar.Word := BitVec.ofNat 256 (2^200)
theorem high_target (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord highOnly::caller} =
 .ok {m with stack := coreWord (LetSequenceCompilation.Controls.update
   (LetSequenceCompilation.Controls.update highOnly))::caller} 0 := target_done highOnly m caller

#guard highOnly ≠ 0
#guard update highOnly = LetSequenceCompilation.Controls.update (LetSequenceCompilation.Controls.update highOnly)
#guard update highOnly ≠ highOnly
#guard update 0 = 0
#guard (evalStmt 1 .nil True.intro LetSequenceCompilation.Controls.source
 LetSequenceCompilation.Controls.artifact.compiled.profile (sourceLocals #v[0])).isNone
#guard (lower 0 source).isNone
#guard (LetSequenceCompilation.lower 11 source).isNone
#guard (evalStmt 0 .nil True.intro source artifact.compiled.profile (sourceLocals #v[dirty])).isNone
-- Both condition variables are intrinsically in range; actual DUP selection
-- accepts only local0..15, independently of source admission or capacity.
def lastSource : Solidity.Yul.Stmt [] [] root 16 := .if_ (.local 15) (.let_ 1 (.literal 0) .skip)
def beyondSource : Solidity.Yul.Stmt [] [] root 17 := .if_ (.local 16) (.let_ 1 (.literal 0) .skip)
#guard (lower 2 lastSource).isSome
#guard (lower 2 beyondSource).isNone
#guard Scalar.stackBound [Backend.Instr.op (.DUP 0)] (1024 : Int) = false
#guard Scalar.run (popPrefix 1) [] = none

/-- info: 'Solidity.Yul.Compilation.LetBranchCompilation.Controls.source_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_done
/-- info: 'Solidity.Yul.Compilation.LetBranchCompilation.Controls.target_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_done
/-- info: 'Solidity.Yul.Compilation.LetBranchCompilation.Controls.zero_early_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_early_source
/-- info: 'Solidity.Yul.Compilation.LetBranchCompilation.Controls.zero_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_target
/-- info: 'Solidity.Yul.Compilation.LetBranchCompilation.Controls.high_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms high_target
end Solidity.Yul.Compilation.LetBranchCompilation.Controls
