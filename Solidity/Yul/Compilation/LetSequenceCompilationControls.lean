import Solidity.Yul.Compilation.LetSequenceCompilation
import Solidity.Yul.Compilation.LetScopeCompilationControls
/-! Actual sequential lexical lowering. The second let initializer reads the
outer value produced by the first scope; both run real structured loop bodies.
Kernel source/model witnesses, not external/native adequacy evidence. -/
namespace Solidity.Yul.Compilation.LetSequenceCompilation.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)

def source : Solidity.Yul.Stmt [] [] root 1 :=
 .seq LetScopeCompilation.Controls.source LetScopeCompilation.Controls.source
def artifact := (lower 11 source).get (by rfl)
def update (b : Scalar.Word) : Scalar.Word := (~~~(~~~(b+dirty)+3)+3)+3

theorem selected : artifact.code = LetScopeCompilation.Controls.artifact.code ++ LetScopeCompilation.Controls.artifact.code := by rfl

theorem source_done (b : Scalar.Word) :
 evalStmt 16 .nil True.intro source artifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[update (update b)],.normal⟩ :=
 LoopControlCompilation.sequence_source LetScopeCompilation.Controls.source LetScopeCompilation.Controls.source
   LetScopeCompilation.Controls.artifact.compiled.profile LetScopeCompilation.Controls.artifact.compiled.profile
   15 (sourceLocals #v[b]) (sourceLocals #v[update b]) (sourceLocals #v[update (update b)])
   (LetScopeCompilation.Controls.source_done b) (LetScopeCompilation.Controls.source_done (update b))

theorem target_done (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord b::caller} =
 .ok {m with stack := coreWord (update (update b))::caller} 0 :=
 by
 exact CompletionControls.normal_output (c := root) #v[update (update b)]
   (fun actual => Evm.run artifact.code {m with stack := coreWord b::caller} =
     .ok {m with stack := actual.toList.map coreWord++caller} 0)
   (artifact.source_to_model 16 #v[b] ⟨sourceLocals #v[update (update b)],.normal⟩
     (source_done b) m caller)

-- Distinguishes true sequential mutation from accidentally reusing input b.
#guard update (update 0) ≠ update 0
#guard update (update 0) ≠ 0
#guard update (update 0) = BitVec.ofNat 256 (2*(2^200+257)+6)
#guard (lower 0 source).isNone
#guard (lower 1 source).isNone
#guard (LetScopeCompilation.lower 11 source).isNone
#guard (evalStmt 0 .nil True.intro source artifact.compiled.profile (sourceLocals #v[dirty])).isNone
-- Unsupported ordinary leaves refuse locally; no admission implication.
def unsupported : Solidity.Yul.Stmt [] [] root 1 := .seq LetScopeCompilation.Controls.source .skip
#guard (lower 11 unsupported).isNone
-- Existing finite selection is preserved independently of 1024 capacity.
#guard Scalar.stackBound [Backend.Instr.op (.DUP 0)] (1024 : Int) = false
#guard Scalar.run (popPrefix 1) [] = none

/-- info: 'Solidity.Yul.Compilation.LetSequenceCompilation.Controls.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms selected
/-- info: 'Solidity.Yul.Compilation.LetSequenceCompilation.Controls.source_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_done
/-- info: 'Solidity.Yul.Compilation.LetSequenceCompilation.Controls.target_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_done
end Solidity.Yul.Compilation.LetSequenceCompilation.Controls
