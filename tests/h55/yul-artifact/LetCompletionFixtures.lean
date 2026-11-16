import Solidity.Yul.Compilation.Artifact
import Solidity.Yul.Compilation.LetScopeCompletionControls
import Solidity.Yul.Compilation.LetSequenceCompletionControls
import Solidity.Yul.Compilation.LetBranchCompletionControls
import Solidity.Yul.Compilation.LetControlCompletionControls

/-! Regression coverage for losing an original source/code pair or assuming a
chosen completion horizon while sharing let-family controls. Four intrinsically
typed rows instantiate the existing generic Artifact. Their semantic fields come
from original producer proofs; table lookup supplies no semantic oracle. Existing
family negative/refusal controls remain in their original modules. -/
namespace Solidity.Yul.Compilation.H55LetCompletionFixtures
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

/-- Exact original fixtures, indexed without erasing their statement types. -/
noncomputable def rows : Vector (Σ stmt : Solidity.Yul.Stmt [] [] SourceLoop.Controls.root 1,
    Solidity.Yul.Compilation.Artifact 0 stmt) 4 :=
 #v[⟨LetScopeCompilation.Controls.source,
     Solidity.Yul.Compilation.Artifact.ofZero
       (c := SourceLoop.Controls.root) (n := 1) (stmt := LetScopeCompilation.Controls.source)
       LetScopeCompilation.Controls.artifact.compiled.profile LetScopeCompilation.Controls.artifact.code
       LetScopeCompilation.Controls.artifact.source_to_model
       (LetScopeCompletion.model_to_source LetScopeCompilation.Controls.artifact)⟩,
    ⟨LetSequenceCompilation.Controls.source,
     Solidity.Yul.Compilation.Artifact.ofZero
       (c := SourceLoop.Controls.root) (n := 1) (stmt := LetSequenceCompilation.Controls.source)
       LetSequenceCompilation.Controls.artifact.compiled.profile LetSequenceCompilation.Controls.artifact.code
       LetSequenceCompilation.Controls.artifact.source_to_model
       (LetSequenceCompletion.artifact_reflected LetSequenceCompilation.Controls.artifact)⟩,
    ⟨LetBranchCompilation.Controls.source,
     Solidity.Yul.Compilation.Artifact.ofZero
       (c := SourceLoop.Controls.root) (n := 1) (stmt := LetBranchCompilation.Controls.source)
       LetBranchCompilation.Controls.artifact.compiled.profile LetBranchCompilation.Controls.artifact.code
       LetBranchCompilation.Controls.artifact.source_to_model
       (LetBranchCompletion.model_to_source LetBranchCompilation.Controls.artifact)⟩,
    ⟨LetControlCompilation.Controls.source,
     Solidity.Yul.Compilation.Artifact.ofZero
       (c := SourceLoop.Controls.root) (n := 1) (stmt := LetControlCompilation.Controls.source)
       LetControlCompilation.Controls.artifact.compiled.profile LetControlCompilation.Controls.artifact.code
       LetControlCompilation.Controls.artifact.source_to_model
       (LetControlCompletion.artifact_reflected LetControlCompilation.Controls.artifact)⟩]

theorem originals_preserved :
 rows.toList.map (fun row => (row.1, row.2.code)) =
 [(LetScopeCompilation.Controls.source, LetScopeCompilation.Controls.artifact.code),
  (LetSequenceCompilation.Controls.source, LetSequenceCompilation.Controls.artifact.code),
  (LetBranchCompilation.Controls.source, LetBranchCompilation.Controls.artifact.code),
  (LetControlCompilation.Controls.source, LetControlCompilation.Controls.artifact.code)] := rfl

/-- Every row retains arbitrary full-word locals and the whole machine frame. -/
theorem completion_iff (i : Fin 4) (locals out : Vector Scalar.Word 1)
    (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ fuel, evalStmt fuel .nil True.intro rows[i].1 rows[i].2.profile (sourceLocals locals) =
   some ⟨sourceLocals out, .normal⟩) ↔
 Evm.run rows[i].2.code {m with stack := locals.toList.map coreWord ++ caller} =
   .ok {m with stack := out.toList.map coreWord ++ caller} 0 := by
 simpa only [Vector.toList_empty, List.nil_append] using
   rows[i].2.completion_iff locals out #v[] m caller

/-- All rows have real source completions for every raw input word. No source
completion or selected target run is a caller premise. -/
theorem source_inhabited (i : Fin 4) (b : Scalar.Word) :
 ∃ (fuel : Nat) (out : Vector Scalar.Word 1),
   evalStmt fuel .nil True.intro rows[i].1 rows[i].2.profile (sourceLocals #v[b]) =
     some ⟨sourceLocals out, .normal⟩ := by
 rcases i with ⟨index, bound⟩
 have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
 rcases choices with zero | one | two | three
 · subst index
   exact ⟨_, _, LetScopeCompilation.Controls.source_done b⟩
 · subst index
   exact ⟨_, _, LetSequenceCompilation.Controls.source_done b⟩
 · subst index
   exact ⟨_, _, LetBranchCompilation.Controls.source_done b⟩
 · subst index
   exact ⟨_, _, LetControlCompilation.Controls.source_done b⟩

/-- Simultaneous ordinary source and actual compiled-model completions for
all rows. This supplies no physical/native adequacy or resource observation. -/
theorem source_model_inhabited (i : Fin 4) (b : Scalar.Word)
    (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ (fuel : Nat) (out : Vector Scalar.Word 1),
   evalStmt fuel .nil True.intro rows[i].1 rows[i].2.profile (sourceLocals #v[b]) =
     some ⟨sourceLocals out, .normal⟩ ∧
   Evm.run rows[i].2.code
     {m with stack := (#v[b] : Vector Scalar.Word 1).toList.map coreWord ++ caller} =
     .ok {m with stack := out.toList.map coreWord ++ caller} 0 := by
 obtain ⟨fuel, out, source⟩ := source_inhabited i b
 exact ⟨fuel, out, source, (completion_iff i #v[b] out m caller).mp ⟨fuel, source⟩⟩

#print axioms originals_preserved
#print axioms completion_iff
#print axioms source_inhabited
#print axioms source_model_inhabited
end Solidity.Yul.Compilation.H55LetCompletionFixtures
