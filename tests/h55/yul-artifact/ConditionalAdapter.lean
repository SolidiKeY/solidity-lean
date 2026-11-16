import Solidity.Yul.Compilation.Artifact
import Solidity.Yul.Compilation.ConditionalCompilation

/-! Exact conditional-producer transport. Guard and arm retain their separate
original fuel indices and all original emitted/selected data. The common source
is the same intrinsic if statement; code is unchanged. -/
namespace Solidity.Yul.Compilation.H55Conditional
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n f g : Nat} {test : Expr [] [] n 1} {body : Stmt [] [] c n}

def encode (a : ConditionalCompilation.Artifact f g test body) : Artifact 0 (.if_ test body) where
  profile := a.profile
  code := a.code
  source_to_model := by
    intro horizon locals result ran newer m caller
    have empty : newer.toList = [] := List.length_eq_zero_iff.mp (by simp only [Vector.length_toList])
    simpa only [empty, List.nil_append] using a.source_to_model horizon locals result ran m caller
  model_to_source := by
    intro locals newer m final caller skip ran
    have empty : newer.toList = [] := List.length_eq_zero_iff.mp (by simp only [Vector.length_toList])
    simp only [empty, List.nil_append] at ran
    simpa only [empty, List.nil_append] using a.model_to_source locals m final caller skip ran

abbrev Image (f g : Nat) (test : Expr [] [] n 1) (body : Stmt [] [] c n) :=
  Artifact.Image (encode (f := f) (g := g) (test := test) (body := body))
def toImage (a : ConditionalCompilation.Artifact f g test body) : Image f g test body :=
  Artifact.toImage encode a
def fromImage (a : Image f g test body) : ConditionalCompilation.Artifact f g test body :=
  Artifact.fromImage a

theorem source_roundtrip (a : ConditionalCompilation.Artifact f g test body) :
    fromImage (toImage a) = a := rfl
theorem image_roundtrip (a : Image f g test body) : toImage (fromImage a) = a :=
  Artifact.image_roundtrip a
theorem code_preserved (a : ConditionalCompilation.Artifact f g test body) :
    (toImage a).artifact.code = a.code := rfl

/-- Exact original block and selected guard/arm evidence are retained. -/
theorem original_selection_preserved (a : ConditionalCompilation.Artifact f g test body) :
    WordControl.blockCode (fromImage (toImage a)).block = some (toImage a).artifact.code := a.selected

namespace Controls
def controlBody : Stmt [] [] ⟨false, false⟩ 1 :=
  .assign (fun _ : Fin 1 => .local 0) (.literal 7)
def controlTest : Expr [] [] 1 1 := .local 0
def producer : ConditionalCompilation.Artifact 3 3 controlTest controlBody :=
  (ConditionalCompilation.lower 3 3 controlTest controlBody).get (by rfl)

theorem inhabited_image : Nonempty (Image 3 3 controlTest controlBody) := ⟨toImage producer⟩

-- These are original compile-time refusals, including a statically false guard.
#guard (ConditionalCompilation.lower 0 3 controlTest controlBody).isNone
#guard (ConditionalCompilation.lower 3 0 controlTest controlBody).isNone
#guard (ConditionalCompilation.lower 3 0 (.literal 0) controlBody).isNone

theorem false_source : evalStmt 4 .nil True.intro (.if_ controlTest controlBody)
    (encode producer).profile (sourceLocals #v[0]) = some ⟨sourceLocals #v[0], .normal⟩ := rfl

theorem true_source : evalStmt 4 .nil True.intro (.if_ controlTest controlBody)
    (encode producer).profile (sourceLocals #v[1]) = some ⟨sourceLocals #v[7], .normal⟩ := by
  apply congrArg some
  apply congrArg (fun vars : Values 1 => (⟨vars, .normal⟩ : Outcome ⟨false, false⟩ 1))
  funext i
  have same : i = 0 := Fin.ext (by omega)
  cases same
  rfl

theorem false_model (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode producer).code {m with stack := coreWord 0 :: caller} =
      .ok {m with stack := coreWord 0 :: caller} 0 := by
  simpa only [Vector.toList_empty, Vector.toList_singleton, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append] using
    (encode producer).normal_to_model 4 #v[0] #v[0] false_source #v[] m caller

theorem true_model (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run (encode producer).code {m with stack := coreWord 1 :: caller} =
      .ok {m with stack := coreWord 7 :: caller} 0 := by
  simpa only [Vector.toList_empty, Vector.toList_singleton, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append] using
    (encode producer).normal_to_model 4 #v[1] #v[7] true_source #v[] m caller
end Controls

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms code_preserved
#print axioms original_selection_preserved
#print axioms Controls.inhabited_image
#print axioms Controls.false_source
#print axioms Controls.true_source
#print axioms Controls.false_model
#print axioms Controls.true_model
end Solidity.Yul.Compilation.H55Conditional
