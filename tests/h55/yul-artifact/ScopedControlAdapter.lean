import Solidity.Yul.Compilation.Artifact
import Solidity.Yul.Compilation.ScopedControlCompletion

/-! Explicit lossless transport for the existing scoped-control producer.
The emitted code and original constructor evidence are retained. This adapter
uses the existing zero-newer-prefix calling convention, with no admission,
fuel, failure, or compilation-totality claim. -/
namespace Solidity.Yul.Compilation.H55ScopedControl
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

variable {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}

/-- Both execution directions are derived from the unchanged producer laws. -/
def encode (a : ScopedControlCompilation.Artifact fuel stmt) : Artifact 0 stmt where
  profile := a.compiled.profile
  code := a.code
  source_to_model := by
    intro horizon locals result ran newer m caller
    have empty : newer.toList = [] := List.length_eq_zero_iff.mp (by simp only [Vector.length_toList])
    simpa only [empty, List.nil_append] using
      a.source_to_model horizon locals result ran m caller
  model_to_source := by
    intro locals newer m final caller skip ran
    have empty : newer.toList = [] := List.length_eq_zero_iff.mp (by simp only [Vector.length_toList])
    simp only [empty, List.nil_append] at ran
    simpa only [empty, List.nil_append] using
      ScopedControlCompletion.model_to_source a.compiled a.block a.code a.emitted a.selected
        locals m final caller skip ran

abbrev Image (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.Image (encode (fuel := fuel) (stmt := stmt))

def toImage (a : ScopedControlCompilation.Artifact fuel stmt) : Image fuel stmt :=
  Artifact.toImage encode a

def fromImage (image : Image fuel stmt) : ScopedControlCompilation.Artifact fuel stmt :=
  Artifact.fromImage image

theorem source_roundtrip (a : ScopedControlCompilation.Artifact fuel stmt) :
    fromImage (toImage a) = a := rfl

theorem image_roundtrip (image : Image fuel stmt) :
    toImage (fromImage image) = image := Artifact.image_roundtrip image

theorem code_preserved (a : ScopedControlCompilation.Artifact fuel stmt) :
    (toImage a).artifact.code = a.code := rfl

/-- The exact original emitted block and selected-code evidence are recovered. -/
theorem producer_preserved (a : ScopedControlCompilation.Artifact fuel stmt) :
    (fromImage (toImage a)).compiled = a.compiled ∧
    (fromImage (toImage a)).block = a.block ∧
    (fromImage (toImage a)).code = a.code := ⟨rfl, rfl, rfl⟩

/-- A real original compiler result inhabits the adapter image. -/
def skipProducer : ScopedControlCompilation.Artifact 1
    (Stmt.skip (c := ⟨false, false⟩) (n := 0)) :=
  (ScopedControlCompilation.lower 1 _).get (by rfl)

theorem inhabited_image : Nonempty (Image 1 (Stmt.skip (c := ⟨false, false⟩) (n := 0))) :=
  ⟨toImage skipProducer⟩

-- The original zero-fuel refusal remains separate from the image laws.
#guard (ScopedControlCompilation.lower 0 (Stmt.skip (c := ⟨false, false⟩) (n := 0))).isNone

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms code_preserved
#print axioms producer_preserved
#print axioms inhabited_image
end Solidity.Yul.Compilation.H55ScopedControl
