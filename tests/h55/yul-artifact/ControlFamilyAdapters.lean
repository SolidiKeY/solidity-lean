import Solidity.Yul.Compilation.Artifact
import Solidity.Yul.Compilation.LetControlCompletion
import Solidity.Yul.Compilation.LetScopeCompletion
import Solidity.Yul.Compilation.LoopControlCompletion

/-! Three explicit producer-to-common-artifact transports. Existing execution
laws supply both directions; exact images retain all original producer data.
These are additive adapters, not compiler migrations or totality claims. -/
namespace Solidity.Yul.Compilation.H55ControlFamilies
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fuel depth : Nat} {stmt : Stmt [] [] c n}

namespace LetControl
def encode (a : LetControlCompilation.Artifact fuel stmt) : Artifact 0 stmt where
  profile := a.compiled.profile
  code := a.code
  source_to_model := by
    intro horizon locals result ran newer m caller
    have empty : newer.toList = [] := List.length_eq_zero_iff.mp (by simp only [Vector.length_toList])
    simpa only [empty, List.nil_append] using a.source_to_model horizon locals result ran m caller
  model_to_source := by
    intro locals newer m final caller skip ran
    have empty : newer.toList = [] := List.length_eq_zero_iff.mp (by simp only [Vector.length_toList])
    simp only [empty, List.nil_append] at ran
    simpa only [empty, List.nil_append] using
      LetControlCompletion.artifact_reflected a locals m final caller skip ran

abbrev Image (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.Image (encode (fuel := fuel) (stmt := stmt))
def toImage (a : LetControlCompilation.Artifact fuel stmt) : Image fuel stmt := Artifact.toImage encode a
def fromImage (a : Image fuel stmt) : LetControlCompilation.Artifact fuel stmt := Artifact.fromImage a

theorem source_roundtrip (a : LetControlCompilation.Artifact fuel stmt) :
    fromImage (toImage a) = a := rfl
theorem image_roundtrip (a : Image fuel stmt) : toImage (fromImage a) = a :=
  Artifact.image_roundtrip a
theorem code_preserved (a : LetControlCompilation.Artifact fuel stmt) :
    (toImage a).artifact.code = a.code := rfl

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms code_preserved
end LetControl

namespace LetScope
def encode (a : LetScopeCompilation.Artifact fuel stmt) : Artifact 0 stmt where
  profile := a.compiled.profile
  code := a.code
  source_to_model := by
    intro horizon locals result ran newer m caller
    have empty : newer.toList = [] := List.length_eq_zero_iff.mp (by simp only [Vector.length_toList])
    simpa only [empty, List.nil_append] using a.source_to_model horizon locals result ran m caller
  model_to_source := by
    intro locals newer m final caller skip ran
    have empty : newer.toList = [] := List.length_eq_zero_iff.mp (by simp only [Vector.length_toList])
    simp only [empty, List.nil_append] at ran
    simpa only [empty, List.nil_append] using
      LetScopeCompletion.model_to_source a locals m final caller skip ran

abbrev Image (fuel : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.Image (encode (fuel := fuel) (stmt := stmt))
def toImage (a : LetScopeCompilation.Artifact fuel stmt) : Image fuel stmt := Artifact.toImage encode a
def fromImage (a : Image fuel stmt) : LetScopeCompilation.Artifact fuel stmt := Artifact.fromImage a

theorem source_roundtrip (a : LetScopeCompilation.Artifact fuel stmt) :
    fromImage (toImage a) = a := rfl
theorem image_roundtrip (a : Image fuel stmt) : toImage (fromImage a) = a :=
  Artifact.image_roundtrip a
theorem code_preserved (a : LetScopeCompilation.Artifact fuel stmt) :
    (toImage a).artifact.code = a.code := rfl

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms code_preserved
end LetScope

namespace LoopControl
/-- The original arbitrary newer prefix is retained, rather than restricted to zero. -/
def encode (a : LoopControlCompilation.Artifact fuel stmt depth) : Artifact depth stmt where
  profile := a.compiled.profile
  code := a.code
  source_to_model := a.source_to_model
  model_to_source := LoopControlCompletion.artifact_reflected a

abbrev Image (fuel depth : Nat) (stmt : Stmt [] [] c n) :=
  Artifact.Image (encode (fuel := fuel) (depth := depth) (stmt := stmt))
def toImage (a : LoopControlCompilation.Artifact fuel stmt depth) : Image fuel depth stmt :=
  Artifact.toImage encode a
def fromImage (a : Image fuel depth stmt) : LoopControlCompilation.Artifact fuel stmt depth :=
  Artifact.fromImage a

theorem source_roundtrip (a : LoopControlCompilation.Artifact fuel stmt depth) :
    fromImage (toImage a) = a := rfl
theorem image_roundtrip (a : Image fuel depth stmt) : toImage (fromImage a) = a :=
  Artifact.image_roundtrip a
theorem code_preserved (a : LoopControlCompilation.Artifact fuel stmt depth) :
    (toImage a).artifact.code = a.code := rfl

#print axioms encode
#print axioms source_roundtrip
#print axioms image_roundtrip
#print axioms code_preserved
end LoopControl

namespace Controls
def skipSource : Stmt [] [] ⟨false, false⟩ 0 := .skip
def letSource : Stmt [] [] ⟨false, false⟩ 0 := .let_ 1 (.literal 0) .skip

def letControlProducer : LetControlCompilation.Artifact 3 letSource :=
  (LetControlCompilation.lower 3 letSource).get (by rfl)
def letScopeProducer : LetScopeCompilation.Artifact 3 letSource :=
  (LetScopeCompilation.lower 3 letSource).get (by rfl)
def loopControlProducer : LoopControlCompilation.Artifact 1 skipSource 2 :=
  (LoopControlCompilation.lower 1 skipSource 2).get (by rfl)

theorem inhabited_images : Nonempty (LetControl.Image 3 letSource) ∧
    Nonempty (LetScope.Image 3 letSource) ∧ Nonempty (LoopControl.Image 1 2 skipSource) :=
  ⟨⟨LetControl.toImage letControlProducer⟩, ⟨LetScope.toImage letScopeProducer⟩,
    ⟨LoopControl.toImage loopControlProducer⟩⟩

-- Original fuel refusals remain explicit, outside the lossless image laws.
#guard (LetControlCompilation.lower 0 letSource).isNone
#guard (LetControlCompilation.lower 1 skipSource).isNone
#guard (LoopControlCompilation.lower 0 skipSource 2).isNone
#print axioms inhabited_images
end Controls
end Solidity.Yul.Compilation.H55ControlFamilies
