import Solidity.Backend.Executable.ScalarArtifact
import Solidity.Backend.Executable.ScalarSequenceChecks

/-! The exact scalar bytes returned/reverted by an actual creation prefix,
with protected creation words and separate populated typed scalar caller words. -/
namespace Solidity.Backend.Executable.ScalarArtifactChecks
open Creation ScalarArtifact ScalarSequenceChecks

def creationTail : List StackWord := [⟨11, by decide⟩, ⟨22, by decide⟩]

/-- The 104-byte scalar encoding is actually returned after both prefix segments. -/
example : Exec (image false true a b [0xaa,0xbb]) (image false true a b [0xaa,0xbb]) creationTail []
    (.returned (runtimeBytes false a b)) := constructor_exec false true a b _ _

/-- The 175-byte checked-test encoding is returned with the same derived offset. -/
example : Exec (image true true a b [0xaa]) (image true true a b [0xaa]) creationTail []
    (.returned (runtimeBytes true a b)) := constructor_exec true true a b _ _

/-- The independent constructor can instead revert those exact nonempty bytes. -/
example : Exec (image true false a b [0xaa,0xbb]) (image true false a b [0xaa,0xbb]) creationTail []
    (.reverted (runtimeBytes true a b)) := constructor_exec true false a b _ _

/-- Runtime, argument and image lengths are derived from actual encoded programs. -/
example : (runtimeBytes false a b).length = 104 ∧ (runtimeBytes true a b).length = 175 ∧
    (front false true a b).length = 16 ∧ (image true true a b [0xaa,0xbb]).length = 193 :=
  ⟨runtime_length false a b, runtime_length true a b, front_length false true a b, image_length true true a b _⟩

example : (image true true a b [0xaa,0xbb]).drop 191 = [0xaa,0xbb] := by
  have slice := arguments_slice true true a b [0xaa,0xbb]
  rw [runtime_length] at slice
  exact slice

example : ¬ Exec (image true true a b [0xaa]) (image true true a b [0xaa]) creationTail []
    (.returned (runtimeBytes true a b ++ [0xaa])) := excludes_argument_bytes true a b _ (by decide) _

example : ¬ Exec (image false true a b [0xaa]) (image false true a b [0xaa]) creationTail []
    (.reverted (runtimeBytes false a b)) := excludes_wrong_tag false a b _ _

example : ¬ Exec (image true false a b [0xaa,0xbb]) (image true false a b [0xaa,0xbb]) creationTail []
    (.reverted (runtimeBytes true a b ++ [0xaa,0xbb])) :=
  excludes_revert_arguments true a b _ (by decide) _

/-- Source, numeric-frame and constructor byte facts are separately established
for the same selected payload, with no equality between the two runners. -/
theorem inhabited_typed_payload :
    (ScalarSequence.resultExpr a b).evalT caller = .ok false ∧
    Scalar.run (runtimeCode false a b) (ScalarSequence.frameTail caller []) =
      some (0 :: BitVec.ofInt 256 (-2) :: ScalarSequence.frameTail caller []) ∧
    Scalar.stackBound (runtimeCode false a b) ((ScalarSequence.frameTail caller []).length : Int) = true ∧
    Exec (image false true a b [0xaa,0xbb]) (image false true a b [0xaa,0xbb]) creationTail []
      (.returned (runtimeBytes false a b)) ∧
    Backend.decode (runtimeBytes false a b) = some (runtimeCode false a b) :=
  typed_payload caller [] (by decide) a b wrapped negative true rfl rfl rfl rfl rfl _ _

/-- info: 'Solidity.Backend.Executable.ScalarArtifactChecks.inhabited_typed_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inhabited_typed_payload
end Solidity.Backend.Executable.ScalarArtifactChecks
