import Solidity.Yul.Composition.Interface

/-! Representation adapter only: existing G01/VY4 Fin256 words and actual
VY3 BitVec256 words. No new pure semantics, source locals or cleanup policy. -/
namespace Solidity.Yul.Composition

def targetWord (w : Solidity.Roadmap.Word) : Solidity.Backend.Scalar.Word := .ofFin w
def worldWord (w : Solidity.Backend.Scalar.Word) : Solidity.Roadmap.Word := w.toFin

theorem world_target_word (w : Solidity.Roadmap.Word) : worldWord (targetWord w) = w := rfl
theorem target_world_word (w : Solidity.Backend.Scalar.Word) : targetWord (worldWord w) = w := rfl

/-- Real target ADD agrees with the existing modular Fin addition and keeps
all256 bits. No Solidity narrow-value/dirty-local projection is inferred. -/
theorem world_word_add (a b : Solidity.Roadmap.Word) (tail : Solidity.Backend.Scalar.Stack) :
    Solidity.Backend.Scalar.run Solidity.Yul.Compilation.addWords.code
      (targetWord a :: targetWord b :: tail) =
      some (targetWord (a + b) :: tail) := rfl

example : (worldWord (targetWord ⟨511, by decide⟩)).val = 511 := rfl
example : (worldWord (targetWord ⟨511, by decide⟩)).val ≠ 255 := by decide +kernel
example : Solidity.Backend.Scalar.run Solidity.Yul.Compilation.addWords.code
    [targetWord ⟨2^256-1, by decide⟩, targetWord ⟨1, by decide⟩] =
      some [targetWord ⟨0, by decide⟩] := by decide +kernel
#print axioms world_target_word
#print axioms target_world_word
#print axioms world_word_add
end Solidity.Yul.Composition
