import Lean

/-! Isolated character-boundary observations for the String API migration.
These finite proofs do not establish equivalence of production functions. -/
namespace H62.MigrateTheory.StringBoundaryWitness

def dropChars (s : String) (n : Nat) : String := toString (s.drop n)
def trimChars (s : String) (n : Nat) : String :=
  String.mk (s.toList.take (s.length - n))

example : dropChars "aλ🙂z" 1 = "λ🙂z" := by decide
example : dropChars "" 8 = "" := by decide
example : dropChars "λ🙂" 8 = "" := by decide
example : trimChars "aλ🙂z" 1 = "aλ🙂" := by decide
example : trimChars "λ🙂" 8 = "" := by decide

end H62.MigrateTheory.StringBoundaryWitness
