import Solidity.Lowering.V08.SharedFailureFixture

/-! Reuse and equivalence control for the original V08 failure-extraction proof. -/
namespace H55.ExtractFailureEquivalence
open Solidity

private theorem original {α : Type} (run : TRes α) (halt : THalt)
    (checked : run.halt? = some halt) : run = .error halt := by
  cases run with
  | ok value => cases checked
  | error actual =>
    have same : actual = halt := Option.some.inj checked
    cases same
    rfl

/-- The shared proof inhabits exactly the original statement for arbitrary inputs. -/
theorem original_statement {α : Type} (run : TRes α) (halt : THalt)
    (checked : run.halt? = some halt) : run = .error halt :=
  Lowering.V08.SharedFailureFixture.extract_failure run halt checked

/-- Both proofs are equal by proof irrelevance at every original input. -/
theorem proof_equivalence {α : Type} (run : TRes α) (halt : THalt)
    (checked : run.halt? = some halt) :
    original run halt checked = original_statement run halt checked :=
  Subsingleton.elim _ _

#print axioms original_statement
#print axioms proof_equivalence
end H55.ExtractFailureEquivalence
