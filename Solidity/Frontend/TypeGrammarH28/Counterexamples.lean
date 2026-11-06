import Solidity.Frontend.Checked.Prec
import Solidity.Frontend.TypeGrammarH28.Layouts

/-! Preserve the false raw-yield uniqueness claim. Array lengths are syntactic
atoms: type-name uniqueness must explicitly account for their identity. This
file proves a counterexample at type-name level, not expression uniqueness. -/
namespace Solidity.Frontend.TypeGrammarH28
open Solidity.Source Solidity.Frontend.Checked

private def atom (n : Nat) : Syn .expr := .lit (.num (.dec n 0 0))

def leftAssociated : Syn .typeName :=
  .array (.elem .bool) (.some (.addSub .add (.addSub .add (atom 1) (atom 2)) (atom 3)))

def rightAssociated : Syn .typeName :=
  .array (.elem .bool) (.some (.addSub .add (atom 1) (.addSub .add (atom 2) (atom 3))))

private def leftShape : Syn .typeName → Bool
  | .array _ (.some (.addSub _ (.addSub ..) _)) => true
  | _ => false

/-- Two actual type names derive the same tokens but are different trees. -/
theorem raw_yield_not_unique :
    leftAssociated.toks [] = rightAssociated.toks [] ∧
    leftAssociated.toks [] ≠ none ∧ leftAssociated ≠ rightAssociated := by
  refine ⟨rfl, by decide +kernel, ?_⟩
  intro h
  have impossible : true = false := congrArg leftShape h
  cases impossible

/-- The existing precedence contract distinguishes the two length atoms. -/
theorem raw_counterexample_precedence :
    leftAssociated.prec = true ∧ rightAssociated.prec = false := by decide +kernel

#print axioms raw_yield_not_unique
#print axioms raw_counterexample_precedence
end Solidity.Frontend.TypeGrammarH28
