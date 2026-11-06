import Solidity.Yul.Compilation.ProducerExpressions
import Solidity.Yul.DirectWords
/-! Concrete raw external-cell compilation using the ACTUAL VY1 WordAdapter,
WordState packing and DirectWords evaluator. No cell layout, dirty-word policy,
source AST or state is duplicated here. This does not establish Solidity
Source/session/pipeline embedding, admission coverage or physical semantics. -/
namespace Solidity.Yul.Compilation.OpenExpressions
open Backend Scalar
open Solidity.Yul.Closed

def packedTerm {X n} (expr : Expr [] X n 1) (policy : Policy.ExprP .A expr) :
    Logic.Term [] (n+wordCellCount X) 1 :=
  WordAdapter.expression expr policy (Fin.castAdd (wordCellCount X))
    (fun cell => Fin.natAdd n cell.slot)

abbrev Compiled {X n} (fuel : Nat) (expr : Expr [] X n 1) (policy : Policy.ExprP .A expr) :=
  ProducerExpressions.Compiled fuel (packedTerm expr policy).code

def compile {X n} (fuel : Nat) (expr : Expr [] X n 1) (policy : Policy.ExprP .A expr) :
    Option (Compiled fuel expr policy) := ProducerExpressions.compile fuel (packedTerm expr policy).code

/-- Pointwise encoding of the producer's real intrinsic packed context. -/
def encoded {X n} (state : WordState X n) : Vector Scalar.Word (n+wordCellCount X) :=
  Vector.ofFn (fun i => BitVec.ofFin (state.pack i))

theorem encoded_locals {X n} (state : WordState X n) :
    ProducerExpressions.sourceLocals (encoded state) = state.pack := by
  funext i
  simp only [ProducerExpressions.sourceLocals,encoded,Vector.getElem_ofFn,
    BitVec.toFin_ofFin,Fin.eta]

/-- Actual original-AST completion is derived, at the identical source fuel,
using the producer's concrete packed_agrees theorem and proven coordinate law. -/
theorem source {X n fuel} {expr : Expr [] X n 1} {policy : Policy.ExprP .A expr}
    (compiled : Compiled fuel expr policy) (state : WordState X n) :
    DirectWords.eval fuel expr policy state =
      some (fun _ => (compiled.value (encoded state)).toFin) := by
  rw [DirectWords.packed_agrees]
  have completed := compiled.source (encoded state)
  rw [encoded_locals] at completed
  exact completed

theorem executes {X n fuel} {expr : Expr [] X n 1} {policy : Policy.ExprP .A expr}
    (compiled : Compiled fuel expr policy) (state : WordState X n)
    (depth : Nat) (code : Program) (emitted : compiled.lowered.code depth = some code)
    (newer : Vector Scalar.Word depth) (caller : Stack) :
    DirectWords.eval fuel expr policy state = some (fun _ => (compiled.value (encoded state)).toFin) ∧
    run code (newer.toList ++ ((encoded state).toList ++ caller)) =
      some (compiled.value (encoded state) :: (newer.toList ++ ((encoded state).toList ++ caller))) :=
  ⟨source compiled state,compiled.lowered.correct depth code emitted (encoded state) newer caller⟩
#print axioms compile
#print axioms encoded_locals
#print axioms source
#print axioms executes
end Solidity.Yul.Compilation.OpenExpressions
