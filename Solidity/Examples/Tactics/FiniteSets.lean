import Solidity.Calculus.Spec
import Solidity.Calculus.SolSpec
import Solidity.Tools.Show
import Solidity.Tools.Counterexample

/-!
# Finite equality-membership in source specifications

One declared primitive sort is checked for the key and every element before
the disjunction is constructed. Empty membership still checks its key.
These predicates reuse KeY equality; they do not introduce first-class sets
or change the meaning of halting specification expressions. Two arithmetic
expressions that both halt remain equal, as under the existing specification
equality: finite membership is not an assertion that its operands return.
-/

namespace Solidity.Examples.Tactics.FiniteSets

open Solidity
open scoped Solidity.Scoped

/-- Solidity `one` returns a value in the finite unsigned choice. -/
def Choices : Contract := contract!{
  uint value;
  ensures \in uint (\result; 1, 2, 2);
  function one() public pure returns (uint) { return 1; }
  requires \in uint (x; 1, 2);
  ensures \in uint (\result; 1, 2);
  function echo(uint x) public pure returns (uint) { return x; }
}

local instance : InContract := ⟨Choices⟩

/-- Solidity `one()` returns `1`, a member even when another element repeats. -/
theorem one_correct : ⊨ᶠ cspec!{ one } := by sol_spec

/-- Solidity `echo(x)` retains its finite-membership precondition. -/
theorem echo_correct : ⊨ᶠ cspec!{ echo } := by sol_spec

/-- info: 'Solidity.Examples.Tactics.FiniteSets.one_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms one_correct
/-- info: 'Solidity.Examples.Tactics.FiniteSets.echo_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms echo_correct

#guard Tools.SpecExpr.fmt (spec!(\in uint (3; 1, 3, 3))) == "\\in uint (3; 1, 3, 3)"
#guard Tools.SpecExpr.fmt (spec!(\in int (-1; -1, 0))) == "\\in int (-1; -1, 0)"
#guard Tools.SpecExpr.fmt (spec!(\in bool (true;))) == "\\in bool (true; )"
#guard Tools.specNums (spec!(\in uint (3; 5, 7, 7))) == [3, 5, 7, 7]
#guard (spec!(\in uint (value; \old(value)))).usesOld
#guard (spec!(\in bool (net(msg.sender) >= 0; true))).usesNet

private def ctx : SpecCtx Choices :=
  {storage := .storage, ensures := false, locals := [], result := none}

private def compile (e : SpecExpr) : Except String (Fml Choices []) := do
  let φ ← e.fml Choices ctx
  φ []

#guard (compile (spec!(\in uint (0; 0, 1)))).isOk
#guard (compile (spec!(\in int (-1; -1, 0)))).isOk
#guard (compile (spec!(\in bool (true; true, false)))).isOk
#guard (compile (spec!(\in address (msg.sender; this)))).isOk
#guard (compile (spec!(\in uint (0;)))).isOk
#guard (compile (spec!(\in uint (missing;)))).isOk == false
#guard (compile (spec!(\in uint (\old(value);)))).isOk == false
#guard (compile (spec!(\in int (0; uint(1))))).isOk == false
#guard (compile (spec!(\in uint (0; net(msg.sender))))).isOk == false
#guard (compile (spec!(\in uint (net(msg.sender);)))).isOk == false
#guard (compile (spec!(\in bool (0; true)))).isOk == false
#guard (compile (spec!(\in uint (-1;)))).isOk == false

run_cmd Lean.Elab.Command.liftTermElabM do
  for original in [spec!(\in uint (3; 1, 3, 3)), spec!(\in int (-1; -1, 0)),
      spec!(\in bool (true;)), spec!(\in address (msg.sender; this)),
      spec!(\forall uint x; x < 2 -> \in uint (x; 0, 1))] do
    let parsed ← match Lean.Parser.runParserCategory (← Lean.getEnv) `spec_expr (Tools.SpecExpr.fmt original) with
      | .ok stx => pure stx
      | .error message => Lean.throwError m!"finite membership printer did not parse: {message}"
    let expanded ← Lean.Elab.liftMacroM (expandSpec ⟨parsed⟩)
    let expression ← Lean.Elab.Term.elabTerm expanded (some (Lean.mkConst ``SpecExpr))
    let decoded ← Lean.Meta.evalExpr SpecExpr (Lean.mkConst ``SpecExpr) expression
    unless reprStr decoded == reprStr original do
      Lean.throwError "finite membership printer changed its syntax tree"

end Solidity.Examples.Tactics.FiniteSets
