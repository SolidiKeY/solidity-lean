import Solidity.Calculus.Spec
import Solidity.Calculus.SolSpec
import Solidity.Tools.Show
import Solidity.Tools.Counterexample
import Solidity.Frontend.Import

/-!
# Literal-domain filtered membership in source specifications

The key is checked outside the guard's binder, including with repeated
source names. Empty domains still validate the key and guard. The generated
formula demands a value for the key, while guard equality keeps KeY's
existing interpretation of halting expressions.
-/

namespace Solidity.Examples.Tactics.FilteredSets

open Solidity
open scoped Solidity.Scoped

/-- Solidity fixtures whose postconditions use finite primitive domains. -/
def Choices : Contract := contract!{
  uint value;
  uint[] entries;
  mapping(uint => uint) table;
  ensures \result \in uint(x; 1, 2, 2; x > 1);
  function one() public pure returns (uint) { return 2; }
  requires x \in uint(k; 1, 2; k > 1);
  ensures \result == 2;
  function echo(uint x) public pure returns (uint) { return x; }
  ensures !(1 \in uint(x; ; x == 1));
  function empty() public pure {}
  ensures !(1 / 0 \in uint(x; 0, 1; true));
  function undefinedKey() public pure {}
  ensures 1 \in uint(x; 1; (1 / 0) == (2 / 0));
  function theoryGuard() public pure {}
}

local instance : InContract := ⟨Choices⟩

/-- Solidity `one()` returns the admitted value even with duplicate domain entries. -/
theorem one_correct : ⊨ᶠ cspec!{ one } := by sol_spec

/-- Solidity `echo(x)` preserves a filter whose only admitted value is `2`. -/
theorem echo_correct : ⊨ᶠ cspec!{ echo } := by sol_spec

/-- An empty literal domain never admits a Solidity value. -/
theorem empty_correct : ⊨ᶠ cspec!{ empty } := by sol_spec

/-- An undefined key cannot match a successfully denoting primitive binder. -/
theorem undefined_key_correct : ⊨ᶠ cspec!{ undefinedKey } := by sol_spec

/-- Guard equality retains the existing Theory failure equality. -/
theorem theory_guard_correct : ⊨ᶠ cspec!{ theoryGuard } := by sol_spec

/-- info: 'Solidity.Examples.Tactics.FilteredSets.one_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms one_correct
/-- info: 'Solidity.Examples.Tactics.FilteredSets.undefined_key_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms undefined_key_correct

private def ctx : SpecCtx Choices :=
  {storage := .storage, ensures := false, locals := [], result := none}

private def compile (e : SpecExpr) : Except String (Fml Choices []) := do
  let φ ← e.fml Choices ctx
  φ []

#guard (compile (spec!(2 \in uint(x; 1, 2; x > 1)))).isOk
#guard (compile (spec!(-1 \in int(x; -2, -1, 0; x < 0)))).isOk
#guard (compile (spec!(true \in bool(x; false, true; x)))).isOk
#guard (compile (spec!(7 \in address(x; 7, 9; x == 7)))).isOk
#guard (compile (spec!(1 \in uint(x; ; true)))).isOk
#guard (compile (spec!(missing \in uint(x; ; true)))).isOk == false
#guard (compile (spec!(1 \in uint(x; ; missing == 0)))).isOk == false
#guard (compile (spec!(1 \in uint(x; ; x + 1)))).isOk == false
#guard (compile (spec!(1 \in uint(x; ; \old(x) == x)))).isOk == false
#guard (compile (spec!(1 \in uint(x; value; true)))).isOk == false
#guard (compile (spec!(1 \in uint(value; value; true)))).isOk == false
#guard (compile (spec!(1 \in uint(x; 1 + 0; true)))).isOk == false
#guard (compile (spec!(1 \in uint(x; net(msg.sender); true)))).isOk == false
#guard (compile (spec!(net(msg.sender) \in uint(x; ; true)))).isOk == false
#guard (compile (spec!(0 \in int(x; uint(1); true)))).isOk == false
#guard (compile (spec!(true \in bool(x; 0; true)))).isOk == false
#guard (compile (spec!(1 \in uint(x; -1; true)))).isOk == false
#guard (compile (spec!(0 \in uint(x; 115792089237316195423570985008687907853269984665640564039457584007913129639936; true)))).isOk == false
#guard (compile (spec!(1 \in uint(entries; 1; entries.length == entries.length)))).isOk == false
#guard (compile (spec!(1 \in uint(entries; ; entries.length == entries.length)))).isOk == false
#guard (compile (spec!(1 \in uint(table; 1; table[0] == table[0])))).isOk == false
#guard (compile (spec!(1 \in uint(result; 1; true)))).isOk == false
#guard (compile (spec!(1 \in uint(old; 1; true)))).isOk == false
#guard (compile (spec!(1 \in uint(oldNet; 1; true)))).isOk == false
#guard (compile (spec!(1 \in uint(result_first; 1; true)))).isOk == false
#guard (compile (spec!(1 \in uint(x; 1; \exists uint result; true)))).isOk == false
#guard (compile (spec!(\forall uint entries; entries.length == entries.length))).isOk == false

#guard (spec!(\old(value) \in uint(x; 1; x == value))).usesOld
#guard (spec!(1 \in uint(x; ; \old(net(msg.sender)) == x))).usesOldNet
#guard Tools.specNums (spec!(3 \in uint(x; 5, 7; x > 2))) == [3, 5, 7, 2]
#guard (spec!(value \in uint(value; 1; value == 1))).names == ["value"]
#guard (spec!(0 \in uint(value; ; value == 1))).names == []

private def shadowed : Except String (Fml Choices [.val .uint]) := do
  let φ ← (spec!(x \in uint(x; 1, 2; x == 2))).fml Choices
    {ctx with locals := [("x", .uint)]}
  φ [(.ofName "x", .val .uint)]

-- The actual key points past the bound guard local, rather than capturing it.
#guard match shadowed with
  | .ok (.not (.all _ _ (.not (.and
      (.eq (.pvV (.there .here)) (.pvV .here)) (.and _ (.eq (.pvV .here) _)))))) => true
  | _ => false

-- Protect new binders without changing prefix membership constant resolution.
#guard Frontend.specHasFilteredMembership "2 \\in uint(N; 1, 2; N == 2)"
#guard !Frontend.specHasFilteredMembership "\\in uint(2; 1, 2)"
#guard Frontend.resolveSpecConstants [("N", 99)] [] "2 \\in uint(N; 1, 2; N == 2)" ==
  "2 \\in uint(N; 1, 2; N == 2)"
#guard Frontend.resolveSpecConstants [("N", 99)] [] "\\in uint(2; N)" ==
  "\\in uint(2; uint(99))"

run_cmd Lean.Elab.Command.liftTermElabM do
  for original in [spec!(2 \in uint(x; 1, 2, 2; x > 1)),
      spec!(-1 \in int(x; -2, -1; x < 0)), spec!(true \in bool(x; ; x)),
      spec!(msg.sender \in address(x; 7; x == 7)),
      spec!(\forall uint x; x < 2 -> x \in uint(x; 0, 1; x < 2)),
      spec!((1 + 1) \in uint(x; 2; x \in uint(x; 2; x == 2)))] do
    let parsed ← match Lean.Parser.runParserCategory (← Lean.getEnv) `spec_expr (Tools.SpecExpr.fmt original) with
      | .ok stx => pure stx
      | .error message => Lean.throwError m!"filtered membership printer did not parse: {message}"
    let expanded ← Lean.Elab.liftMacroM (expandSpec ⟨parsed⟩)
    let expression ← Lean.Elab.Term.elabTerm expanded (some (Lean.mkConst ``SpecExpr))
    let decoded ← Lean.Meta.evalExpr SpecExpr (Lean.mkConst ``SpecExpr) expression
    unless reprStr decoded == reprStr original do
      Lean.throwError "filtered membership printer changed its syntax tree"
  -- Free key, domain, guard and sibling reads cannot inherit a guard binder.
  for (text, expected) in [
      ("2 \\in uint(N; 1, 2; N == 2)", false),
      ("N \\in uint(N; 1, 2; true)", true),
      ("2 \\in uint(N; N; true)", true),
      ("2 \\in uint(x; 1, 2; x == N)", true),
      ("(2 \\in uint(N; 1, 2; N == 2)) && N == 99", true),
      ("2 \\in uint(x; 1, 2; N.field == x)", true),
      ("2 \\in uint(x; 1, 2; pair.N == x)", false),
      ("2 \\in uint(N; 1, 2; \\old(N) == N)", false),
      ("\\forall uint N; N == N", false)] do
    let parsed ← match Lean.Parser.runParserCategory (← Lean.getEnv) `spec_expr text with
      | .ok stx => pure stx
      | .error message => Lean.throwError m!"free-name query did not parse: {message}"
    unless Frontend.specReadsFreeName "N" [] parsed == expected do
      Lean.throwError m!"free-name query lost binder scope: {text}"

end Solidity.Examples.Tactics.FilteredSets
