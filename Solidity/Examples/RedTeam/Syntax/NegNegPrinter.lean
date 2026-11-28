import Solidity.Tools.Run

/-!
# The program printer writes `-(-y)` as the decrement `--y`

Claim: the scoped program printer does not round-trip a double negation.
`sol{ z = -(-y); }` prints as `z = --y;`. As Solidity, `--y` is a
pre-decrement: the printed statement writes `y` and stores `y - 1` in `z`,
where the program assigns `y` to `z` and leaves `y` alone. (Inside a
`sol{ … }` block the printed text is worse still: `--` opens a Lean line
comment, which is why this grammar spells the decrement `−−`, U+2212.)

Witness, from the fresh state with `y := 3`: the elaborated program runs to
`y = 3, z = 3`; the printed program, read as Solidity (spelled here with the
grammar's `−−`), runs to `y = 2, z = 2`.

Culprit: `Solidity/Syntax/Scoped.lean:590` (`Val.toStr`, the `unop` arm)
prints a negation's operand without parentheses and joins it with
`UnOp.show` (`Solidity/AST.lean:1029`), which concatenates `-` with the
operand's text. The same pattern is in `RawExpr.toStr`
(`Solidity/Syntax/Elab/Context.lean:324`) and `SpecExpr.fmt`
(`Solidity/Tools/Show.lean:145`, where `spec!(- -x)` prints `--x`).

Suggested fix: in `UnOp.show`, parenthesise (or separate with a space) an
operand whose text starts with `-` when the operator is `-`.
-/
namespace Solidity.Examples.RedTeam.Syntax.NegNegPrinter

def N : Contract := contract!{
  int y;
  int z;
  function negNeg() { z = -(-y); }
  function printed() { z = −−y; }
}

/-- The printer: `z = -(-y);` comes back as `z = --y;`. -/
example : Prog.toStr [] (sol[N]{ z = -(-y); } : Prog N [] _) = "z = --y;" := rfl

-- The clause printer has the same defect: `- -x` comes back as `--x`.
#guard Tools.SpecExpr.fmt (spec!(- -x)) == "--x"

-- The program as written: `z` gets `y`, `y` is unchanged.
/--
info: ok
y = 3
z = 3
-/
#guard_msgs in #run N.negNeg() with y := 3

-- The printed program, read as Solidity: `y` is decremented first.
/--
info: ok
y = 2
z = 2
-/
#guard_msgs in #run N.printed() with y := 3

end Solidity.Examples.RedTeam.Syntax.NegNegPrinter
