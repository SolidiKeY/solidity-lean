import Solidity.Tools.Run

/-!
# Literal arithmetic beyond `+ - * /` is evaluated at run time, not exactly

Claim: `contract!{ … }` elaborates a literal-only expression containing `%`,
`**` or `<<` to run-time `uint256` arithmetic, where solc evaluates every
literal expression exactly, as a rational constant, before converting it to the
target type (Solidity documentation, "Rational and Integer Literals": literal
expressions keep arbitrary precision, `(2**800 + 1) - 2**800` is `1` and
`.5 * 8` is `4`). On the stated inputs (no arguments, a fresh state):

| expression | solc (exact constant) | this model (`#run` below) |
|---|---|---|
| `7 % 2 / 2 * 2` | `1` | `0` |
| `2 ** 2 / 8 * 2` | `1` | `0` |
| `(1 << 2) / 8 * 2` | `1` | `0` |
| `2 ** 256 - 1` | `2^256 - 1` | revert (checked overflow) |

The solc column follows the documented literal semantics; no solc binary was
available to run in the lane that wrote this module.

Culprit: `Solidity/Syntax/Elab/Context.lean:842` (`RawExpr.constRat?`) folds
only numerals, unary `-`, `+`, binary `-`, `*` and `/`; any `%`, `**`, shift or bitwise
operator makes the whole expression non-constant, so `foldConst` leaves it and
the operands are typed at the target word type. `BinOp.foldLit?`
(`Solidity/Syntax/Elab/Values.lean:41`) has the same operator set.

Suggested fix: fold `%`, `**` (integral exponent, with solc's size limit),
shifts and bitwise operators on integral constants in `constRat?`; or reject a
literal-only expression containing an unfolded operator instead of evaluating
it at run time.
-/
namespace Solidity.Examples.RedTeam.Syntax.LiteralFolding

/-- The culprit: a literal `%` is not a constant to the folder. -/
example : (RawExpr.binop .mod (.num 7) (.num 2)).constRat? = none := rfl

/-- The culprit: neither is a literal `**`. -/
example : (RawExpr.binop .pow (.num 2) (.num 2)).constRat? = none := rfl

def Lits : Contract := contract!{
  uint n;
  function modDiv() returns (uint) { return 7 % 2 / 2 * 2; }
  function powDiv() returns (uint) { return 2 ** 2 / 8 * 2; }
  function shlDiv() returns (uint) { return (1 << 2) / 8 * 2; }
  function powMax() returns (uint) { return 2 ** 256 - 1; }
}

-- solc: `1`.
/--
info: ok
returns 0
n = 0
-/
#guard_msgs in #run Lits.modDiv()

-- solc: `1`.
/--
info: ok
returns 0
n = 0
-/
#guard_msgs in #run Lits.powDiv()

-- solc: `1`.
/--
info: ok
returns 0
n = 0
-/
#guard_msgs in #run Lits.shlDiv()

-- solc: `115792089237316195423570985008687907853269984665640564039457584007913129639935`.
/-- info: revert -/
#guard_msgs in #run Lits.powMax()

end Solidity.Examples.RedTeam.Syntax.LiteralFolding
