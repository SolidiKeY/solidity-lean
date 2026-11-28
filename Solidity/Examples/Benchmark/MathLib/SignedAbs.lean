import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: signed absolute value and negation at `type(int256).min`

Sources: OpenZeppelin Contracts v4.9.6, `SignedMath.abs`,
<https://github.com/OpenZeppelin/openzeppelin-contracts/blob/dc44c9f1a4c3b10af99492eed84f83ed244203f6/contracts/utils/math/SignedMath.sol#L34-L42>; checked negation
as the Solidity 0.8.24 documentation states it (`-x` does not fit for
`x = type(int).min`: checked, it fails),
<https://github.com/ethereum/solidity/blob/e11b9ed9f2c254bc894d844c0a64a0eb76bbb4fd/docs/types/value-types.rst?plain=1#L100-L103>.

Changes: `public` instead of `internal` and the `@custom:key` clauses. `abs`
is the source's (unchecked, "in order to support `n = type(int256).min`");
`neg` is the one-expression function the documentation describes.

Natural specifications: `abs(n)` is `|n|` as an unsigned number, `2^255` at
`type(int256).min`; `neg(n)` is `-n`, and reverts at `type(int256).min`
(the box formula admits the revert; the run below shows it).
-/
namespace Solidity.Examples.Benchmark.MathLib.SignedAbs

def SignedAbs : Contract := contract!{
  function abs(int256 n) public pure returns (uint256) {
    unchecked {
      return uint256(n >= 0 ? n : -n);
    }
  }
  ensures \result == -n;
  function neg(int256 n) public pure returns (int256) {
    return -n;
  }
}
local instance : InContract := ⟨SignedAbs⟩
open scoped Scoped

/-- `neg`: the negation, wherever it returns. -/
theorem spec_neg : ⊢ spec!{ neg } := by sol_prove <;> (sol_leaf; sol_close)

/-- `abs`'s natural specification over the integers. Unknown as a clause:
`ensures n >= 0 -> \result == n` is refused ("`n` is a `int`, used as a
`uint`"), and the clause language has `uint(…)` of a literal only.
Missing: a widening `int`/`uint` comparison (KeY's `int`) in `SpecExpr`. -/
def AbsNaturalSpec (n result : Int) : Prop := result = if 0 ≤ n then n else -n

/-- The edge case: `abs(type(int256).min)` is `2^255`, no revert. -/
example : ((Prog.run (State.ofStorage (C := SignedAbs) .nil)
      (sol{ uint r = abs(type(int256).min); })).toOption.map fun o => o.st.env.1.1) =
    some (2 ^ 255) := by
  decide +kernel

/-- The edge case: checked `-type(int256).min` halts (solc's `Panic(0x11)`;
the run halts with `.revert`). -/
example : ((Prog.run (State.ofStorage (C := SignedAbs) .nil)
      (sol{ int r = neg(type(int256).min); })).halt?) = some .revert := by
  decide +kernel

end Solidity.Examples.Benchmark.MathLib.SignedAbs
