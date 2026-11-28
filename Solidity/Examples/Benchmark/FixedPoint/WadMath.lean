import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Fixed point: WAD mul/div rounded down and up

Source: Morpho Blue v1.0.0 `src/libraries/MathLib.sol`:
<https://github.com/morpho-org/morpho-blue/blob/v1.0.0/src/libraries/MathLib.sol>.

The library's `internal` functions are public pure functions here; the file
constant `WAD = 1e18` is inlined as a literal (a `constant` would be a
storage root set by the constructor). Bodies are as published, `mulDivDown` and `mulDivUp` moved first (a
call needs its callee declared before it), the calls
`wMulDown → mulDivDown` and `wDivDown/wDivUp → mulDivDown/mulDivUp` kept
and inlined by the calculus. `wTaylorCompounded` is not part of this
benchmark.

Natural specifications state the rounding direction: a rounded-down
quotient `q` of `n / d` has `q * d <= n < (q + 1) * d`; a rounded-up one
has `n <= q * d < n + d`. Checked overflow and division by zero revert;
the box clauses do not claim totality.

Status (every clause kept exactly):
* all five obligations unknown: `sol_prove` leaves the arithmetic leaf
  `q = (x * y) / d ⟹ q * d <= x * y ∧ …` and `sol_close` fails in `grind`
  (literal divisor) or stops its bounded nonlinear search (symbolic divisor):
  the closer lacks SolKey's `div_axiom`-style bounds for a quotient of a
  product, `0 <= n → 0 < d → (n / d) * d <= n < (n / d + 1) * d`, with
  `n` a nonlinear atom;
* proved: `wMulDown(x, 0) == 0` (`sol_prove`, its leaf `x * 0 / 1e18 = 0`
  by `sol_close`); `mulDivDown(0, y, d) == 0` is not closed either
  (symbolic divisor).
-/

namespace Solidity.Examples.Benchmark.FixedPoint.WadMath

/-- Morpho Blue `MathLib`, with rounding-direction clauses. -/
def WadMath : Contract := contract!{
  ensures \result * d <= x * y;
  ensures x * y < (\result + 1) * d;
  function mulDivDown(uint256 x, uint256 y, uint256 d) public pure returns (uint256) {
    return (x * y) / d;
  }
  ensures x * y <= \result * d;
  ensures \result * d < x * y + d;
  function mulDivUp(uint256 x, uint256 y, uint256 d) public pure returns (uint256) {
    return (x * y + (d - 1)) / d;
  }
  ensures \result * 1000000000000000000 <= x * y;
  ensures x * y < (\result + 1) * 1000000000000000000;
  function wMulDown(uint256 x, uint256 y) public pure returns (uint256) {
    return mulDivDown(x, y, 1000000000000000000);
  }
  ensures \result * y <= x * 1000000000000000000;
  ensures x * 1000000000000000000 < (\result + 1) * y;
  function wDivDown(uint256 x, uint256 y) public pure returns (uint256) {
    return mulDivDown(x, 1000000000000000000, y);
  }
  ensures x * 1000000000000000000 <= \result * y;
  ensures \result * y < x * 1000000000000000000 + y;
  function wDivUp(uint256 x, uint256 y) public pure returns (uint256) {
    return mulDivUp(x, 1000000000000000000, y);
  }
}
local instance : InContract := ⟨WadMath⟩
open scoped Scoped

/-- `wMulDown`: rounded down. Unknown (quotient-of-product bounds). -/
def wMulDown_obligation : Fml WadMath [] := spec!{ wMulDown }
/-- `wDivDown`: rounded down. Unknown (quotient-of-product bounds). -/
def wDivDown_obligation : Fml WadMath [] := spec!{ wDivDown }
/-- `wDivUp`: rounded up. Unknown (quotient-of-product bounds). -/
def wDivUp_obligation : Fml WadMath [] := spec!{ wDivUp }
/-- `mulDivDown`: rounded down. Unknown (quotient-of-product bounds). -/
def mulDivDown_obligation : Fml WadMath [] := spec!{ mulDivDown }
/-- `mulDivUp`: rounded up. Unknown (quotient-of-product bounds). -/
def mulDivUp_obligation : Fml WadMath [] := spec!{ mulDivUp }

/-- `wMulDown(x, 0)` is `0`. -/
theorem wMulDown_zero : ⊢ dl!{ [ uint z = wMulDown(x, 0); ] z == 0 } := by
  sol_prove
  all_goals (sol_leaf; sol_close)


end Solidity.Examples.Benchmark.FixedPoint.WadMath
