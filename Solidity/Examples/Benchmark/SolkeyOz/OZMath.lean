import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Benchmark: `OZMath`
Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/contracts/real-world/OZMath.sol>
(solkey's port of OpenZeppelin v5.0.0 `utils/math/Math.sol`, the library a
contract, without `mulDiv`, `sqrt`, `log*` and the rounding variants).
Changes: only the spelling of `contract!{ … }` (a branch is a block ending
in `;`) and solkey's `@custom:key` clauses written above the functions they
annotate.
Verdicts: `tryAdd`, `max`, `min`: proved.  `trySub`, `tryMul`, `tryDiv`,
`tryMod`, `average`, `ceilDiv`: unknown (every clause true; each `def` below
names the leaf `sol_auto` leaves and the closer law it lacks).
-/
namespace Solidity.Examples.Benchmark.SolkeyOz.OZMath
/-- `OZMath.sol` with solkey's clauses. -/
def OZMath : Contract := contract!{
  requires a >= 0 && b >= 0;
  ensures success -> r == a + b;
  ensures !success -> r == 0;
  function tryAdd(uint256 a, uint256 b) public pure returns (bool success, uint256 r) {
    unchecked { uint256 c = a + b; if (c < a) { return (false, 0); }; return (true, c); }
  }
  requires a >= 0 && b >= 0;
  ensures success <-> b <= a;
  ensures success -> r == a - b;
  ensures !success -> r == 0;
  function trySub(uint256 a, uint256 b) public pure returns (bool success, uint256 r) {
    unchecked {
      if (b > a) { return (false, 0); };
      return (true, a - b);
    }
  }
  requires a >= 0 && b >= 0;
  ensures success -> r == a * b;
  ensures !success -> r == 0;
  function tryMul(uint256 a, uint256 b) public pure returns (bool success, uint256 r) {
    unchecked {
      if (a == 0) { return (true, 0); };
      uint256 c = a * b;
      if (c / a != b) { return (false, 0); };
      return (true, c);
    }
  }
  ensures (r == a || r == b) && r >= a && r >= b;
  function max(uint256 a, uint256 b) public pure returns (uint256 r) { return a > b ? a : b; }
  ensures (r == a || r == b) && r <= a && r <= b;
  function min(uint256 a, uint256 b) public pure returns (uint256 r) { return a < b ? a : b; }
  requires a >= 0 && b >= 0;
  ensures success <-> b != 0;
  ensures success -> r == a / b;
  ensures !success -> r == 0;
  function tryDiv(uint256 a, uint256 b) public pure returns (bool success, uint256 r) {
    unchecked {
      if (b == 0) { return (false, 0); };
      return (true, a / b);
    }
  }
  requires a >= 0 && b >= 0;
  ensures success <-> b != 0;
  ensures success -> r == a % b;
  ensures !success -> r == 0;
  function tryMod(uint256 a, uint256 b) public pure returns (bool success, uint256 r) {
    unchecked {
      if (b == 0) { return (false, 0); };
      return (true, a % b);
    }
  }
  requires a >= 0 && b >= 0;
  ensures r == (a + b) / 2;
  function average(uint256 a, uint256 b) public pure returns (uint256 r) { return (a & b) + (a ^ b) / 2; }
  requires a >= 0 && b > 0;
  ensures a == 0 -> r == 0;
  ensures a > 0 -> r * b >= a && (r - 1) * b < a;
  function ceilDiv(uint256 a, uint256 b) public pure returns (uint256 r) {
    if (b == 0) { return a / b; };
    return a == 0 ? 0 : (a - 1) / b + 1;
  }
}
local instance : InContract := ⟨OZMath⟩
open scoped Scoped
/-- `requires a >= 0 && b >= 0`, `ensures success -> r == a + b`,
`ensures !success -> r == 0`. -/
theorem spec_tryAdd : ⊢ spec!{ tryAdd } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_spec_close
/-- UNKNOWN: `ensures success <-> b <= a`, `success -> r == a - b`,
`!success -> r == 0`.  The early `return (false, 0)` in `unchecked` merges
into conditional updates (`{ se3 := (se6 ? false : se3) }`, …,
`se1 -% se2`); no leaf tactic splits them and closes the `<->`. -/
def trySub_obligation := spec!{ trySub }
/-- UNKNOWN: `ensures success -> r == a * b`, `!success -> r == 0`.  The leaf
needs `c == a *% b ∧ c / a == b ⟹ c == a * b` (no law relates a wrapping
product, its quotient and the exact product), under merged conditional
updates, as in `trySub`. -/
def tryMul_obligation := spec!{ tryMul }
/-- `ensures (r == a || r == b) && r >= a && r >= b`. -/
theorem spec_max : ⊢ spec!{ max } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close
/-- `ensures (r == a || r == b) && r <= a && r <= b`. -/
theorem spec_min : ⊢ spec!{ min } := by
  sol_prove (steps := 128)
  sol_leaf
  sol_close
/-- UNKNOWN: `ensures success <-> b != 0`, `success -> r == a / b`,
`!success -> r == 0`; merged conditional updates, as in `trySub`. -/
def tryDiv_obligation := spec!{ tryDiv }
/-- UNKNOWN: `ensures success <-> b != 0`, `success -> r == a % b`,
`!success -> r == 0`; merged conditional updates, as in `trySub`. -/
def tryMod_obligation := spec!{ tryMod }
/-- UNKNOWN: `ensures r == (a + b) / 2`.  The leaf needs
`(a & b) + (a ^ b) / 2 == (a + b) / 2` (no closer law for `&`, `^`; the
`&` even prints as a `‹…›` escape). -/
def average_obligation := spec!{ average }
/-- UNKNOWN: `ensures a == 0 -> r == 0`,
`a > 0 -> r * b >= a && (r - 1) * b < a`.  The leaf needs the nonlinear
`b > 0 ⟹ ((a - 1) / b + 1) * b >= a ∧ ((a - 1) / b) * b < a` (no closer law
bounds a quotient times its divisor). -/
def ceilDiv_obligation := spec!{ ceilDiv }
end Solidity.Examples.Benchmark.SolkeyOz.OZMath
