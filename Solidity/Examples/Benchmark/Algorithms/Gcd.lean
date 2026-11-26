import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Euclid's algorithm

Source: Cormen et al., *Introduction to Algorithms*, 3rd edition (2009),
section 31.2, EUCLID. Adaptation: iterative remainder form over uint256.
The natural specification preserves exactly the positive common divisors;
together with gcd(0,0)=0 this characterizes gcd, without a false positivity
requirement on the all-zero input.
-/
namespace Solidity.Examples.Benchmark.Algorithms.Gcd

def Gcd : Contract := contract!{
  ensures \result == 0 <-> a == 0 && b == 0;
  ensures \forall uint d; d > 0 -> ((a % d == 0 && b % d == 0) <-> \result % d == 0);
  function gcd(uint a, uint b) public pure returns (uint) {
    uint x = a; uint y = b;
    /// @custom:key invariant (x == 0 && y == 0) == (a == 0 && b == 0)
    /// @custom:key invariant \forall uint d; d > 0 && a % d == 0 && b % d == 0 -> x % d == 0 && y % d == 0
    /// @custom:key invariant \forall uint d; d > 0 && x % d == 0 && y % d == 0 -> a % d == 0 && b % d == 0
    /// @custom:key decreases y
    while (y != 0) {
      uint r = x % y; x = y; y = r;
    }
    return x;
  }
}
local instance : InContract := ⟨Gcd⟩
open scoped Scoped
/-- Unknown: preservation needs the common-divisor equivalence for
(x,y) -> (y,x % y), under d > 0 and y > 0. Needed: modulo/common-divisor
congruence closure; both sol_prove and the standard leaf fallback fail. -/
def correctnessTarget := spec!{ gcd }

end Solidity.Examples.Benchmark.Algorithms.Gcd
