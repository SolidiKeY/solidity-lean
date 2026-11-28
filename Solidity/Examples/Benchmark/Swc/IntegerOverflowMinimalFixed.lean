import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# SWC-101: `IntegerOverflowMinimal` (fixed)

Source: SWC registry, `integer_overflow_minimal_fixed.sol`, pinned revision:
<https://github.com/SmartContractSecurity/SWC-registry/blob/1b6227074ecd180b374e4844153afdda0332f979/entries/docs/SWC-101.md#integer_overflow_minimal_fixedsol>.

Changes: the initializer `count = 1` is dropped, as in the vulnerable
module (`Swc/IntegerOverflowMinimal.lean`), which carries the same clause.
SafeMath's `sub` is kept as an internal function, declared before
`run` (`contract!` resolves a call against earlier functions); inside it `a - b` is the
checked subtraction of 0.8 (the guard `b <= a` already excludes wrapping).

```solidity
contract IntegerOverflowMinimal {
    uint public count = 1;
    function run(uint256 input) public {
        count = sub(count,input);
    }
    //from SafeMath
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b <= a);//SafeMath uses assert here
        return a - b;
    }
}
```

Verdict: `run` proved.
-/

namespace Solidity.Examples.Benchmark.Swc.IntegerOverflowMinimalFixed

/-- `integer_overflow_minimal_fixed.sol`, with the vulnerable clause. -/
def IntegerOverflowMinimal : Contract := contract!{
  uint public count;
  function sub(uint256 a, uint256 b) internal pure returns (uint256) {
    require(b <= a);
    return a - b;
  }
  ensures count == \old(count) - input;
  function run(uint256 input) public {
    count = sub(count, input);
  }
}

local instance : InContract := ⟨IntegerOverflowMinimal⟩
open scoped Scoped

/-- `run`: `ensures count == \old(count) - input`. -/
theorem spec_run : ⊢ spec!{ run } := by
  sol_prove

end Solidity.Examples.Benchmark.Swc.IntegerOverflowMinimalFixed
