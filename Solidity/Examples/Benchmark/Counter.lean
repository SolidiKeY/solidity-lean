import Solidity.Calculus.Close

/-!
# Benchmark: `Counter`

Source: <https://raw.githubusercontent.com/Cyfrin/solidity-by-example.github.io/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/first-app/Counter.sol>
(solkey's `keyext.solidity.examples/benchmark/Counter.sol`).

Changes: none but the spelling of `contract!{ … }` (the comments are Lean's).
The functions are internal functions here, and a call inlines one
(`Examples/Calls.lean`); solkey's `@custom:key` clauses are the theorems
below, a clause `ensures count == \old(count) + 1` stated with a parameter
`c` for the old value.  `requires count >= 1` has no counterpart: the
formula language has `==` and `!=` only, and the box needs none (a `dec()`
that underflows reverts, and a reverted run satisfies every box formula).

```solidity
contract Counter {
    uint256 public count;

    // Function to get the current count
    function get() public view returns (uint256) {
        return count;
    }

    // Function to increment count by 1
    function inc() public {
        count += 1;
    }

    // Function to decrement count by 1
    function dec() public {
        // This function will fail if count = 0
        count -= 1;
    }
}
```
-/

namespace Solidity.Examples.Benchmark.Counter

open Proves

/-- `Counter.sol`, as published. -/
def Counter : Contract := contract!{
  uint256 public count;
  function get() public view returns (uint256) {
    return count;
  }
  function inc() public {
    count += 1;
  }
  function dec() public {
    count -= 1;
  }
}

local instance : InContract := ⟨Counter⟩

/-- `inc()`: `ensures count == \old(count) + 1`. -/
theorem inc_spec : ⊨ dl!{ c == count → [ inc(); ] count == c + 1 } := by
  sol_symex
  sol_close

/-- `dec()`: `ensures count == \old(count) - 1` (when it does not revert). -/
theorem dec_spec : ⊨ dl!{ c == count → [ dec(); ] count == c - 1 } := by
  sol_symex
  sol_close

/-- `get()` returns `count`. -/
theorem get_spec : ⊨ dl!{ [ uint y = get(); ] y == count } := by
  sol_symex
  sol_close

end Solidity.Examples.Benchmark.Counter
