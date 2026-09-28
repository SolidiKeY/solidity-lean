import Solidity.Calculus.Close

/-!
# Benchmark: `SimpleStorage`

Source: <https://raw.githubusercontent.com/ethereum/solidity/v0.8.30/docs/introduction-to-smart-contracts.rst>
(solkey's `keyext.solidity.examples/benchmark/SimpleStorage.sol`).

Changes: none but the spelling of `contract!{ … }`.  solkey's clauses
`requires x >= 0` (true of every `uint`) and `ensures storedData == x` are
the theorem below.

```solidity
contract SimpleStorage {
    uint storedData;

    function set(uint x) public {
        storedData = x;
    }

    function get() public view returns (uint) {
        return storedData;
    }
}
```
-/

namespace Solidity.Examples.Benchmark.SimpleStorage

open Proves

/-- `SimpleStorage.sol`, as published. -/
def SimpleStorage : Contract := contract!{
  uint storedData;
  function set(uint x) public {
    storedData = x;
  }
  function get() public view returns (uint) {
    return storedData;
  }
}

local instance : InContract := ⟨SimpleStorage⟩

/-- `set(x)`: `ensures storedData == x`.  It runs to the end (no revert), so
the diamond holds too. -/
theorem set_spec : ⊨ dl!{ [ set(x); ] storedData == x } := by
  sol_symex
  sol_close

/-- `set(x)` then `get()` returns `x`. -/
theorem set_get : ⊨ dl!{ [ set(x); uint y = get(); ] y == x } := by
  sol_symex
  sol_close

end Solidity.Examples.Benchmark.SimpleStorage
