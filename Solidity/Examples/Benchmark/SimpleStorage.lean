import Solidity.Calculus.Spec

/-!
# Benchmark: `SimpleStorage`

Source: <https://raw.githubusercontent.com/ethereum/solidity/v0.8.30/docs/introduction-to-smart-contracts.rst>
(solkey's `keyext.solidity.examples/benchmark/SimpleStorage.sol`).

Changes: none but the spelling of `contract!{ … }` and solkey's clauses,
written above the functions: `requires x >= 0` (true of every `uint`) and
`ensures storedData == x` of `set`, `ensures \result == storedData` of
`get`.  They are proved as `spec!{f}`, the obligation solkey synthesizes
(`spec_set`, `spec_get`), and `set`'s by hand before it.

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

/-- `SimpleStorage.sol`, as published, with solkey's clauses. -/
def SimpleStorage : Contract := contract!{
  uint storedData;
  requires x >= 0;
  ensures storedData == x;
  function set(uint x) public {
    storedData = x;
  }
  ensures \result == storedData;
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

/-- `set(x)`'s obligation: `ensures storedData == x`. -/
theorem spec_set : ⊨ spec!{ set } := by sol_spec
/-- `get()`'s obligation: `ensures \result == storedData`. -/
theorem spec_get : ⊨ spec!{ get } := by sol_spec

end Solidity.Examples.Benchmark.SimpleStorage
