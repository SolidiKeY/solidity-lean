import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `ArrayReplaceFromEnd` (solkey real-world)

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/contracts/real-world/ArrayReplaceFromEnd.sol>
(after Solidity by Example's `array/ArrayReplaceFromEnd.sol`, revision `5bcdca02`).

Changes: none but the spelling of `contract!{ … }` (solkey already drops
the comments and replaces `arr = [1, 2, 3, 4]` by `delete arr` and four
pushes).  `test()` calls `remove`, which inlines.  Verdicts: `remove`
unknown (its length clause proved by hand); `test` proved, and it returns
from every state (its `assert`s hold).

```solidity
contract ArrayReplaceFromEnd {
    uint256[] public arr;

    /// @custom:key ensures arr.length == \old(arr.length) - 1
    /// @custom:key ensures index < arr.length -> arr[index] == \old(arr[arr.length - 1])
    /// @custom:key ensures \forall uint i; 0 <= i && i < arr.length && i != index -> arr[i] == \old(arr[i])
    function remove(uint256 index) public {
        arr[index] = arr[arr.length - 1];
        arr.pop();
    }

    function test() public {
        delete arr;
        arr.push(1); arr.push(2); arr.push(3); arr.push(4);
        remove(1);
        assert(arr.length == 3); assert(arr[0] == 1); assert(arr[1] == 4); assert(arr[2] == 3);
        remove(2);
        assert(arr.length == 2); assert(arr[0] == 1); assert(arr[1] == 4);
    }
}
```
-/

namespace Solidity.Examples.Benchmark.SolkeyData.ArrayReplaceFromEnd

/-- `ArrayReplaceFromEnd.sol`, as solkey publishes it, with its clauses. -/
def ArrayReplaceFromEnd : Contract := contract!{
  uint256[] public arr;
  ensures arr.length == \old(arr.length) - 1;
  ensures index < arr.length -> arr[index] == \old(arr[arr.length - 1]);
  ensures \forall uint i; 0 <= i && i < arr.length && i != index -> arr[i] == \old(arr[i]);
  function remove(uint256 index) public {
    arr[index] = arr[arr.length - 1];
    arr.pop();
  }
  function test() public {
    delete arr;
    arr.push(1);
    arr.push(2);
    arr.push(3);
    arr.push(4);
    remove(1);
    assert(arr.length == 3);
    assert(arr[0] == 1);
    assert(arr[1] == 4);
    assert(arr[2] == 3);
    remove(2);
    assert(arr.length == 2);
    assert(arr[0] == 1);
    assert(arr[1] == 4);
  }
}

local instance : InContract := ⟨ArrayReplaceFromEnd⟩

open scoped Scoped

/-- `remove(index)`: `ensures arr.length == \old(arr.length) - 1`. -/
theorem remove_length : ⊢ dl!{ n == arr.length → [ remove(k); ] arr.length == n - 1 } := by
  sol_prove
/-- Unknown: `remove(index)`'s obligation (the length clause alone is
`remove_length`).  After `sol_derive` one leaf is left: the reads
`find(storage, arr[index])` and `find(storage, arr[i])` past
`save(delAt(save(storage, arr[index], find(old, arr[len - 1])), arr[len - 1]), arr.length, len - 1)`;
`sol_spec`, `sol_decide`, `sol_close_quantified` and `sol_close` leave it
open, and so does `sol_prove` on each clause alone with its index fixed
(`k + 1 < arr.length && v == arr[arr.length - 1] → [ remove(k); ] arr[k] == v`).
Missing: a closer that reads an array slot through `delAt` at a symbolic
index distinct from the read index (`findOnDelAtBelow` with `i < len - 1`
taken from the guard) and then through the `save` at `arr[index]`. -/
def removeTarget := spec!{ remove }
/-- `test()` has no clause: its obligation is the box `true`. -/
theorem spec_test : ⊢ spec!{ test } := by
  sol_prove
/-- `test()` returns from every state: its `assert`s hold (the diamond; a box
would hold of a reverting run too). -/
theorem test_returns : ⊢ dl!{ ⟨ test(); ⟩ true } := by
  sol_prove

end Solidity.Examples.Benchmark.SolkeyData.ArrayReplaceFromEnd
