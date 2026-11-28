import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `ArrayRemoveByShifting` (solkey real-world)

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/contracts/real-world/ArrayRemoveByShifting.sol>
(after Solidity by Example's `array/ArrayRemoveByShifting.sol`, revision `5bcdca02`).

Changes: none but the spelling of `contract!{ … }` (solkey already drops
the comments and the `require` message, adds the loop invariant, and
replaces the array literals by `delete arr` and pushes).  solkey's own
clauses here state only the bounds check; the functional specification is
the open variant, `ArrayRemoveByShiftingOpen.lean`.  Verdicts: `remove` and
`test` unknown (the loop leaves; see their targets).

```solidity
contract ArrayRemoveByShifting {
    uint256[] public arr;

    /// @custom:key requires _index >= 0
    /// @custom:key ensures _index < \old(arr.length)
    function remove(uint256 _index) public {
        require(_index < arr.length);

        /// @custom:key invariant i + 1 <= arr.length
        for (uint256 i = _index; i < arr.length - 1; i++) {
            arr[i] = arr[i + 1];
        }
        arr.pop();
    }

    function test() external {
        delete arr;
        arr.push(1); arr.push(2); arr.push(3); arr.push(4); arr.push(5);
        remove(2);
        assert(arr[0] == 1); assert(arr[1] == 2); assert(arr[2] == 4); assert(arr[3] == 5);
        assert(arr.length == 4);

        delete arr;
        arr.push(1);
        remove(0);
        assert(arr.length == 0);
    }
}
```
-/

namespace Solidity.Examples.Benchmark.SolkeyData.ArrayRemoveByShifting

/-- `ArrayRemoveByShifting.sol`, as solkey publishes it, with its clauses. -/
def ArrayRemoveByShifting : Contract := contract!{
  uint256[] public arr;
  requires _index >= 0;
  ensures _index < \old(arr.length);
  function remove(uint256 _index) public {
    require(_index < arr.length);
    /// @custom:key invariant i + 1 <= arr.length
    for (uint256 i = _index; i < arr.length - 1; i++) {
      arr[i] = arr[i + 1];
    }
    arr.pop();
  }
  function test() external {
    delete arr;
    arr.push(1);
    arr.push(2);
    arr.push(3);
    arr.push(4);
    arr.push(5);
    remove(2);
    assert(arr[0] == 1);
    assert(arr[1] == 2);
    assert(arr[2] == 4);
    assert(arr[3] == 5);
    assert(arr.length == 4);
    delete arr;
    arr.push(1);
    remove(0);
    assert(arr.length == 0);
  }
}

local instance : InContract := ⟨ArrayRemoveByShifting⟩

open scoped Scoped

/-- Unknown: `remove(_index)`'s obligation, `ensures _index < \old(arr.length)`.
`sol_derive` takes the require and the invariant rule (`whileInvariantBox`)
and leaves three leaves, none of which `sol_close` closes:
* `init`, `{ se4 := arr.length } { se3 := se1 < se4 }, se3 = true, { se2 := se1 } ⟹ se2 + 1 <= arr.length`:
  `sol_spec`'s `grind` holds `_index + 1 ≤ len` and the negated goal as
  `∀ a : uint, len = a.val → a.val ≤ _index`, which it does not instantiate
  (`sol_decide`, `sol_close_facts`, `sol_close_reads` leave it too);
* `thn` (preserved: the length past `save(storage, arr[i], …)` under the
  anonymised `arr`) and `els` (used: `_index < find(old, arr.length)`, with
  `old` outside the anonymising update) exhaust the heartbeats in `sol_close`.
Missing: in `Calculus/Close.lean`, instantiating a quantified `uint` read at
the length it equals, and a bounded closer for the two loop leaves. -/
def removeTarget := spec!{ remove }
/-- Unknown: `test()`'s `assert`s are obligations (they are not the box's
reverting run).  Past each loop the invariant rule anonymises `arr`, and
`i + 1 <= arr.length` keeps neither its length nor its elements, so the
leaves `find(storage, arr[0]) == 1`, …, `arr.length == 0` are not
consequences of the invariant.  Missing: unwinding the two concrete loops
(solkey's file has no `unwind` clause, which would change the source). -/
def testTarget := spec!{ test }

end Solidity.Examples.Benchmark.SolkeyData.ArrayRemoveByShifting
