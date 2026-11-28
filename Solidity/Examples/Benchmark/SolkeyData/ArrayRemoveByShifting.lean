import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface

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

/-- Unknown: `remove(_index)`'s obligation, `ensures _index < \old(arr.length)`.  Past the
require and `whileInvariantBox`, `sol_close` closes none of the three leaves: `init`
(`se1 < arr.length` ⟹ `se2 + 1 <= arr.length`, `se2 := se1`), where `sol_spec`'s `grind`
holds the negated goal as `∀ a : uint, len = a.val → a.val ≤ _index` and does not
instantiate it (nor do `sol_decide`, `sol_close_facts`, `sol_close_reads`); `thn` (the
length past `save(storage, arr[i], …)` under the anonymised `arr`) and `els`
(`_index < find(old, arr.length)`, `old` outside the anonymising update) exhaust the
heartbeats.  Missing (`Calculus/Close.lean`): instantiating a quantified `uint` read at
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
