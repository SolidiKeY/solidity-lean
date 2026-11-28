import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: `ArrayRemoveByShifting`, open variant (solkey real-world)

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/contracts/real-world/open/ArrayRemoveByShifting.sol>
(after Solidity by Example's `array/ArrayRemoveByShifting.sol`, revision `5bcdca02`).

Changes: none but the spelling of `contract!{ … }`; `test()` is in
`ArrayRemoveByShifting.lean`, as solkey has it in the other file.

Verdict: unknown, not refuted.  The specification is true of the program
(the shift moves `arr[j + 1]` to `arr[j]` for `_index <= j < len - 1` and
the `pop` drops the last slot, after `require(_index < arr.length)`).  It is
unprovable with the published invariant, for the reason solkey's file gives:
`i + 1 <= arr.length` states neither the unchanged length nor the shifted
prefix, the invariant grammar (`RawInv`, current state only) has no `\old`,
and the invariant rule anonymises `arr` (`{ storage := anon(storage, arr, …) }`),
so the `ensures` clauses are lost past the loop.  Missing: entry-state reads
in loop invariants (as `Examples/Benchmark/Algorithms/Reverse.lean` notes);
a stronger invariant would change the source.

-/

namespace Solidity.Examples.Benchmark.SolkeyData.ArrayRemoveByShiftingOpen

/-- `open/ArrayRemoveByShifting.sol`, as solkey publishes it, with its clauses. -/
def ArrayRemoveByShifting : Contract := contract!{
  uint256[] public arr;
  requires _index >= 0;
  ensures arr.length == \old(arr.length) - 1;
  ensures \forall uint j; 0 <= j && j < _index -> arr[j] == \old(arr[j]);
  ensures \forall uint j; _index <= j && j < arr.length -> arr[j] == \old(arr[j + 1]);
  function remove(uint256 _index) public {
    require(_index < arr.length);
    /// @custom:key invariant i + 1 <= arr.length
    for (uint256 i = _index; i < arr.length - 1; i++) {
      arr[i] = arr[i + 1];
    }
    arr.pop();
  }
}

local instance : InContract := ⟨ArrayRemoveByShifting⟩

open scoped Scoped

/-- Unknown (see the module docstring): `remove(_index)`'s full functional
obligation. -/
def removeTarget := spec!{ remove }

end Solidity.Examples.Benchmark.SolkeyData.ArrayRemoveByShiftingOpen
