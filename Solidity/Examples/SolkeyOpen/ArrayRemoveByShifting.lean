import Solidity.Calculus.Closers
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface

/-!
# solkey open problems: `ArrayRemoveByShifting`

Source: <https://github.com/SolidiKeY/solkey/blob/8f0bb7a56bdc7292240250d93bafe93727ef266b/keyext.solidity.examples/contracts/real-world/open/ArrayRemoveByShifting.sol>.
Changes: comments dropped; solkey's `@custom:key` clauses are `requires`/`ensures` members and
the loop invariant stays where it is.  The obligation is `spec!{remove}`.
solkey: the invariant can state neither the shifted prefix nor the unchanged length, and the loop
rule anonymises storage, so the `ensures` are lost across the loop.
-/

namespace Solidity.Examples.SolkeyOpen.ArrayRemoveByShifting

def ArrayRemoveByShifting : Contract := contract!{
  uint256[] public arr;
  requires _index >= 0;
  ensures arr.length == \old(arr.length) - 1;
  ensures \forall uint j; 0 <= j && j < _index -> arr[j] == \old(arr[j]);
  ensures \forall uint j; _index <= j && j < arr.length -> arr[j] == \old(arr[j + 1]);
  function remove(uint256 _index) public {
    require(_index < arr.length);
    /// @custom:key invariant i + 1 <= arr.length
    for (uint256 i = _index; i < arr.length - 1; i++) { arr[i] = arr[i + 1]; }
    arr.pop();
  }
}

local instance : InContract := ⟨ArrayRemoveByShifting⟩
open scoped Scoped

/-- Unknown: `sol_prove` leaves three leaves, `sol_leaf; sol_close` stops on them (`sol_close_nonlin`)
and `sol_refute` finds no witness.  Two are the invariant, initially
(`se1 < arr.length ⟹ se1 + 1 <= arr.length`) and preserved: a missing closer.  The third is the use
case, solkey's gap: after `anon(se2)`, `storage := anon(storage, arr, anonStorage)` the leaf knows
only `se2 + 1 <= arr.length`, and owes the three `ensures` over `old`. -/
def remove_obligation : Fml ArrayRemoveByShifting [] := spec!{ remove }

end Solidity.Examples.SolkeyOpen.ArrayRemoveByShifting
