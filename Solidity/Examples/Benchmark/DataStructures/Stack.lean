import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: storage stack

Source: <https://raw.githubusercontent.com/Cyfrin/solidity-by-example.github.io/5bcdca0239409d7336a07b66a6fca8d0bcc710e6/contracts/src/array/Array.sol>
(its `push`/`pop` on `uint256[] public arr`).  Kept: `arr`, `push`, `pop`.
Omitted: `arr2`, `myFixedSizeArr`, `get`, `getArr`, `getLength`, `remove`,
`examples`.  Added: `top()`, the stack read `arr[arr.length - 1]` (an empty
stack reverts, as `get` does out of range).

Natural specification: `push` grows the length by one, stores the value on
top and keeps every lower slot; `pop` shrinks the length by one and keeps
every slot below; `top` returns the last slot.

Verdicts: `top` proved.  `push`, `pop`: unknown (length and top components
proved).  Each full obligation stops on the frame clause
`find(save(s, arr[arr.length], v), arr[j]) = find(s, arr[j])` for `j < arr.length`
(and the `delAt` analogue for `pop`): the closers have no distinctness law for
array element paths with symbolic indices (even `j != arr.length` as a
premise stays open), unlike mapping keys.
-/
namespace Solidity.Examples.Benchmark.DataStructures.Stack

def Stack : Contract := contract!{
  uint256[] public arr;
  ensures arr.length == \old(arr.length) + 1;
  ensures arr[\old(arr.length)] == i;
  ensures \forall uint256 j; j < \old(arr.length) -> arr[j] == \old(arr[j]);
  function push(uint256 i) public {
    arr.push(i);
  }
  ensures arr.length == \old(arr.length) - 1;
  ensures \forall uint256 j; j < arr.length -> arr[j] == \old(arr[j]);
  function pop() public {
    arr.pop();
  }
  ensures \result == arr[arr.length - 1];
  function top() public view returns (uint256) {
    return arr[arr.length - 1];
  }
}
local instance : InContract := ⟨Stack⟩
open scoped Scoped

/-- Unknown: array element frame (module docstring). -/
def pushTarget := spec!{ push }
/-- Unknown: array element frame (module docstring). -/
def popTarget := spec!{ pop }

/-- `top()`: `ensures \result == arr[arr.length - 1]`. -/
theorem spec_top : ⊢ spec!{ top } := by
  sol_prove

/-- Component of `push`: the length grows by one. -/
theorem push_length : ⊢ dl!{ n == arr.length → [ push(i); ] arr.length == n + 1 } := by
  sol_prove
/-- Component of `push`: the value lands on top. -/
theorem push_top : ⊢ dl!{ n == arr.length → [ push(i); ] arr[n] == i } := by
  sol_prove
/-- Component of `pop`: the length shrinks by one. -/
theorem pop_length : ⊢ dl!{ n == arr.length → [ pop(); ] arr.length == n - 1 } := by
  sol_prove

end Solidity.Examples.Benchmark.DataStructures.Stack
