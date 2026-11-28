import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Bubble sort of a small memory array

Source: <https://raw.githubusercontent.com/TheAlgorithms/Solidity/08cba51fb38e276062b0c9791d7e0ee494ffa903/src/Sorts/BubbleSort.sol>
(TheAlgorithms/Solidity, `BubbleSort.bubbleSort`).
Changes: the spelling of `contract!{ … }`; `length` renamed `n` (a
reserved word here) and `i--` written `i -= 1`; the comments dropped; at most eight elements (`requires`); the array sorted in
place and not returned (a function here returns value types only), so the
clauses read `_arr` itself.
Natural specification: the result is sorted and a permutation of the
input (`NaturalSpec`). Outer invariant: the suffix from `i` is sorted and
holds the largest elements; inner invariant: `arr[j]` is the maximum of
`arr[0..j]`.  The permutation half needs the entry memory, which the
surface does not snapshot, and multiset syntax; the contract states the
sortedness half and `NaturalSpec` keeps the whole target.
-/
namespace Solidity.Examples.Benchmark.MemoryAlgorithms.BubbleSort

def NaturalSpec (before after : List Nat) : Prop :=
  before.Perm after ∧ after.Pairwise (fun a b => a <= b)

def BubbleSort : Contract := contract!{
  requires _arr.length <= 8;
  ensures \forall uint p; \forall uint q; p < q && q < _arr.length -> _arr[p] <= _arr[q];
  function bubbleSort(uint256[] memory _arr) public pure {
    uint256 n = _arr.length;
    bool noSwaps;
    /// @custom:key invariant i <= n && n == _arr.length
    /// @custom:key invariant \forall uint p; \forall uint q; p < q && q < n && i <= q -> _arr[p] <= _arr[q]
    /// @custom:key decreases i
    for (uint256 i = n; i > 0; i -= 1) {
      noSwaps = true;
      /// @custom:key invariant j + 1 <= i && i <= n && n == _arr.length
      /// @custom:key invariant \forall uint p; p < j -> _arr[p] <= _arr[j]
      /// @custom:key invariant \forall uint p; \forall uint q; p < q && q < n && i <= q -> _arr[p] <= _arr[q]
      /// @custom:key invariant \forall uint p; \forall uint q; noSwaps && p < q && q <= j -> _arr[p] <= _arr[q]
      /// @custom:key decreases i - 1 - j
      for (uint256 j = 0; j < (i - 1); j++) {
        if (_arr[j] > _arr[j + 1]) {
          uint256 lesser = _arr[j + 1];
          uint256 higher = _arr[j];
          _arr[j + 1] = higher;
          _arr[j] = lesser;
          noSwaps = false;
        }
      };
      if (noSwaps) { break; }
    }
  }
}
local instance : InContract := ⟨BubbleSort⟩
open scoped Scoped

/-- Unknown, not refuted. `sol_prove` leaves `leaf1` as `… ⟹ false`: the loop
cut over a body that writes memory has no frame (`Blocks.loopStep` needs
`Prog.frame`; a memory write has none), so the walk keeps the unprovable
leaf instead of the invariant's obligations. Needed: a sound heap
modifies/havoc frame for loop bodies with memory writes. -/
def correctnessTarget := spec!{ bubbleSort }

end Solidity.Examples.Benchmark.MemoryAlgorithms.BubbleSort
