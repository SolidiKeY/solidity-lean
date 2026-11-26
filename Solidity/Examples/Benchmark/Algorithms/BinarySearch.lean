import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Binary search in a sorted array

Source: Cormen et al., *Introduction to Algorithms*, 3rd edition (2009),
exercise 2.3-5. Adaptation: half-open interval and overflow-safe midpoint;
the array length denotes absence. No uniqueness of equal keys is assumed.
-/
namespace Solidity.Examples.Benchmark.Algorithms.BinarySearch

def BinarySearch : Contract := contract!{
  requires \forall uint i; \forall uint j; i < j && j < xs.length -> xs[i] <= xs[j];
  ensures \result <= xs.length;
  ensures \result < xs.length -> xs[\result] == key;
  ensures \result == xs.length -> (\forall uint j; j < xs.length -> xs[j] != key);
  function search(uint[] memory xs, uint key) public pure returns (uint) {
    uint lo = 0; uint hi = xs.length;
    /// @custom:key invariant lo <= hi && hi <= xs.length
    /// @custom:key invariant \forall uint j; j < lo -> xs[j] < key
    /// @custom:key invariant \forall uint j; hi <= j && j < xs.length -> key < xs[j]
    /// @custom:key decreases hi - lo
    while (lo < hi) {
      uint mid = lo + (hi - lo) / 2;
      if (xs[mid] < key) { lo = mid + 1; }
      else { if (key < xs[mid]) { hi = mid; } else { return mid; } }
    }
    return xs.length;
  }
}
local instance : InContract := ⟨BinarySearch⟩
open scoped Scoped
/-- Unknown: loop initialization lo <= hi <= xs.length and subsequent
interval leaves remain open. Needed: reference-length propagation and
closure of quantified sorted-interval facts through generated updates. -/
def correctnessTarget := spec!{ search }

end Solidity.Examples.Benchmark.Algorithms.BinarySearch
