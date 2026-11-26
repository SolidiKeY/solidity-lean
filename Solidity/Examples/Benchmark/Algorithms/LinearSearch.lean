import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Linear search, returning the first matching index

Source: Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*,
3rd edition (MIT Press, 2009), exercise 2.1-3 (linear search).
Adaptation: zero-based unsigned indices; the array length denotes absence.
The natural specification includes both the successful and absent cases and
minimality of the returned index. Arithmetic is Solidity checked arithmetic.
-/
namespace Solidity.Examples.Benchmark.Algorithms.LinearSearch

def LinearSearch : Contract := contract!{
  ensures \result <= xs.length;
  ensures \result < xs.length -> xs[\result] == key;
  ensures \forall uint j; j < \result -> xs[j] != key;
  function find(uint[] memory xs, uint key) public pure returns (uint) {
    uint i = 0;
    /// @custom:key invariant i <= xs.length
    /// @custom:key invariant \forall uint j; j < i -> xs[j] != key
    /// @custom:key decreases xs.length - i
    while (i < xs.length) {
      if (xs[i] == key) { return i; }
      i++;
    }
    return xs.length;
  }
}

local instance : InContract := ⟨LinearSearch⟩
open scoped Scoped

/-- Unknown: initialization leaves i <= xs.length under generated reference
aliases. Standard leaf closure also fails. Needed: expose live-reference
length/read facts through the loop and anonymous-update contexts. -/
def correctnessTarget := spec!{ find }

end Solidity.Examples.Benchmark.Algorithms.LinearSearch
