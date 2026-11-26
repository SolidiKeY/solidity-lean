import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Find the first negative element

Source: K. Rustan M. Leino, *Program Proofs* (MIT Press, 2023),
array traversal and loop-invariant method. Adaptation: signed Solidity
array, with its length as the sentinel. This is predicate search rather
than the equality search in LinearSearch.
-/
namespace Solidity.Examples.Benchmark.Algorithms.FindIndex

def FindIndex : Contract := contract!{
  ensures \result <= xs.length;
  ensures \result < xs.length -> xs[\result] < 0;
  ensures \forall uint j; j < \result -> xs[j] >= 0;
  function firstNegative(int[] memory xs) public pure returns (uint) {
    uint i = 0;
    /// @custom:key invariant i <= xs.length
    /// @custom:key invariant \forall uint j; j < i -> xs[j] >= 0
    /// @custom:key decreases xs.length - i
    while (i < xs.length) {
      if (xs[i] < 0) { return i; }
      i++;
    }
    return xs.length;
  }
}
local instance : InContract := ⟨FindIndex⟩
open scoped Scoped
/-- Unknown: initialization leaves i <= xs.length under generated reference
aliases; the quantified prefix also remains open. Needed: propagate
reference length/read facts through loop and anonymous-update contexts. -/
def correctnessTarget := spec!{ firstNegative }

end Solidity.Examples.Benchmark.Algorithms.FindIndex
