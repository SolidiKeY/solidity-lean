import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Maximum of a nonempty array

Source: David Gries, *The Science of Programming* (Springer, 1981),
loop-invariant method; the standard prefix-maximum scan.
Adaptation: uint256 memory array and zero-based indices; a local witness
index records where the current maximum was seen.
The natural specification says the result is an element and bounds every
input element, rather than merely asserting an upper bound.
-/
namespace Solidity.Examples.Benchmark.Algorithms.Maximum

def Maximum : Contract := contract!{
  requires xs.length > 0;
  ensures \forall uint j; j < xs.length -> xs[j] <= \result;
  ensures \exists uint j; j < xs.length && xs[j] == \result;
  function maximum(uint[] memory xs) public pure returns (uint) {
    uint m = xs[0]; uint i = 1; uint witness = 0;
    /// @custom:key invariant 1 <= i && i <= xs.length
    /// @custom:key invariant witness < i && xs[witness] == m
    /// @custom:key invariant \forall uint j; j < i -> xs[j] <= m
    /// @custom:key decreases xs.length - i
    while (i < xs.length) {
      if (m < xs[i]) { m = xs[i]; witness = i; }
      i++;
    }
    return m;
  }
}

local instance : InContract := ⟨Maximum⟩
open scoped Scoped

/-- Unknown: prefix initialization and preservation remain open, including
forall j < i, xs[j] <= m. Needed: memory read/alias and quantified-prefix
closure, then symbolic witness introduction for the attained maximum. -/
def correctnessTarget := spec!{ maximum }

end Solidity.Examples.Benchmark.Algorithms.Maximum
