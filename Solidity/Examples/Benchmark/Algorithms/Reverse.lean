import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Reverse an array in place

Source: K. Rustan M. Leino, *Program Proofs* (MIT Press, 2023),
array reversal by symmetric swaps. Adaptation: a Solidity storage array;
this permits the exact entry-state specification with the existing
storage snapshot (the surface does not snapshot memory heaps).
Natural loop invariant: indices below i and at least n-i are reversed;
the middle still equals its entry state. This relation needs entry-storage
reads inside loop annotations, whose RawExpr grammar has no \old.
Natural specification: unchanged length and element i equals the old
length-1-i element, for every valid index, including empty arrays.
-/
namespace Solidity.Examples.Benchmark.Algorithms.Reverse

def Reverse : Contract := contract!{
  uint[] values;
  ensures values.length == \old(values.length);
  ensures \forall uint j; j < values.length -> values[j] == \old(values[values.length - 1 - j]);
  function reverse() public {
    uint i = 0; uint n = values.length;
    /// @custom:key invariant i <= n / 2 && n == values.length
    /// @custom:key decreases n / 2 - i
    while (i < n / 2) {
      uint t = values[i]; values[i] = values[n - 1 - i];
      values[n - 1 - i] = t; i++;
    }
  }
}
local instance : InContract := ⟨Reverse⟩
open scoped Scoped
/-- Unknown: even 0 <= values.length / 2 remains open at initialization.
The full target also needs the reversed-prefix/unchanged-middle invariant
against entry storage. Needed: array-length closure and snapshot-aware
loop formulas; current RawInv contains only current-state expressions. -/
def correctnessTarget := spec!{ reverse }

end Solidity.Examples.Benchmark.Algorithms.Reverse
