import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Prefix sums into a caller's memory array

Source: the Dafny guide, sections "Loop Invariants", "Arrays" and
"Quantifiers" (pinned): <https://raw.githubusercontent.com/dafny-lang/dafny/0b85e632f110f2a078e22cf1f0e94b976ed571ba/docs/OnlineTutorial/guide.md>.
Program: `out[0] = 0`, then `out[i + 1] = out[i] + xs[i]`.
Adaptation: uint256 memory arrays; the sums go to a caller's array `out` of
length `xs.length + 1` (Dafny's `modifies`), since a function here returns
value types only; checked addition (an overflowing prefix reverts).
Natural specification: the zero first entry and the recurrence at every
index. Invariant: the recurrence below `i`; variant `xs.length - i`.
-/
namespace Solidity.Examples.Benchmark.MemoryAlgorithms.PrefixSums

def PrefixSums : Contract := contract!{
  requires out.length == xs.length + 1;
  ensures out[0] == 0;
  ensures \forall uint j; j < xs.length -> out[j + 1] == out[j] + xs[j];
  function prefixSums(uint[] memory xs, uint[] memory out) public pure {
    out[0] = 0;
    uint i = 0;
    /// @custom:key invariant i <= xs.length && out.length == xs.length + 1 && out[0] == 0
    /// @custom:key invariant \forall uint j; j < i -> out[j + 1] == out[j] + xs[j]
    /// @custom:key decreases xs.length - i
    while (i < xs.length) { out[i + 1] = out[i] + xs[i]; i++; }
  }
}
local instance : InContract := ⟨PrefixSums⟩
open scoped Scoped

/-- Unknown, not refuted. `sol_prove` leaves `leaf1` as `… ⟹ false`: the loop
cut over a body that writes memory has no frame (`Blocks.loopStep` needs
`Prog.frame`; a memory write has none), so the walk keeps the unprovable
leaf instead of the invariant's obligations. Needed: a sound heap
modifies/havoc frame for loop bodies with memory writes. -/
def correctnessTarget := spec!{ prefixSums }

end Solidity.Examples.Benchmark.MemoryAlgorithms.PrefixSums
