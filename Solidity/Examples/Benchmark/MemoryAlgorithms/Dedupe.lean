import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Duplicates removed from a sorted memory array

Source: the Dafny guide, sections "Loop Invariants", "Quantifiers" and
"Predicates" (`sorted`) (pinned): <https://raw.githubusercontent.com/dafny-lang/dafny/0b85e632f110f2a078e22cf1f0e94b976ed571ba/docs/OnlineTutorial/guide.md>.
Program: copy each first occurrence (an element differing from its
predecessor) to the next free slot; return the count.
Adaptation: uint256 memory arrays; the distinct values go to a caller's
array `out` of the input's length (Dafny's `modifies`), since a function here
returns value types only and the surface does not snapshot a memory heap.
Natural specification: on a sorted input, `out[0..result)` is strictly
increasing, every input element occurs in it, and every element of it
occurs in the input.  Invariant: the same three facts for `xs[0..i)` and
`out[0..m)`, and `out[m - 1] == xs[i - 1]`; variant `xs.length - i`.  The two
covering facts are existential, which a loop clause cannot state
(`sol_loop_inv`: `\forall`, `a -> c`, or an expression), so the annotation
carries the other two.
-/
namespace Solidity.Examples.Benchmark.MemoryAlgorithms.Dedupe

def Dedupe : Contract := contract!{
  requires out.length == xs.length;
  requires \forall uint p; \forall uint q; p < q && q < xs.length -> xs[p] <= xs[q];
  ensures \result <= xs.length;
  ensures \forall uint p; \forall uint q; p < q && q < \result -> out[p] < out[q];
  ensures \forall uint p; p < xs.length -> (\exists uint q; q < \result && out[q] == xs[p]);
  ensures \forall uint q; q < \result -> (\exists uint p; p < xs.length && xs[p] == out[q]);
  function dedupe(uint[] memory xs, uint[] memory out) public pure returns (uint) {
    uint m = 0; uint i = 0;
    /// @custom:key invariant i <= xs.length && m <= i && out.length == xs.length
    /// @custom:key invariant \forall uint p; \forall uint q; p < q && q < m -> out[p] < out[q]
    /// @custom:key invariant m == 0 || i == 0 || out[m - 1] == xs[i - 1]
    /// @custom:key decreases xs.length - i
    while (i < xs.length) {
      if (i == 0 || xs[i] != xs[i - 1]) { out[m] = xs[i]; m++; }
      i++;
    }
    return m;
  }
}
local instance : InContract := ⟨Dedupe⟩
open scoped Scoped

/-- Unknown, not refuted. `sol_prove` leaves `leaf1` as `… ⟹ false`: the loop
cut over a body that writes memory has no frame (`Blocks.loopStep` needs
`Prog.frame`; a memory write has none), so the walk keeps the unprovable
leaf instead of the invariant's obligations. Needed: a sound heap
modifies/havoc frame for loop bodies with memory writes. -/
def correctnessTarget := spec!{ dedupe }

end Solidity.Examples.Benchmark.MemoryAlgorithms.Dedupe
