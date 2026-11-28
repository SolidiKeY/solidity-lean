import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Two-pointer pair sum on a sorted memory array

Source: the Dafny guide, sections "Loop Invariants", "Quantifiers" and
"Predicates" (`sorted`) (pinned): <https://raw.githubusercontent.com/dafny-lang/dafny/0b85e632f110f2a078e22cf1f0e94b976ed571ba/docs/OnlineTutorial/guide.md>.
Program: `lo` and `hi` close in from both ends; a sum below the target
moves `lo` up, one above moves `hi` down.
Adaptation: uint256 memory array; a `found` flag in the guard instead of a
`return` inside the loop; checked addition (an overflowing sum reverts).
Natural specification: on a sorted array, the result is true exactly when
two distinct positions sum to the target. Invariant: no pair with an index
outside `[lo, hi]` sums to the target; variant `hi - lo`.
-/
namespace Solidity.Examples.Benchmark.MemoryAlgorithms.PairSum

def PairSum : Contract := contract!{
  requires \forall uint p; \forall uint q; p < q && q < xs.length -> xs[p] <= xs[q];
  ensures \result == true -> (\exists uint p; \exists uint q; p < q && q < xs.length && xs[p] + xs[q] == t);
  ensures (\exists uint p; \exists uint q; p < q && q < xs.length && xs[p] + xs[q] == t) -> \result == true;
  function hasPair(uint[] memory xs, uint t) public pure returns (bool) {
    if (xs.length < 2) { return false; }
    uint lo = 0; uint hi = xs.length - 1; bool found = false;
    /// @custom:key invariant lo <= hi && hi < xs.length
    /// @custom:key invariant !found || (lo < hi && xs[lo] + xs[hi] == t)
    /// @custom:key invariant \forall uint p; \forall uint q; p < q && q < xs.length && (p < lo || q > hi) -> xs[p] + xs[q] != t
    /// @custom:key decreases hi - lo
    while (!found && lo < hi) {
      uint s = xs[lo] + xs[hi];
      if (s == t) { found = true; } else { if (s < t) { lo++; } else { hi -= 1; } }
    }
    return found;
  }
}
local instance : InContract := ⟨PairSum⟩
open scoped Scoped

/-- Unknown. `sol_auto` stops at `leaf1`, the early `return false` for
`xs.length < 2`: the goal is `¬∃ p q, p < q < xs.length ∧ …`, which needs an
existential premise opened and `q < 2` with `p < q` refuted; no leaf tactic
does it. The loop leaves (the invariant with an index outside `[lo, hi]`)
need the sorted premise instantiated at `lo` and `hi`. Needed: existential
elimination in the closers (`Calculus/Close.lean`). -/
def correctnessTarget := spec!{ hasPair }

end Solidity.Examples.Benchmark.MemoryAlgorithms.PairSum
