import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Sortedness check of a memory array

Source: the Dafny guide, sections "Loop Invariants", "Arrays" and
"Quantifiers" (pinned): <https://raw.githubusercontent.com/dafny-lang/dafny/0b85e632f110f2a078e22cf1f0e94b976ed571ba/docs/OnlineTutorial/guide.md>.
Program: the adjacent-pair scan; the loop stops at the first descent.
Adaptation: uint256 memory array; `i + 1 < xs.length` guards the reads.
Natural specification: the result is true exactly when every adjacent pair
is ordered (two clauses, one per direction). Invariant: the pairs below `i`
are ordered; variant `xs.length - i`.
-/
namespace Solidity.Examples.Benchmark.MemoryAlgorithms.IsSorted

def IsSorted : Contract := contract!{
  ensures \result == true -> (\forall uint j; j + 1 < xs.length -> xs[j] <= xs[j + 1]);
  ensures (\forall uint j; j + 1 < xs.length -> xs[j] <= xs[j + 1]) -> \result == true;
  function isSorted(uint[] memory xs) public pure returns (bool) {
    uint i = 0;
    /// @custom:key invariant \forall uint j; j < i && j + 1 < xs.length -> xs[j] <= xs[j + 1]
    /// @custom:key decreases xs.length - i
    while (i + 1 < xs.length && xs[i] <= xs[i + 1]) { i++; }
    return i + 1 >= xs.length;
  }
}
local instance : InContract := ⟨IsSorted⟩
open scoped Scoped

/-- Unknown. `sol_prove` leaves three leaves (initialization, step, exit;
the exit splits by the short-circuit guard and by clause into four goals);
`sol_auto` stops at the step `leaf2`, and `sol_leaf_keep; sol_close`
closes none (`sol_close_nonlin`: bounded search stopped, also at ten times
the heartbeats). Each is true: opened by `sol_close_eval` and finished by
hand, the step needs the `∀` premise below the old `i` and the two guard
reads at `i`; the exit needs it below `i` and, for the converse, the
descent read against the instantiated sortedness premise. Needed: a closer
step that splits `n < i ∨ n = i` against a quantified premise and
identifies a read with a guard read (`Calculus/Close.lean`); opening all
leaves already costs about 130 k of the 200 k heartbeats. -/
def correctnessTarget := spec!{ isSorted }

end Solidity.Examples.Benchmark.MemoryAlgorithms.IsSorted
