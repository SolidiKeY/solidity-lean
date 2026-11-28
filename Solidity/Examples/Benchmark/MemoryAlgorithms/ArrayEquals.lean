import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Equality of two memory arrays

Source: the Dafny guide, sections "Loop Invariants" and "Quantifiers"
(pinned): <https://raw.githubusercontent.com/dafny-lang/dafny/0b85e632f110f2a078e22cf1f0e94b976ed571ba/docs/OnlineTutorial/guide.md>.
Program: compare the lengths, then scan while the elements agree.
Adaptation: uint256 memory arrays.
Natural specification: the result is true exactly when the lengths agree
and every element agrees. Invariant: the elements below `i` agree;
variant `a.length - i`.
-/
namespace Solidity.Examples.Benchmark.MemoryAlgorithms.ArrayEquals

def ArrayEquals : Contract := contract!{
  ensures \result == true -> a.length == b.length && (\forall uint j; j < a.length -> a[j] == b[j]);
  ensures a.length == b.length && (\forall uint j; j < a.length -> a[j] == b[j]) -> \result == true;
  function equals(uint[] memory a, uint[] memory b) public pure returns (bool) {
    if (a.length != b.length) { return false; }
    uint i = 0;
    /// @custom:key invariant i <= a.length && a.length == b.length
    /// @custom:key invariant \forall uint j; j < i -> a[j] == b[j]
    /// @custom:key decreases a.length - i
    while (i < a.length && a[i] == b[i]) { i++; }
    return i == a.length;
  }
}
local instance : InContract := ⟨ArrayEquals⟩
open scoped Scoped

/-- Unknown. `sol_auto` closes the leaves before the step leaf `leaf3`
(`{se6 := se6 + 1}` after both reads agree), which no leaf tactic closes:
it needs the `∀ j < i` premise instantiated below the old `i` and the guard
reads `a[i] == b[i]` at the new index. Needed: a closer step that splits
`j < i ∨ j = i` against a quantified premise and identifies a read with a
guard read (`Calculus/Close.lean`). -/
def correctnessTarget := spec!{ equals }

end Solidity.Examples.Benchmark.MemoryAlgorithms.ArrayEquals
