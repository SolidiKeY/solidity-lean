import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Occurrences of a key in a memory array

Source: the Dafny guide, sections "Loop Invariants" and "Arrays"
(pinned): <https://raw.githubusercontent.com/dafny-lang/dafny/0b85e632f110f2a078e22cf1f0e94b976ed571ba/docs/OnlineTutorial/guide.md>.
Program: one scan, counting the positions equal to the key.
Adaptation: uint256 memory array; checked increment (it cannot overflow:
the count stays at most `i`).
Natural specification: the result is the number of positions holding the
key (`NaturalSpec`). Invariant: `c` counts the key in `xs[0..i)`;
variant `xs.length - i`.  SolSpec has no counting aggregate, so the
contract states no clause; `NaturalSpec` keeps the target exact instead of
replacing it by a bound.
-/
namespace Solidity.Examples.Benchmark.MemoryAlgorithms.CountOccurrences

def NaturalSpec (xs : List Nat) (key result : Nat) : Prop :=
  result = (xs.filter (· == key)).length

def CountOccurrences : Contract := contract!{
  function count(uint[] memory xs, uint key) public pure returns (uint) {
    uint c = 0; uint i = 0;
    /// @custom:key invariant i <= xs.length && c <= i
    /// @custom:key decreases xs.length - i
    while (i < xs.length) {
      if (xs[i] == key) { c++; }
      i++;
    }
    return c;
  }
}
local instance : InContract := ⟨CountOccurrences⟩
open scoped Scoped
-- Unknown: the counting postcondition and prefix invariant cannot be written
-- in SpecExpr; a counting (filter-length) aggregate is missing.
-- NaturalSpec is a mathematical target, not a proof about the contract.
end Solidity.Examples.Benchmark.MemoryAlgorithms.CountOccurrences
