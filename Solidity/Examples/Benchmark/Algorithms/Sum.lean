import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Sum of an array

Source: K. Rustan M. Leino, *Program Proofs* (MIT Press, 2023),
sequence summation by a prefix loop. Adaptation: checked uint256 addition.
Natural specification: result = sum(input), on normal return. The prefix
invariant is s = sum(input.take(i)), and the variant is input.length-i.
The SolSpec surface has no sequence fold; `NaturalSpec` retains this exact
specification instead of replacing it by a bound or a constant-array case.
-/
namespace Solidity.Examples.Benchmark.Algorithms.Sum

def NaturalSpec (input : List Nat) (result : Nat) : Prop := result = input.sum

def Sum : Contract := contract!{
  function sum(uint[] memory xs) public pure returns (uint) {
    uint s = 0; uint i = 0;
    /// @custom:key invariant i <= xs.length
    /// @custom:key decreases xs.length - i
    while (i < xs.length) { s += xs[i]; i++; }
    return s;
  }
}
local instance : InContract := ⟨Sum⟩
open scoped Scoped
-- Unknown: the exact fold postcondition and prefix invariant cannot be
-- lowered by SpecExpr; a sequence-fold specification rule is missing.
-- NaturalSpec is a mathematical target, not a proof about the contract.
end Solidity.Examples.Benchmark.Algorithms.Sum
