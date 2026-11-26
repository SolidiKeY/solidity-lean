import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Exponentiation by squaring

Source: Cormen et al., *Introduction to Algorithms*, 3rd edition (2009),
section 31.6, repeated-squaring method. Adaptation: ordinary checked uint256
multiplication rather than modular multiplication. Natural specification:
result=base^exponent, including 0^0=1. The mathematical loop invariant is
r*x^e=base^exponent; the variant is e. Squaring is skipped once e=0 so that
a discarded intermediate square cannot cause an unnecessary overflow.
-/
namespace Solidity.Examples.Benchmark.Algorithms.FastExponentiation

def NaturalSpec (base exponent result : Nat) : Prop := result = base ^ exponent

def FastExponentiation : Contract := contract!{
  function power(uint base, uint exponent) public pure returns (uint) {
    uint r = 1; uint x = base; uint e = exponent;
    /// @custom:key invariant e <= exponent
    /// @custom:key decreases e
    while (e > 0) {
      if (e % 2 == 1) { r *= x; }
      e = e / 2;
      if (e > 0) { x *= x; }
    }
    return r;
  }
}
local instance : InContract := ⟨FastExponentiation⟩
open scoped Scoped
-- Unknown: SpecExpr has no mathematical exponentiation operator.
-- Missing: power lowering and nonlinear repeated-squaring invariant closure.
-- NaturalSpec is a mathematical target, not a proof about the contract.
end Solidity.Examples.Benchmark.Algorithms.FastExponentiation
