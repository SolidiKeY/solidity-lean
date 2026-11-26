import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Fibonacci by two accumulators

Source: K. Rustan M. Leino, *Program Proofs* (MIT Press, 2023),
Fibonacci loop. Adaptation: uint256 checked arithmetic. F(0)=0, F(1)=1.
Natural specification: result=F(n); invariant a=F(i), b=F(i+1), i<=n;
variant n-i. Overflow reverts; normal-return correctness is the target.
-/
namespace Solidity.Examples.Benchmark.Algorithms.Fibonacci

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

def NaturalSpec (n result : Nat) : Prop := result = fib n

def Fibonacci : Contract := contract!{
  function fibonacci(uint n) public pure returns (uint) {
    uint a = 0; uint b = 1; uint i = 0;
    /// @custom:key invariant i <= n
    /// @custom:key decreases n - i
    while (i < n) { uint t = a + b; a = b; b = t; i++; }
    return a;
  }
}
local instance : InContract := ⟨Fibonacci⟩
open scoped Scoped
-- Unknown: SpecExpr has no recursive mathematical function application.
-- Missing: lowering fib and its recurrence through the loop invariant.
-- NaturalSpec is a mathematical target, not a proof about the contract.
end Solidity.Examples.Benchmark.Algorithms.Fibonacci
