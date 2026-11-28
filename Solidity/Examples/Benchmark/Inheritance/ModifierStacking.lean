import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Benchmark: one modifier stacked three times

Source: solc's semantic test `modifiers/function_modifier_multiple_times.sol`,
<https://raw.githubusercontent.com/ethereum/solidity/v0.8.26/test/libsolidity/semanticTests/modifiers/function_modifier_multiple_times.sol>
(expected `f(3) -> 10`, then `a() -> 10`).

Unchanged but for the spelling of `contract!{ … }`.  The three applications
of `mod` are inlined around `f`'s body outermost first, `mod(2)`, `mod(5)`,
then `mod(x)`, each with its own copy of the parameter `x`, so the body
reads `a` after all three additions.  The additions commute, so the clause
does not tell the three orders apart: this module shows stacking, not order
(`ModifierOrder.lean` shows order).
```solidity
contract C {
    uint256 public a;
    modifier mod(uint256 x) { a += x; _; }
    function f(uint256 x) public mod(2) mod(5) mod(x) returns (uint256) { return a; }
}
```

Verdicts: `f`: proved.
-/

namespace Solidity.Examples.Benchmark.Inheritance.ModifierStacking
/-- `C`, with the clause. -/
def C : Contract := contract!{
  uint256 public a;
  modifier mod(uint256 x) { a += x; _; }
  ensures a == \old(a) + 2 + 5 + x && \result == a;
  function f(uint256 x) public mod(2) mod(5) mod(x) returns (uint256) { return a; }
}

local instance : InContract := ⟨C⟩

open scoped Scoped
/-- `f(x)`: the three modifiers add `2 + 5 + x` before the body returns `a`. -/
theorem spec_f : ⊢ spec!{ f } := by
  sol_prove

end Solidity.Examples.Benchmark.Inheritance.ModifierStacking
