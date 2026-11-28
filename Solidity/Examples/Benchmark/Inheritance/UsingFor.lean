import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: a library function bound with `using … for`

Source: solc's semantic test `libraries/using_for_function_on_int.sol`,
<https://raw.githubusercontent.com/ethereum/solidity/v0.8.26/test/libsolidity/semanticTests/libraries/using_for_function_on_int.sol>
(expected `f(9) -> 18`).

`using D for uint;` makes `a.double()` the call `D.double(a)`, the receiver
the first argument.  `contract!{ … }` has no libraries, so `D.double` is
written as an internal function `D_double` of `C` and the bound call as
`D_double(a)`.  `double` is `public`, which solc compiles to a
`DELEGATECALL` into the deployed library; the model inlines it, so the
library's address and linking are not modeled.  Nothing else is changed.

```solidity
library D { function double(uint self) public returns (uint) { return 2 * self; } }
contract C {
    using D for uint;
    function f(uint a) public returns (uint) { return a.double(); }
}
```

Verdicts: `D_double`, `f`: proved.
-/

namespace Solidity.Examples.Benchmark.Inheritance.UsingFor

/-- `C` with `D.double` beside it, with the clauses. -/
def C : Contract := contract!{
  ensures \result == 2 * self;
  function D_double(uint self) public returns (uint) { return 2 * self; }
  ensures \result == 2 * a;
  function f(uint a) public returns (uint) { return D_double(a); }
}

local instance : InContract := ⟨C⟩

open scoped Scoped

/-- `D.double(self)` is `2 * self` (a product that overflows reverts). -/
theorem spec_D_double : ⊢ spec!{ D_double } := by
  sol_prove
/-- `f(a)`: `a.double()` binds `a` as `self`, `2 * a`. -/
theorem spec_f : ⊢ spec!{ f } := by
  sol_prove

end Solidity.Examples.Benchmark.Inheritance.UsingFor
