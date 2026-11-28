import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Benchmark: virtual dispatch beside an explicit base call

Source: solc's semantic test `inheritance/explicit_base_class.sol`,
<https://raw.githubusercontent.com/ethereum/solidity/v0.8.26/test/libsolidity/semanticTests/inheritance/explicit_base_class.sol>
(expected `g() -> 3`, `f() -> 1`).

`Derived` is written linearized (`Derived, Base, BaseBase`), each version
of `g` its own function named after its contract, with the source's
attributes (which `contract!{ … }` drops).  `BaseBase.g()`
names `BaseBase`'s version statically, past both overrides, and `g` itself is
`Derived`'s.  Nothing else is changed.
```solidity
contract BaseBase { function g() public virtual returns (uint256 r) { return 1; } }
contract Base is BaseBase {
    function g() public virtual override returns (uint256 r) { return 2; } }
contract Derived is Base {
    function f() public returns (uint256 r) { return BaseBase.g(); }
    function g() public override returns (uint256 r) { return 3; }
}
```

Verdicts: `BaseBase_g`, `Base_g`, `f`, `g`: proved.
-/

namespace Solidity.Examples.Benchmark.Inheritance.ExplicitBase
/-- `Derived`, linearized `Derived, Base, BaseBase`, with the clauses. -/
def Derived : Contract := contract!{
  ensures \result == 1;
  function BaseBase_g() public virtual returns (uint256 r) { return 1; }
  ensures \result == 2;
  function Base_g() public virtual override returns (uint256 r) { return 2; }
  ensures \result == 1;
  function f() public returns (uint256 r) { return BaseBase_g(); }
  ensures \result == 3;
  function g() public override returns (uint256 r) { return 3; }
}

local instance : InContract := ⟨Derived⟩

open scoped Scoped
/-- `BaseBase.g()` returns `1`. -/
theorem spec_BaseBase_g : ⊢ spec!{ BaseBase_g } := by
  sol_prove
/-- `Base.g()` returns `2`. -/
theorem spec_Base_g : ⊢ spec!{ Base_g } := by
  sol_prove
/-- `f()`: `BaseBase.g()` skips both overrides, `1`. -/
theorem spec_f : ⊢ spec!{ f } := by
  sol_prove
/-- `g()` is `Derived`'s, `3`. -/
theorem spec_g : ⊢ spec!{ g } := by
  sol_prove

end Solidity.Examples.Benchmark.Inheritance.ExplicitBase
