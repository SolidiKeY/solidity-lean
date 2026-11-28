import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Benchmark: a base constructor's argument, through a chain of bases

Source: solc's semantic test `constructor/base_constructor_arguments.sol`,
<https://raw.githubusercontent.com/ethereum/solidity/v0.8.26/test/libsolidity/semanticTests/constructor/base_constructor_arguments.sol>
(expected `getA() -> 49`).

`Derived` is written linearized (`Derived, Base, BaseBase`).  Its implicit
constructor runs the base constructors' bodies most base first:
`BaseBase`'s with the argument `7` that `Base`'s header passes
(`is BaseBase(7)`), then `Base`'s.  Each base constructor is an internal
function named after its contract (`BaseBase_constructor`,
`Base_constructor`), and `Derived`'s constructor calls them in that order.
Nothing else is changed.

```solidity
contract BaseBase { uint256 m_a; constructor(uint256 a) { m_a = a; } }
contract Base is BaseBase(7) { constructor() { m_a *= m_a; } }
contract Derived is Base { function getA() public returns (uint256 r) { return m_a; } }
```

Verdicts: `BaseBase_constructor`, `Base_constructor`, the constructor,
`getA`: proved.
-/

namespace Solidity.Examples.Benchmark.Inheritance.ConstructorArgs

/-- `Derived`, linearized `Derived, Base, BaseBase`, with the clauses. -/
def Derived : Contract := contract!{
  uint256 m_a;
  ensures m_a == a;
  function BaseBase_constructor(uint256 a) { m_a = a; }
  ensures m_a == \old(m_a) * \old(m_a);
  function Base_constructor() { m_a *= m_a; }
  ensures m_a == 49;
  constructor() { BaseBase_constructor(7); Base_constructor(); }
  ensures \result == m_a;
  function getA() public returns (uint256 r) { return m_a; }
}

local instance : InContract := ⟨Derived⟩

open scoped Scoped

/-- `BaseBase`'s constructor stores its argument. -/
theorem spec_BaseBase_constructor : ⊢ spec!{ BaseBase_constructor } := by
  sol_prove
/-- `Base`'s constructor squares `m_a`. -/
theorem spec_Base_constructor : ⊢ spec!{ Base_constructor } := by
  sol_prove
/-- `Derived`'s constructor: `7`, then squared, `49`. -/
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove
/-- `getA()` returns `m_a`. -/
theorem spec_getA : ⊢ spec!{ getA } := by
  sol_prove

end Solidity.Examples.Benchmark.Inheritance.ConstructorArgs
