import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Benchmark: base constructor arguments, in linearization order

Source: solc's semantic test `constructor/order_of_evaluation.sol`,
<https://raw.githubusercontent.com/ethereum/solidity/v0.8.26/test/libsolidity/semanticTests/constructor/order_of_evaluation.sol>
(expected `g() -> 0x20, 4, 1, 3, 2, 4`).

`X is D, C, B, A` linearizes to `X, A, B, C, D`, and the arguments of the
base constructors are evaluated in that order, not in the header's
(`A(f(1)) C(f(2)) B(f(3)) D(f(4))`): `x` ends `[1, 3, 2, 4]`.  `X` is written
linearized: each base constructor is a function named after its contract,
its unnamed parameter named, and `X`'s constructor calls them in that order.
```solidity
contract A { constructor(uint) {} }
contract B { constructor(uint) {} }
contract C { constructor(uint) {} }
contract D { constructor(uint) {} }
contract X is D, C, B, A {
    uint[] x;
    function f(uint _x) internal returns (uint) { x.push(_x); }
    function g() public view returns (uint[] memory) { return x; }
    constructor() A(f(1)) C(f(2)) B(f(3)) D(f(4)) {}
}
```

Verdicts: `f`, the constructor: proved; `g` (a memory copy of `x`) has
no clause.
-/

namespace Solidity.Examples.Benchmark.Inheritance.ConstructorOrder
/-- `X`, linearized `X, A, B, C, D`, with the clauses. -/
def X : Contract := contract!{
  uint[] x;
  function A_constructor(uint a) {}
  function B_constructor(uint b) {}
  function C_constructor(uint c) {}
  function D_constructor(uint d) {}
  ensures x.length == \old(x.length) + 1 && x[\old(x.length)] == _x && \result == 0;
  function f(uint _x) internal returns (uint) { x.push(_x); }
  skip;
  function g() public view returns (uint[] memory) { return x; }
  ensures x.length == 4 && x[0] == 1 && x[1] == 3 && x[2] == 2 && x[3] == 4;
  constructor() { A_constructor(f(1)); B_constructor(f(3)); C_constructor(f(2)); D_constructor(f(4)); }
}

local instance : InContract := ⟨X⟩

open scoped Scoped
/-- `f(_x)` appends `_x` and returns the default `0`. -/
theorem spec_f : ⊢ spec!{ f } := by
  sol_prove
/-- The constructor: `A`'s argument first, then `B`'s, `C`'s, `D`'s. -/
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove

end Solidity.Examples.Benchmark.Inheritance.ConstructorOrder
