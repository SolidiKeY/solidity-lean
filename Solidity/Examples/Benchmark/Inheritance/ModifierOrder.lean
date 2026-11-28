import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Benchmark: modifier order beside base constructor arguments

Source: solc's semantic test `modifiers/evaluation_order.sol`,
<https://raw.githubusercontent.com/ethereum/solidity/v0.8.26/test/libsolidity/semanticTests/modifiers/evaluation_order.sol>
(expected `query() -> 0x20, 7, 4, 2, 6, 1, 3, 5, 7`).

`D`'s constructor header mixes modifiers and base constructor calls.  The
base constructors' arguments are evaluated first, in the linearization
`D, C, B, A` (`f(4)`, `f(2)`, `f(6)`); then the modifiers are entered in the
order they are written, each evaluating its argument as it is entered
(`m2`, `m1`, `m3`: `f(1)`, `f(3)`, `f(5)`); then the body (`f(7)`).
`D` is written linearized: each base constructor is a function named after
its contract, its unnamed parameter named, and their calls are the
outermost modifier `bases`, which `contract!{ … }` inlines before the
others.  The modifiers' unnamed parameters are named too.
```solidity
contract A { constructor(uint) {} }
contract B { constructor(uint) {} }
contract C { constructor(uint) {} }
contract D is A, B, C {
    uint[] x;
    constructor() m2(f(1)) B(f(2)) m1(f(3)) C(f(4)) m3(f(5)) A(f(6)) {
        f(7);
    }
    function query() public view returns (uint[] memory) { return x; }
    modifier m1(uint) { _; }
    modifier m2(uint) { _; }
    modifier m3(uint) { _; }
    function f(uint y) internal returns (uint) { x.push(y); return 0; }
}
```

Verdicts: `f`, the constructor: proved; `query` (a memory copy of `x`) has
no clause.
-/

namespace Solidity.Examples.Benchmark.Inheritance.ModifierOrder
/-- `D`, linearized `D, C, B, A`, with the clauses. -/
def D : Contract := contract!{
  uint[] x;
  function A_constructor(uint a) {}
  function B_constructor(uint b) {}
  function C_constructor(uint c) {}
  ensures x.length == \old(x.length) + 1 && x[\old(x.length)] == y && \result == 0;
  function f(uint y) internal returns (uint) { x.push(y); return 0; }
  skip;
  function query() public view returns (uint[] memory) { return x; }
  modifier m1(uint p) { _; }
  modifier m2(uint p) { _; }
  modifier m3(uint p) { _; }
  modifier bases() { C_constructor(f(4)); B_constructor(f(2)); A_constructor(f(6)); _; }
  ensures x.length == 7 && x[0] == 4 && x[1] == 2 && x[2] == 6 && x[3] == 1 && x[4] == 3 && x[5] == 5 && x[6] == 7;
  constructor() bases m2(f(1)) m1(f(3)) m3(f(5)) { f(7); }
}

local instance : InContract := ⟨D⟩
open scoped Scoped
/-- `f(y)` appends `y` and returns `0`. -/
theorem spec_f : ⊢ spec!{ f } := by
  sol_prove
/-- The constructor: base arguments `4, 2, 6`, modifier arguments `1, 3, 5`, body `7`. -/
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove

end Solidity.Examples.Benchmark.Inheritance.ModifierOrder
