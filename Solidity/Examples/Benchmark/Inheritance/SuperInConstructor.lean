import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Benchmark: a `super` chain over a diamond, in a constructor

Source: solc's semantic test `inheritance/super_in_constructor.sol`,
<https://raw.githubusercontent.com/ethereum/solidity/v0.8.26/test/libsolidity/semanticTests/inheritance/super_in_constructor.sol>
(expected `f() -> 15`).

`contract!{ … }` writes one contract, so `D` is written linearized, as solc
compiles it: D's C3 order is `D, C, B, A`, and every base version of `f` is
its own function, named after its contract (`A_f`, `B_f`, `C_f`), with the
source's attributes (which `contract!{ … }` drops).
`super.f()` in a version calls the next version in *D's* order, not its own
parent's: `D`'s constructor calls `C_f`, `C`'s `super.f()` is `B_f` (although
`C is A`), and `B`'s is `A_f`.  D's own `f` overrides all three.  Nothing else
is changed.
```solidity
contract A { function f() public virtual returns (uint256 r) { return 1; } }
contract B is A {
    function f() public virtual override returns (uint256 r) { return super.f() | 2; } }
contract C is A {
    function f() public virtual override returns (uint256 r) { return super.f() | 4; } }
contract D is B, C {
    uint256 data;
    constructor() { data = super.f() | 8; }
    function f() public override (B, C) returns (uint256 r) { return data; }
}
```

Verdicts: `A_f`, `B_f`, `C_f`, the constructor and `f`: proved.
-/

namespace Solidity.Examples.Benchmark.Inheritance.SuperInConstructor
/-- `D`, linearized `D, C, B, A`, with the clauses. -/
def D : Contract := contract!{
  uint256 data;
  ensures \result == 1;
  function A_f() public virtual returns (uint256 r) { return 1; }
  ensures \result == 3;
  function B_f() public virtual override returns (uint256 r) { return A_f() | 2; }
  ensures \result == 7;
  function C_f() public virtual override returns (uint256 r) { return B_f() | 4; }
  ensures data == 15;
  constructor() { data = C_f() | 8; }
  ensures \result == data;
  function f() public override returns (uint256 r) { return data; }
}

local instance : InContract := ⟨D⟩

open scoped Scoped
/-- `A.f()` returns `1`. -/
theorem spec_A_f : ⊢ spec!{ A_f } := by
  sol_prove
/-- `B.f()` in `D`: `super` is `A`, `1 | 2`. -/
theorem spec_B_f : ⊢ spec!{ B_f } := by
  sol_prove
/-- `C.f()` in `D`: `super` is `B` (not `C`'s parent `A`), `3 | 4`. -/
theorem spec_C_f : ⊢ spec!{ C_f } := by
  sol_prove
/-- The constructor: `super.f()` is `C`'s, so `data` is `7 | 8 = 15`. -/
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove
/-- `D.f()` returns `data`. -/
theorem spec_f : ⊢ spec!{ f } := by
  sol_prove

end Solidity.Examples.Benchmark.Inheritance.SuperInConstructor
