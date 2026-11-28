import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.DecideComplete
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
/-!
# Benchmark: overridden modifiers and a virtual hook, in the constructor

Source: solc's semantic test
`modifiers/function_modifier_calling_functions_in_creation_context.sol`,
<https://raw.githubusercontent.com/ethereum/solidity/v0.8.26/test/libsolidity/semanticTests/modifiers/function_modifier_calling_functions_in_creation_context.sol>
(expected `getData() -> 0x4300`).

`C` is written linearized (`C, A`).  An overridden version is its own
member named after its contract (`A_mod1`, `A_f3`), which nothing applies or
calls any more: `A`'s constructor applies `mod1`, which is `C`'s, so it calls
`f4`, not `f2`; `mod2` calls the virtual `f3`, which is `C`'s, and then
skips `f1`'s body (`if (false) _;`).  Nothing else is changed.
```solidity
contract A {
    uint256 data;
    constructor() mod1 { f1(); }
    function f1() public mod2 { data |= 0x1; }
    function f2() public { data |= 0x20; }
    function f3() public virtual {}
    modifier mod1 virtual { f2(); _; }
    modifier mod2 { f3(); if (false) _; }
    function getData() public returns (uint256 r) { return data; }
}
contract C is A {
    modifier mod1 override { f4(); _; }
    function f3() public override { data |= 0x300; }
    function f4() public { data |= 0x4000; }
}
```

`|` has no spelling in a `@custom:key` clause (`spec_expr`) nor in a
`dl!{ … }` formula, so the functions that `|=` into `data` state their effect
as a box formula that computes the expected value first, in the program
(`uint e = data | 768; f3();`, then `data == e`).  The constructor's clause,
read on a fresh deployment's zeroed `data`, is the number `0x4300 = 17152`.
The one spelling change: `if (false) _;` is written with its block,
`if (false) { _; }`, since `contract!{ … }` reads an `if` branch as a block.

Verdicts: `f1`, `f2`, `A_f3`, `f3`, `f4`, the constructor, `getData`:
proved.
-/

namespace Solidity.Examples.Benchmark.Inheritance.ModifierOverride
/-- `C`, linearized `C, A`, with the clauses. -/
def C : Contract := contract!{
  uint256 data;
  function f2() public { data |= 0x20; }
  ensures data == \old(data);
  function A_f3() public virtual {}
  function f3() public override { data |= 0x300; }
  function f4() public { data |= 0x4000; }
  modifier A_mod1() { f2(); _; }
  modifier mod1() { f4(); _; }
  modifier mod2() { f3(); if (false) { _; } }
  function f1() public mod2 { data |= 0x1; }
  ensures data == 17152;
  constructor() mod1 { f1(); }
  ensures \result == data;
  function getData() public returns (uint256 r) { return data; }
}

local instance : InContract := ⟨C⟩

open scoped Scoped
/-- `f2()` sets bit `0x20`. -/
theorem f2_spec : ⊢ dl!{ [ uint e = data | 32; f2(); ] data == e } := by
  sol_prove
/-- `A.f3()`, overridden, changes nothing. -/
theorem spec_A_f3 : ⊢ spec!{ A_f3 } := by
  sol_prove
/-- `C.f3()` sets bits `0x300`. -/
theorem f3_spec : ⊢ dl!{ [ uint e = data | 768; f3(); ] data == e } := by
  sol_prove
/-- `f4()` sets bit `0x4000`. -/
theorem f4_spec : ⊢ dl!{ [ uint e = data | 16384; f4(); ] data == e } := by
  sol_prove
/-- `f1()`: `mod2` runs `C.f3()` and skips the body, so bit `0x1` stays as it was. -/
theorem f1_spec : ⊢ dl!{ [ uint e = data | 768; f1(); ] data == e } := by
  sol_prove
/-- The constructor: `C.mod1` sets `0x4000`, `f1()` sets `0x300`: `0x4300`. -/
theorem spec_constructor : ⊢ spec!{ constructor } := by
  sol_prove
/-- `getData()` returns `data`. -/
theorem spec_getData : ⊢ spec!{ getData } := by
  sol_prove

end Solidity.Examples.Benchmark.Inheritance.ModifierOverride
