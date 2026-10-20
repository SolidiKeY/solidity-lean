import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# What solkey's `solc/open` ports needed of the elaborator

Two readings the front end's ports of solc's tests (solkey's
`keyext.solidity.examples/solc/open/`) found missing:

* a conversion `E(x)` to an enum of `n` members is a capture of `x` and
  `assert(x < n)`: solc panics (`0x21`) on a value that names no member
  (`enumCapture`);
* a call's value has its callee's return width, so `add16(a, b) + c` inside
  `unchecked` wraps at `2^16` (`intTyOf`).
-/

namespace Solidity.Examples.Tactics.SolcOpen

/-- An enum of two members and a function of a narrow return. -/
def Open : Contract := contract!{
  enum D { Left, Right }
  function add16(uint16 a, uint16 b) returns (uint16) { return a + b; }
}

local instance : InContract := ⟨Open⟩

open scoped Scoped

/-! ## 1 · `E(x)` -/

/-- `D(x)` holds `x` in a fresh local and asserts that it names a member. -/
example : Prog.toStr [] (sol{ uint x = 1; uint p = D(x); }) =
    "uint x = 1; uint se1 = x; assert(se1 < 2); uint p = se1;" := rfl

/-- `enum_from_uint.sol`: `D(0)` is `D.Left`. -/
theorem enumFromUint : ⊨ dl!{ ⟨ uint x = 0; uint p = D(x); assert(p == D.Left); ⟩ true } := by
  sol_symex
  sol_close

/-! ## 2 · A call's width -/

/-- `checked_called_by_unchecked.sol`: the checked `add16(0xe000, 0x1000)`
is `0xf000`, and adding `0x1000` to it unchecked wraps to `0`. -/
theorem checkedCalledByUnchecked : ⊨ dl!{ ⟨ uint16 a = 57344; uint16 b = 4096; uint16 c = 4096;
    uint16 r; unchecked { r = add16(a, b) + c; }; assert(r == 0); ⟩ true } := by
  sol_symex
  sol_close

end Solidity.Examples.Tactics.SolcOpen
