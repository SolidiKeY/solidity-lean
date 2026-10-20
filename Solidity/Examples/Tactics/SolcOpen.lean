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
  `unchecked` wraps at `2^16` (`intTyOf`);
* `type(T).max` and `type(T).min` are values of `T` (`uint8(255)`, so
  `type(uint8).max + 1` overflows at `uint8`), an enum's its last and first
  member (`typeBoundExpr`, `enumLit?`);
* a conditional of two literals has the smallest type holding both, solc's
  mobile type (`mobileTy`): `(t ? 63 : 255) + (f ? 63 : 255)` is a `uint8`
  addition, and overflows.
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

/-! ## 3 · `type(T).max`, `type(T).min` -/

/-- A bound is a cast of the literal: a value of `T`. -/
example : Prog.toStr [] (sol{ uint8 a = type(uint8).max; uint e = type(D).max; }) =
    "uint se1 = 255; uint a = se1; uint e = 1;" := rfl

theorem typeBounds : ⊨ dl!{ ⟨ uint8 a = type(uint8).max; int8 b = type(int8).min;
    uint e = type(D).max; uint f = type(D).min; int8 m = -128; int g = type(int).min + 1;
    assert(a == 255); assert(b == m); assert(e == D.Right); assert(f == D.Left);
    assert(g + 57896044618658097711785492504343953926634992332820282019728792003956564819967 == 0); ⟩
    true } := by
  sol_symex
  sol_close

/-- `type(uint8).max + 1` is a `uint8` addition: it overflows although `y` is a
`uint` (`SourceTypes.sol`'s `narrowOverflowPanics`). -/
theorem typeMaxOverflows : ⊨ dl!{ [ uint y = type(uint8).max + 1; ] false } := by
  sol_symex
  sol_close

/-! ## 4 · A conditional of literals

`ternary_operator_with_literal_types_overflow.sol` (`SolcTypesOpen.sol`'s
`ternaryLiteralOverflow`): `t ? 63 : 255` is a `uint8`, so the sum of two is
checked at `uint8`, and `63 + 255` reverts (solc's `Panic(0x11)`).  The
claim the port states, that `r == 318`, is false on the EVM. -/

example : Prog.toStr [] (sol{ bool t = true; bool f = false; uint16 r = (t ? 63 : 255) + (f ? 63 : 255);
    assert(r == 318); } : Prog Open [] _) =
    "bool t = true; bool f = false; uint r = (t ? 63 : 255) + (f ? 63 : 255); require(r <= 255); " ++
    "assert(r == 318);" := rfl

/-- The typed run reverts. -/
theorem ternaryLiteral_reverts : (Prog.run (State.init Open) (sol{ bool t = true; bool f = false;
    uint16 r = (t ? 63 : 255) + (f ? 63 : 255); assert(r == 318); } : Prog Open [] _)).halt? =
    some .revert := by
  decide +kernel

/-- So the port's diamond is not valid. -/
theorem ternaryLiteralOverflow :
    ¬ (⊨ dl!{ ⟨ bool t = true; bool f = false; uint16 r = (t ? 63 : 255) + (f ? 63 : 255);
      assert(r == 318); ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail (h (State.init _)) (by decide +kernel)

/-- Inside `unchecked` the `uint8` sum wraps: `63 + 255` is `62`. -/
theorem ternaryLiteralWraps : ⊨ dl!{ ⟨ bool t = true; bool f = false; uint16 r;
    unchecked { r = (t ? 63 : 255) + (f ? 63 : 255); }; assert(r == 62); ⟩ true } := by
  sol_symex
  sol_close

/-- A literal that needs more bits widens the conditional: `t ? 63 : 256` is a
`uint16`, and so is the sum. -/
theorem ternaryLiteralWide : ⊨ dl!{ ⟨ bool t = true; bool f = false;
    uint16 r = (t ? 63 : 256) + (f ? 63 : 255); assert(r == 318); ⟩ true } := by
  sol_symex
  sol_close

end Solidity.Examples.Tactics.SolcOpen
