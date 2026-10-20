import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Casts between `uint` and `int`, and signed `unchecked`

solc's conversions keep the low bits of a value's two's complement word: a
`uintN` takes them as they are, an `intN` reads them signed.  The
elaborator writes each cast as a capture at its type through the two
conversions of `UnOp` (`int(u)`, `uint(i)`: the same 256-bit word, read
signed or unsigned), and signed `+ - *` inside `unchecked` as the cast of
the operation on the operands' words (`narrowWrapNode`, `castCapture`);
unary `-` is `0 -% x` on the word, `x / y` that negation where `y` is `-1`
(`-128 / -1` is `-128`, at `int256` too), and `x ** k` the words' power.
The cases are solkey's `SolcTypesOpen.sol` and `SolcArithmeticOpen.sol`
(solc's `smtCheckerTests/typecast` and `overflow`), true on the EVM.
-/

namespace Solidity.Examples.Tactics.SignedCasts

local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-! ## 1 · Casts -/

/-- `downcast.sol`: `int8(uint8(uint16(200)))` is `-56`, `uint8(int8(int16(300)))` is `44`. -/
theorem downcast : ⊨ dl!{ ⟨ int8 y = int8(uint8(uint16(200))); uint8 v = uint8(int8(int16(300)));
    int8 e = -56; assert(y == e); assert(v == 44); ⟩ true } := by
  sol_symex
  sol_close

/-- `same_size.sol`: `int8(uint8(200))` is `-56`, `uint8(int8(-100))` is `156`. -/
theorem sameSize : ⊨ dl!{ ⟨ int8 p = int8(uint8(200)); uint8 q = uint8(int8(-100));
    int8 e = -56; assert(p == e); assert(q == 156); ⟩ true } := by
  sol_symex
  sol_close

/-- `upcast.sol`: `int8(int(255))` wraps to `-1`, and widening keeps it. -/
theorem upcast : ⊨ dl!{ ⟨ int z = int(int8(int(255))); int e = -1; assert(z == e); ⟩ true } := by
  sol_symex
  sol_close

/-- `number_literal.sol`: `uint(-1)` is `2^256 - 1`. -/
theorem numberLiteral : ⊨ dl!{ ⟨ int d = -1; uint e = uint(d);
    assert(e == 115792089237316195423570985008687907853269984665640564039457584007913129639935); ⟩
    true } := by
  sol_symex
  sol_close

/-- `packing_signed_types.sol`: `int8(0xfa)` is `-6`. -/
theorem packingSigned : ⊨ dl!{ ⟨ uint8 x = 0xfa; int8 y = int8(x); int8 e = -6; assert(y == e); ⟩
    true } := by
  sol_symex
  sol_close

/-! ## 2 · Signed `unchecked` -/

/-- `overflow_sum_signed.sol`: at `int8`, `127 + 1` is `-128`, `127 + 127` is `-2`,
`-127 + -127` is `2`. -/
theorem uncheckedSum : ⊨ dl!{ ⟨ int8 x = 127; int8 y;
    unchecked { y = x + 1; }; int8 e1 = -128; assert(y == e1);
    unchecked { y = x + 127; }; int8 e2 = -2; assert(y == e2); ⟩ true } := by
  sol_symex
  sol_close

theorem uncheckedSumNeg : ⊨ dl!{ ⟨ int8 x = -127; int8 y;
    unchecked { y = x + -127; }; assert(y == 2); ⟩ true } := by
  sol_symex
  sol_close

/-- `overflow_mul_signed.sol`: at `int8`, `100 * 2` is `-56`. -/
theorem uncheckedMul : ⊨ dl!{ ⟨ int8 x = 100; int8 y; unchecked { y = x * 2; };
    int8 e = -56; assert(y == e); ⟩ true } := by
  sol_symex
  sol_close

/-- A compound assignment wraps the same way: `127 += 1` is `-128`. -/
theorem uncheckedCompound : ⊨ dl!{ ⟨ int8 x = 127; unchecked { x += 1; }; int8 e = -128;
    assert(x == e); ⟩ true } := by
  sol_symex
  sol_close

/-- `-(-128)` and `-128 / -1` at `int8` inside `unchecked`: each wraps to
`-128` (`-x` is `0 -% x` on the words, a quotient taken at `int` and read back). -/
theorem uncheckedNegDiv : ⊨ dl!{ ⟨ int8 x = -128; int8 m = -1; int8 y; int8 z;
    unchecked { y = -x; z = x / m; }; assert(y == x); assert(z == x); ⟩ true } := by
  sol_symex
  sol_close

/-- Signed `**` inside `unchecked`, the words' power: `(-2) ** 7` is `-128`,
`(-2) ** 8` wraps to `0` (`sol_decide`: `sol_close` reduces the
`2^256`-bit words' powers by `whnf`, past its budget). -/
theorem uncheckedPow : ⊨ dl!{ ⟨ int8 b = -2; int8 p; unchecked { p = b ** 7; }; int8 e = -128;
    assert(p == e); unchecked { p = b ** 8; }; assert(p == 0); ⟩ true } := by
  sol_symex
  sol_decide

/-- At `int256` too: `type(int).min / -1` and `-type(int).min` are `type(int).min`. -/
theorem uncheckedNegDiv256 : ⊨ dl!{ ⟨ int x = type(int).min; int m = -1; int y; int z;
    unchecked { y = -x; z = x / m; }; assert(y == x); assert(z == x); ⟩ true } := by
  sol_symex
  sol_close

/-- A quotient by another divisor is the checked one's: `-128 / 2` is `-64`. -/
theorem uncheckedDivOther : ⊨ dl!{ ⟨ int8 x = -128; int8 d = 2; int8 z; unchecked { z = x / d; };
    int8 e = -64; assert(z == e); ⟩ true } := by
  sol_symex
  sol_close

/-- Checked, the same operations revert (solc's `Panic(0x11)`). -/
theorem checkedNegReverts : ⊨ dl!{ [ int8 x = -128; int8 y = -x; ] false } := by
  sol_symex
  sol_close

theorem checkedDivReverts : ⊨ dl!{ [ int8 x = -128; int8 m = -1; int8 z = x / m; ] false } := by
  sol_symex
  sol_close

theorem checkedDiv256Reverts : ⊨ dl!{ [ int x = type(int).min; int m = -1; int z = x / m; ] false } := by
  sol_symex
  sol_close

/-! ## 3 · What the elaborator writes

(`#eval`, not `decide`: the kernel does not print a negative number.) -/

-- A cast of an `int8` to `uint8`: its word, cut to 8 bits; to `int8` from a
-- `uint8`: the 8 bits read signed.
/--
info: "int x = -1; uint se1 = uint(x) % 256; uint y = se1; int se2 = int(((y +% 128) % 256) -% 128); int z = se2;"
-/
#guard_msgs in #eval Prog.toStr [] (sol{ int8 x = -1; uint8 y = uint8(x); int8 z = int8(y); })

-- Signed `unchecked`: the operation on the words, read back at `int8`.
/--
info: "int x = 127; int y; uint se1 = uint(x); int se2 = int((((se1 -% 1) +% 128) % 256) -% 128); y = se2;"
-/
#guard_msgs in #eval Prog.toStr [] (sol{ int8 x = 127; int8 y; unchecked { y = x + -1; } })

-- Signed `-`, `/` and `**` inside `unchecked`: on the words, read back at `int8`.
/--
info: "int x = -128; int m = -1; int y; uint se1 = uint(x); int se2 = int((((0 -% se1) +% 128) % 256) -% 128); y = se2; int se3 = m; int se4 = x; int se5 = int(((uint(se4 / se3) +% 128) % 256) -% 128); y = se5; uint se6 = uint(x); int se7 = int((((se6 **% 3) +% 128) % 256) -% 128); y = se7;"
-/
#guard_msgs in #eval Prog.toStr [] (sol{ int8 x = -128; int8 m = -1; int8 y; unchecked { y = -x; y = x / m; y = x ** 3; } })

end Solidity.Examples.Tactics.SignedCasts
