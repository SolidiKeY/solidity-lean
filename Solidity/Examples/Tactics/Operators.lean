import Solidity.Calculus.Close
import Solidity.Evm.Examples

/-!
# Operators: bitwise, shifts, `unchecked`

The `uint` operators solkey has no taclet for, and the wrapping arithmetic of
an `unchecked { … }` block.  None needs a rule of its own: each is a `BinOp`
(or `UnOp`) constructor, so `binopAssignment`, `binopUnfoldLeft`/`Right` and
`unopAssignment` cover it at `op := .band` and so on, and the interpreter's
`applyBinOp` gives its meaning, solc's at `uint256`.

* `&`, `|`, `^`, `~`, `<<`, `>>` at `uint` only (`BinOp.accepts`): at `int`
  solc reads them in two's complement, which is left out.  Their precedence is
  solc's: `+ -` > `<< >>` > `&` > `^` > `|` > comparisons.  `&= |= ^= <<= >>=`
  are `x = x & e;` and so on, the target's effects captured first.
* `unchecked { … }` is not a statement: the elaborator writes its `+ - * **`
  as the wrapping `+% -% *% **%` (Zig's spelling, which the printers write
  and `sol{ … }` reads back), `x += e;` as `x = x +% e;`, `x++;` as
  `x = x +% 1;`.  A called function stays checked, as in solc.

Every obligation is proved by the strategy: `sol_symex` runs the rules,
`sol_close` the arithmetic.  The last section compiles the same operators to
`AND`/`OR`/`XOR`/`NOT`/`SHL`/`SHR`/`EXP` and runs them on the machine.
-/

namespace Solidity.Examples.Tactics.Operators

open Proves

local instance : InContract := ⟨StandardExample⟩

/-! ## Bitwise and shifts -/

/-- `12 & 10` is `8`, `12 | 10` is `14`, `12 ^ 10` is `6`. -/
theorem bitwise :
    ⊨ dl!{ ⟨ uint a = 12; uint b = 10; uint x = a & b; uint y = a | b; uint z = a ^ b; ⟩
      x == 8 && y == 14 && z == 6 } := by
  sol_symex
  sol_close

/-- `~0` is `2^256 - 1`, and `~x` of it is `0` again. -/
theorem complement :
    ⊨ dl!{ ⟨ uint a = 0; uint x = ~a; uint y = ~x; ⟩
      x == 115792089237316195423570985008687907853269984665640564039457584007913129639935 &&
      y == 0 } := by
  sol_symex
  sol_close

/-- `1 << 255` is `2^255`; one more shift wraps it to `0`, and a shift by `256`
or more is `0`; `x >> 3` divides by `8`. -/
theorem shifts :
    ⊨ dl!{ ⟨ uint a = 1; uint n = 255; uint x = a << n; uint y = x << a; uint z = a << 300;
             uint w = 100 >> 3; ⟩
      x == 57896044618658097711785492504343953926634992332820282019728792003956564819968 &&
      y == 0 && z == 0 && w == 12 } := by
  sol_symex
  sol_close

/-- solc's precedence: `1 + 2 << 3` is `(1 + 2) << 3`, `1 | 6 & 3` is
`1 | (6 & 3)`, `5 ^ 3 & 1` is `5 ^ (3 & 1)`, and `a & 1 == 0` compares
`a & 1`. -/
theorem precedence :
    ⊨ dl!{ ⟨ uint a = 1; uint b = 2; uint x = a + b << 3; uint y = a | 6 & 3;
             uint z = 5 ^ 3 & a; bool c = b & a == 0; ⟩
      x == 24 && y == 3 && z == 4 && c == true } := by
  sol_symex
  sol_close

/-- The compound forms: `x &= 6; x |= 1; x ^= 3; x <<= 2; x >>= 1;` from `13`. -/
theorem compound :
    ⊨ dl!{ ⟨ uint x = 13; x &= 6; x |= 1; x ^= 3; x <<= 2; x >>= 1; ⟩ x == 12 } := by
  sol_symex
  sol_close

/-- A compound target in storage, its index captured once: `balances[i++] |= 4;`
reads and writes `balances[0]`, and bumps `i` once. -/
theorem compoundStorage :
    ⊨ dl!{ [ uint i = 0; balances[0] = 3; balances[i++] |= 4; uint r = balances[0]; ]
      r == 7 && i == 1 } := by
  sol_symex
  sol_close

/-! ## `unchecked { … }`

The checked `x + 1` at `2^256 - 1` reverts, and has no terminating run
(`Values.overflowBox` and the diamond twin after it); inside
`unchecked` it wraps to `0`. -/

/-- `unchecked { x = x + 1; }` at `2^256 - 1` gives `0`. -/
theorem uncheckedAdd :
    ⊨ dl!{ ⟨ uint x = 115792089237316195423570985008687907853269984665640564039457584007913129639935;
             unchecked { x = x + 1; }; ⟩ x == 0 } := by
  sol_symex
  sol_close

/-- `0 - 1` wraps to `2^256 - 1`; `x++` and `x -= 2` wrap too; `2 ** 256` is `0`
and `2 ** 255 * 2` is `0`. -/
theorem uncheckedWrap :
    ⊨ dl!{ ⟨ uint x = 0; uint y; uint z = 2; uint p;
             unchecked { y = x - 1; y++; x -= 2; p = z ** 256 + z ** 255 * z; }; ⟩
      y == 0 &&
      x == 115792089237316195423570985008687907853269984665640564039457584007913129639934 &&
      p == 0 } := by
  sol_symex
  sol_close

/-- Division inside `unchecked` still reverts on a zero divisor. -/
example : ¬ (⊨ dl!{ ⟨ uint x = 1; uint y = 0; unchecked { x = x / y; }; ⟩ true }) :=
  fun h => h Semantics.State.exampleStore

/-! ## What the elaborator writes -/

/-- `unchecked` is its wrapping operators, printed as they read back. -/
example : Prog.toStr (sol{ uint x = 1; unchecked { x += 1; x = x * 2 - 1; x++; }; }) =
    "uint x = 1; x = x +% 1; x = (x *% 2) -% 1; x = x +% 1;" := by decide

/-- `&=` is `x = x & e;`. -/
example : Prog.toStr (sol{ uint x = 1; x &= ~x; x <<= 2; }) =
    "uint x = 1; x = x & ~x; x = x << 2;" := by decide

/-- error: Solidity elaboration failed: operator & does not take int -/
#guard_msgs in #check sol[TestSuite]{ int x = 1; x = x & x; }

/-- error: Solidity elaboration failed: operator +% does not take int -/
#guard_msgs in #check sol[TestSuite]{ int x = 1; unchecked { x = x + x; }; }

/-- error: Solidity elaboration failed: `++` or `−−` inside an expression in `unchecked` -/
#guard_msgs in #check sol{ uint i = 0; unchecked { values[i++] = 1; }; }

/-! ## On the machine

The operators compile to their opcodes with no guard (`uTail`), and the
compiler's correctness covers them (`tail_sim`). -/

open Evm in
/-- `total = 12 & 10 | 1 << 4;` stores `24`; `unchecked { total = total + 1; }`
at `2^256 - 1` stores `0`, where the checked `total += 1;` reverts. -/
theorem machine_run :
    Evm.Examples.storeAt (run (compileProg sol{ total = 12 & 10 | 1 << 4; }) Evm.Examples.fresh)
      (.root 0) = some 24 ∧
    Evm.Examples.storeAt (run (compileProg sol{
      total = 115792089237316195423570985008687907853269984665640564039457584007913129639935;
      unchecked { total = total + 1; }; }) Evm.Examples.fresh) (.root 0) = some 0 ∧
    Evm.Examples.storeAt (run (compileProg sol{ total = 0; total = ~total >> 255; total ^= 3; })
      Evm.Examples.fresh) (.root 0) = some 2 ∧
    Evm.Examples.storeAt (run (compileProg sol{ unchecked { total = 3 ** 2 - 10; }; })
      Evm.Examples.fresh) (.root 0) =
      some 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by
  decide

end Solidity.Examples.Tactics.Operators
