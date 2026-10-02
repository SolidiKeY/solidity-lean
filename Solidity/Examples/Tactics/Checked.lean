import Solidity.Calculus.Chains
import Solidity.Calculus.Close

/-!
# Checked arithmetic at the narrow widths

`uint8 x = 250; x += 10;` (its trace is `Examples/Chains/CheckedArithmetic.lean`'s), and the
rest of `uint8` … `uint248`, `int8` … `int248`.  A narrow type is not a type
of the syntax: the elaborator reads `uint8 x` as a `uint` 8 bits wide
(`narrowTy?`, `Syntax.lean`) and writes solc's range check where solc panics,
as a `require` of `inTy(uint8, e)` after the operation's write
(`narrowPost`): `x += 10;` is `x += 10; require(x <= 255);`.  A revert discards
the write, so checking after it is checking before it, and the guarded rule
sketched (`arith-checked-local`) is `localOpAssign` followed by
`requireSimple`'s two goals — no rule of its own, and nothing below the
elaborator changed.  An operation inside an expression is captured with its
check before the statement (`narrowCapture`), `unchecked` wraps modulo `2^N`,
and a cast is a capture at its type.  What is not modelled is in
`docs/solc-alignment.md`.

* §1 — the runs: overflow and underflow revert, in range and `unchecked` do not;
* §2 — state variables and functions of a narrow type;
* §3 — what the elaborator writes, and what it refuses.
-/

namespace Solidity.Examples.Tactics.Checked

open Proves

local instance : InContract := ⟨StandardExample⟩

/-! ## 1 · The runs

`260` is not a `uint8`: the box proves every postcondition, `false`
included — the calculus image of `Panic(0x11)` — and the diamond none. -/

/-- The example: the box holds of `false`. -/
theorem overflowBox : ⊨ dl!{ [ uint8 x = 250; x += 10; ] false } := by
  sol_symex
  sol_close

/-- … and the diamond of nothing. -/
theorem overflowDiamond : ¬ (⊨ dl!{ ⟨ uint8 x = 250; x += 10; ⟩ true }) :=
  fun h => h Semantics.State.exampleStore

/-- In range, the check passes: `250 + 5` is `255`. -/
theorem inRangeAdd : ⊨ dl!{ ⟨ uint8 x = 250; x += 5; ⟩ x == 255 } := by
  sol_symex
  sol_close

/-- `int8`'s floor is `-128`: `-100 - 28` reaches it, `-100 - 29` is below. -/
theorem int8Floor : ⊨ dl!{ ⟨ int8 y = -100; y -= 28; ⟩ y + 128 == 0 } := by
  sol_symex
  sol_close

theorem int8Underflow : ⊨ dl!{ [ int8 y = -100; y -= 29; ] false } := by
  sol_symex
  sol_close

example : ¬ (⊨ dl!{ ⟨ int8 y = -100; y -= 29; ⟩ true }) := fun h => h Semantics.State.exampleStore

/-- `++` and unary `-` are checked too: `255++`, and `-(-128)` at `int8`. -/
example : ¬ (⊨ dl!{ ⟨ uint8 i = 255; i++; ⟩ true }) := fun h => h Semantics.State.exampleStore
example : ¬ (⊨ dl!{ ⟨ int8 y = -128; int8 z = -y; ⟩ true }) := fun h => h Semantics.State.exampleStore

/-- `unchecked` wraps at `2^8`: `250 + 10` is `4`, `4 - 5` is `255`, `255 * 2` is `254`. -/
theorem uncheckedWrap :
    ⊨ dl!{ ⟨ uint8 x = 250; uint8 y; uint8 z; unchecked { x += 10; y = x - 5; z = y * 2; }; ⟩
      x == 4 && y == 255 && z == 254 } := by
  sol_symex
  sol_close

/-- An operation's type is its operands': `a + b` at `uint8` overflows although
`c` is a `uint` (solc checks it at `uint8`); with `a` cast to `uint` first it
does not. -/
example : ¬ (⊨ dl!{ ⟨ uint8 a = 200; uint8 b = 100; uint c = a + b; ⟩ true }) :=
  fun h => h Semantics.State.exampleStore

theorem widenedAdd : ⊨ dl!{ ⟨ uint8 a = 200; uint8 b = 100; uint c = uint(a) + b; ⟩ c == 300 } := by
  sol_symex
  sol_close

/-- Inside a condition the operation is captured and checked first. -/
example : ¬ (⊨ dl!{ ⟨ uint8 a = 200; bool t = a * 2 > a; ⟩ true }) :=
  fun h => h Semantics.State.exampleStore

/-- A narrowing cast keeps the low bits: `uint8(300)` of a `uint` is `44`. -/
theorem castTruncates : ⊨ dl!{ ⟨ uint w = 300; uint8 z = uint8(w); ⟩ z == 44 } := by
  sol_symex
  sol_close

/-! ## 2 · State variables and functions

A state variable, a parameter and a return variable carry their width
(`Contract.widths`, `FunDecl.widths`); an inlined call checks its body at the
declared widths. -/

/-- A contract with narrow state variables and functions. -/
def Narrow : Contract := contract!{
  uint8 level;
  int16 temp;
  function raise(uint8 d) returns (uint8 r) { level += d; r = level; }
  function avg(uint8 a, uint8 b) returns (uint8 m) { m = uint8((uint(a) + b) / 2); }
  function wide(uint8 a) returns (uint16 w) { w = a; }
  function add(uint8 a, uint8 b) returns (uint8 r) { r = a + b; }
}

example : Narrow.widths = [("level", 8), ("temp", 16)] := rfl

/-- A narrow parameter and return: `add(250, 5)` is `255`, `add(250, 6)` reverts. -/
theorem addInRange : ⊨ dl[Narrow]{ ⟨ uint8 r = add(250, 5); ⟩ r == 255 } := by
  sol_symex
  sol_close

theorem addOverflows : ⊨ dl[Narrow]{ [ uint8 r = add(250, 6); ] false } := by
  sol_symex
  sol_close

/-- A narrow state variable: `level += 6` at `250` reverts. -/
theorem raiseOverflows : ⊨ dl[Narrow]{ [ level = 250; uint8 r = raise(6); ] false } := by
  sol_symex
  sol_close

/-- The mean of two `uint8`s, the sum taken at `uint`: `avg(255, 255)` is `255`. -/
theorem avgWidened : ⊨ dl[Narrow]{ ⟨ uint8 m = avg(255, 255); ⟩ m == 255 } := by
  sol_symex
  sol_close

/-! ## 3 · What the elaborator writes -/

-- An operation's check follows its write, on the variable written: at `int8`
-- both bounds (the kernel does not print a negative number: `#eval`, not `decide`).
/--
info: "int y = -100; y -= 50; require((-128 <= y) && (y <= 127)); int z = -y; require((-128 <= z) && (z <= 127));"
-/
#guard_msgs in #eval Prog.toStr (sol{ int8 y = -100; y -= 50; int8 z = -y; })

/-- Checked at the operation's type, which is its operands', not the target's. -/
example : Prog.toStr (sol{ uint8 a = 200; uint8 b = 100; uint c = a + b; uint16 d = a; d = d * b; }) =
    "uint a = 200; uint b = 100; uint c = a + b; require(c <= 255); uint d = a; d = d * b; " ++
    "require(d <= 65535);" := by decide

/-- Inside an expression, captured with its check before the statement. -/
example : Prog.toStr (sol{ uint8 a = 1; bool t = a + 1 > 3; if (a * 2 > a) { a = 0; } }) =
    "uint a = 1; uint se1 = a + 1; require(se1 <= 255); bool t = se1 > 3; uint se2 = a * 2; " ++
    "require(se2 <= 255); if (se2 > a) { a = 0; } else {  }" := by decide

/-- `++` and `−−`, as a statement and inside an expression. -/
example : Prog.toStr (sol{ uint8 i = 0; i++; uint8 j = i++; uint k = ++i + 1; }) =
    "uint i = 0; i++; require(i <= 255); uint se1; se1 = i++; require(i <= 255); uint j = se1; " ++
    "uint se2; se2 = ++i; require(i <= 255); uint k = se2 + 1; require(k <= 255);" := by decide

/-- `unchecked`, `~` and `<<` at `uint8`: modulo `2^8`. -/
example : Prog.toStr (sol{ uint8 x = 255; unchecked { x += 1; x = x * 3 - 7; x++; x = ~x; } x <<= 1; }) =
    "uint x = 255; x = (x +% 1) % 256; x = (((x *% 3) % 256) -% 7) % 256; x = (x +% 1) % 256; " ++
    "x = 255 -% x; x = (x << 1) % 256;" := by decide

/-- A cast is a capture at its type: `% 2^N` narrowing a `uint`, the value as it
is widening one. -/
example : Prog.toStr (sol{ uint8 z = uint8(total); uint16 w = uint16(z) + 300; total = uint(z) + 1; }) =
    "uint se1 = total % 256; uint z = se1; uint se2 = z; uint w = se2 + 300; require(w <= 65535); " ++
    "uint se3 = z; total = se3 + 1;" := by decide

/-- Arithmetic on literals alone, which solc folds and refuses, is checked at
run time. -/
example : Prog.toStr (sol{ uint8 z = 200 + 100; }) = "uint z = 200 + 100; require(z <= 255);" := by decide

/-- error: Solidity elaboration failed: a uint where a uint8 is expected: write uint8(…) -/
#guard_msgs in #check sol{ uint8 x = total; }

/-- error: Solidity elaboration failed: 300 does not fit uint8 -/
#guard_msgs in #check sol{ uint8 x = 300; }

/-- error: Solidity elaboration failed: 300 does not fit uint8 -/
#guard_msgs in #check sol{ uint8 x = 1; x = x + 300; }

/-- error: Solidity elaboration failed: narrow arithmetic under a short-circuit operator: its check would run where the program does not evaluate it -/
#guard_msgs in #check sol{ uint8 x = 1; bool b = true && x + 1 > 0; }

/-- error: Solidity elaboration failed: uint8: a narrow integer type is the type of a local, a parameter, a return value or a state variable only, not of an array's element, a mapping's key or value, or a struct's member -/
#guard_msgs in #check sol{ uint8[] storage x; }

/-- error: Solidity elaboration failed: uint8(x): a cast between uint and int is not modelled -/
#guard_msgs in #check sol{ int8 x = 1; uint8 y = uint8(x); }

/-- error: Solidity elaboration failed: int8(x): a cast narrowing an int is not modelled -/
#guard_msgs in #check sol{ int16 x = 1; int8 y = int8(x); }

/-- error: Solidity elaboration failed: operator +% does not take int -/
#guard_msgs in #check sol{ int8 x = 1; unchecked { x += 1; } }

/-- error: Solidity elaboration failed: wide returns a uint16, where a uint8 is expected -/
#guard_msgs in #check sol[Narrow]{ uint8 t = wide(1); }

end Solidity.Examples.Tactics.Checked
