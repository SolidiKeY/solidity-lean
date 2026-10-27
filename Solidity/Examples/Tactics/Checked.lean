import Solidity.Calculus.RewriteChains
import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect

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


local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-! ## 1 · The runs

`260` is not a `uint8`: the box proves every postcondition, `false`
included — the calculus image of `Panic(0x11)` — and the diamond none. -/

/-- The example: the box holds of `false`. -/
theorem overflowBox : ⊨ᶠ dl!{ [ uint8 x = 250; x += 10; ] false } := by
  sol_symex
  sol_close

/-- … and the diamond of nothing. -/
theorem overflowDiamond : ¬ (⊨ᶠ dl!{ ⟨ uint8 x = 250; x += 10; ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail
    (h (State.init _)) (by decide +kernel)

/-- In range, the check passes: `250 + 5` is `255`. -/
theorem inRangeAdd : ⊨ᶠ dl!{ ⟨ uint8 x = 250; x += 5; ⟩ x == 255 } := by
  sol_symex
  sol_close

/-- `int8`'s floor is `-128`: `-100 - 28` reaches it, `-100 - 29` is below. -/
theorem int8Floor : ⊨ᶠ dl!{ ⟨ int8 y = -100; y -= 28; ⟩ y + 128 == 0 } := by
  sol_symex
  sol_close

theorem int8Underflow : ⊨ᶠ dl!{ [ int8 y = -100; y -= 29; ] false } := by
  sol_symex
  sol_close

example : ¬ (⊨ᶠ dl!{ ⟨ int8 y = -100; y -= 29; ⟩ true }) := fun h => Modality.afterRunTR_diamond_fail
    (h (State.init _)) (by decide +kernel)

/-- `++` and unary `-` are checked too: `255++`, and `-(-128)` at `int8`. -/
example : ¬ (⊨ᶠ dl!{ ⟨ uint8 i = 255; i++; ⟩ true }) := fun h => Modality.afterRunTR_diamond_fail
    (h (State.init _)) (by decide +kernel)
example : ¬ (⊨ᶠ dl!{ ⟨ int8 y = -128; int8 z = -y; ⟩ true }) := fun h => Modality.afterRunTR_diamond_fail
    (h (State.init _)) (by decide +kernel)

/-- `unchecked` wraps at `2^8`: `250 + 10` is `4`, `4 - 5` is `255`, `255 * 2` is `254`. -/
theorem uncheckedWrap :
    ⊨ᶠ dl!{ ⟨ uint8 x = 250; uint8 y; uint8 z; unchecked { x += 10; y = x - 5; z = y * 2; }; ⟩
      x == 4 && y == 255 && z == 254 } := by
  sol_symex
  sol_close

/-- An operation's type is its operands': `a + b` at `uint8` overflows although
`c` is a `uint` (solc checks it at `uint8`); with `a` cast to `uint` first it
does not. -/
example : ¬ (⊨ᶠ dl!{ ⟨ uint8 a = 200; uint8 b = 100; uint c = a + b; ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail
    (h (State.init _)) (by decide +kernel)

theorem widenedAdd : ⊨ᶠ dl!{ ⟨ uint8 a = 200; uint8 b = 100; uint c = uint(a) + b; ⟩ c == 300 } := by
  sol_symex
  sol_close

/-- Inside a condition the operation is captured and checked first. -/
example : ¬ (⊨ᶠ dl!{ ⟨ uint8 a = 200; bool t = a * 2 > a; ⟩ true }) :=
  fun h => Modality.afterRunTR_diamond_fail
    (h (State.init _)) (by decide +kernel)

/-- A narrowing cast keeps the low bits: `uint8(300)` of a `uint` is `44`. -/
theorem castTruncates : ⊨ᶠ dl!{ ⟨ uint w = 300; uint8 z = uint8(w); ⟩ z == 44 } := by
  sol_symex
  sol_close

/-- A narrow operation is checked only where solc evaluates it: under `&&`/`||`
when the left operand does not decide, in the branch of `c ? a : b` taken. -/
theorem shortCircuitUnchecked : ⊨ᶠ dl!{ ⟨ uint8 x = 255; bool b = false && x + 1 > 0;
    bool d = true || x + 1 > 0; ⟩ b == false && d == true } := by
  sol_symex
  sol_close

theorem shortCircuitChecked : ⊨ᶠ dl!{ [ uint8 x = 255; bool b = true && x + 1 > 0; ] false } := by
  sol_symex
  sol_close

theorem ternaryBranchUntaken : ⊨ᶠ dl!{ ⟨ uint8 x = 255; bool c = false; uint8 y = c ? x + 1 : x; ⟩
    y == 255 } := by
  sol_symex
  sol_close

theorem ternaryBranchTaken : ⊨ᶠ dl!{ [ uint8 x = 255; bool c = true; uint8 y = c ? x + 1 : x; ] false } := by
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
theorem addInRange : ⊨ᶠ dl[Narrow]{ ⟨ uint8 r = add(250, 5); ⟩ r == 255 } := by
  sol_symex
  sol_close

theorem addOverflows : ⊨ᶠ dl[Narrow]{ [ uint8 r = add(250, 6); ] false } := by
  sol_symex
  sol_close

/-- A narrow state variable: `level += 6` at `250` reverts. -/
theorem raiseOverflows : ⊨ᶠ dl[Narrow]{ [ level = 250; uint8 r = raise(6); ] false } := by
  sol_symex
  sol_close

/-- The mean of two `uint8`s, the sum taken at `uint`: `avg(255, 255)` is `255`. -/
theorem avgWidened : ⊨ᶠ dl[Narrow]{ ⟨ uint8 m = avg(255, 255); ⟩ m == 255 } := by
  sol_symex
  sol_close

/-! ### Narrow types inside a state variable's type

An array's element, a mapping's key or value: the position has its width,
kept beside the variable's (`Contract.widths`, keyed `small[]`, `byKey{}`),
so a read of it has that type and a write is checked, or wrapped, at it. -/

/-- A contract with narrow elements, values and keys. -/
def NarrowNested : Contract := contract!{
  uint8[] small;
  mapping(uint => int8) temps;
  mapping(uint8 => uint) byKey;
  uint16[3] fixedW;
  mapping(uint => uint8[]) lists;
  mapping(uint => uint16) wide;
  mapping(uint => mapping(uint => uint8)) grid;
}

example : NarrowNested.widths =
    [("small[]", 8), ("temps[]", 8), ("byKey{}", 8), ("fixedW[]", 16), ("lists[][]", 8),
     ("wide[]", 16), ("grid[][]", 8)] := rfl

/-- A mapping's narrow value: `-100 - 29` leaves `int8`, `-100 - 28` does not. -/
theorem valueUnderflows : ⊨ᶠ dl[NarrowNested]{ [ temps[1] = -100; temps[1] -= 29; ] false } := by
  sol_symex
  sol_close

theorem valueInRange : ⊨ᶠ dl[NarrowNested]{ ⟨ temps[1] = -100; temps[1] -= 28; int8 e = -128;
    assert(temps[1] == e); ⟩ true } := by
  sol_symex
  sol_close

/-- A narrow element read has its type: `60000 + 60000` overflows at `uint16`. -/
theorem elementOpType : ⊨ᶠ dl[NarrowNested]{ [ wide[0] = 60000; uint w = wide[0] + wide[0]; ]
    false } := by
  sol_symex
  sol_close

/-- … and wraps at it inside `unchecked`. -/
theorem elementWraps : ⊨ᶠ dl[NarrowNested]{ ⟨ wide[1] = 65535; unchecked { wide[1] += 1; };
    assert(wide[1] == 0); ⟩ true } := by
  sol_symex
  sol_close

/-- A nested value: `200 + 100` at `uint8`. -/
theorem nestedElementOverflows : ⊨ᶠ dl[NarrowNested]{ [ grid[2][3] = 200; grid[2][3] += 100; ]
    false } := by
  sol_symex
  sol_close

/-- A narrow key: an index converts to it implicitly, so it fits. -/
theorem narrowKey : ⊨ᶠ dl[NarrowNested]{ ⟨ uint8 k = 7; byKey[k] = 1; byKey[255] = 2;
    assert(byKey[7] == 1); ⟩ true } := by
  sol_symex
  sol_close

/-! ### Struct members, locals, parameters and modifiers

A struct's narrow member has its width (`structWidths`: `struct Packed {
uint8 a; int16 b; uint c; uint8[] xs; }`), in storage, in memory and as an
element.  A storage alias, a memory local and a reference parameter carry the
narrow positions of their type in the binding (`LocalTy.shape`), so a copy or an
alias of `small` is a `uint8[]` too; one of another shape is refused, as solc
refuses it.  A modifier's narrow parameter is a local of its type. -/

/-- A contract with a struct of narrow members, and narrow reference parameters. -/
def NarrowShapes : Contract := contract!{
  uint8[] small;
  uint[] wide;
  Packed p;
  Packed[] ps;
  mapping(uint => Packed) byId;
  modifier atMost(uint8 cap) { require(cap > 1); _; }
  function sum(uint8[] memory xs) returns (uint8 r) { r = xs[0] + xs[1]; }
  function bump(uint8[] storage xs) { xs[0] += 1; }
  function capped(uint8 c) atMost(c) returns (uint8 r) { r = c; }
  function badCap() atMost(300) returns (uint8 r) { r = 1; }
}

/-- A member of a storage struct: `250 + 6` leaves `uint8`. -/
theorem memberOverflows : ⊨ᶠ dl[NarrowShapes]{ [ p.a = 250; p.a += 6; ] false } := by
  sol_symex
  sol_close

theorem memberInRange : ⊨ᶠ dl[NarrowShapes]{ ⟨ p.b = -32768; p.b += 32767; int16 e = -1;
    assert(p.b == e); ⟩ true } := by
  sol_symex
  sol_close

/-- A struct as a mapping's value, and a narrow array inside a struct. -/
theorem valueMemberOverflows : ⊨ᶠ dl[NarrowShapes]{ [ byId[1].a = 200; byId[1].a += 100; ] false } := by
  sol_symex
  sol_close

theorem memberArrayOverflows : ⊨ᶠ dl[NarrowShapes]{ [ p.xs[0] = 255; p.xs[0] += 1; ] false } := by
  sol_symex
  sol_close

/-- A struct in memory. -/
theorem memoryMemberOverflows : ⊨ᶠ dl[NarrowShapes]{ [ Packed memory q; q.a = 255; q.a++; ] false } := by
  sol_symex
  sol_close

/-- A storage alias of `small` is a `uint8[]`: `s[0]` reverts, past the end or
at `256`. -/
theorem aliasOverflows : ⊨ᶠ dl[NarrowShapes]{ [ uint8[] storage s = small; s[0] = 255; s[0] += 1; ]
    false } := by
  sol_symex
  sol_close

/-- A memory array of `uint8`, allocated or copied from `small`. -/
theorem memoryOverflows : ⊨ᶠ dl[NarrowShapes]{ [ uint8[] memory m = new uint8[](2); m[0] = 255;
    m[0] += 1; ] false } := by
  sol_symex
  sol_close

theorem copyOverflows : ⊨ᶠ dl[NarrowShapes]{ [ uint8[] memory m = small; m[0] = 255; m[0]++; ]
    false } := by
  sol_symex
  sol_close

/-- A memory parameter and a storage parameter of `uint8[]`. -/
theorem paramOverflows : ⊨ᶠ dl[NarrowShapes]{ [ uint8[] memory m = new uint8[](2); m[0] = 200;
    m[1] = 100; uint8 r = sum(m); ] false } := by
  sol_symex
  sol_close

theorem storageParamOverflows : ⊨ᶠ dl[NarrowShapes]{ [ small[0] = 255; bump(small); ] false } := by
  sol_symex
  sol_close

/-! Whole uses whose narrow positions are checked: a conditional's branches
(each against the target, `shapeCheck`; `tests/solc/NarrowNested.sol` proves
`ternaryAliasPanics`), a struct constructor's arguments, positional or named
(each against its member, by the member write it is written as): the
member's element is checked at `uint8`. -/

/--
info: "bool c = true; uint[] storage sp1; if (c) { sp1 = small; } else { sp1 = small; } uint[] storage s = sp1; s[0] += 1; require(s[0] <= 255);"
-/
#guard_msgs in #eval Prog.toStr [] (sol[NarrowShapes]{ bool c = true;
  uint8[] storage s = c ? small : small; s[0] += 1; })

/--
info: "uint[] memory m = new uint[](1); Packed memory mv1; mv1.a = 1; mv1.b = 2; mv1.c = 3; mv1.xs = m; Packed memory q = mv1; q.xs[0] += 1; require(q.xs[0] <= 255);"
-/
#guard_msgs in #eval Prog.toStr [] (sol[NarrowShapes]{ uint8[] memory m = new uint8[](1);
  Packed memory q = Packed({xs: m, a: 1, b: 2, c: 3}); q.xs[0] += 1; })

/-- A modifier's narrow parameter. -/
theorem modifierParam : ⊨ᶠ dl[NarrowShapes]{ ⟨ uint8 r = capped(5); ⟩ r == 5 } := by
  sol_symex
  sol_close

/-! ## 3 · What the elaborator writes -/

-- An operation's check follows its write, on the variable written: at `int8`
-- both bounds (the kernel does not print a negative number: `#eval`, not `decide`).
/--
info: "int y = -100; y -= 50; require((-128 <= y) && (y <= 127)); int z = -y; require((-128 <= z) && (z <= 127));"
-/
#guard_msgs in #eval Prog.toStr [] (sol{ int8 y = -100; y -= 50; int8 z = -y; })

/-- Checked at the operation's type, which is its operands', not the target's. -/
example : Prog.toStr [] (sol{ uint8 a = 200; uint8 b = 100; uint c = a + b; uint16 d = a; d = d * b; }) =
    "uint a = 200; uint b = 100; uint c = a + b; require(c <= 255); uint d = a; d = d * b; " ++
    "require(d <= 65535);" := by decide

/-- Inside an expression, captured with its check before the statement. -/
example : Prog.toStr [] (sol{ uint8 a = 1; bool t = a + 1 > 3; if (a * 2 > a) { a = 0; } }) =
    "uint a = 1; uint se1 = a + 1; require(se1 <= 255); bool t = se1 > 3; uint se2 = a * 2; " ++
    "require(se2 <= 255); if (se2 > a) { a = 0; } else { }" := by decide

/-- `++` and `−−`, as a statement and inside an expression. -/
example : Prog.toStr [] (sol{ uint8 i = 0; i++; uint8 j = i++; uint k = ++i + 1; }) =
    "uint i = 0; i++; require(i <= 255); uint se1; se1 = i++; require(i <= 255); uint j = se1; " ++
    "uint se2; se2 = ++i; require(i <= 255); uint k = se2 + 1; require(k <= 255);" := by decide

/-- `unchecked`, `~` and `<<` at `uint8`: modulo `2^8`. -/
example : Prog.toStr [] (sol{ uint8 x = 255; unchecked { x += 1; x = x * 3 - 7; x++; x = ~x; } x <<= 1; }) =
    "uint x = 255; x = (x +% 1) % 256; x = (((x *% 3) % 256) -% 7) % 256; x = (x +% 1) % 256; " ++
    "x = 255 -% x; x = (x << 1) % 256;" := by decide

/-- A cast is a capture at its type: `% 2^N` narrowing a `uint`, the value as it
is widening one. -/
example : Prog.toStr [] (sol{ uint8 z = uint8(total); uint16 w = uint16(z) + 300; total = uint(z) + 1; }) =
    "uint se1 = total % 256; uint z = se1; uint se2 = z; uint w = se2 + 300; require(w <= 65535); " ++
    "uint se3 = z; total = se3 + 1;" := by decide

/-- error: Solidity elaboration failed: 300 does not fit uint8 -/
#guard_msgs in #check sol{ uint8 z = 200 + 100; }

/-- error: Solidity elaboration failed: a uint where a uint8 is expected: write uint8(…) -/
#guard_msgs in #check sol{ uint8 x = total; }

/-- error: Solidity elaboration failed: 300 does not fit uint8 -/
#guard_msgs in #check sol{ uint8 x = 300; }

/-- error: Solidity elaboration failed: 300 does not fit uint8 -/
#guard_msgs in #check sol{ uint8 x = 1; x = x + 300; }

/-- Narrow arithmetic under `&&` is checked only where solc evaluates it: in
the branch the left operand takes. -/
example : Prog.toStr [] (sol{ uint8 x = 1; bool b = true && x + 1 > 0; } :
    Prog StandardExample [] _) =
    "uint x = 1; bool se1 = true; if (se1) { uint se2 = x + 1; require(se2 <= 255); se1 = se2 > 0; } else { } bool b = se1;" := by
  decide

/-- … and in a conditional's branch: a capture assigned in each branch, the
check in the branch that computes it. -/
example : Prog.toStr [] (sol{ uint8 x = 1; bool c = true; uint8 y = c ? x + 1 : x; } :
    Prog StandardExample [] _) =
    "uint x = 1; bool c = true; uint se1; if (c) { se1 = x + 1; require(se1 <= 255); } else { se1 = x; } uint y = se1;" := by
  decide


-- A cast between `uint` and `int`, one narrowing an `int`, and signed
-- `unchecked`: through the words (`Examples/Tactics/SignedCasts.lean`).
/--
info: "int x = 1; uint se1 = uint(x) % 256; uint y = se1; int se2 = int(((uint(x) +% 128) % 256) -% 128); int z = se2; x = z;"
-/
#guard_msgs in #eval Prog.toStr [] (sol{ int16 x = 1; uint8 y = uint8(x); int8 z = int8(x); x = z; })

/--
info: "int x = 1; uint se1 = uint(x); int se2 = int((((se1 +% 1) +% 128) % 256) -% 128); x = se2;"
-/
#guard_msgs in #eval Prog.toStr [] (sol{ int8 x = 1; unchecked { x += 1; } })

/-- error: Solidity elaboration failed: wide returns a uint16, where a uint8 is expected -/
#guard_msgs in #check sol[Narrow]{ uint8 t = wide(1); }

-- A narrow position's operation is checked on the position written.
/--
info: "temps[1] = -100; temps[1] -= 28; require((-128 <= temps[1]) && (temps[1] <= 127)); small.push(3);"
-/
#guard_msgs in #eval Prog.toStr [] (sol[NarrowNested]{ temps[1] = -100; temps[1] -= 28; small.push(3); })

/-- error: Solidity elaboration failed: 200 does not fit int8 -/
#guard_msgs in #check sol[NarrowNested]{ temps[1] = 200; }

/-- error: Solidity elaboration failed: a uint where a uint8 is expected: write uint8(…) -/
#guard_msgs in #check sol[NarrowNested]{ small.push(total); }

/-- error: Solidity elaboration failed: 300 does not fit uint8 -/
#guard_msgs in #check sol[NarrowNested]{ byKey[300] = 1; }

/-- error: Solidity elaboration failed: a uint where a uint8 is expected: write uint8(…) -/
#guard_msgs in #check sol[NarrowNested]{ uint k = 1; byKey[k] = 1; }

/-- A part with a narrow position below it is used through an index, a member,
`delete`, or whole where its narrow positions are checked against the
target's: a reference type has no width to carry them. -/
example : Prog.toStr [] (sol[NarrowNested]{ delete small; small.pop(); uint n = small.length; }) =
    "delete small; small.pop(); uint n = small.length;" := by decide

-- Tuple capture must retain exactly the same narrow source/target check.
/--
error: Solidity elaboration failed: small has narrow positions ·[] 8 bits wide where none are expected: solc converts no reference type to one of another element type
-/
#guard_msgs in #check sol[NarrowNested]{ uint[] storage p; uint k; (p, k) = (small, 1); }

-- A reference local of another shape: solc refuses the conversion too.
/--
error: Solidity elaboration failed: small has narrow positions ·[] 8 bits wide where none are expected: solc converts no reference type to one of another element type
-/
#guard_msgs in #check sol[NarrowNested]{ uint[] storage p = small; }

/--
error: Solidity elaboration failed: new uint[](2) has narrow positions none where ·[] 8 bits wide are expected: solc converts no reference type to one of another element type
-/
#guard_msgs in #check sol[NarrowShapes]{ uint8[] memory m = new uint[](2); }

-- An argument captured before the call is named as written.
/--
error: Solidity elaboration failed: m has narrow positions none where ·[] 8 bits wide are expected: solc converts no reference type to one of another element type
-/
#guard_msgs in #check sol[NarrowShapes]{ uint[] memory m = new uint[](2); uint8 r = sum(m); }

/--
error: Solidity elaboration failed: c ? small : wide has a narrow element, key or value: it is used through an index, `.length`, `.push`, `.pop` or `delete`, or whole where the same narrow positions are expected, not whole
-/
#guard_msgs in #check sol[NarrowShapes]{ bool c = true; bump(c ? small : wide); }

-- A conditional's branches of another shape than each other: solc has no common type.
/--
error: Solidity elaboration failed: small has narrow positions ·[] 8 bits wide where none are expected: solc converts no reference type to one of another element type
-/
#guard_msgs in #check sol[NarrowShapes]{ bool c = true; uint[] storage s = c ? wide : small; }

-- A struct constructor's argument of another shape than its member's.
/--
error: Solidity elaboration failed: w has narrow positions none where ·[] 8 bits wide are expected: solc converts no reference type to one of another element type
-/
#guard_msgs in #check sol[NarrowShapes]{ uint[] memory w = new uint[](1); Packed memory q = Packed(1, 2, 3, w); }

-- A struct's narrow member, and a modifier's narrow parameter, must fit.
/--
error: Solidity elaboration failed: 300 does not fit uint8
-/
#guard_msgs in #check sol[NarrowShapes]{ p.a = 300; }

/--
error: Solidity elaboration failed: 300 does not fit uint8
-/
#guard_msgs in #check sol[NarrowShapes]{ uint8 r = badCap(); }

-- A member's operation is checked at the member's type.
/--
info: "p.a += 6; require(p.a <= 255); Packed memory q; int se1 = q.b * 2; require((-32768 <= se1) && (se1 <= 32767)); q.b = se1;"
-/
#guard_msgs in #eval Prog.toStr [] (sol[NarrowShapes]{ p.a += 6; Packed memory q; q.b = q.b * 2; })

end Solidity.Examples.Tactics.Checked
