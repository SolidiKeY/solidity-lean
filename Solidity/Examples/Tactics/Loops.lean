import Solidity.Tools.Run
import Solidity.Tools.Inspect

/-!
# Loops

`while`, `for`, `do … while`, `break`, `continue` and a `return` inside a
loop (`docs/loops.md`).  The elaborator lowers them to `Stmt.loop`, solkey's
lowered `while`, by solkey's `LoopLowering` (`lowerLoops`): the flags `brk`,
`cnt`, `ret`, made only when used; the pins below are its shapes.  A loop
runs as the least fixed point of its unwinding (`Loop.run`), so `#run` runs
it and a concrete one is decided by `Prog.run_loop_of_iterN`.  No rule of the
calculus proves anything about a loop yet: it closes to `false`
(`LeanTaclet.whileClose`).
-/

namespace Solidity.Examples.Loops

open Semantics

local instance : InContract := ⟨StandardExample⟩

/-! ## The lowering

A loop with no jump keeps its condition.  `continue` sets `cnt`, declared at
the head of each iteration; `break` sets `brk`, declared before the loop and
tested by its condition; the rest of a block after a statement that may set
a flag runs under `if (!flag…)`, and a `for`'s update under the flags that
end the loop, so that `continue` still runs it. -/

/-- info: uint i = 0;
while (i < 3) { i++; } -/
#guard_msgs in
#eval IO.println (Prog.show (sol{ uint i = 0; while (i < 3) { i++; } }))

/-- info: uint s = 0;
uint i = 0;
bool brk2 = false;
while (!brk2 && (i < 9)) { bool cnt1 = false; if (i == 1) { cnt1 = true; } else {  } if (!cnt1) { if (i == 5) { brk2 = true; } else {  } if (!brk2) { s += i; } else {  } } else {  } if (!brk2) { i++; } else {  } } -/
#guard_msgs in
#eval IO.println (Prog.show (sol{ uint s = 0;
  for (uint i = 0; i < 9; i++) { if (i == 1) { continue; } if (i == 5) { break; } s += i; } }))

/-! `do body while (c)` runs the body once before the condition, by a flag
`first`: the body is not copied. -/

/-- info: uint i = 5;
bool first1 = true;
while (first1 || (i < 3)) { first1 = false; i++; } -/
#guard_msgs in
#eval IO.println (Prog.show (sol{ uint i = 5; do { i++; } while (i < 3); }))

/-! A statement after a `break` in its block is dropped, as solkey drops it. -/

/-- info: uint i = 0;
bool brk1 = false;
while (!brk1 && (i < 3)) { i++; brk1 = true; } -/
#guard_msgs in
#eval IO.println (Prog.show (sol{ uint i = 0; while (i < 3) { i++; break; i++; } }))

/-! The specification above a loop is its annotation (`LoopAnn`): solkey's
`invariant` and `decreases` clauses, or Lean's bound on unwinding; a loop
with neither is unwound zero times. -/

/-- info: uint i = 0;
/// @custom:key invariant i <= 3 /// @custom:key decreases 3 - i while (i < 3) { i++; } -/
#guard_msgs in
#eval IO.println (Prog.show (sol{ uint i = 0;
  /// @custom:key invariant i <= 3
  /// @custom:key decreases 3 - i
  while (i < 3) { i++; } }))

/-- info: uint i = 0;
/// @custom:key unwind 4 while (i < 3) { i++; } -/
#guard_msgs in
#eval IO.println (Prog.show (sol{ uint i = 0;
  /// @custom:key unwind 4
  for (; i < 3; ) { i++; } }))

/-! ## `return` inside a loop

In a function's body, `return e;` inside a loop assigns the return variable
and sets `ret`, which nested loops share; the outermost loop is followed by
`if (ret) return;`, which `lowerReturns` lowers as any early `return`: the
statements after the loop move into its `else`. -/

def Loops : Contract := contract!{
  uint total; uint[] values;
  function sum(uint n) returns (uint s) {
    for (uint i = 1; i <= n; i++) { s += i; }
  }
  function firstOdd(uint n) returns (uint r) {
    uint i = 0;
    while (true) {
      i++;
      if (i % 2 == 0) { continue; }
      if (i > n) { break; }
      r = i;
    }
  }
  function atLeastOnce(uint n) returns (uint k) {
    do { k++; } while (k < n);
  }
  function fill(uint n) {
    uint i = 0;
    while (i < n) { values.push(i * i); i++; }
    total = values.length;
  }
  function find(uint x) returns (uint) {
    for (uint i = 0; i < values.length; i++) {
      if (values[i] == x) { return i; }
    }
    return 100;
  }
  function search(uint n, uint x) returns (uint) {
    fill(n);
    return find(x);
  }
  function pair(uint n, uint t) returns (uint) {
    for (uint i = 0; i < n; i++) {
      for (uint j = 0; j < n; j++) {
        if (i + j == t) { return 10 * i + j; }
      }
    }
    return 100;
  }
}

/-- info: uint y;
uint se1 = 3;
uint se2;
uint se3 = 0;
bool ret4 = false;
while (!ret4 && (se3 < values.length)) { if (values[se3] == se1) { se2 = se3; ret4 = true; } else {  } if (!ret4) { se3++; } else {  } }
if (ret4) {  } else { se2 = 100; }
y = se2; -/
#guard_msgs in
#eval IO.println (Prog.show (Prog.inlined (sol[Loops]{ uint y = find(3); })))

/-! Nested loops share `ret`: the inner loop's condition tests it, and so do
the outer loop's condition and the rest of its body. -/

/-- info: uint y;
uint se1 = 3;
uint se2 = 4;
uint se3;
uint se4 = 0;
bool ret6 = false;
while (!ret6 && (se4 < se1)) { uint se5 = 0; while (!ret6 && (se5 < se1)) { if ((se4 + se5) == se2) { se3 = (10 * se4) + se5; ret6 = true; } else {  } if (!ret6) { se5++; } else {  } } if (!ret6) { se4++; } else {  } }
if (ret6) {  } else { se3 = 100; }
y = se3; -/
#guard_msgs in
#eval IO.println (Prog.show (Prog.inlined (sol[Loops]{ uint y = pair(3, 4); })))

/-! ## Refused -/

/-- error: Solidity elaboration failed: `break` outside a loop -/
#guard_msgs in
example : Prog StandardExample := sol{ break; }

/-- error: Solidity elaboration failed: i++ < 3: a loop's condition with an effect -/
#guard_msgs in
example : Prog StandardExample := sol{ uint i = 0; while (i++ < 3) { } }

/-- error: Solidity elaboration failed: a loop has an `invariant` or an `unwind` clause, not both -/
#guard_msgs in
example : Prog StandardExample := sol{ uint i = 0;
  /// @custom:key invariant i <= 3
  /// @custom:key unwind 3
  while (i < 3) { i++; } }

/-- error: Solidity elaboration failed: `break`, `continue` or `return` inside `try` inside a loop -/
#guard_msgs in
example : Prog StandardExample := sol{ uint i = 0;
  while (i < 3) { try address(7).get() { break; } catch { } i++; } }

/-! ## Runs

`#run` runs a loop by iterating it (`Loop.runImpl`, which the kernel never
sees): `sum(4)` is `1 + 2 + 3 + 4`; `firstOdd(6)` the last odd number up to
`6`, skipping the even ones by `continue` and leaving by `break`; a
`do … while` runs its body once even when the condition is false at once;
`search` fills `values` with squares and finds `9` at index `3`, and
`pair(3, 4)` leaves both loops at `i = 2`, `j = 2`. -/

/--
info: ok
returns 10
total = 0
values = []
-/
#guard_msgs in #run Loops.sum(4)

/--
info: ok
returns 5
total = 0
values = []
-/
#guard_msgs in #run Loops.firstOdd(6)

/--
info: ok
returns 1
total = 0
values = []
-/
#guard_msgs in #run Loops.atLeastOnce(0)

/--
info: ok
returns 3
total = 4
values = [0, 1, 4, 9]
-/
#guard_msgs in #run Loops.search(4, 9)

/--
info: ok
returns 22
total = 0
values = []
-/
#guard_msgs in #run Loops.pair(3, 4)

/-! A modifier's `_;` in a loop runs the body once per iteration, and two
`_;` run it twice, in the same locals (`Examples/Benchmark/Syntax.lean`):
`g()` under `thrice` adds `2` three times, `f(0)` under `twice` returns `1`. -/

def Twice : Contract := contract!{ uint n;
  modifier twice() { _; _; }
  modifier thrice() { for (uint i = 0; i < 3; i++) { _; } }
  function f(uint a) twice returns (uint r) { r = a++; }
  function g() thrice { n += 2; } }

/--
info: ok
n = 6
-/
#guard_msgs in #run Twice.g()

/--
info: ok
returns 1
n = 0
-/
#guard_msgs in #run Twice.f(0)

/-! ## A loop decided

The kernel does not reduce `Loop.run` (it is classical), but a loop done at
its `n`-th iteration runs as that iteration, which it does compute:
`while (i < 3) { i++; }` from `i = 0` is done at the fourth (three bodies,
then the condition false). -/

def countTo3 : Prog StandardExample := sol{ uint i = 0; while (i < 3) { i++; } }

example : (Prog.run State.exampleStore countTo3 >>= fun σ => σ.getEnv (.user "i")) =
    .ok (.val (.int 3)) := by
  unfold countTo3
  rw [Prog.run_cons_ok rfl, Prog.run_loop_of_iterN (n := 4) rfl]
  rfl

/-! ## No rule yet

A loop closes to `false` under either modality (`whileClose`), so nothing
about a loop is derived until the loop rules land. -/

/--
info: Solidity.LeanTaclet.whileClose : ∀ {C : Contract} {k : Nat} {m : Modality} {ann : LoopAnn C} {e : Val C PrimTy.bool}
  {body : List (Stmt C)}, dl[LeanTaclet C k]{ ⟨[ while (e) body; ]⟩ ⇝ false }
solkey: none (a rule solkey does not have)
printed: none (theory only Lean has)
sound: Solidity.LeanTaclet.sound
-/
#guard_msgs in #taclet whileClose

end Solidity.Examples.Loops
