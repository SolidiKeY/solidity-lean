import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# Several returns with memory ones

A function of several returns may return memory objects beside values
(`CallRet.rets` with `RetBinders.snocMem`, `docs/feature-work/finite-dispatch.md`,
"Lane FU2-A"): the call enters each memory return as a fresh default object,
as solc allocates one on entry, and the tuple's target takes the callee's
object by pointer, so a returned parameter aliases the caller's argument.
A storage return among several stays refused.

* §1 — a value and a memory return, two memory returns, aliasing, defaults;
* §2 — the same through function values, named and not (`fnTupleDispatch`);
* §3 — what is refused.
-/

namespace Solidity.Examples.Tactics.MemoryReturns

open scoped Scoped

/-- Functions of several returns, some in memory. -/
def MemRets : Contract := contract!{
  uint calls;
  function split(uint k) returns (uint a, uint[] memory b) {
    calls = calls + 1;
    b = new uint[](2); b[0] = k; b[1] = k + 1; a = k * 2;
  }
  function both(uint[] memory xs) returns (uint[] memory p, uint[] memory q) {
    p = xs; q = new uint[](1); q[0] = 7;
  }
  function untouched() returns (uint a, uint[] memory b) { a = 3; }
  function split2(uint k) returns (uint a, uint[] memory b) {
    b = new uint[](1); b[0] = 100; a = k;
  }
  function swapped(uint[] memory xs) returns (uint[] memory p, uint[] memory q) {
    q = xs; p = new uint[](1); p[0] = 8;
  }
}

local instance : InContract := ⟨MemRets⟩

/-! ## 1 · Runs -/

/-- `(a, b) = split(5)`: the value and the callee's array. -/
private def splitAssign := sol[MemRets]{
  uint a; uint[] memory b;
  (a, b) = split(5);
  assert(a == 10); assert(b.length == 2); assert(b[0] == 5); assert(b[1] == 6);
  assert(calls == 1);
}

/-- `uint a; uint[] memory b; (a, b) = split(5);`: `a == 10`, `b` is `[5, 6]`. -/
theorem splitAssign_run :
    (Prog.run (State.init MemRets) splitAssign).toOption.isSome = true := by
  decide +kernel

/-- `(p, q) = both(xs)`: `p` is the caller's `xs` (the callee returned its
parameter), so a write through `p` is seen through `xs`; `q` is the
callee's fresh array. -/
private def bothAlias := sol[MemRets]{
  uint[] memory xs = new uint[](1); xs[0] = 1;
  uint[] memory p; uint[] memory q;
  (p, q) = both(xs);
  p[0] = 9;
  assert(xs[0] == 9); assert(q.length == 1); assert(q[0] == 7);
}

/-- `(p, q) = both(xs); p[0] = 9;`: `xs[0] == 9` (aliasing), `q[0] == 7`. -/
theorem bothAlias_run :
    (Prog.run (State.init MemRets) bothAlias).toOption.isSome = true := by
  decide +kernel

/-- A memory return the callee never assigns is the default, an empty array. -/
private def untouchedDefault := sol[MemRets]{
  uint a; uint[] memory b;
  (a, b) = untouched();
  assert(a == 3); assert(b.length == 0);
}

/-- `(a, b) = untouched();`: `a == 3`, `b.length == 0`. -/
theorem untouchedDefault_run :
    (Prog.run (State.init MemRets) untouchedDefault).toOption.isSome = true := by
  decide +kernel

/-- One target omitted, and the call as a statement: the callee still runs. -/
private def omitted := sol[MemRets]{
  uint[] memory b;
  (, b) = split(1);
  split(2);
  assert(b[1] == 2); assert(calls == 2);
}

/-- `(, b) = split(1); split(2);`: `b[1] == 2`, two calls ran. -/
theorem omitted_run :
    (Prog.run (State.init MemRets) omitted).toOption.isSome = true := by
  decide +kernel

/-- A false observation fails by the assertion's panic: the runs above do not
hold vacuously. -/
private def falseObservation := sol[MemRets]{
  uint[] memory xs = new uint[](1); xs[0] = 1;
  uint[] memory p; uint[] memory q;
  (p, q) = both(xs);
  p[0] = 9;
  assert(xs[0] == 1);
}

/-- `assert(xs[0] == 1)` after the write through the alias: a panic. -/
theorem falseObservation_panics :
    (match Prog.run (State.init MemRets) falseObservation with
      | .error .panic => true
      | _ => false) = true := by
  decide +kernel

/-- A narrow element among several returns: the target's element width
is the return's (`uint8[] memory`). -/
def NarrowRets : Contract := contract!{
  function nw() returns (uint a, uint8[] memory b) { b = new uint8[](1); b[0] = 255; a = 1; }
}

/-- `uint a; uint8[] memory b; (a, b) = nw();`: `b[0] == 255`. -/
private def narrowAssign := sol[NarrowRets]{
  uint a; uint8[] memory b;
  (a, b) = nw();
  assert(a == 1); assert(b[0] == 255);
}

/-- `(a, b) = nw()` into a `uint8[] memory` target: `b[0] == 255`. -/
theorem narrowAssign_run :
    (Prog.run (State.init NarrowRets) narrowAssign).toOption.isSome = true := by
  decide +kernel

/-- **By the calculus**: `functionBodyExpand` declares the memory return
(`T memory r;`, a fresh default object) beside the value one, and the
targets read them: `(a, b) = untouched()` ends with `a == 3`. Reads of the
returned object are left to the runs above: the closer does not resolve a
memory array's length after its allocation (`[ uint[] memory b; ] b.length
== 0` stays open with no call at all; `finite-dispatch.md`, "Lane FU2-A"). -/
theorem untouched_proved : ⊨ᶠ dl!{ [ uint a; uint[] memory b; (a, b) = untouched(); ]
    a == 3 } := by
  sol_symex
  sol_close

/-- The same through `split`, whose body allocates the returned array and
writes it and a state variable: `(a, b) = split(5)` ends with `a == 10`. -/
theorem split_proved : ⊨ᶠ dl!{ [ uint a; uint[] memory b; (a, b) = split(5); ] a == 10 } := by
  sol_symex
  sol_close

/-! ## 2 · Through function values -/

/-- `(a, b) = h(5)` with `h = split`: the dispatch's arm is the direct
call's tuple assignment. -/
private def valueSplit := sol[MemRets]{
  function (uint) returns (uint, uint[] memory) h = split;
  uint a; uint[] memory b;
  (a, b) = h(5);
  assert(a == 10); assert(b[0] == 5); assert(b[1] == 6); assert(calls == 1);
}

/-- `h = split; (a, b) = h(5);`: `a == 10`, `b` is `[5, 6]`. -/
theorem valueSplit_run :
    (Prog.run (State.init MemRets) valueSplit).toOption.isSome = true := by
  decide +kernel

/-- A callee that is not a name, `(c ? split : split2)(5)`, with `c` true:
`split` runs, once. -/
private def valueTernaryT := sol[MemRets]{
  bool c = true; uint a; uint[] memory b;
  (a, b) = (c ? split : split2)(5);
  assert(a == 10); assert(b[1] == 6); assert(calls == 1);
}

/-- `(c ? split : split2)(5)` with `c` true runs `split` only. -/
theorem valueTernaryT_run :
    (Prog.run (State.init MemRets) valueTernaryT).toOption.isSome = true := by
  decide +kernel

/-- The same with `c` false: `split2` runs, `split` does not. -/
private def valueTernaryF := sol[MemRets]{
  bool c = false; uint a; uint[] memory b;
  (a, b) = (c ? split : split2)(5);
  assert(a == 5); assert(b[0] == 100); assert(calls == 0);
}

/-- `(c ? split : split2)(5)` with `c` false runs `split2` only. -/
theorem valueTernaryF_run :
    (Prog.run (State.init MemRets) valueTernaryF).toOption.isSome = true := by
  decide +kernel

/-- Two memory returns through a function value: the returned parameter
aliases the caller's argument, whichever position it is returned at. -/
private def valueAlias := sol[MemRets]{
  uint[] memory xs = new uint[](1); xs[0] = 1;
  function (uint[] memory) returns (uint[] memory, uint[] memory) g = swapped;
  uint[] memory p; uint[] memory q;
  (p, q) = g(xs);
  q[0] = 9;
  assert(xs[0] == 9); assert(p[0] == 8);
}

/-- `g = swapped; (p, q) = g(xs); q[0] = 9;`: `xs[0] == 9`, `p[0] == 8`. -/
theorem valueAlias_run :
    (Prog.run (State.init MemRets) valueAlias).toOption.isSome = true := by
  decide +kernel

/-! ## 3 · What is refused -/

/-- A storage return among several. -/
def StoreRets : Contract := contract!{
  uint[] values;
  function st() returns (uint a, uint[] storage s) { s = values; a = 1; }
}

/-- error: Solidity elaboration failed: st: `storage` on a return of a function of several returns -/
#guard_msgs in #check sol[StoreRets]{ uint a; uint[] storage s = values; (a, s) = st(); }

-- A target of another element width, which solc rejects (no conversion
-- between memory arrays of different element types).
/-- error: Solidity elaboration failed: mv2 has narrow positions ·[] 8 bits wide where none are expected: solc converts no reference type to one of another element type -/
#guard_msgs in #check sol[NarrowRets]{ uint a; uint[] memory b; (a, b) = nw(); }

/-- info: 'Solidity.Examples.Tactics.MemoryReturns.bothAlias_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bothAlias_run

/-- info: 'Solidity.Examples.Tactics.MemoryReturns.valueAlias_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms valueAlias_run

end Solidity.Examples.Tactics.MemoryReturns
