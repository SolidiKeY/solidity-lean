import Solidity.Syntax

/-!
# What elaborates away

The benchmark's contracts (`Examples/Benchmark/`) are written with parts of
Solidity that no statement holds: `sol{ … }` and `contract!{ … }` read them
and leave the statements they stand for (`Syntax.lean`, "What elaborates
away").  Each is pinned here by what it elaborates to, printed.

* an ether or time unit on a literal is the literal times the unit;
* `payable(e)` and `address(e)` of a value are `e`;
* `emit E(a, b);` evaluates what of its arguments may revert or has an
  effect, and drops the log; `event` and `error` declarations are dropped;
* `require(c, "msg")`, `require(c, Err(a))` are `require(c)` (or a branch,
  when evaluating `a` may revert); `revert Err(a);`, `revert("msg");` are
  `revert();`;
* an enum member is its position, a `uint`;
* a struct constructor `T(a, b)`, `T({b: y, a: x})` is a fresh memory object
  written member by member, the arguments evaluated first, left to right;
* a modifier is inlined around the body of the function that applies it.
-/

namespace Solidity.Examples.Benchmark.Syntax

/-- A contract with a bit of everything that elaborates away. -/
def Elaborates : Contract := contract!{
  uint public total;
  address payable public owner;
  Pair pair;
  Pair[] pairs;
  enum Phase { Open, Closed }
  Phase public phase;
  event Paid(address indexed to, uint amount);
  error TooLow(uint got, uint want);
  modifier onlyOwner(uint who) { require(who == owner, "not owner"); _; }
  modifier inPhase(Phase p) { if (phase != p) { revert TooLow(0, 1); }; _; }
  modifier counted() { _; total += 1; }
  function pay(uint who, uint v) external onlyOwner(who) inPhase(Phase.Open) counted {
    total += v; emit Paid(who, v); }
  function get() public view returns (uint) { return total; }
}

local instance : InContract := ⟨Elaborates⟩

/-! ## Units and casts -/

/-- `2 ether` is `2 * 10^18`, `3 days` is `3 * 86400`, `1 gwei` is `10^9`. -/
example : Prog.toStr (sol{ total = 2 ether + 3 days; total = 1 gwei; }) =
    "total = 2000000000000000000 + 259200; total = 1000000000;" := rfl

/-- `payable(e)` and `address(e)` are `e`. -/
example : Prog.toStr (sol{ owner = payable(address(total)); owner = address(0); }) =
    "owner = total; owner = 0;" := rfl

/--
error: `address(this)` is not a value here
---
error: cannot evaluate code because 'sorryAx' uses 'sorry' and/or contains errors
-/
#guard_msgs in #check sol{ owner = address(this); }

/--
error: a unit is one of wei gwei ether seconds minutes hours days weeks
---
error: cannot evaluate code because 'sorryAx' uses 'sorry' and/or contains errors
-/
#guard_msgs in #check sol{ total = 1 parsecs; }

/-! ## Events and errors -/

/-- An event's arguments that cannot revert are not evaluated; one that may
(an addition may overflow) is, into a local nothing reads. -/
example : Prog.toStr (sol{ emit Paid(owner, total); emit Paid(owner, total + 1); }) =
    "uint se1 = total + 1;" := rfl

/-- An `++` in an event's argument happens, after the arguments before it
are read. -/
example : Prog.toStr (sol{ emit Paid(owner, total++); }) =
    "uint se1 = owner; uint se2; se2 = total++;" := rfl

/-- `require` with a message or an error, `revert` with an error or a
message. -/
example : Prog.toStr (sol{ require(total > 0, "empty"); require(total > 0, TooLow(total, 2));
    revert TooLow(1, 2); revert("no"); }) =
    "require(total > 0); require(total > 0); revert(); revert();" := rfl

/-- An error's argument that may revert is evaluated when the condition
holds, as solc evaluates it before the check. -/
example : Prog.toStr (sol{ require(total > 0, TooLow(total + 1, 2)); }) =
    "if (total > 0) { uint se1 = total + 1; } else { revert(); }" := rfl

/-! ## Enums -/

/-- `Phase.Closed` is the second member: `1`. -/
example : Prog.toStr (sol{ phase = Phase.Closed; }) = "phase = 1;" := rfl

/-! ## Struct constructors -/

/-- A storage target is written from a fresh memory object (the arguments may
read the target: `pair = Pair(pair.b, pair.a)` swaps). -/
example : Prog.toStr (sol{ pair = Pair(total, 2); }) =
    "Pair memory mv1; mv1.a = total; mv1.b = 2; pair = mv1;" := rfl

/-- Named arguments are put in the members' order. -/
example : Prog.toStr (sol{ pair = Pair({b: 2, a: total}); }) =
    "Pair memory mv1; mv1.a = total; mv1.b = 2; pair = mv1;" := rfl

/-- A memory local names the fresh object; a push is a default slot written
with its copy. -/
example : Prog.toStr (sol{ Pair memory q = Pair(1, 2); pairs.push(Pair(1, 2)); }) =
    "Pair memory mv1; mv1.a = 1; mv1.b = 2; Pair memory q = mv1; \
    Pair memory mv2; mv2.a = 1; mv2.b = 2; pairs.push(); pairs[pairs.length - 1] = mv2;" := rfl

/-- error: Solidity elaboration failed: Pair({…}) names each member of Pair once: [a, b] -/
#guard_msgs in #check sol{ pair = Pair({a: 1}); }

/-- error: Solidity elaboration failed: Pair has 2 members, not 1 -/
#guard_msgs in #check sol{ pair = Pair(1); }

/-! ## Modifiers -/

/-! `pay(owner, 5)`: `onlyOwner(who)` outermost, then `inPhase(Phase.Open)`,
then `counted`, whose code after `_;` runs after the body; each modifier's
parameter a fresh local bound when the modifier is entered. -/

/--
info: uint se1 = owner; uint se2 = 5; uint se4 = se1; require(se4 == owner); uint se3 = 0; if (phase != se3) { revert(); } else {  } total += se2; total += 1;
-/
#guard_msgs in #eval IO.println (Prog.toStr (Prog.inlined (sol{ pay(owner, 5); })))

/--
error: `_;` stands once, at the top level of a modifier's body
---
error: cannot evaluate code because 'sorryAx' uses 'sorry' and/or contains errors
-/
#guard_msgs in #check sol{ _; }

/-- error: a modifier's body has one `_;`, at its top level -/
#guard_msgs (error, drop info) in
#check contract!{ uint n; modifier twice() { _; _; } }

/-- A modifier applied without its argument. -/
def MissingArg : Contract := contract!{ uint owner;
  modifier onlyOwner(uint who) { require(who == owner); _; }
  function f() onlyOwner { owner = 1; } }

/-- error: Solidity elaboration failed: modifier onlyOwner takes 1 arguments, not 0 -/
#guard_msgs in #check sol[MissingArg]{ f(); }

end Solidity.Examples.Benchmark.Syntax
