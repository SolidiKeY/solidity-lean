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
* a modifier is inlined around the body of the function that applies it;
* a call with named arguments `f({q: b, p: a})` is `f(a, b)`, in the
  parameters' order;
* a `constructor` is the contract's constructor, which only a deployment
  calls (`constructor(args);`), and `constant`, like `immutable`, is a
  storage root, with its initializer run by the constructor.
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

/-- `address(this)` is the contract's own address, an environment value. -/
example : Prog.toStr (sol{ owner = address(this); }) = "owner = address(this);" := rfl

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

/-- A local of an enum type is a `uint`. -/
example : Prog.toStr (sol{ Phase p = Phase.Closed; phase = p; }) = "uint p = 1; phase = p;" := rfl

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

/-- error: Solidity elaboration failed: `_;` outside a modifier's body -/
#guard_msgs in #check sol{ _; }

/-- error: a modifier's body has a `_;` -/
#guard_msgs (error, drop info) in
#check contract!{ uint n; modifier none() { n = 1; } }

/-! A modifier may run the body several times, with `_;` anywhere: the body
runs again in the same locals, as solc's legacy pipeline runs it
(`Examples/Tactics/Loops.lean`'s `ModifierRuns` pins its inlining and runs
it). -/

/-- A modifier applied without its argument. -/
def MissingArg : Contract := contract!{ uint owner;
  modifier onlyOwner(uint who) { require(who == owner); _; }
  function f() onlyOwner { owner = 1; } }

/-- error: Solidity elaboration failed: modifier onlyOwner takes 1 arguments, not 0 -/
#guard_msgs in #check sol[MissingArg]{ f(); }

/-- A modifier applied twice: each application has locals of its own, so
the outer `x = c;` writes the outer `c` (solc's
`function_modifier_multiple_times_local_vars`: `x` ends `2`). -/
def Twice : Contract := contract!{ uint x;
  modifier m(uint y) { uint c = y; _; x = c; }
  function h() m(2) m(5) { } }

/--
info: uint se3 = 2; uint se4 = se3; uint se1 = 5; uint se2 = se1; x = se2; x = se4;
-/
#guard_msgs in #eval IO.println (Prog.toStr (Prog.inlined (sol[Twice]{ h(); })))

/-! ## Named arguments of a call

`f({q: 2, s: 3, p: 1})` binds by name: the arguments are put in the
parameters' order before the call is inlined (solc's `named_args`). -/

def NamedArgs : Contract := contract!{ uint r;
  function f(uint p, uint q, uint s) returns (uint) { return p * 100 + q * 10 + s; }
  function g() { r = f({q: 2, s: 3, p: 1}); } }

/--
info: uint se1; uint se2 = 1; uint se3 = 2; uint se4 = 3; uint se5; se5 = ((se2 * 100) + (se3 * 10)) + se4; se1 = se5; r = se1;
-/
#guard_msgs in #eval IO.println (Prog.toStr (Prog.inlined (sol[NamedArgs]{ r = f({q: 2, s: 3, p: 1}); })))

/-- error: Solidity elaboration failed: f({…}) names each parameter of f once: [p, q, s] -/
#guard_msgs in #check sol[NamedArgs]{ r = f({q: 2, p: 1}); }

/-! ## Constructors and constants -/

/-- `constructor(…) { … }` is the contract's constructor (`Contract.ctor`),
not one of its functions; `constant`, like `immutable`, is a root, and
`uint constant limit = 10;` an initializer the constructor runs first
(`Contract.inits`), as solkey reads both. -/
def WithCtor : Contract := contract!{
  uint constant limit = 10;
  address public immutable owner;
  uint total;
  enum Phase { Open, Closed }
  constructor(uint start) payable {
    Phase p = Phase.Open;
    if (start > limit) { total = limit; } else if (start > 0) { total = start; } else { total = 1; }
    owner = msg.sender;
  }
}

example : WithCtor.funs.map (·.1) = [] := rfl
example : WithCtor.ctor.isSome = true := rfl
example : WithCtor.inits.map (·.1) = ["limit"] := rfl
example : WithCtor.vars.map (·.1) = ["limit", "owner", "total"] := rfl

/-- A deployment, `constructor(5);`: its body, an enum local and an `else if`
in it, inlined after `limit = 10;`, as one call. -/
example : Prog.toStr (C := WithCtor) (sol[WithCtor]{ constructor(5); }) = "constructor(5);" := rfl

/-- No `constructor`: the implicit one runs the initializers. -/
def WithInits : Contract := contract!{ uint x = 5; uint y; }

example : Prog.toStr (C := WithInits) (sol[WithInits]{ constructor(); }) = "constructor();" := rfl

/-- A function that calls the constructor. -/
def CallsCtor : Contract := contract!{ uint n; constructor() { n = 1; } function f() { constructor(); } }

/-- error: Solidity elaboration failed: constructor(…) in a function's body or a block: only a program's own statements deploy -/
#guard_msgs in #check sol[CallsCtor]{ f(); }

/-- error: Solidity elaboration failed: constructor(…) in a function's body or a block: only a program's own statements deploy -/
#guard_msgs in #check sol[CallsCtor]{ if (n == 0) { constructor(); } }

/-- error: Solidity elaboration failed: constructor(…) in a function's body or a block: only a program's own statements deploy -/
#guard_msgs in #check sol[CallsCtor]{ while (n == 0) { constructor(); } }

/-- error: a second constructor: a contract declares one -/
#guard_msgs (error, drop info) in
#check contract!{ uint n; constructor() { n = 1; } constructor() { n = 2; } }

/-- error: a constructor returns nothing: no `returns` -/
#guard_msgs (error, drop info) in
#check contract!{ uint n; constructor() returns (uint r) { r = 1; } }

/-- error: `constructor` names the constructor, not a function -/
#guard_msgs (error, drop info) in
#check contract!{ uint n; function constructor() { n = 1; } }

/-- An initializer that does not fit its variable: refused where it is run,
at the first deployment. -/
def BadInit : Contract := contract!{ uint8 small = 300; }

/-- error: Solidity elaboration failed: 300 does not fit uint8 -/
#guard_msgs in #check sol[BadInit]{ constructor(); }

/-- error: unknown type uint7: the integer types are `uint8` … `uint256` and `int8` … `int256`, in steps of 8 -/
#guard_msgs (error, drop info) in #check contract!{ uint7 small; }

end Solidity.Examples.Benchmark.Syntax
