import Solidity.Calculus.Close

/-!
# Calls: a function's body, inlined

`CallsExample` declares internal functions (`Syntax.lean`), and a call is
written as Solidity writes it: `f(a, b);`, `y = f(a);`, `uint y = f(a);`.
The elaborator inlines the callee where it is called — its parameters and its
return variable fresh for the call, its `return` an assignment to the return
variable — so a call statement carries its body, as KeY's
`FunctionBodyStatement` carries the function it stands for.  A function calls
only the functions declared before it: a recursive one cannot be written.

Two rules run a call.  An argument that is not simple is captured first,
the leftmost first (`functionCallArgCapture`, printed `unfoldArgument`, a
`LeanTaclet`: solkey has no such taclet, so the derivation is `⊢`, not `⊢ₖ`);
with every argument simple, `functionBodyExpand` inlines the body: the
parameters declared with the arguments, the return variable declared, the
body, the result assigned (KeY's `expand_function_body`).  From there the
body's statements run by their own rules.
-/

namespace Solidity.Examples.Tactics.Calls

open Proves

local instance : InContract := ⟨CallsExample⟩

/-! ## The rules -/

/--
info: @Taclet.functionBodyExpand : ∀ {C : Contract} {k : Nat} {m : Modality} {f : Name} {args : List (Arg C)} {ret : CallRet}
  {body : List (Stmt C)}, dl{ ⟨[ fbs; ]⟩ ⇝ ⟨[ expand_function_body(fbs); ]⟩ }
-/
#guard_msgs in #check @Taclet.functionBodyExpand

/-! ## Calls run their bodies -/

/-- `uint y = addOne(4);` — `addOne(uint x) returns (uint r) { r = x + 1; }`,
inlined: `uint x' = 4; uint r'; r' = x' + 1; y = r';`. -/
theorem callAddOne : ⊨ dl!{ ⟨ uint y = addOne(4); ⟩ y == 5 } := by
  sol_symex
  sol_close

/-- The same, one rule at a time: the declaration of `y`, the call inlined,
then the body's statements. -/
theorem callAddOneWalk : ⊨ dl!{ [ uint y = addOne(4); ] y == 5 } := by
  apply Proves.valid
  apply update .valueDeclSkip        -- uint y;
  apply unfold .functionBodyExpand   -- y = addOne(4);
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign     -- uint x' = 4;
  apply update .valueDeclSkip        -- uint r';
  apply update .binopAssignment      -- r' = x' + 1;
  apply update .localValueAssign     -- y = r';
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `uint y = double(3);` — `return x + x;` is an assignment to the return
variable. -/
theorem callDouble : ⊨ dl!{ ⟨ uint y = double(3); ⟩ y == 6 } := by
  sol_symex
  sol_close

/-- `uint y = addTwo(3);` — `addTwo` calls `addOne` twice: the inner calls
are inlined in its body. -/
theorem callNested : ⊨ dl!{ ⟨ uint y = addTwo(3); ⟩ y == 5 } := by
  sol_symex
  sol_close

/-- `uint z = larger(a, b);` — a `return` in each branch of the body's last
`if`. -/
theorem callLarger : ⊨ dl!{ ⟨ uint z = larger(3, 7); ⟩ z == 7 } := by
  sol_symex
  sol_close

/-! ## Arguments that are not simple -/

/-- `uint y = addOne(x + 1);` — the argument is captured before the call
(`functionCallArgCapture`), then the body is inlined. -/
theorem callCapture : ⊨ dl!{ x == 1 → ⟨ uint y = addOne(x + 1); ⟩ y == 3 } := by
  sol_symex
  sol_close

/-- The same, one rule at a time: the capture, its declaration, the call,
the body. -/
theorem callCaptureWalk : ⊨ dl!{ x == 1 → [ uint y = addOne(x + 1); ] y == 3 } := by
  apply Proves.valid
  apply intro
  apply update .valueDeclSkip            -- uint y;
  apply unfoldLean .functionCallArgCapture   -- y = addOne(x + 1);  ⇝  uint se = x + 1; y = addOne(se);
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply unfold .functionBodyExpand       -- uint x' = se; uint r'; r' = x' + 1; y = r';
  apply unfold .localValueDeclInitDrop
  apply update .localValueAssign
  apply update .valueDeclSkip
  apply update .binopAssignment
  apply update .localValueAssign
  apply empty
  refine close ?_
  sol_symex
  sol_close

/-- `if (x > 0) { y = addOne(1); } else { y = double(1); }`: a call in each branch. -/
theorem callInBranch :
    ⊨ dl!{ [ uint y; if (x > 0) { y = addOne(1); } else { y = double(1); }; ] y == 2 } := by
  sol_symex
  sol_close

/-! ## Calls with effects on storage -/

set_option maxHeartbeats 2000000 in
/-- `credit(k, 5);` — the callee writes storage: two compound assignments. -/
theorem callCredit :
    ⊨ dl!{ [ uint b = balances[k]; credit(k, 5); uint c = balances[k]; ] c == b + 5 } := by
  sol_symex
  sol_close

/-- `bump(); bump();` — a call with no parameters and no return value, twice. -/
theorem callBumpTwice : ⊨ dl!{ [ uint c = count; bump(); bump(); uint d = count; ] d == c + 2 } := by
  sol_symex
  sol_close

/-! ## What cannot be written -/

/-- A function that calls itself: its body cannot be inlined. -/
def Recursive : Contract := contract!{ uint n; function down(uint x) { down(x); } }

/-- error: Solidity elaboration failed: down is not a function declared before this one -/
#guard_msgs in #check sol[Recursive]{ down(1); }

/-- error: Solidity elaboration failed: bump returns no value -/
#guard_msgs in #check sol{ uint y = bump(); }

/-- error: Solidity elaboration failed: `return` outside a function's body -/
#guard_msgs in #check sol{ return 1; }

/-! ## Early returns

A `return` may stand anywhere in a body.  The elaborator lowers it away when
it inlines the body (`lowerReturns`): the value assigned to the return
variable, what follows the `return` in its block dropped, and the statements
after an `if` that returns in one branch moved into the other.  A `return`
ends the callee it is written in, never its caller: the lowering is per
body. -/

/-- Early returns: a guard clause, a `return` before a declaration, a
checked withdrawal, and a caller that goes on after its callee returned
early. -/
def Returns : Contract := contract!{
  uint total;
  mapping(uint => uint) balances;
  function clamp(uint x) returns (uint) { if (x > 10) { return 10; }; return x; }
  function pick(uint a, uint b) returns (uint r) { if (a > 0) { return a; }; uint c = b + 1; return c; }
  function withdraw(uint k, uint v) returns (bool) {
    if (balances[k] < v) { return false; };
    balances[k] -= v; total -= v;
    return true;
  }
  function clampPlusOne(uint x) returns (uint) { uint y = clamp(x); return y + 1; }
  function incr(uint x) returns (uint) { return x + 1; }
  function twiceIncr(uint x) returns (uint) { return incr(x) * 2; }
}

/-- `if (x > 10) { return 10; }; return x;` is
`if (x > 10) { r = 10; } else { r = x; }`. -/
theorem clampHigh : ⊨ dl[Returns]{ ⟨ uint y = clamp(42); ⟩ y == 10 } := by
  sol_symex
  sol_close

theorem clampLow : ⊨ dl[Returns]{ ⟨ uint y = clamp(7); ⟩ y == 7 } := by
  sol_symex
  sol_close

/-- The statements after the `if` declare `c`: they move into the `else`
branch, where the declaration is the branch's own. -/
theorem pickFallThrough : ⊨ dl[Returns]{ ⟨ uint y = pick(0, 4); ⟩ y == 5 } := by
  sol_symex
  sol_close

set_option maxHeartbeats 2000000 in
/-- `withdraw` returns `false` early and writes nothing when the balance is
short. -/
theorem withdrawShort :
    ⊨ dl[Returns]{ [ uint b = balances[k]; bool ok = withdraw(k, b + 1); uint c = balances[k]; ]
      (ok == false ∧ c == b) } := by
  sol_symex
  sol_close

/-- The `return` in `clamp` ends `clamp`, not `clampPlusOne`, which adds one
after the call. -/
theorem returnEndsCallee : ⊨ dl[Returns]{ ⟨ uint y = clampPlusOne(42); ⟩ y == 11 } := by
  sol_symex
  sol_close

/-- A function that returns nothing may not return a value. -/
def NoValue : Contract := contract!{ uint n; function f(uint x) { if (x > 0) { return x; }; n = x; } }

/-- error: Solidity elaboration failed: `return` of a value from a function that returns none -/
#guard_msgs in #check sol[NoValue]{ f(1); }

/-! ## Calls inside expressions

A call inside an expression is run before its statement, into a fresh local
(`hoist`), as an `++` is: `uint z = incr(a) + 1;` is
`uint se; se = incr(a); uint z = se + 1;` with `incr` inlined.  The order is
the one pinned for `++` (Decision "Effects inside expressions"): a binary
operator's right operand first, a call's arguments left to right, and an
operand read before a call is captured first. -/

/-- `uint z = incr(a) + 1;` -/
theorem callPlusOne : ⊨ dl[Returns]{ ⟨ uint z = incr(4) + 1; ⟩ z == 6 } := by
  sol_symex
  sol_close

/-- `uint z = incr(a) + incr(b);`: two calls in one expression. -/
theorem callPlusCall : ⊨ dl[Returns]{ ⟨ uint z = incr(1) + incr(2); ⟩ z == 5 } := by
  sol_symex
  sol_close

/-- `uint z = incr(incr(1));`: a call as another's argument. -/
theorem callOfCall : ⊨ dl[Returns]{ ⟨ uint z = incr(incr(1)); ⟩ z == 3 } := by
  sol_symex
  sol_close

/-- `require(incr(a) > 0);`: a call in a condition. -/
theorem callInRequire : ⊨ dl[Returns]{ ⟨ require(incr(0) > 0); uint z = 1; ⟩ z == 1 } := by
  sol_symex
  sol_close

/-- `return incr(x) * 2;`: a call inside a returned expression. -/
theorem callInReturn : ⊨ dl[Returns]{ ⟨ uint z = twiceIncr(3); ⟩ z == 8 } := by
  sol_symex
  sol_close

/-- The elaborated form: the call captured into a fresh `se`, the
statement reading it. -/
example : Prog.toStr (sol[Returns]{ uint z = incr(4) + 1; } : Prog Returns) =
    "uint se1; se1 = incr(4); uint z = se1 + 1;" := rfl

/-- error: Solidity elaboration failed: a call under a short-circuit operator -/
#guard_msgs in #check sol[Returns]{ bool b = total > 0 && incr(1) > 0; }

/-- error: Solidity elaboration failed: a call in a conditional's branch -/
#guard_msgs in #check sol[Returns]{ uint z = total > 0 ? incr(1) : 0; }

/-! ## Several returns, tuples and blocks

A function may return several values (`returns (uint lo, uint hi)`; unnamed,
`_ret0`, `_ret1`, …), and a call of one is a tuple assignment's right-hand
side: `(uint lo, , uint sum) = f(a);`.  The call returns them all
(`CallRet.rets`), each return variable declared at its default, and the
targets are assigned after it, left to right, as solkey's
`ParserUtils.tupleAssignment` writes it out.  `return (e₀, e₁);` assigns
each return variable; when a component reads one, through temporaries
first.  A tuple of values goes through temporaries too, so
`(a, b) = (b, a);` swaps.  A bare block `{ … }` scopes its declarations,
and a `return` inside one ends the function (solkey's `blockReturn`). -/

/-- The new call shapes of solkey's `TestSuite.sol`, and `zero`, whose named
return is never assigned. -/
def Tuples : Contract := contract!{
  uint total;
  function returnOrdered(uint x, uint y) returns (uint lo, uint hi) {
    if (x < y) { return (x, y); }
    return (y, x);
  }
  function returnSwapped() returns (uint x, uint y) {
    x = 1;
    y = 2;
    return (y, x);
  }
  function returnStats(uint x, uint y) returns (uint lo, uint hi, uint sum, bool same) {
    lo = x < y ? x : y;
    hi = x < y ? y : x;
    return (lo, hi, x + y, x == y);
  }
  function returnFromNestedBlock(uint x) returns (uint) {
    {
      {
        if (x > 0) { return 1; }
      }
      x = 5;
    }
    return x;
  }
  function returnOrFallThrough(bool stop) returns (uint r) {
    r = 5;
    if (stop) { return r; }
    r = 6;
  }
  function zero() returns (uint r) {}
}

/-- A named return that the body never assigns is its type's default, as in
solc: the call declares it at `0`. -/
theorem namedReturnDefault : ⊨ dl[Tuples]{ ⟨ uint y = zero(); ⟩ y == 0 } := by
  sol_symex
  sol_close

theorem tupleReturnPair :
    ⊨ dl[Tuples]{ ⟨ (uint lo, uint hi) = returnOrdered(5, 2); ⟩ (lo == 2 ∧ hi == 5) } := by
  sol_symex
  sol_close

/-- `return (y, x);` reads the return variables it writes: through
temporaries. -/
theorem tupleReturnReadsReturnVariables :
    ⊨ dl[Tuples]{ ⟨ (uint x, uint y) = returnSwapped(); ⟩ (x == 2 ∧ y == 1) } := by
  sol_symex
  sol_close

theorem tupleReturnDiscardsComponents :
    ⊨ dl[Tuples]{ ⟨ (uint lo, , uint sum, bool same) = returnStats(3, 1); ⟩
      (lo == 1 ∧ sum == 4 ∧ same == false) } := by
  sol_symex
  sol_close

/-- A storage target among the targets (a box: on an arbitrary state the
write to `total` may fail). -/
theorem tupleReturnAssignsExisting :
    ⊨ dl[Tuples]{ [ uint hi; (total, hi) = returnOrdered(9, 4); ] (total == 4 ∧ hi == 9) } := by
  sol_symex
  sol_close

theorem tupleAssignmentRotates :
    ⊨ dl[Tuples]{ ⟨ uint first = 1; uint second = 2; uint third = 3;
      (first, second, third) = (second, third, first); ⟩
      (first == 2 ∧ second == 3 ∧ third == 1) } := by
  sol_symex
  sol_close

theorem tupleDeclaration :
    ⊨ dl[Tuples]{ ⟨ (uint first, , bool third) = (4, 5, true); ⟩ (first == 4 ∧ third == true) } := by
  sol_symex
  sol_close

theorem returnLeavesNestedBlocks :
    ⊨ dl[Tuples]{ ⟨ uint one = returnFromNestedBlock(3); uint five = returnFromNestedBlock(0); ⟩
      (one == 1 ∧ five == 5) } := by
  sol_symex
  sol_close

theorem returnOrFallThroughNamed :
    ⊨ dl[Tuples]{ ⟨ uint stopped = returnOrFallThrough(true); uint finished = returnOrFallThrough(false); ⟩
      (stopped == 5 ∧ finished == 6) } := by
  sol_symex
  sol_close

/-- A block's declaration is its own: the name is free again after it. -/
theorem blockScope : ⊨ dl[Tuples]{ [ { uint w = 1; total = w; }; uint w = 2; ] (total == 1 ∧ w == 2) } := by
  sol_symex
  sol_close

/-- The call and the assignments after it print as the tuple assignment
they are elaborated from (`Stmt.tupleCallStr?`). -/
example : Prog.toStr (sol[Tuples]{ uint lo; uint sum; (lo, , sum, ) = returnStats(3, 1); } :
    Prog Tuples) = "uint lo; uint sum; (lo, , sum, ) = returnStats(3, 1);" := rfl

/-- error: Solidity elaboration failed: returnOrdered returns 2 values, not 3 -/
#guard_msgs in #check sol[Tuples]{ (uint a, uint b, uint c) = returnOrdered(1, 2); }

/-- error: Solidity elaboration failed: returnOrdered returns 2 values, which a tuple assignment takes -/
#guard_msgs in #check sol[Tuples]{ uint a = returnOrdered(1, 2); }

/-- error: Solidity elaboration failed: a tuple assignment to the same target twice -/
#guard_msgs in #check sol[Tuples]{ uint a; (a, a) = returnOrdered(1, 2); }

/-- error: Solidity elaboration failed: a tuple assignment to two targets that are not stack locals -/
#guard_msgs in #check sol[Tuples]{ (total, total) = (1, 2); }

end Solidity.Examples.Tactics.Calls
