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

namespace Solidity.Examples.Calls

open Proves

local instance : InContract := ⟨CallsExample⟩

/-! ## The rules -/

/--
info: @Taclet.functionBodyExpand : ∀ {C : Contract} {k : Nat} {m : Modality} {f : Name} {args : List (Arg C)}
  {hsep : Arg.separatedFrom [] args = true} {ret : CallRet} {body : List (Stmt C)},
  Taclet C k m (Stmt.call f args hsep ret body) (Premise.unfold (Stmt.expandBody args ret body))
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

/-- error: Solidity elaboration failed: `return` only ends a function's body -/
#guard_msgs in #check sol{ return 1; }

end Solidity.Examples.Calls
