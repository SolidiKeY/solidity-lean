import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Recursion

/-!
# Recursive functions

A call of a recursive function is `Stmt.callRec` (`docs/kernel-port.md`,
"Recursion"): the elaborator writes its body once per frame, lazily, the
frames `recUnroll`'s (`recDepth` of them, the bottom one exhausted, as the
EVM's stack is past 1024 frames).  A recursive call runs as the call of its
body, so a run with concrete arguments is computed (`decide +kernel`).
The strategy unfolds it frame by frame (`recursiveCallUnfold`) and, as it
splits an `if` whatever its condition, without end: `sol_symex` is no proof
of a recursive call.  The call is proved by its
contract (`rec_contract`, `rec_contract_by`), the contract by induction over
the frames (`RecContract.unroll`): the step is the body's obligation with
its own recursive calls proved by the hypothesis `ih`, which
`sol_symex_rec` stops at.
-/

namespace Solidity.Examples.Tactics.Recursion

/-- A countdown (solc's `functions_recursive.sol`, `functionsRecursiveUnbounded`
of `tests/solc/open/SolcFunctionCallsOpen.sol`), a recursive sum, and two
mutually recursive functions. -/
def RecursionExample : Contract := contract!{
  uint a;
  function countdown() {
    if (a > 0) { a = a - 1; countdown(); } else { assert(a == 0); }
  }
  function add(uint x, uint y) returns (uint r) {
    if (y == 0) { return x; }
    return add(x, y - 1) + 1;
  }
  function even(uint n) returns (bool b) { if (n == 0) { return true; } return odd(n - 1); }
  function odd(uint n) returns (bool b) { if (n == 0) { return false; } return even(n - 1); }
}

local instance : InContract := ⟨RecursionExample⟩

open scoped Scoped

/-! ## Elaborated and run -/

/-- A recursive call prints as the call it is. -/
example : Prog.toStr [] (sol{ uint z = add(3, 4); countdown(); }) =
    "uint z; z = add(3, 4); countdown();" := rfl

def runCore := sol{ uint z = add(3, 4); bool e = even(5); bool o = odd(5); }

/-- `add(3, 4)` is `7`; `5` is odd, not even. -/
example : (match Prog.run (State.ofStorage (Storage.init RecursionExample)) runCore with
    | .ok o => some ((TEnv.get (.there (.there .here)) o.st.env : PrimTy.uint.Denote).1,
        (TEnv.get (.there .here) o.st.env : PrimTy.bool.Denote),
        (TEnv.get .here o.st.env : PrimTy.bool.Denote))
    | .error _ => none) = some (7, false, true) := by
  decide +kernel

/-! ## By contract, proved by induction over the frames -/

/-- **The countdown never fails its assertion**, whatever `a` is: the box
of `countdown();`, its contract `true`/`true` (every frame ends without a
panic, or does not end).  In the step the frame's own call is proved by the
hypothesis, `a = a - 1` is checked (`a > 0` there), and the `else` branch
asserts `a == 0` where `a > 0` is false. -/
theorem countdownNoPanic : ⊨ dl!{ [ countdown(); ] true } := by
  rec_contract_by .nonpayable cdlIn![]{ true } cdlIn![old, oldNet]{ true }
  case hc =>
    apply RecContract.unroll
    intro n t ih
    refine ⟨FunContract.forall_none ?_, ?_, rfl⟩
    · apply FunContract.ofValidCtx []
      sol_symex_rec
      case h₁ =>
        rec_contract ih
        case pre => sol_symex; sol_close
        case post => sol_symex; sol_close
      all_goals sol_close
    · simp only [Prog.within, Stmt.within, ih.2.1, Bool.and_true]
      rfl
  case pre => sol_symex; sol_close
  case post => sol_symex; sol_close

/-- **A recursive sum**: `add(x, y)` is `x + y`, its contract
`x <= 1000 && y <= 1000` / `r == x + y`; the step reads the frame below's
result `r'` as `x + (y - 1)` (the hypothesis), so `r' + 1` is `x + y`. -/
theorem addSum : ⊨ dl!{ x <= 1000 → y <= 1000 → [ z = add(x, y); ] z == x + y } := by
  rec_contract_by .pure cdlIn![uint a, uint b]{ a <= 1000 && b <= 1000 }
    cdlIn![uint a, uint b, old, oldNet, uint r]{ r == a + b }
  case hc =>
    apply RecContract.unroll
    intro n t ih
    refine ⟨FunContract.forall_val ?_, ?_, rfl⟩
    · apply FunContract.ofValidCtx [.user "b", .user "a"]
      sol_symex_rec
      case h₁ => sol_close
      case h₂ =>
        rec_contract ih
        case pre => sol_symex; sol_close
        case post => sol_symex; sol_close
    · simp only [Prog.within, Stmt.within, ih.2.1, Bool.and_true]
      rfl
  case pre => sol_symex; sol_close
  case post => sol_symex; sol_close

/-- **The countdown, automatically** (`rec_auto`, what the solc import's
runner does): the box's own contract, `true`/`true`, at `nonpayable`, by
induction over the frames; the same proof as `countdownNoPanic`. -/
theorem countdownAuto : ⊨ dl!{ [ countdown(); ] true } := by rec_auto

/-- info: 'Solidity.Examples.Tactics.Recursion.addSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms addSum

end Solidity.Examples.Tactics.Recursion
