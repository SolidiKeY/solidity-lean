import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Recursion
import Solidity.Calculus.RecursionCallback

/-!
# Recursive functions

A call of a recursive function is `Stmt.callRec` (`docs/kernel-port.md`,
"Recursion"): the elaborator writes its body once per frame, lazily, the
frames `recUnroll`'s (`recDepth` of them, the bottom one exhausted, as the
EVM's stack is past 1024 frames).  A recursive call runs as the call of its
body, so a run with concrete arguments is computed (`decide +kernel`).
The strategy stops at it (`symexS`): `recursiveCallUnfold` would unfold it
frame by frame and, as it splits an `if` whatever its condition, without
end, so `sol_symex` is no proof of a recursive call.  The call is proved by its
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
  ensures b == (n % 2 == 0);
  function even(uint n) returns (bool b) { if (n == 0) { return true; } return odd(n - 1); }
  ensures b == (n % 2 == 1);
  function odd(uint n) returns (bool b) { if (n == 0) { return false; } return even(n - 1); }
  requires x <= 1000 && y <= 1000;
  ensures r == x + y;
  function sum(uint x, uint y) returns (uint r) {
    if (y == 0) { return x; }
    return sum(x, y - 1) + 1;
  }
  requires y > 0;
  ensures r < y && r <= x && q <= x;
  function divmod(uint x, uint y) returns (uint q, uint r) {
    if (x < y) { return (0, x); }
    (uint q1, uint r1) = divmod(x - y, y);
    return (q1 + 1, r1);
  }
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

/-- **Reference returns**: a recursive function may return a storage alias
or a fresh memory object; such a call runs, but has no contract (its body
has no mutability, `docs/kernel-port.md`, "Recursion"). -/
def RefReturns : Contract := contract!{
  uint[] values;
  function pick(uint n) returns (uint[] storage r) {
    if (n == 0) { r = values; return r; }
    return pick(n - 1);
  }
  function mk(uint n) returns (Person memory p) {
    if (n == 0) { p.age = 7; return p; }
    return mk(n - 1);
  }
}

def refCore := sol[RefReturns]{
  uint[] storage s = pick(3); s.push(5); Person memory q = mk(2); uint z = q.age; }

/-- `mk(2)` returns the object its bottom frame wrote. -/
example : (match Prog.run (State.ofStorage (Storage.init RefReturns)) refCore with
    | .ok o => some (TEnv.get .here o.st.env : PrimTy.uint.Denote).1
    | .error _ => none) = some 7 := by
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

/-- **The countdown ends**, from any `a`, the diamond: below `recDepth`
frames its run ends normally, above them it is exhausted (the EVM's stack
overflows), which the diamond accepts; the contract under the diamond is
proved by induction over the frames as the box's (`docs/kernel-port.md`,
"Recursion"). -/
theorem countdownEnds : ⊨ dl!{ ⟨ countdown(); ⟩ true } := by rec_auto

/-! ## By the source's contracts

`rec_auto` proves a recursive call by its callee's `requires`/`ensures`
(`recSpecContract`, here `contract!{}`'s clauses, in a solc import the
`/// @custom:key` ones), each by induction over the frames; a call of the
frame below by the induction's hypothesis. -/

/-- `sum(3, 4)` is `7`: the call by `sum`'s contract. -/
theorem sumSeven : ⊨ dl!{ [ uint z = sum(3, 4); ] z == 7 } := by rec_auto

/-- `sum`'s own obligation (`spec!{sum}`): its call by its contract. -/
theorem sumSpec : ⊨ spec!{sum} := by rec_auto

/-- **Mutual recursion**: `even`'s contract by induction over its frames,
in whose step `odd`'s by induction over its own, in whose step the call of
`even` is the outer hypothesis's. -/
theorem evenFour : ⊨ dl!{ [ bool z = even(4); ] z == true } := by rec_auto

/-- **Several returns**: a recursive call returns to a tuple's targets. -/
theorem divmodSeven : ⊨ dl!{ [ uint q; uint r; (q, r) = divmod(7, 2); ] r < 2 && q <= 7 } := by
  rec_auto

/-- The strategy stops at a recursive call: `sol_symex` says so. -/
example : ⊨ dl!{ [ uint z = sum(3, 4); ] z == 7 } := by
  fail_if_success sol_symex
  rec_auto

/-! ## Under the callback reading

`docs/kernel-port.md`, "Recursion", row "Callbacks (O7)".  Whether a
recursive call calls back is read off one frame of its unrolling
(`sol_no_callback`, `Prog.callsBack_recUnroll`): where none does, the
formula reads as without callbacks (`validT_noCallback_iff`) and `rec_auto`
proves it.  Past a callback, `rec_auto_c` walks `ProvesC` and proves a
recursive call by `ProvesC.recValid` where nothing calls back, else by a
contract over the callback runs (`ProvesC.recContract`, `RecContractC`). -/

/-- The countdown hands control to no callee: one frame read, the frame
below by hypothesis. -/
example : Fml.callsBack false dl!{ [ countdown(); ] true } = false := by sol_no_callback

/-- So does a sum and a mutual recursion, even where payments call back. -/
example : Fml.callsBack true dl!{ [ uint z = add(3, 4); bool e = even(z); ] true } = false := by
  sol_no_callback

/-- **The countdown with callbacks**: nothing calls back, so the callback
reading is the plain one. -/
theorem countdownT : ValidT .noCallback dl!{ [ countdown(); ] true } := by
  rw [validT_noCallback_iff (by sol_no_callback)]
  rec_auto

/-- **A value call, then the countdown** (`tests/solc/Recursion.sol`'s
`callThenCount`): the callee may call back, the countdown after it does
not (`ProvesC.recValid`). -/
theorem callThenCount :
    ValidT .noCallback dl!{ [ (bool ok, ) = to.call{value: 0}(""); countdown(); ] true } := by
  rec_auto_c

/-- A recursive function that calls back: a value call in every frame. -/
def PayDown : Contract := contract!{
  uint a;
  function payDown(uint to) {
    bool more = a > 0;
    if (more) { a = a - 1; (bool ok, ) = to.call{value: 0}(""); payDown(to); }
  }
}

section PayDown

local instance : InContract := ⟨PayDown⟩

/-- **A recursive call that calls back, by its contract over the callback
runs** (`ProvesC.recContract`): `true`/`true` at `nonpayable`, proved by
induction over the frames (`RecContractC.unroll`), each frame's obligation
by the walk of `ProvesC` and its call of the frame below by the hypothesis
`ih`; "post" opened so that the walk sees its `{havoc}`. -/
theorem payDownNoPanic : ValidT .noCallback dl!{ [ payDown(to); ] true } := by
  refine ProvesC.validT ?_
  simp only [TransferSem.inv, TransferSem.pay]
  apply ProvesC.allIntro
  refine ProvesC.recContract (μ := .nonpayable) (req := .tt) (ens := .tt) ?hc ?hr ?hk ?pre ?post
  case hc =>
    apply RecContractC.unroll
    intro n t ih
    refine ⟨FunContractC.forall_none ?_, ?_, rfl⟩
    · apply FunContractC.ofProvesC [] rfl rfl rfl
      sol_prove
      all_goals
        refine ProvesC.recContract ih (by rfl) (by rfl) ?_ ?_
        all_goals (dsimp only [Fml.callPost, Fml.anonC, Fml.callResult]; sol_prove)
    · simp only [Prog.within, Stmt.within, ih.2.1, Bool.and_true]
      rfl
  case hr => rfl
  case hk => rfl
  case pre => sol_prove
  case post => dsimp only [Fml.callPost, Fml.anonC, Fml.callResult]; sol_prove

/-- The same, automatically. -/
theorem payDownAuto : ValidT .noCallback dl!{ [ payDown(to); ] true } := by rec_auto_c

/-- Under the diamond: no frame reverts (the bottom one is exhausted, which
the diamond accepts); the walk's first-order leaves under the induction's
free frame closed by `sol_leaf` at placeholders (`Symex.placeholders`). -/
theorem payDownEnds : ValidT .noCallback dl!{ ⟨ payDown(to); ⟩ true } := by rec_auto_c

/-- info: 'Solidity.Examples.Tactics.Recursion.payDownNoPanic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms payDownNoPanic

end PayDown

/-- `payDown` with its condition not captured by hand: `if (a > 0)` is
captured by `ifElseUnfold` under callbacks (`ProvesC.capture`), though the
branch calls back. -/
def PayDownDirect : Contract := contract!{
  uint a;
  function payDown(uint to) {
    if (a > 0) { a = a - 1; (bool ok, ) = to.call{value: 0}(""); payDown(to); }
  }
}

section PayDownDirect

local instance : InContract := ⟨PayDownDirect⟩

/-- **`payDown` on `if (a > 0)`, with callbacks.** -/
theorem payDownDirect : ValidT .noCallback dl!{ [ payDown(to); ] true } := by rec_auto_c

/-- Under the diamond. -/
theorem payDownDirectEnds : ValidT .noCallback dl!{ ⟨ payDown(to); ⟩ true } := by rec_auto_c

/-- info: 'Solidity.Examples.Tactics.Recursion.payDownDirect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms payDownDirect

end PayDownDirect

/-- info: 'Solidity.Examples.Tactics.Recursion.addSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms addSum

/-- info: 'Solidity.Examples.Tactics.Recursion.evenFour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms evenFour

end Solidity.Examples.Tactics.Recursion
