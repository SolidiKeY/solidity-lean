import Solidity.Tools.Run
import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect

/-!
# A `try` of the contract itself

`try this.setIx() { … } catch { … }` calls the contract's own function: on
the EVM its body runs, in a frame of its own, and its writes are seen by the
success block.  When the callee is a function declared before the caller
(here, every function of the contract, the program being the contract's
top level), the elaborator carries its body in the `try` (`Stmt.tryCall`'s
`self`), `msg.sender` read as `address(this)` and `msg.value` as `0`; the run
executes it when the receiver is the contract's own address, reverts at
address `0` (no code there), and reads any other receiver as the
transaction's oracle (`TRun.tryCall`, `docs/options.md` O7).

The rule is Lean's (`tryCallSelfBox`; solkey's `try` never runs its callee):
the self-call's goal is the callee inlined and the success block after it,
behind `require(a != 0); require(a == address(this));`, the oracle's goal
behind `require(a != 0); require(a != address(this));`, and each `catch`
block from the caller's state.
-/

namespace Solidity.Examples.Tactics.SelfCall

open Semantics

/-- `ix`, and the functions a `try` of `this` runs. -/
def SelfCaller : Contract := contract!{
  int ix;
  function setIx() { ix = 42; }
  function gOne(bool b) returns (uint) { require(b); return 13; }
  function getIx() returns (int) { return ix; }
}

local instance : InContract := ⟨SelfCaller⟩

open scoped Scoped

/-! ## The rule -/

/--
info: @LeanTaclet.tryCallSelfBox : ∀ {C : Contract} {k : Nat} {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} {call : ExtCall C Γ}
  {rets : Binders ρ} {body : Prog C (ρ ++ Γ) Γ₁} {errorBody : Prog C Γ Γ₂} {code : CodeBinder κ}
  {panicBody : Prog C (κ ++ Γ) Γ₃} {otherBody : Prog C Γ Γ₄} {selfArgs : Args C Γ ps} {selfBody : Prog C (ρ ++ ps) Γf},
  LeanTaclet C k Modality.box
    (Stmt.tryCall call rets body errorBody code panicBody otherBody selfArgs selfBody true)
    (trySelfStep call rets body errorBody code panicBody otherBody selfArgs selfBody)
-/
#guard_msgs in #check @LeanTaclet.tryCallSelfBox

/-! ## Proving -/

/-- **The callee's write is seen on success** (solc's `try_2.sol`, with
`this` for the harness's address): the success block reads `ix == 42`, the
catch-all the caller's `ix == 0`. -/
theorem setIxSeen : ⊨ dl!{ [ ix = 0;
    try this.setIx() { int r = ix; assert(r == 42); } catch { int r = ix; assert(r == 0); }; ]
      true } := by
  sol_symex
  sol_close

/-- **The callee's return value is bound** (solc's `simple_notuple.sol`):
`gOne(true)` returns `13` to the success block.  Each `catch` block is a goal
from the caller's state, the callee not known to end normally: so the
success block states what the return is, not the code after the `try`
(`docs/options.md` O7). -/
theorem gOneReturns : ⊨ dl!{ [
    try this.gOne(true) returns (uint a) { assert(a == 13); } catch { }; ] true } := by
  sol_symex
  sol_close

/-- A reverting callee runs the catch-all, its writes undone: `gOne(false)`
reverts at its `require`. -/
theorem gOneReverts : ⊨ dl!{ [ uint r = 0;
    try this.gOne(false) returns (uint a) { r = a; } catch { r = 9; }; ] r == 9 } := by
  sol_symex
  sol_close

/-- A getter of the contract returns its storage (solc's `try_nested_1.sol`). -/
theorem getIxReturns : ⊨ dl!{ [ ix = 5; int y = 0;
    try this.getIx() returns (int v) { y = v; } catch { y = 5; }; ] y == ix } := by
  sol_symex
  sol_close

/-! ## Refuting: the callee keeps nothing of the caller's view

Read as the oracle (solkey's `noCallback`), a successful call keeps the
caller's storage, and `assert(ix == 0)` after `try this.setIx()` would hold.
The run executes the callee: from any state whose own address is not `0`,
the success block sees `ix == 42` and the `assert` panics. -/

private def keepsP : Prog SelfCaller [] [] :=
  sol{ ix = 0; try this.setIx() { int r = ix; assert(r == 0); } catch { } }

/-- The contract deployed at `7`. -/
def at7 : State SelfCaller [] :=
  { State.init SelfCaller with tx := { selfAddress := ⟨7, rfl⟩ } }

/-- The typed run panics: the callee wrote `ix = 42`. -/
theorem keeps_panics : (Prog.run at7 keepsP).halt? = some .panic := by
  decide +kernel

/-- So the claim the oracle reading proves is not valid. -/
theorem keeps_invalid : ¬ ⊨ dl!{ [ ix = 0;
    try this.setIx() { int r = ix; assert(r == 0); } catch { }; ] true } := by
  intro h
  have h7 := h at7
  have hr := keeps_panics
  revert h7 hr
  show holds at7 (.modal .box keepsP .nil .tt) → _
  rw [holds_modal_iff]
  cases hP : Prog.runSt at7 keepsP with
  | ok τ =>
    intro _ hr
    simp only [Prog.runSt, Except.map] at hP
    revert hr hP
    cases Prog.run at7 keepsP <;> simp [TRes.halt?]
  | error e =>
    intro h7 hr
    simp only [Prog.runSt, Except.map] at hP
    revert hr hP h7
    cases Prog.run at7 keepsP with
    | ok => simp
    | error e' =>
      simp only [TRes.halt?, Option.some.injEq, Except.error.injEq]
      rintro rfl rfl
      simp [Except.bind, Modality.afterRunTR]

/-! ## Address `0` has no code

A call to address `0` reverts in the caller: `r.f()` outside a `try` is
`try r.f() { } catch { revert(); }`, so whatever follows is unreachable. -/

theorem noCodeAtZero : ⊨ dl!{ [ try I(0).setIx() { } catch { revert(); }; assert(false); ]
    true } := by
  sol_symex
  sol_close

end Solidity.Examples.Tactics.SelfCall
