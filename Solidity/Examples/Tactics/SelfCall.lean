import Solidity.Tools.Run
import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect
import Solidity.Calculus.CallbackDerive

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
transaction's oracle (`TRun.tryCall`, `docs/options.md` O8).

The rule is Lean's (`tryCallSelfBox`; solkey's `try` never runs its callee):
the self-call's goal is the callee inlined and the success block after it,
behind `require(a != 0); require(a == address(this));`, the oracle's goal
behind `require(a != 0); require(a != address(this));`, and each `catch`
block from the caller's state, where the call does not end normally as a
self-call: `fails(call)`, `¬⟨ require(a == address(this)); f(args) → rets; ⟩
true` (`ExtCall.selfFails`).  The walks prove the diamond instead of the
`catch` goal where they can (`Proves.notLeft`), and drop it otherwise
(`Proves.hideLeft`).
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

/-! ## The rule

Its two success goals print their blocks escaped (`‹body›`): the
`require`s and the inlined callee in front of `body` are not schema
variables (`trySelfStep`); its `catch` goals behind `fails(call)`. -/

/--
info: @LeanTaclet.tryCallSelfBox : ∀ {C : Contract} {k : Nat} {Γ ρ κ Γ₁ Γ₂ Γ₃ Γ₄ ps Γf : Ctx} {call : ExtCall C Γ}
  {rets : Binders ρ} {body : Prog C (ρ ++ Γ) Γ₁} {errorBody : Prog C Γ Γ₂} {code : CodeBinder κ}
  {panicBody : Prog C (κ ++ Γ) Γ₃} {otherBody : Prog C Γ Γ₄} {selfArgs : Args C Γ ps} {selfBody : Prog C (ρ ++ ps) Γf},
  dl[LeanTaclet C k]{ [ try call returns (rets) body catch Error errorBody catch Panic(code) panicBody catch otherBody;
    ] ⇝
    "self call succeeded": [ ‹body› ] ; "call succeeded": ∀ rets. [ ‹body› ] ;
      "Error caught": fails(call) → [ errorBody ] ; "Panic caught": fails(call) → ∀ code. [ panicBody ] ;
      "other failure caught": fails(call) → [ otherBody ] }
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
`gOne(true)` returns `13` to the success block. -/
theorem gOneReturns : ⊨ dl!{ [
    try this.gOne(true) returns (uint a) { assert(a == 13); } catch { }; ] true } := by
  sol_symex
  sol_close

/-- **The `catch` block is not reached when the callee ends normally**
(solc's `simple_notuple.sol`, `tryCatchExactReturn`): each `catch` goal
assumes `¬⟨ require(this == address(this)); gOne(true) → a; ⟩ true`
(`ExtCall.selfFails`), which the walk refutes by proving the diamond
(`notLeft`), so `r == 13` after the `try`. -/
def gOneExactF : Fml SelfCaller [] := dl!{ [ uint r = 0;
    try this.gOne(true) returns (uint a) { r = a; } catch { r = 9; }; ] r == 13 }

theorem gOneExact : ⊨ gOneExactF := by
  sol_prove

/-- The same with callbacks (`ValidT .noCallback`, `ProvesC.trySelf`). -/
theorem gOneExactT : ValidT .noCallback gOneExactF := by
  sol_prove

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

/-- `[ keepsP ] true`. -/
def keepsF : Fml SelfCaller [] := .modal .box keepsP .nil .tt

/-- So the claim the oracle reading proves is not valid. -/
theorem keeps_invalid : ¬ Valid keepsF := by
  intro h
  have h7 := (holds_modal_iff at7 keepsP .nil .tt).1 (h at7)
  have hr : Prog.runSt at7 keepsP = .error .panic := by
    have := keeps_panics
    unfold Prog.runSt
    revert this
    cases Prog.run at7 keepsP with
    | ok => intro h; cases h
    | error e => intro h; cases h; rfl
  rw [hr] at h7
  exact h7.2 rfl

/-! ## Address `0` has no code

A call to address `0` reverts in the caller: `r.f()` outside a `try` is
`try r.f() { } catch { revert(); }`, so whatever follows is unreachable. -/

theorem noCodeAtZero : ⊨ dl!{ [ try I(0).setIx() { } catch { revert(); }; assert(false); ]
    true } := by
  sol_symex
  sol_close

end Solidity.Examples.Tactics.SelfCall
