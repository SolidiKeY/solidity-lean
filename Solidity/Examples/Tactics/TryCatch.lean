import Solidity.Calculus.Callback
import Solidity.Calculus.Close

/-!
# `try`/`catch`: an external call and a block per way it ends

`try e.f(a) returns (uint v) { … } catch Error(string memory) { … }
catch Panic(uint c) { … } catch { … }` calls a function of another contract
(`Stmt.tryCall`).  Its callee is never run: without callbacks it changes
nothing of this contract, and how it ends is the transaction's
(`TxEnv.ext`), a call with no entry reaching an address with no code and
reverting in the caller.  So a proof of a `try` has a goal per clause
(`tryCallNoCallbackBox`): the success block for every value of the returned
data, and each `catch` block from the state the call was made in.  A
missing `Error`/`Panic` clause is the catch-all's block, and a missing
catch-all `revert();`, as solkey's `TryStatement.of` normalises it.

With callbacks (`tryCallWithCallbackBox`, `ProvesC.tryCall`) the contract
also owes its invariant where control leaves, and its success block runs
from any state the callee may leave in which the invariant holds.  A
diamond `try` closes to `false` (`tryCallDiamond`, solkey has no rule): the
call may revert in the caller, and no formula says it does not.
-/

namespace Solidity.Examples.Tactics.TryCatch

open Proves Semantics

/-- A pinger: how often a ping went through, and how often it failed. -/
def Pinger : Contract := contract!{ uint pings; uint fails; uint last; }

local instance : InContract := ⟨Pinger⟩

/-! ## The rules -/

/--
info: @Taclet.tryCallNoCallbackBox : ∀ {C : Contract} {k : Nat} {call : ExtCall C} {rets : List (PrimTy × Var)}
  {ok err : List (Stmt C)} {code : Option Var} {pnc other : List (Stmt C)},
  dl{ [ try call returns (rets) ok catch Error err catch Panic(code) pnc catch other; ] ⇝
    ∀ rets. ⟨[ ok ]⟩ ; ⟨[ err ]⟩ ; ∀ code. ⟨[ pnc ]⟩ ; ⟨[ other ]⟩ }
-/
#guard_msgs in #check @Taclet.tryCallNoCallbackBox

/--
info: @LeanTaclet.tryCallDiamond : ∀ {C : Contract} {k : Nat} {call : ExtCall C} {rets : List (PrimTy × Var)}
  {ok err : List (Stmt C)} {code : Option Var} {pnc other : List (Stmt C)},
  dl{ ⟨ try call returns (rets) ok catch Error err catch Panic(code) pnc catch other; ⟩ ⇝ false }
-/
#guard_msgs in #check @LeanTaclet.tryCallDiamond

/--
info: dl{
  [
    try address(7).get() returns (uint v) {last = v;} catch Error(string memory) {} catch Panic(uint c) {last = c;}
      catch {};
    ] true } : Fml Pinger
-/
#guard_msgs in
#check (dl!{ [ try I(7).get() returns (uint v) { last = v; } catch Panic(uint c) { last = c; }
  catch { }; ] true } : Fml Pinger)

/-! ## Reading and printing -/

/-- The clauses normalised: the missing `Error` and `Panic` clauses are the
catch-all's block, and the receiver `I(a)` is `a`. -/
example : Prog.toStr (sol{ uint a = 7;
    try I(a).ping() { pings += 1; } catch { fails += 1; } }) =
    "uint a = 7; try address(a).ping() { pings += 1; } \
      catch Error(string memory) { fails += 1; } catch Panic(uint) { fails += 1; } \
      catch { fails += 1; }" := rfl

/-- A missing catch-all reverts: the call's failure passes on to the caller. -/
example : Prog.toStr (sol{ uint a = 7;
    try I(a).get(1) returns (uint v) { last = v; } catch Panic(uint c) { last = c; } }) =
    "uint a = 7; try address(a).get(1) returns (uint v) { last = v; } \
      catch Error(string memory) { revert(); } catch Panic(uint c) { last = c; } \
      catch { revert(); }" := rfl

/-- A receiver that is not simple is read into a local before the call. -/
example : Prog.toStr (sol{ try I(last).ping() { pings += 1; } catch { fails += 1; } }) =
    "uint se1 = last; try address(se1).ping() { pings += 1; } \
      catch Error(string memory) { fails += 1; } catch Panic(uint) { fails += 1; } \
      catch { fails += 1; }" := rfl

/-! ## Running -/

/-- The call's outcome is the transaction's: here `ping` on `7` returns. -/
def pingOk : State where
  storage := Pinger.initStorage
  tx := { ext := [(⟨7, "ping", []⟩, .ok [])] }

/-- info: Except.ok (Solidity.Semantics.SVal.prim (Solidity.Semantics.PrimVal.int 1)) -/
#guard_msgs in
#eval do
  let σ ← Prog.run pingOk (sol{ uint a = 7; try I(a).ping() { pings += 1; } catch { fails += 1; } })
  σ.findStorage "pings" []

/-- The same call reverting with `Panic(0x11)`: the `Panic` clause runs, with
the code bound. -/
def pingPanic : State where
  storage := Pinger.initStorage
  tx := { ext := [(⟨7, "ping", []⟩, .panic (.int 17))] }

/-- info: Except.ok (Solidity.Semantics.SVal.prim (Solidity.Semantics.PrimVal.int 17)) -/
#guard_msgs in
#eval do
  let σ ← Prog.run pingPanic (sol{ uint a = 7;
    try I(a).ping() { pings += 1; } catch Panic(uint c) { last = c; } catch { fails += 1; } })
  σ.findStorage "last" []

/-- With no entry, the address has no code: the caller reverts. -/
example : Prog.run { storage := Pinger.initStorage } (sol{ uint a = 7;
    try I(a).ping() { pings += 1; } catch { fails += 1; } }) = .error .revert := by decide

/-! ## Proving, without callbacks -/

/-- Whatever the call does, one of the two counters goes up: the success
block and each `catch` block are a goal. -/
theorem pingCounts :
    ⊨ dl!{ pings == 0 ∧ fails == 0 →
      [ uint a = 7; try I(a).ping() { pings += 1; } catch { fails += 1; }; ]
        pings + fails == 1 } := by
  sol_symex
  sol_close

/-- The returned value is a value of its type, whatever the callee returned:
data that does not decode reverts in the caller. -/
theorem getStores :
    ⊨ dl!{ [ try I(7).get() returns (uint v) { last = v; pings = v; } catch { last = 0; pings = 0; }; ]
        last == pings } := by
  sol_symex
  sol_close

/-- One rule at a time: `tryCallNoCallbackBox` leaves a goal per clause, the
success block's for every value of `v`. -/
theorem getWalk :
    ⊨ dl!{ [ try I(7).get() returns (uint v) { last = v; } catch { last = 0; }; ] true } := by
  apply Proves.valid
  apply branches .tryCallNoCallbackBox
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true,
    Fml.alls, codeBinders, Option.toList, List.map]
  refine ⟨allIntro ?_, ?_, ?_, ?_⟩ <;>
  · sol_derive
    all_goals
      refine close ?_
      sol_symex
      sol_close

/-! ## Proving, with callbacks

`fails <= pings` is the pinger's invariant: it holds where control leaves the
contract, and the success block may assume it of whatever state the callee
leaves. -/

/-- `fails <= pings`. -/
def pingInv : Invariant Pinger := ⟨dl!{ fails <= pings }, rfl, rfl⟩

/-- A ping keeps the invariant with callbacks: it holds at the call, the
success block counts a ping in a state where it holds, and a failed call
changes nothing. -/
theorem pingKeepsInv :
    ValidC pingInv dl!{ fails <= pings →
      [ try I(7).ping() { pings += 1; } catch { }; ] fails <= pings } := by
  apply ProvesC.valid
  apply ProvesC.intro
  apply ProvesC.tryCall .tryCallWithCallbackBox
  · -- invariant on exit
    apply ProvesC.plain _ rfl
    exact close (Hyp.wrap_assumption [] rfl)
  · -- call succeeded: from any state the callee leaves in which `I` holds
    apply ProvesC.plain _ rfl
    simp only [Fml.alls]
    sol_derive
    refine close (Hyp.valid_after_havoc (Γ := [_]) rfl ?_)
    sol_symex
    sol_close
  · -- each `catch` block, from where the call was made
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true,
      Fml.alls, codeBinders, Option.toList, List.map]
    refine ⟨?_, ?_, ?_⟩ <;>
    · apply ProvesC.plain _ rfl
      sol_derive
      all_goals
        refine close ?_
        sol_symex
        sol_close

/-- What holds with callbacks holds without: the deterministic run is one of
the runs with callbacks. -/
theorem pingKeepsInv_noCallback :
    ⊨ dl!{ fails <= pings →
      [ try I(7).ping() { pings += 1; } catch { }; ] fails <= pings } :=
  valid_of_validC pingKeepsInv rfl rfl

end Solidity.Examples.Tactics.TryCatch
