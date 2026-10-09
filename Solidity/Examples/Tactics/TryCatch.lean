import Solidity.Tools.Run
import Solidity.Calculus.NFmlClose
import Solidity.Calculus.Core.Surface
import Solidity.Calculus.Core.Closers
import Solidity.Calculus.Core.CallbackSound
import Solidity.Tools.Inspect

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

open NFml.Proves Semantics

/-- A pinger: how often a ping went through, and how often it failed. -/
def Pinger : Contract := contract!{ uint pings; uint fails; uint last; }

local instance : InContract := ⟨Pinger⟩

open scoped Core.Scoped

/-! ## The rules -/

/--
info: @Core.Taclet.tryCallNoCallbackBox : ∀ {C : Contract} {k : Nat} {Γ : Core.Ctx} {call : Core.ExtCall C Γ} {x : Core.Ctx}
  {rets : Core.Binders x} {x_1 : Core.Ctx} {body : Core.Prog C (x ++ Γ) x_1} {x_2 : Core.Ctx}
  {errorBody : Core.Prog C Γ x_2} {x_3 : Core.Ctx} {code : Core.CodeBinder x_3} {x_4 : Core.Ctx}
  {panicBody : Core.Prog C (x_3 ++ Γ) x_4} {x_5 : Core.Ctx} {otherBody : Core.Prog C Γ x_5},
  dl{ [ try call returns (rets) body catch Error errorBody catch Panic(code) panicBody catch otherBody; ] ⇝
    "call succeeded": ∀ rets. [ body ] ; "Error caught": [ errorBody ] ; "Panic caught": ∀ code. [ panicBody ] ;
      "other failure caught": [ otherBody ] }
-/
#guard_msgs in #check @Core.Taclet.tryCallNoCallbackBox

/--
info: @Core.LeanTaclet.tryCallDiamond : ∀ {C : Contract} {k : Nat} {Γ : Core.Ctx} {call : Core.ExtCall C Γ} {x : Core.Ctx}
  {rets : Core.Binders x} {x_1 : Core.Ctx} {body : Core.Prog C (x ++ Γ) x_1} {x_2 : Core.Ctx}
  {errorBody : Core.Prog C Γ x_2} {x_3 : Core.Ctx} {code : Core.CodeBinder x_3} {x_4 : Core.Ctx}
  {panicBody : Core.Prog C (x_3 ++ Γ) x_4} {x_5 : Core.Ctx} {otherBody : Core.Prog C Γ x_5},
  dl[Core.LeanTaclet C k]{ ⟨
    try call returns (rets) body catch Error errorBody catch Panic(code) panicBody catch otherBody; ⟩ ⇝ false }
-/
#guard_msgs in #check @Core.LeanTaclet.tryCallDiamond

/--
info: dl{
  [
    try address(7).get() returns (uint v) {last = v;} catch Error(string memory) {} catch Panic(uint c) {last = c;}
      catch {};
    ] true } : Core.Fml Pinger []
-/
#guard_msgs in
#check (dl!{ [ try I(7).get() returns (uint v) { last = v; } catch Panic(uint c) { last = c; }
  catch { }; ] true } : Core.Fml Pinger [])

/-! ## Reading and printing -/

/-- The clauses normalised: the missing `Error` and `Panic` clauses are the
catch-all's block, and the receiver `I(a)` is `a`. -/
example : Surface.Prog.toStr (sol{ uint a = 7;
    try I(a).ping() { pings += 1; } catch { fails += 1; } }) =
    "uint a = 7; try address(a).ping() { pings += 1; } \
      catch Error(string memory) { fails += 1; } catch Panic(uint) { fails += 1; } \
      catch { fails += 1; }" := rfl

/-- A missing catch-all reverts: the call's failure passes on to the caller. -/
example : Surface.Prog.toStr (sol{ uint a = 7;
    try I(a).get(1) returns (uint v) { last = v; } catch Panic(uint c) { last = c; } }) =
    "uint a = 7; try address(a).get(1) returns (uint v) { last = v; } \
      catch Error(string memory) { revert(); } catch Panic(uint c) { last = c; } \
      catch { revert(); }" := rfl

/-- A receiver that is not simple is read into a local before the call. -/
example : Surface.Prog.toStr (sol{ try I(last).ping() { pings += 1; } catch { fails += 1; } }) =
    "uint se1 = last; try address(se1).ping() { pings += 1; } \
      catch Error(string memory) { fails += 1; } catch Panic(uint) { fails += 1; } \
      catch { fails += 1; }" := rfl

/-! ## Running -/

/-- The call's outcome is the transaction's: here `ping` on `7` returns. -/
def pingOk : Semantics.State where
  storage := Pinger.initStorage
  tx := { ext := [(⟨7, "ping", []⟩, .ok [])] }

/-- info: Except.ok (Solidity.Semantics.SVal.prim (Solidity.Semantics.PrimVal.int 1)) -/
#guard_msgs in
#eval do
  let σ ← Surface.Prog.runT pingOk (sol{ uint a = 7; try I(a).ping() { pings += 1; } catch { fails += 1; } })
  σ.findStorage "pings" []

/-- The same call reverting with `Panic(0x11)`: the `Panic` clause runs, with
the code bound. -/
def pingPanic : Semantics.State where
  storage := Pinger.initStorage
  tx := { ext := [(⟨7, "ping", []⟩, .panic (.int 17))] }

/-- info: Except.ok (Solidity.Semantics.SVal.prim (Solidity.Semantics.PrimVal.int 17)) -/
#guard_msgs in
#eval do
  let σ ← Surface.Prog.runT pingPanic (sol{ uint a = 7;
    try I(a).ping() { pings += 1; } catch Panic(uint c) { last = c; } catch { fails += 1; } })
  σ.findStorage "last" []

private def pingNoCodeP : Surface.Prog Pinger := sol{ uint a = 7;
  try I(a).ping() { pings += 1; } catch { fails += 1; } }

open Lean Elab Command in
run_cmd liftCoreM do
  if let some e ← Core.Prog.defineCore `Solidity.Examples.Tactics.TryCatch.pingNoCodeCore
      ``Pinger [] pingNoCodeP then
    throwError "pingNoCodeCore: {e}"

/-- With no entry, the address has no code: the caller reverts (the typed
run from `Pinger`'s initial state, by the kernel). -/
theorem pingNoCode : (Core.Prog.trun (Core.TState.init Pinger) pingNoCodeCore).halt? = some .revert := by
  decide +kernel

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
success block's for every value of `v` (`allRight`). -/
theorem getWalk :
    ⊨ dl!{ [ try I(7).get() returns (uint v) { last = v; } catch { last = 0; }; ] true } := by
  apply Proves.valid
  apply branches .tryCallNoCallbackBox <;>
      (try simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]) <;>
    (try and_intros)
  · apply allRight
    apply update .storageRootWriteStore
    refine close ?_
    sol_symex
    sol_close
  all_goals
    apply update .storageRootWriteStore
    refine close ?_
    sol_symex
    sol_close

/-! ## Proving, with callbacks

`fails <= pings` is the pinger's invariant: it holds where control leaves the
contract, and the success block may assume it of whatever state the callee
leaves.  The calculus with callbacks is `Calculus/Core/Callback.lean`'s
`ProvesC`, sound against `ValidC` for a first-order invariant
(`ProvesC.valid`, `Calculus/Core/CallbackSound.lean`); the success block's
goal reads the invariant assumed at its scope (`Proves.openInv`), past the
callee's `{havoc}`. -/

/-- `fails <= pings`. -/
def pingInv : Core.Invariant Pinger := ⟨dl!{ fails <= pings }, rfl⟩

/-- A ping keeps the invariant with callbacks: it holds at the call, the
success block counts a ping in a state where it holds, and a failed call
changes nothing. -/
theorem pingKeepsInv :
    Core.ValidC pingInv dl!{ fails <= pings →
      [ try I(7).ping() { pings += 1; } catch { }; ] fails <= pings } := by
  apply Core.ProvesC.valid rfl
  apply Core.ProvesC.intro
  apply Core.ProvesC.tryCall .tryCallWithCallbackBox
  · -- invariant on exit
    apply Core.ProvesC.plain _ rfl
    refine close ?_
    sol_symex
    sol_close
  · -- call succeeded: from any state the callee leaves in which `I` holds
    apply Core.ProvesC.plain _ rfl
    sol_derive
    refine Core.Proves.openInv ?_
    refine close ?_
    sol_symex
    refine Hyp.valid_after_havoc (Γ := [.pre _]) (Δ := []) rfl ?_
    sol_close
  · -- each `catch` block, from where the call was made
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    refine ⟨?_, ?_, ?_⟩ <;>
    · apply Core.ProvesC.plain _ rfl
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
  Core.valid_of_validC pingKeepsInv rfl rfl

end Solidity.Examples.Tactics.TryCatch
