import Solidity.Calculus.Callback
import Solidity.Calculus.Close

/-!
# Callbacks: re-entrancy-safe and unsafe withdrawals

The callback semantics of `transfer` (`Semantics/Callback.lean`): the
recipient may call back into the contract, and all that is known of the
state it leaves is the contract invariant.  A vault keeps

```solidity
uint balance;    // what the customer may still withdraw
uint paidOut;    // what was paid out
uint deposited;  // what was paid in
```

with the invariant `balance + paidOut == deposited`.  Two withdrawals:

* **checks-effects-interactions** — `uint amt = balance; balance = 0;
  paidOut += amt; to.transfer(amt);` — books the withdrawal before paying, so
  the invariant holds when control leaves the contract, and holds after any
  callback that keeps it.  It is valid with callbacks, proved in `ProvesC`
  with `transferWithCallbackBox`;
* **interaction first** — `uint amt = balance; to.transfer(amt); balance = 0;
  paidOut += amt;` — pays before booking.  Without callbacks it keeps the
  invariant (`⊨`, the strategy proves it); with callbacks it does not: a
  re-entrant withdrawal pays `amt` out a second time before the first is
  booked, and the booking then counts it twice.  The counterexample is a run
  with callbacks, built step by step.
-/

namespace Solidity.Examples.Callback

open Proves Semantics

/-- A vault: what the customer may still withdraw, what was paid out, what
was deposited. -/
def Vault : Contract := contract!{ uint balance; uint paidOut; uint deposited; }

local instance : InContract := ⟨Vault⟩

/-- `balance + paidOut == deposited`: what the vault owes whenever control
leaves it, and may assume whenever it comes back. -/
def vaultInv : Invariant Vault := ⟨dl!{ balance + paidOut == deposited }, rfl, rfl⟩

/-! ## Checks, effects, interactions: safe -/

set_option maxHeartbeats 2000000 in
/-- `uint amt = balance; balance = 0; paidOut += amt; to.transfer(amt);` keeps
the invariant with callbacks: the ordinary rules run the effects, and
`transferWithCallbackBox` owes the invariant at the exit (booked already)
and resumes into `[ ]`, which a callee that keeps the invariant cannot
break. -/
theorem withdrawSafe :
    ValidC vaultInv dl!{ balance + paidOut == deposited →
      [ uint amt = balance; balance = 0; paidOut += amt; to.transfer(amt); ]
        balance + paidOut == deposited } := by
  apply ProvesC.valid
  apply ProvesC.intro
  apply ProvesC.unfold .localValueDeclInitDrop rfl rfl
  apply ProvesC.update .storageRootReadSelect rfl
  apply ProvesC.update .storageRootWriteStore rfl
  apply ProvesC.update .storageRootOpAssign rfl
  apply ProvesC.callback .transferWithCallbackBox
  · -- invariant on exit
    apply ProvesC.plain _ rfl
    refine close ?_
    sol_symex
    sol_close
  · -- resume after callback: `{U} {havoc} (I → [ ] I)`
    apply ProvesC.plain _ rfl
    apply empty
    rw [show ∀ (Γ : List (Hyp Vault)) a b c, Γ ++ [a, b, c] = (Γ ++ [a, b]) ++ [c] by simp]
    exact close (Hyp.wrap_assumption _ rfl)

/-- What is safe with callbacks is safe without: the deterministic run is one
of the runs with callbacks. -/
theorem withdrawSafe_noCallback :
    ⊨ dl!{ balance + paidOut == deposited →
      [ uint amt = balance; balance = 0; paidOut += amt; to.transfer(amt); ]
        balance + paidOut == deposited } :=
  valid_of_validC withdrawSafe rfl rfl

/-! ## Interaction first: unsafe -/

/-- `uint amt = balance; to.transfer(amt); balance = 0; paidOut += amt;`, with
the invariant before and after. -/
def withdrawUnsafe : Fml Vault := dl!{ balance + paidOut == deposited →
  [ uint amt = balance; to.transfer(amt); balance = 0; paidOut += amt; ]
    balance + paidOut == deposited }

set_option maxHeartbeats 2000000 in
/-- Without callbacks the interaction-first withdrawal keeps the invariant:
`balance` moves to `paidOut`. -/
theorem withdrawUnsafe_valid : ⊨ dl!{ balance + paidOut == deposited →
    [ uint amt = balance; to.transfer(amt); balance = 0; paidOut += amt; ]
      balance + paidOut == deposited } := by
  sol_symex
  sol_close

/-- The same, as the no-callback semantics. -/
theorem withdrawUnsafe_noCallback : ValidT .noCallback withdrawUnsafe :=
  validT_noCallback.2 withdrawUnsafe_valid

/-- A vault holding `5` for its customer, nothing paid out, `to` the
customer's address. -/
def before : State :=
  { storage := [("balance", .int 5), ("paidOut", .int 0), ("deposited", .int 5)],
    env := [(.user "to", .val (.int 7))], selfBalance := 10 }

/-- What a re-entrant withdrawal leaves when the vault pays: the `5` booked
as paid out, the invariant kept. -/
def reentered : List (Name × SVal) :=
  [("balance", .int 0), ("paidOut", .int 5), ("deposited", .int 5)]

/-- **Interaction first is not safe with callbacks.**  From `before`, the
customer is paid `5`, calls back to withdraw again (leaving `reentered`,
which keeps the invariant), and the first withdrawal's booking then adds its
`5` a second time: `paidOut` is `10` against `5` deposited. -/
theorem withdrawUnsafe_withCallback : ¬ ValidT (.withCallback vaultInv) withdrawUnsafe := by
  intro h
  have h := h before
  simp only [withdrawUnsafe, holdsT, holdsC] at h
  have hI : holds before vaultInv.fml := rfl
  -- the run: `amt = 5`; pay `5`; the callee withdraws again (`reentered`);
  -- `balance = 0`; `paidOut += 5`
  have H := h hI _
    (.cons (ExecS.of_run rfl rfl)
      (.cons (ExecS.transferResume (st := reentered) (nt := []) (bal := 0) rfl rfl rfl)
        (.cons (ExecS.of_run rfl rfl)
          (.cons (ExecS.of_run rfl rfl) .nil))))
  -- `0 + 10 == 5` fails
  cases H

/-! ## The diamond owes the funds -/

/-- A vault with no funds. -/
def broke : State := { before with selfBalance := 0 }

/-- `⟨ to.transfer(5); ⟩ true` is not valid with callbacks: from a vault with
no funds the transfer reverts, and a diamond admits no halting run
(`transferWithCallbackDiamond` owes the booking to succeed: solkey's
"sufficient funds"). -/
theorem unfunded_diamond : ¬ ValidC vaultInv dl!{ ⟨ to.transfer(5); ⟩ true } := by
  intro h
  have H := h broke _ (.stop (.transferHalt rfl) rfl)
  exact H

/-! ## The rules -/

/--
info: @CallbackTaclet.transferWithCallbackBox : ∀ {C : Contract} {sadr se : Simple C PrimTy.uint},
  CallbackTaclet C Modality.box (stmt{ sadr .transfer(se); }) [UpdElem.transfer sadr.lower se.lower]
-/
#guard_msgs in #check @CallbackTaclet.transferWithCallbackBox

end Solidity.Examples.Callback
