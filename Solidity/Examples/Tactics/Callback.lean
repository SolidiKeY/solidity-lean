import Solidity.Calculus.Callback
import Solidity.Calculus.Close
import Solidity.Calculus.Core.Surface
import Solidity.Calculus.Core.Closers
import Solidity.Calculus.Core.CallbackSound
import Solidity.Calculus.Core.WalkSyntax

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

A `send` (`PiggyBankNet`'s `callTo`) is read so too, with a third outcome:
the callee refuses, and the send returns `false` with nothing booked
(`sendWithCallbackBox`, `ProvesC.send`).

The withdrawals read scoped (`open scoped Solidity.Core.Surface`): the
calculus with callbacks is `Calculus/Core/Callback.lean`'s `ProvesC`, sound
against `ValidC` for a first-order invariant (`ProvesC.valid`,
`Calculus/Core/CallbackSound.lean`); a rule takes its taclet as a `Rule`
(`.key`), `localValueDeclInitDrop` is a hidden binder's rule
(`ProvesC.bind`), and "resume after callback" closes by the invariant
assumed (`Proves.assumeInv`).  The counterexample run, the send and the
rules' pins are read without the switch, at the end.
-/

namespace Solidity.Examples.Tactics.Callback

open Proves Semantics

/-- A vault: what the customer may still withdraw, what was paid out, what
was deposited. -/
def Vault : Contract := contract!{ uint balance; uint paidOut; uint deposited; }

local instance : InContract := ⟨Vault⟩

open scoped Solidity.Core.Surface

/-- `balance + paidOut == deposited`: what the vault owes whenever control
leaves it, and may assume whenever it comes back. -/
def vaultInv : Core.Invariant Vault := ⟨dl!{ balance + paidOut == deposited }, rfl⟩

/-! ## Checks, effects, interactions: safe -/

/-- `uint amt = balance; balance = 0; paidOut += amt; to.transfer(amt);` keeps
the invariant with callbacks: the ordinary rules run the effects, and
`transferWithCallbackBox` owes the invariant at the exit (booked already)
and resumes into `[ ]`, which a callee that keeps the invariant cannot
break. -/
theorem withdrawSafe :
    Core.ValidC vaultInv dl!{ balance + paidOut == deposited →
      [ uint amt = balance; balance = 0; paidOut += amt; to.transfer(amt); ]
        balance + paidOut == deposited } := by
  apply Core.ProvesC.valid rfl
  apply Core.ProvesC.allIntro
  apply Core.ProvesC.intro
  apply Core.ProvesC.bind (.key .localValueDeclInitDrop) rfl rfl
  apply Core.ProvesC.update (.key .storageRootReadSelect) rfl
  apply Core.ProvesC.update (.key .storageRootWriteStore) rfl
  apply Core.ProvesC.update (.key .storageRootOpAssign) rfl
  apply Core.ProvesC.callback .transferWithCallbackBox
  · -- invariant on exit: `{U} I`
    apply Core.ProvesC.plain _ rfl
    refine close ?_
    sol_symex
    sol_close
  · -- resume after callback: `{U} {havoc} (I → [ ] I)`
    apply Core.ProvesC.plain _ rfl
    exact Core.Proves.assumeInv

/-- What is safe with callbacks is safe without: the deterministic run is one
of the runs with callbacks. -/
theorem withdrawSafe_noCallback :
    ⊨ dl!{ balance + paidOut == deposited →
      [ uint amt = balance; balance = 0; paidOut += amt; to.transfer(amt); ]
        balance + paidOut == deposited } :=
  fun σ v => Core.holds_of_holdsC_imp (withdrawSafe σ v) rfl rfl

/-! ## Interaction first: unsafe -/

/-- `uint amt = balance; to.transfer(amt); balance = 0; paidOut += amt;`, with
the invariant before and after. -/
def withdrawUnsafe : Core.Fml Vault [] := dl!{ balance + paidOut == deposited →
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
theorem withdrawUnsafe_noCallback : Core.ValidT .noCallback withdrawUnsafe :=
  Core.validT_noCallback.2 withdrawUnsafe_valid

end Solidity.Examples.Tactics.Callback

/-! ## Read without the switch

The counterexample is a run with callbacks over today's states
(`Semantics/Callback.lean`'s `ExecS`), built step by step from a storage
written out; the typed run's would need a typed storage of `Vault`
(`TState`) and its `ExecS` steps.  The send's "send succeeded" goal reads
the invariant past `sent = ok;`, a storage write in front of a goal that
reads the storage, which the scoped sequent applies by no rule yet
(today's `applyStorageBox`).  The rules are pinned as today's prints them. -/

namespace Solidity.Examples.Tactics.Callback.Untyped

open Proves Semantics

local instance : InContract := ⟨Vault⟩

/-- `balance + paidOut == deposited`, today's. -/
def vaultInv : Invariant Vault := ⟨dl!{ balance + paidOut == deposited }, rfl, rfl⟩

/-- `uint amt = balance; to.transfer(amt); balance = 0; paidOut += amt;`, with
the invariant before and after. -/
def withdrawUnsafe : Fml Vault := dl!{ balance + paidOut == deposited →
  [ uint amt = balance; to.transfer(amt); balance = 0; paidOut += amt; ]
    balance + paidOut == deposited }

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
  have hI : holds before vaultInv.fml := holds_eqD_iff.2 ⟨_, rfl, rfl⟩
  -- the run: `amt = 5`; pay `5`; the callee withdraws again (`reentered`);
  -- `balance = 0`; `paidOut += 5`
  have H := h hI _
    (.cons (ExecS.of_run rfl rfl)
      (.cons (ExecS.transferResume (st := reentered) (nt := []) rfl
        (holds_eqD_iff.2 ⟨_, rfl, rfl⟩) (holds_eqD_iff.2 ⟨_, rfl, rfl⟩))
        (.cons (ExecS.of_run rfl rfl)
          (.cons (ExecS.of_run rfl rfl) .nil))))
  -- `0 + 10 == 5` fails
  obtain ⟨x, hx, hy⟩ := holds_eqD_iff.1 H
  cases hx; cases hy

/-! ## `send`: a callee that may refuse

`PiggyBankNet`'s `callTo` is `(bool ok, ) = a.call{value: 5}(""); sent = ok;`,
which solkey's parser lowers to `bool ok = a.send(5); sent = ok;`, and so do
we here (the lowering needs tuples, which this calculus does not read yet).
With callbacks, `sendWithCallbackBox` owes the invariant after the booking,
the rest after a callback that keeps it (`ok` true), and the rest with
nothing booked (`ok` false): the callee may refuse and revert whatever it
did.  solkey's `net-call-withcallback-simple.key` states an invariant of the
ledger (`net(to) <= 0`); `Invariant` is one of the storage here. -/

/-- The vault with a flag for the last payment's outcome. -/
def SendVault : Contract :=
  contract!{ uint balance; uint paidOut; uint deposited; bool sent; }

/-- `balance + paidOut == deposited`, of `SendVault`. -/
def sendVaultInv : Invariant SendVault := ⟨dl[SendVault]{ balance + paidOut == deposited }, rfl, rfl⟩

/-- `callTo` keeps the invariant with callbacks: the booking touches no
storage ("invariant on exit"), a callee that keeps the invariant leaves it
for `sent = ok;` ("send succeeded", `ok` true), and a refused send books
nothing ("send failed", `ok` false). -/
theorem callToKeepsInv :
    ValidC sendVaultInv dl[SendVault]{ balance + paidOut == deposited →
      [ bool ok = to.send(5); sent = ok; ] balance + paidOut == deposited } := by
  apply ProvesC.valid
  apply ProvesC.intro
  apply ProvesC.update .valueDeclSkip rfl
  apply ProvesC.send .sendWithCallbackBox
  · -- invariant on exit: `{net := …} I`, the booking touching no storage
    apply ProvesC.plain _ rfl
    refine close ?_
    sol_symex
    sol_close
  · -- send succeeded: `ok` true, from any state the callee leaves keeping `I`
    apply ProvesC.plain _ rfl
    sol_derive
    refine close (Hyp.valid_after_havoc (Γ := [_, _, _]) rfl ?_)
    sol_symex
    sol_close
  · -- send failed: `ok` false, nothing booked
    apply ProvesC.plain _ rfl
    sol_derive
    refine close ?_
    sol_symex
    sol_close

/-- What holds with callbacks holds without. -/
theorem callToKeepsInv_noCallback :
    ⊨ dl[SendVault]{ balance + paidOut == deposited →
      [ bool ok = to.send(5); sent = ok; ] balance + paidOut == deposited } :=
  valid_of_validC callToKeepsInv rfl rfl

/-! ## The rules -/

/--
info: @CallbackTaclet.transferWithCallbackBox : ∀ {C : Contract} {sadr se : Simple C PrimTy.uint},
  dl[CallbackTaclet C]{ [ sadr .transfer(se); ] ⇝
    { net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @CallbackTaclet.transferWithCallbackBox

/--
info: @CallbackTaclet.sendWithCallbackBox : ∀ {C : Contract} {pv : Var} {sadr se : Simple C PrimTy.uint},
  dl[CallbackTaclet C]{ [ pv = sadr .send(se); ] ⇝
    "send succeeded": { net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) ‖ pv := true } ⟨[ ]⟩ ;
      "send failed": { pv := false } ⟨[ ]⟩ }
-/
#guard_msgs in #check @CallbackTaclet.sendWithCallbackBox

end Solidity.Examples.Tactics.Callback.Untyped
