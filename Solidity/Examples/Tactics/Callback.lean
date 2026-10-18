import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.CallbackSound
import Solidity.Calculus.WalkSyntax

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

The withdrawals read scoped (`open scoped Solidity.Scoped`): the
calculus with callbacks is `Calculus/Callback.lean`'s `ProvesC`, sound
against `ValidC` for a first-order invariant (`ProvesC.valid`,
`Calculus/CallbackSound.lean`); a rule takes its taclet as a `Rule`
(`.key`), `localValueDeclInitDrop` is a hidden binder's rule
(`ProvesC.bind`), and "resume after callback" closes by the invariant
assumed (`Proves.assumeInv`), or by the invariant opened at its scope
(`Proves.openInv`) and the closer.  The counterexample is a typed run with
callbacks (`Semantics/Callback.lean`'s `ExecS` over `State`), and the
rules are pinned as the scoped calculus has them (`CallbackTaclet`).
-/

namespace Solidity.Examples.Tactics.Callback

open Semantics

/-- A vault: what the customer may still withdraw, what was paid out, what
was deposited. -/
def Vault : Contract := contract!{ uint balance; uint paidOut; uint deposited; }

local instance : InContract := ⟨Vault⟩

open scoped Scoped

/-- `balance + paidOut == deposited`: what the vault owes whenever control
leaves it, and may assume whenever it comes back. -/
def vaultInv : Invariant Vault := ⟨dl!{ balance + paidOut == deposited }, rfl⟩

/-! ## Checks, effects, interactions: safe -/

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
  apply ProvesC.allIntro
  apply ProvesC.intro
  apply ProvesC.bind (.key .localValueDeclInitDrop) rfl rfl
  apply ProvesC.update (.key .storageRootReadSelect) rfl
  apply ProvesC.update (.key .storageRootWriteStore) rfl
  apply ProvesC.update (.key .storageRootOpAssign) rfl
  apply ProvesC.callback .transferWithCallbackBox
  · -- invariant on exit: `{U} I`
    apply ProvesC.plain _ rfl
    sol_leaf
    sol_close
  · -- resume after callback: `{U} {havoc} (I → [ ] I)`
    apply ProvesC.plain _ rfl
    exact Proves.assumeInv

/-- What is safe with callbacks is safe without: the deterministic run is one
of the runs with callbacks. -/
theorem withdrawSafe_noCallback :
    ⊨ dl!{ balance + paidOut == deposited →
      [ uint amt = balance; balance = 0; paidOut += amt; to.transfer(amt); ]
        balance + paidOut == deposited } :=
  fun σ v => holds_of_holdsC_imp (withdrawSafe σ v) rfl rfl

/-! ## Interaction first: unsafe -/

/-- `uint amt = balance; to.transfer(amt); balance = 0; paidOut += amt;`, with
the invariant before and after. -/
def withdrawUnsafe : Fml Vault [] := dl!{ balance + paidOut == deposited →
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
def sendVaultInv : Invariant SendVault := ⟨dl[SendVault]{ balance + paidOut == deposited }, rfl⟩

/-- `callTo` keeps the invariant with callbacks: the booking touches no
storage ("invariant on exit"), a callee that keeps the invariant leaves it
for `sent = ok;` ("send succeeded", `ok` true), and a refused send books
nothing ("send failed", `ok` false). -/
theorem callToKeepsInv :
    ValidC sendVaultInv dl[SendVault]{ balance + paidOut == deposited →
      [ bool ok = to.send(5); sent = ok; ] balance + paidOut == deposited } := by
  apply ProvesC.valid
  apply ProvesC.allIntro
  apply ProvesC.intro
  apply ProvesC.update (.key .valueDeclSkip) rfl
  apply ProvesC.send .sendWithCallbackBox
  · -- invariant on exit: `{net := …} I`, the booking touching no storage
    apply ProvesC.plain _ rfl
    sol_leaf
    sol_close
  · -- send succeeded: `ok` true, from any state the callee leaves keeping `I`
    apply ProvesC.plain _ rfl
    sol_derive
    refine Proves.openInv ?_
    sol_leaf
    sol_close
  · -- send failed: `ok` false, nothing booked
    apply ProvesC.plain _ rfl
    sol_derive
    sol_leaf
    sol_close

/-- What holds with callbacks holds without. -/
theorem callToKeepsInv_noCallback :
    ⊨ dl[SendVault]{ balance + paidOut == deposited →
      [ bool ok = to.send(5); sent = ok; ] balance + paidOut == deposited } :=
  fun σ v => holds_of_holdsC_imp (callToKeepsInv σ v) rfl rfl

/-! ## The counterexample, a typed run with callbacks

From a vault holding `5` for its customer, the interaction-first withdrawal
runs with callbacks (`ExecP`, `Semantics/Callback.lean`) over typed
states: the storage at `Vault`'s types (`Storage Vault`), each step the
typed run's (`ExecS.det`) but the payment, where the callee calls back
(`ExecS.transferResume`). -/

/-- A `uint`. -/
def u (n : Int) (h : PrimTy.uint.inRange n = true := by decide) : PrimTy.uint.Denote := ⟨n, h⟩

/-- `Vault`'s storage: `balance`, `paidOut`, `deposited`. -/
def vault (b p d : Int) (hb : PrimTy.uint.inRange b = true := by decide)
    (hp : PrimTy.uint.inRange p = true := by decide)
    (hd : PrimTy.uint.inRange d = true := by decide) : Storage Vault :=
  .cons (.prim (u b hb)) (.cons (.prim (u p hp)) (.cons (.prim (u d hd)) .nil))

/-- A vault holding `5` for its customer, nothing paid out, `10` in funds. -/
def before : State Vault [] :=
  { storage := vault 5 0 5, H := [], heap := Heap.empty, env := (), selfBalance := u 10 }

/-- A statement that pays nothing runs as the typed run, to the state it ends in. -/
theorem execOfRun {C : Contract} {J : StateInv C} {Γ Γ' : Ctx} {σ : State C Γ}
    {s : Stmt C Γ Γ'} {o : Out C σ.H Γ'} (hf : s.forks = false)
    (h : s.run σ = .ok o) : ExecS J σ s (.ok o) := by
  have := ExecS.det (J := J) (σ := σ) hf
  rwa [h] at this

/-- **Interaction first is not safe with callbacks.**  From `before`, with
`to` the address `7`, the customer is paid `5`, calls back to withdraw
again (leaving `balance = 0`, `paidOut = 5`, which keeps the invariant), and
the first withdrawal's booking then adds its `5` a second time: `paidOut`
is `10` against `5` deposited. -/
theorem withdrawUnsafe_withCallback : ¬ ValidT (.withCallback vaultInv) withdrawUnsafe := by
  intro h
  -- the run: `amt = 5`; pay `5`; the callee withdraws again; `balance = 0`; `paidOut += 5`
  have H := h before (u 7) ?inv _
    (.cons (execOfRun rfl rfl)
      (.cons (ExecS.transferResume (st := vault 0 5 5) (nt := []) rfl ?exit ?resume)
        (.cons (execOfRun rfl rfl)
          (.cons (execOfRun rfl rfl) .nil))))
  case inv =>
    simp only [holdsC, holds]
    with_unfolding_all exact rfl
  case exit => with_unfolding_all exact rfl
  case resume => with_unfolding_all exact rfl
  have H2 := H _ ExecF.nil
  simp only [COut.after, holdsC, holds] at H2
  have hE := H2
  -- `0 + 10 == 5` fails
  exact absurd hE (by with_unfolding_all decide)

/-! ## The rules -/

/--
info: @CallbackTaclet.transferWithCallbackBox : ∀ {C : Contract} {k : Nat} {Γ : Ctx} {sadr se : Simple C Γ PrimTy.uint},
  dl[CallbackTaclet C k]{ [ sadr .transfer(se); ] ⇝
    { net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @CallbackTaclet.transferWithCallbackBox

/--
info: @CallbackTaclet.sendWithCallbackBox : ∀ {C : Contract} {k : Nat} {Γ : Ctx} {pv : Idx Γ (LTy.val PrimTy.bool)}
  {sadr se : Simple C Γ PrimTy.uint},
  dl[CallbackTaclet C k]{ [ pv = sadr .send(se); ] ⇝
    "send succeeded": { net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) ‖ pv := true } ⟨[ ]⟩ ;
      "send failed": { pv := false } ⟨[ ]⟩ }
-/
#guard_msgs in #check @CallbackTaclet.sendWithCallbackBox

end Solidity.Examples.Tactics.Callback
