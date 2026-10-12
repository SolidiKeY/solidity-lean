import Solidity.Tools.Run
import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Tools.Inspect

/-!
# Payment: what a `transfer` changes

`a.transfer(v);` books a debit of `v` on the `net` ledger at `a`, with no
callback (`transferNoCallbackBox`, solkey's `netHeader.key`), and does
nothing else (`Semantics.transferAt`): `to`'s entry down by `v`, unless
`to` is the contract itself (`this`, `address(this)`), which books nothing.
The rule and its single-statement walk are `Payment.lean`'s.

What a transfer changes is the ledger, `net(to)` `5` less after
`to.transfer(5);` (§2), and nothing else: its **frame**, storage, locals and
memory as they were (§1).  Both are theorems for every state.  §3 runs the
typed interpreter from the example store, checked by the kernel (solkey's
`net-*.key` files; `net-manual-update.key`, a raw update with no program,
has no counterpart).  `net-msg-value.key` reads `msg.value` and
`msg.sender`, the transaction's values (`Simple.env`), into storage (§4).
On the EVM the ledger is the money that moved (`Evm.compile_net`).
`ok = a.send(v);` books the same payment or none, as the transaction's
oracle says, and its claims hold of both (§5, `net-send-simple.key`).
-/

namespace Solidity.Examples.Tactics.Net

open Semantics

local instance : InContract := ⟨StandardExample⟩

open scoped Scoped

/-! ## 1 · The frame -/

/-- `alice.age = 1; to.transfer(x + 2); uint y = alice.age;` — a storage write
before a transfer reads the same after it.  The amount is captured first
(`transfer_unfold_rightSndArgument`), then booked (`transferNoCallbackBox`). -/
theorem transferFrameStorage :
    ⊨ dl!{ [ alice.age = 1; to.transfer(x + 2); uint y = alice.age; ] y == 1 } := by
  apply Proves.valid
  apply update .storageFieldWriteSave
  apply unfold .transfer_unfold_rightSndArgument
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply update .transferNoCallbackBox
  -- { net := if(to = this) then net else store(net, at(to), net(to) - se1) }
  apply unfold .localValueDeclInitDrop
  apply update .storageFieldReadFind
  apply empty
  sol_leaf
  sol_close

/-- `uint z = total; owner.transfer(5);` — a state variable as the receiver is
captured (`transfer_unfold_leftFstReceiver`), and the transfer leaves it, and
every other root, as it was. -/
theorem transferFrameRoot :
    ⊨ dl!{ [ uint z = total; owner.transfer(5); ] total == z } := by
  apply Proves.valid
  apply unfold .localValueDeclInitDrop
  apply update .storageRootReadSelect
  apply unfold .transfer_unfold_leftFstReceiver
  apply unfold .localValueDeclInitDrop
  apply update .storageRootReadSelect
  apply update .transferNoCallbackBox
  apply empty
  sol_leaf
  sol_close

/-- `uint z = balances[k]; to.transfer(5); uint y = balances[k];` — a mapping
entry, read before and after. -/
theorem transferFrameMapping :
    ⊨ dl!{ [ uint z = balances[k]; to.transfer(5); uint y = balances[k]; ] y == z } := by
  sol_symex
  sol_close

/-- `uint y = 7; to.transfer(5); to.transfer(2);` — the locals are untouched
by two transfers. -/
theorem transferFrameLocal :
    ⊨ dl!{ [ uint y = 7; to.transfer(5); to.transfer(2); ] y == 7 } := by
  sol_symex
  sol_close

/-- `Person memory m = alice; m.age = 4; to.transfer(1); uint y = m.age;` — and
so is memory. -/
theorem transferFrameMemory :
    ⊨ dl!{ [ Person memory m = alice; m.age = 4; to.transfer(1); uint y = m.age; ] y == 4 } := by
  sol_symex
  sol_close

/-! ## 2 · The ledger, as formulas

A payment is booked at `to`'s end alone, and only when `to` is not the
contract itself.  So a claim about `to` needs `to != this`: paying the
contract itself moves nothing, and books nothing (`netSelfTransfer`), and
the contract's own entry is never moved (`netTransferThis`). -/

/-- `net(to) = 7 → [ to.transfer(5); ] net(to) = 2`: the booking, at every
state where `to` is not the contract (`net-transfer-simple.key`). -/
theorem netTransfer :
    ⊨ dl!{ to != this → net(to) = 7 → [ to.transfer(5); ] net(to) = 2 } := by
  sol_symex
  sol_close

/-- …and the contract's own entry is as it was. -/
theorem netTransferThis :
    ⊨ dl!{ to != this → net(this) = 1 → [ to.transfer(5); ] net(this) = 1 } := by
  sol_symex
  sol_close

/-- **A payment to the contract itself books nothing**: `net(this)` is as it
was. -/
theorem netSelfTransfer :
    ⊨ dl!{ net(this) = 7 → [ address(this).transfer(5); ] net(this) = 7 } := by
  sol_symex
  sol_close

/-- `owner.transfer(5);` — a storage receiver, captured first
(`net-transfer-capture-receiver.key`). -/
theorem netTransferStorageReceiver :
    ⊨ dl!{ owner != this → net(owner) = 7 → [ owner.transfer(5); ] net(owner) = 2 } := by
  sol_symex
  sol_close

/-- `to.transfer(x + 2);` — a captured amount (`net-transfer-capture-argument.key`). -/
theorem netTransferCapturedAmount :
    ⊨ dl!{ x = 3 → to != this → net(to) = 7 → [ to.transfer(x + 2); ] net(to) = 2 } := by
  sol_symex
  sol_close

/-- Two transfers to one address accumulate. -/
theorem netTransfersAccumulate :
    ⊨ dl!{ to != this → net(to) = 9 → [ to.transfer(5); to.transfer(2); ] net(to) = 2 } := by
  sol_symex
  sol_close

/-! ## 3 · The ledger, run

Each block is elaborated scoped (`sol{ … }` at `Prog C [] _`) and checked
by the kernel as its definition, then run typed (`Prog.run`) from
`Storage.standardExample`, the storage of `State.exampleStore`, by the kernel
(`decide +kernel`). -/

private def payNineCore := (sol{ uint to = 9; to.transfer(5); } : Prog StandardExample [] _)
private def payOwnerCore := (sol{ owner = 7; owner.transfer(5); } : Prog StandardExample [] _)
private def paySelfCore := (sol{ uint to = 0; to.transfer(5); } : Prog StandardExample [] _)
private def sendNineCore := (sol{ uint to = 9; bool ok = to.send(5); } : Prog StandardExample [] _)

/-- The initial store, typed. -/
private abbrev start : State StandardExample [] :=
  State.ofStorage Storage.standardExample

/-- The ledger at `a` (`State.getNet`) after `P` runs from `σ`; `none` on a
halt. -/
def netAfter {Γ' : Ctx} (σ : State StandardExample []) (P : Prog StandardExample [] Γ')
    (a : Int) : Option Int :=
  (Prog.run σ P).toOption.map fun o => (lookupBy a o.st.net).getD 0

/-- `uint to = 9; to.transfer(5);` debits `9` by `5` (`net-transfer-simple.key`). -/
theorem netTransferSimple : netAfter start payNineCore 9 = some (-5) := by decide +kernel

/-- `owner = 7; owner.transfer(5);` — a storage receiver
(`net-transfer-capture-receiver.key`, its `owner = 7` premise inlined). -/
theorem netTransferStorageReceiverRun : netAfter start payOwnerCore 7 = some (-5) := by
  decide +kernel

/-- An address nobody paid stays at zero… -/
theorem netUntouched : netAfter start payNineCore 2 = some 0 := by decide +kernel

/-- …and so does the contract's own entry, at `0` in `State.exampleStore`. -/
theorem netThis : netAfter start payNineCore 0 = some 0 := by decide +kernel

/-- A payment to the contract itself books nothing. -/
theorem netSelfRun : netAfter start paySelfCore 0 = some 0 := by decide +kernel

/-- The funds are not the transfer's: `address(this).balance` reads `3`
after a payment of `5` from `3`. -/
theorem transferLeavesFunds :
    ((Prog.run { start with selfBalance := ⟨3, rfl⟩ } payNineCore).toOption.map
      fun o => ((lookupBy 9 o.st.net).getD 0, o.st.selfBalance.1)) = some (-5, 3) := by
  decide +kernel

/-! ## 4 · `msg.value`, `msg.sender`

`net-msg-value.key`: `PiggyBankNet.readMsg` stores the transaction's value
and sender. -/

/-- `PiggyBankNet`'s fields `readMsg` writes, and `readMsg`. -/
def PiggyMsg : Contract := contract!{
  address paidBy; uint paidValue;
  function readMsg() { paidValue = msg.value; paidBy = msg.sender; }
}

/-- `[ readMsg(); ] paidValue == msg.value && paidBy == msg.sender`
(`net-msg-value.key`). -/
theorem netMsgValue :
    ⊨ dl[PiggyMsg]{ [ readMsg(); ] paidValue == msg.value && paidBy == msg.sender } := by
  sol_symex
  sol_close

/-! ## 5 · `send`

`ok = a.send(v);` pays as `a.transfer(v);` does when the recipient takes the
payment, `ok` then `true`, and books nothing when it refuses, `ok` then
`false`; it never reverts (`TRun.send`).  Which, the transaction says
(`TxEnv.ext`, at `sendKey a v`): no entry is an address with no code, which
takes it.  The calculus reads none of it, `sendNoCallbackBox` having a goal
for each outcome, so a claim about the ledger after a send holds of both. -/

/-- `PiggyBankNet`'s field `sent` and `sendTo`, which stores the outcome. -/
def PiggySend : Contract := contract!{
  bool sent;
  function sendTo(address a) { bool ok = a.send(5); sent = ok; }
}

/-- `net-send-simple.key`: after `sendTo(to)` from an empty ledger, `to`'s
entry is `-5` or still `0`, and an untouched address's is `0`. -/
theorem netSendSimple :
    ⊨ dl[PiggySend]{ to != this → to != other → net(to) = 0 → net(other) = 0 →
      [ sendTo(to); ] ((net(to) + 5 = 0 ∨ net(to) = 0) ∧ net(other) = 0) } := by
  sol_symex
  sol_close

/-- A send that went through booked the payment: `ok` true, `to`'s entry
down by `5`. -/
theorem netSendOk :
    ⊨ dl!{ to != this → net(to) = 7 → [ ok = to.send(5); ] (ok == true → net(to) = 2) } := by
  sol_symex
  sol_close

/-- A ledger read crosses a storage write: `total = 1;` leaves `net` as it
was (`Modality.wp_box_saveStorage`). -/
theorem netTransferThenStore :
    ⊨ dl!{ to != this → net(to) = 7 → [ to.transfer(5); total = 1; ] net(to) = 2 } := by
  sol_symex
  sol_close

/-- With no entry for it, the send is taken: `9`'s entry is `-5`. -/
theorem netSendRun : netAfter start sendNineCore 9 = some (-5) := by decide +kernel

/-- With the recipient refusing, nothing is booked and `ok` is `false`. -/
theorem netSendRefusedRun :
    ((Prog.run { start with tx := { ext := [(sendKey 9 5, .error)] } } sendNineCore).toOption.map
      fun o => ((lookupBy 9 o.st.net).getD 0, (TEnv.get .here o.st.env : PrimTy.bool.Denote))) =
      some (0, false) := by
  decide +kernel

end Solidity.Examples.Tactics.Net
