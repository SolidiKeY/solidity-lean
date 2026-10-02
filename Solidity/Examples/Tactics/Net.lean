import Solidity.Calculus.Close

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
interpreter from `State.exampleStore`, checked by `rfl` (solkey's
`net-*.key` files; `net-manual-update.key`, a raw update with no program,
has no counterpart).  `net-msg-value.key` reads `msg.value` and
`msg.sender`, the transaction's values (`Simple.env`), into storage (§4).
On the EVM the ledger is the money that moved (`Evm.compile_net`).
-/

namespace Solidity.Examples.Tactics.Net

open Proves Semantics

local instance : InContract := ⟨StandardExample⟩

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
  refine close ?_
  sol_symex
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
  refine close ?_
  sol_symex
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

/-! ## 3 · The ledger, run -/

/-- The ledger at `a` after `P` runs from the store `σ`. -/
def netAfter {C : Contract} (σ : State) (P : Prog C) (a : Int) : Res Int := do
  return (← Prog.run σ P).getNet a

/-- `uint to = 9; to.transfer(5);` debits `9` by `5` (`net-transfer-simple.key`). -/
theorem netTransferSimple :
    netAfter State.exampleStore sol{ uint to = 9; to.transfer(5); } 9 = .ok (-5) := rfl

/-- `owner = 7; owner.transfer(5);` — a storage receiver
(`net-transfer-capture-receiver.key`, its `owner = 7` premise inlined). -/
theorem netTransferStorageReceiverRun :
    netAfter State.exampleStore sol{ owner = 7; owner.transfer(5); } 7 = .ok (-5) := rfl

/-- An address nobody paid stays at zero… -/
theorem netUntouched :
    netAfter State.exampleStore sol{ uint to = 9; to.transfer(5); } 2 = .ok 0 := rfl

/-- …and so does the contract's own entry, at `0` in `State.exampleStore`. -/
theorem netThis :
    netAfter State.exampleStore sol{ uint to = 9; to.transfer(5); } 0 = .ok 0 := rfl

/-- A payment to the contract itself books nothing. -/
theorem netSelfRun :
    netAfter State.exampleStore sol{ uint to = 0; to.transfer(5); } 0 = .ok 0 := rfl

/-- The funds are not the transfer's: `address(this).balance` reads `3`
after a payment of `5` from `3`. -/
theorem transferLeavesFunds :
    (do let σ ← Prog.run { State.exampleStore with selfBalance := 3 }
          (sol{ uint to = 9; to.transfer(5); } : Prog StandardExample)
        pure (σ.getNet 9, σ.selfBalance)) = .ok (-5, 3) := rfl

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

end Solidity.Examples.Tactics.Net
