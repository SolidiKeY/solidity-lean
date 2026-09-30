import Solidity.Calculus.Close

/-!
# Payment: what a `transfer` changes

`a.transfer(v);` books a debit of `v` on the `net` ledger at `a`, with no
callback (`transferNoCallback`, solkey's `netHeader.key`), and reverts when
the contract's own funds do not cover `v` — the EVM's value-transfer check
that solc's `transfer` inherits (`Semantics.transferAt`).  The rules, and the
two modalities parting company at the funds check, are `Revert.lean`'s
"Payment" section; the single-statement walks (`transferSimple`,
`transferRootReceiver`) are `StorageSteps.lean`'s.

What a formula can observe of a transfer is its **frame**: no term reads the
ledger (`Close.lean`), so a claim about it is a claim that everything else is
as it was — storage, locals and memory.  Those are theorems for every state.
The ledger itself, and the revert when the contract is unfunded, are runs of
the interpreter from `State.exampleStore` (which holds `10⁹` wei), checked by
`rfl` (solkey's `net-*.key` files; `net-manual-update.key`, a raw update with
no program, has no counterpart).  `net-msg-value.key` reads `msg.value` and
`msg.sender`, the transaction's values (`Simple.env`), into storage (§4).
-/

namespace Solidity.Examples.Net

open Proves Semantics

local instance : InContract := ⟨StandardExample⟩

/-! ## 1 · The frame -/

/-- `alice.age = 1; to.transfer(x + 2); uint y = alice.age;` — a storage write
before a transfer reads the same after it.  The amount is captured first
(`transfer_unfold_rightSndArgument`), then booked (`transferNoCallback`). -/
theorem transferFrameStorage :
    ⊨ dl!{ [ alice.age = 1; to.transfer(x + 2); uint y = alice.age; ] y == 1 } := by
  apply Proves.valid
  apply update .storageFieldWriteSave
  apply unfold .transfer_unfold_rightSndArgument
  apply unfold .localValueDeclInitDrop
  apply update .binopAssignment
  apply guard .transferNoCallback
  · -- { selfBalance := selfBalance - se1 ‖ net := store(net, at(to), net(to) - se1) }
    apply unfold .localValueDeclInitDrop
    apply update .storageFieldReadFind
    apply empty
    refine close ?_
    sol_symex
    sol_close
  · -- ¬(0 <= se1 ∧ se1 <= selfBalance): the transfer reverts
    apply done .revertBox
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
  apply guard .transferNoCallback
  · apply empty
    refine close ?_
    sol_symex
    sol_close
  · apply done .revertBox
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

/-! ## 2 · The ledger, run -/

/-- The ledger at `a` after `P` runs from the store `σ`. -/
def netAfter {C : Contract} (σ : State) (P : Prog C) (a : Int) : Res Int := do
  return (← Prog.run σ P).getNet a

/-- `uint to = 9; to.transfer(5);` debits `9` by `5` (`net-transfer-simple.key`). -/
theorem netTransferSimple :
    netAfter State.exampleStore sol{ uint to = 9; to.transfer(5); } 9 = .ok (-5) := rfl

/-- `owner = 7; owner.transfer(5);` — a storage receiver
(`net-transfer-capture-receiver.key`, its `owner = 7` premise inlined). -/
theorem netTransferStorageReceiver :
    netAfter State.exampleStore sol{ owner = 7; owner.transfer(5); } 7 = .ok (-5) := rfl

/-- `to.transfer(x + 2);` — a captured amount (`net-transfer-capture-argument.key`). -/
theorem netTransferCapturedAmount :
    netAfter State.exampleStore sol{ uint to = 9; uint x = 3; to.transfer(x + 2); } 9 =
      .ok (-5) := rfl

/-- Two transfers accumulate. -/
theorem netTransfersAccumulate :
    netAfter State.exampleStore sol{ uint to = 9; to.transfer(5); to.transfer(2); } 9 =
      .ok (-7) := rfl

/-- An address nobody paid stays at zero. -/
theorem netUntouched :
    netAfter State.exampleStore sol{ uint to = 9; to.transfer(5); } 2 = .ok 0 := rfl

/-! ## 3 · The funds check, run

With `3` wei the contract cannot pay `5`: the run reverts, so the diamond of
the transfer is false there and the box holds (`Revert.lean`).  With exactly
`5` it pays once, and a second payment of the same size reverts. -/

/-- Unfunded: a revert. -/
theorem transferUnfunded :
    Prog.run { State.exampleStore with selfBalance := 3 }
      (sol{ uint to = 9; to.transfer(5); } : Prog StandardExample) = .error .revert := rfl

/-- Exactly funded: the debit is booked. -/
theorem transferExactlyFunded :
    netAfter { State.exampleStore with selfBalance := 5 } sol{ uint to = 9; to.transfer(5); } 9 =
      .ok (-5) := rfl

/-- …and the funds are spent: a second payment reverts. -/
theorem transferDrained :
    Prog.run { State.exampleStore with selfBalance := 5 }
      (sol{ uint to = 9; to.transfer(3); to.transfer(3); } : Prog StandardExample) =
      .error .revert := rfl

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

end Solidity.Examples.Net
