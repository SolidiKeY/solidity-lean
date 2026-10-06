import Solidity.Calculus.LastLine
import Solidity.Calculus.Close
import Solidity.Calculus.Sequents
import Solidity.FreshNames

/-!
# Payment: `transfer`, as chains

The calculus's worked examples of `transfer` (the paper's payment section), each one chain term under the
box, the only modality with a transfer rule (`Calculus/Chains.lean`, `.claude/rules/derivations.md`).
`transferNoCallbackBox` books the payment on the ledger and nothing else: the update
`{ net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) }`, `sadr`'s entry down by
the amount unless `sadr` is the contract itself, which books nothing.  The receiver's capture is a
`uint pv`, not an `address payable`.

Every line is written, a printed `⇝` is a `~[r]~>` and a `⇝*` a `~*>`.  The booking and the `⟨[ ]⟩` it
leaves are one `~*>`, as the paper never shows that line; past the program the stack merges
(`~[sequentialToParallel]~>`) and each read is resolved one law a link, every capture kept to the last
line, which `#last_line` checks.  A free parameter (`to`, `x`) and the storage a program reads (`owner`)
get a concrete value in an update on the first line, so the amount and the receiver end at literals.
Two parts of the booking stay symbolic at the last line, as `storage` does in a write over it: the booking
is relative to the ledger the program found (`net(3) - 9`), which the update language writes only so, and
`3 = this` does not fold, `this` being any address.  That the programs' boxes hold of `true` in every state,
for every receiver and amount, is `Examples/Tactics/Payment.lean`'s.
-/

namespace Solidity.Examples.Chains.Payment

local instance : InContract := ⟨StandardExample⟩

/-- The printed name of the captured amount or receiver. -/
def names : FreshTable := [("pv", "se1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

variable (φ : Post StandardExample)

/-! ## Example: Symbolic Execution of `to.transfer(5)` -/

namespace Transfer5

/-- `to.transfer(5);` with `to` 3: the booking and its `⟨[ ]⟩`, the paper's one step; the merge puts the
receiver in it. -/
theorem chain :
    dl![.box]{ { to := 3 } ⟨[ to.transfer(5); ]⟩ φ }
    ~*> dl![.box]{ { to := 3 } { net := if(to = this) then net else store(net, at(to), net(to) - 5) } φ }
    ~[sequentialToParallel]~>
      dl![.box]{ { to := 3 ‖ net := if(3 = this) then net else store(net, at(3), net(3) - 5) } φ } := by
  sol_chain
#last_line chain

end Transfer5

/-! ## Example: Symbolic Execution of `to.transfer(x + 2)` -/

namespace TransferSum

/-- `to.transfer(x + 2);` with `to` 3 and `x` 7: the amount is nonsimple, so it is captured first
(`transfer_unfold_rightSndArgument`) and its declaration dropped with the binding it leaves; the booking
reads the capture.  The merge puts `7 + 2` for `pv`, which folds to 9. -/
theorem chain :
    dl![.box]{ { to := 3 ‖ x := 7 } ⟨[ to.transfer(x + 2); ]⟩ φ }
    ~[transfer_unfold_rightSndArgument]~>
      dl![.box]{ { to := 3 ‖ x := 7 } ⟨[ uint pv = x + 2; to.transfer(pv); ]⟩ φ }
    ~*> dl![.box]{ { to := 3 ‖ x := 7 } { pv := x + 2 } ⟨[ to.transfer(pv); ]⟩ φ }
    ~*> dl![.box]{ { to := 3 ‖ x := 7 } { pv := x + 2 }
        { net := if(to = this) then net else store(net, at(to), net(to) - pv) } φ }
    ~[sequentialToParallel]~> dl![.box]{ { to := 3 ‖ x := 7 ‖ pv := 7 + 2 ‖
        net := if(3 = this) then net else store(net, at(3), net(3) - (7 + 2)) } φ }
    ~[add_literals]~> dl![.box]{ { to := 3 ‖ x := 7 ‖ pv := 9 ‖
        net := if(3 = this) then net else store(net, at(3), net(3) - 9) } φ } := by
  sol_chain
#last_line chain

end TransferSum

/-! ## Example: Symbolic Execution of `owner.transfer(5)` -/

namespace TransferOwner

/-- `owner.transfer(5);` from a storage where `owner` is 3: the receiver is the nonsimple part, captured by
`transfer_unfold_leftFstReceiver`; the booking is at the capture.  The merge reads `owner` in the starting
storage, and the read of the write resolves to 3 (`findOnSave`). -/
theorem chain :
    dl![.box]{ { storage := save(storage, owner, 3) } ⟨[ owner.transfer(5); ]⟩ φ }
    ~[transfer_unfold_leftFstReceiver]~>
      dl![.box]{ { storage := save(storage, owner, 3) } ⟨[ uint pv = owner; pv.transfer(5); ]⟩ φ }
    ~*> dl![.box]{ { storage := save(storage, owner, 3) } { pv := find(storage, owner) } ⟨[ pv.transfer(5); ]⟩ φ }
    ~*> dl![.box]{ { storage := save(storage, owner, 3) } { pv := find(storage, owner) }
        { net := if(pv = this) then net else store(net, at(pv), net(pv) - 5) } φ }
    ~[sequentialToParallel]~> dl![.box]{
        { storage := save(storage, owner, 3) ‖ pv := find(save(storage, owner, 3), owner) ‖
          net := if(find(save(storage, owner, 3), owner) = this) then net else
            store(net, at(find(save(storage, owner, 3), owner)), net(find(save(storage, owner, 3), owner)) - 5) }
        φ }
    ~[findOnSave]~> dl![.box]{ { storage := save(storage, owner, 3) ‖ pv := 3 ‖
        net := if(3 = this) then net else store(net, at(3), net(3) - 5) } φ } := by
  sol_chain
#last_line chain

end TransferOwner

end Solidity.Examples.Chains.Payment
