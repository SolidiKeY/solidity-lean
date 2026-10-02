import Solidity.Calculus.Sequents

/-!
# Payment: `transfer`, as `⊢` walks

`sadr.transfer(se);` has one rule, under the box, `transferNoCallbackBox`,
which books the payment on the ledger and nothing else: the update
`{ net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) }`,
`sadr`'s entry down by the amount unless `sadr` is the contract itself,
which books nothing (solkey's `\if(sadr = self)`).  Under the diamond a
payment has no rule (`LeanTaclet.transferDiamond` closes it to `false`).
Whether the world pays is not the rule's: on the EVM a refused payment
reverts, which the box does not see (`Evm.compile_box`).  The worked
examples' traces are `Examples/Chains/Payment.lean`'s; here the sequents
themselves, each with its whole context, are the goals of a walk, each a
checked line `show sequent!{ Γ ⟹ ψ }` (`Calculus/Sequents.lean`).

The ledger's postconditions and the frame of a transfer are `Net.lean`'s;
the callback rules are `Callback.lean`'s.
-/

namespace Solidity.Examples.Tactics.Payment

open Proves

local instance : InContract := ⟨StandardExample⟩

/-! ## 1 · The rule -/

/--
info: @Taclet.transferNoCallbackBox : ∀ {C : Contract} {k : Nat} {sadr se : Simple C PrimTy.uint},
  dl{ [ sadr .transfer(se); ] ⇝ { net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.transferNoCallbackBox

/-! ## 2 · The walk -/

/-- `[ to.transfer(5); ] true` as a `⊢` walk: one rule, one goal, a checked
sequent (`Calculus/Sequents.lean`); the chain is
`Chains.Payment.Transfer5.box`. -/
theorem transferBox : ⊢ dl!{ [ to.transfer(5); ] true } := by
  apply update .transferNoCallbackBox
  show sequent!{ { net := if(to = this) then net else store(net, at(to), select(net, at(to)) - 5) }
      ⟹ [ ] true }
  apply empty
  show sequent!{ { net := if(to = this) then net else store(net, at(to), select(net, at(to)) - 5) }
      ⟹ true }
  refine close ?_
  sol_symex
  sol_close

end Solidity.Examples.Tactics.Payment
