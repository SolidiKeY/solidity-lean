import Solidity.Calculus.Sequents

/-!
# Payment: `transfer`, as `⊢` walks

`sadr.transfer(se);` has one rule for both modalities, `transferNoCallback`,
which books the payment on the ledger and nothing else: where `0 <= se`, the
amount a word, the update `{ net := store(net, at(sadr), net(sadr) - se) }`,
and where not a `revert();`, which the box closes to `true` (`revertBox`).
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
info: @Taclet.transferNoCallback : ∀ {C : Contract} {k : Nat} {m : Modality} {sadr se : Simple C PrimTy.uint},
  dl{ ⟨[ sadr .transfer(se); ]⟩ ⇝
    0 <= se ⟹
        { net := store(net, at(sadr), net(sadr) - se) } ⟨[ ]⟩ ;
      ¬(0 <= se) ⟹ ⟨[ revert(); ]⟩ }
-/
#guard_msgs in #check @Taclet.transferNoCallback

/-! ## 2 · The walk -/

/-- `[ to.transfer(5); ] true` as a `⊢` walk: one rule, two goals, each a
checked sequent (`Calculus/Sequents.lean`); the chain is
`Chains.Payment.Transfer5.box`. -/
theorem transferBox : ⊢ dl!{ [ to.transfer(5); ] true } := by
  apply guard .transferNoCallback
  · show sequent!{ 0 <= 5, { net := store(net, at(to), select(net, at(to)) - 5) } ⟹ [ ] true }
    apply empty
    show sequent!{ 0 <= 5, { net := store(net, at(to), select(net, at(to)) - 5) } ⟹ true }
    refine close ?_
    sol_symex
    sol_close
  · show sequent!{ ¬(0 <= 5) ⟹ [ revert(); ] true }
    apply done .revertBox
    show sequent!{ ¬(0 <= 5) ⟹ true }
    refine close ?_
    sol_symex
    sol_close

end Solidity.Examples.Tactics.Payment
