import Solidity.Calculus.Sequents

/-!
# Payment: `transfer`, as `⊢` walks

`sadr.transfer(se);` has one rule for both modalities, `transferNoCallback`,
whose guard is the EVM's value-transfer check: where `0 <= se <= selfBalance`
the booking, and where not a `revert();`, which the box closes to `true`
(`revertBox`) and the diamond to `false` (`revertDiamond`).  The worked
examples' traces are `Examples/Chains/Payment.lean`'s; here the sequents themselves,
each with its whole context, are the goals of a walk, each a checked line
`show sequent!{ Γ ⟹ ψ }` (`Calculus/Sequents.lean`), and what the box proves.

The frame of a transfer and the ledger's runs are `Net.lean`'s; the
callback rules are `Callback.lean`'s.
-/

namespace Solidity.Examples.Tactics.Payment

open Proves

local instance : InContract := ⟨StandardExample⟩

/-! ## 1 · The rule -/

/--
info: @Taclet.transferNoCallback : ∀ {C : Contract} {k : Nat} {m : Modality} {sadr se : Simple C PrimTy.uint},
  dl{ ⟨[ sadr .transfer(se); ]⟩ ⇝
    0 <= se ∧ se <= selfBalance ⟹
        { selfBalance := selfBalance - se ‖ net := store(net, at(sadr), net(sadr) - se) } ⟨[ ]⟩ ;
      ¬(0 <= se ∧ se <= selfBalance) ⟹ ⟨[ revert(); ]⟩ }
-/
#guard_msgs in #check @Taclet.transferNoCallback

/-! ## 2 · The walks -/

/-- `[ to.transfer(5); ] true` as a `⊢` walk: one rule, two goals, each a
checked sequent (`Calculus/Sequents.lean`); the chain is
`Chains.Payment.Transfer5.box`. -/
theorem transferBox : ⊢ dl!{ [ to.transfer(5); ] true } := by
  apply guard .transferNoCallback
  · show sequent!{ 0 <= 5 <= selfBalance,
      { selfBalance := selfBalance - 5 ‖ net := store(net, at(to), select(net, at(to)) - 5) }
        ⟹ [ ] true }
    apply empty
    show sequent!{ 0 <= 5 <= selfBalance,
      { selfBalance := selfBalance - 5 ‖ net := store(net, at(to), select(net, at(to)) - 5) }
        ⟹ true }
    refine close ?_
    sol_symex
    sol_close
  · show sequent!{ ¬(0 <= 5 <= selfBalance) ⟹ [ revert(); ] true }
    apply done .revertBox
    show sequent!{ ¬(0 <= 5 <= selfBalance) ⟹ true }
    refine close ?_
    sol_symex
    sol_close

/-- The funded diamond as a `⊢` walk, two sequents: the context
`to >= 0, 5 <= selfBalance` is in front of both goals, and the `false` the
revert leaves is proved from it. -/
theorem transferDiamond :
    sequent!{ to >= 0, 5 <= selfBalance ⟹ ⟨ to.transfer(5); ⟩ true } := by
  apply guard .transferNoCallback
  · show sequent!{ to >= 0, 5 <= selfBalance, 0 <= 5 <= selfBalance,
      { selfBalance := selfBalance - 5 ‖ net := store(net, at(to), select(net, at(to)) - 5) }
        ⟹ ⟨ ⟩ true }
    apply empty
    refine close ?_
    sol_symex
    sol_close
  · show sequent!{ to >= 0, 5 <= selfBalance, ¬(0 <= 5 <= selfBalance) ⟹ ⟨ revert(); ⟩ true }
    apply done .revertDiamond
    show sequent!{ to >= 0, 5 <= selfBalance, ¬(0 <= 5 <= selfBalance) ⟹ false }
    refine close ?_
    sol_symex
    sol_close

/-! ## 3 · What the box proves

The booking goal keeps the funds check as an assumption, so the box
continues only in states the EVM reaches. -/

/-- `selfBalance < 5 → [ to.transfer(5); ] false`: the two assumptions of the
booking goal contradict each other. -/
theorem boxUnderfunded : ⊨ dl!{ selfBalance < 5 → [ to.transfer(5); ] false } := by
  sol_symex
  sol_close

/-- `[ to.transfer(5); ] selfBalance >= 0`, with no assumption. -/
theorem boxNonNegative : ⊨ dl!{ [ to.transfer(5); ] selfBalance >= 0 } := by
  sol_symex
  sol_close

end Solidity.Examples.Tactics.Payment
