import Solidity.Calculus.Chains
import Solidity.Calculus.Close
import Solidity.Calculus.Sequents
import Solidity.FreshNames

/-!
# Payment: `transfer`, as chains

The calculus's worked examples of `transfer` under the box, each a `calc`
(`Calculus/Chains.lean`).  `transferNoCallback` books the payment on the
ledger and nothing else: under `0 <= se`, the amount a word, the update
`{ net := store(net, at(sadr), net(sadr) - se) }`, else a `revert();`, which
the box closes; the two goals are one formula, `(c ⟹ ψ₁) ∧ (¬c ⟹ ψ₂)`.
Where a chain differs from the printed lines: the rule leaves `⟨[ ]⟩` after
the booking, which `emptyModality` drops; a capture `{ pv := x + 2 }` stays in
front of both goals instead of being applied; the receiver's capture is a
`uint pv`, not an `address payable`.
-/

namespace Solidity.Examples.Chains.Payment

local instance : InContract := ⟨StandardExample⟩

/-- The printed name of the captured amount or receiver. -/
def names : FreshTable := [("pv", "se1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes StandardExample names).isEmpty

/-! ## Example: Symbolic Execution of `to.transfer(5)` -/

namespace Transfer5

variable (φ : Post StandardExample)

/-- `[ to.transfer(5); ] φ`: the second goal is a revert, which `revertBox`
closes. -/
def box :
    dl![.box]{ ⟨[ to.transfer(5); ]⟩ φ }
    ~*> dl![.box]{ (0 <= 5 ⟹ { net := store(net, at(to), select(net, at(to)) - 5) } φ) ∧
            (¬(0 <= 5) ⟹ true) } :=
  calc dl![.box]{ ⟨[ to.transfer(5); ]⟩ φ }
    _ ~[transferNoCallback]~>
        dl![.box]{ (0 <= 5 ⟹ { net := store(net, at(to), select(net, at(to)) - 5) } ⟨[ ]⟩ φ) ∧
            (¬(0 <= 5) ⟹ ⟨[ revert(); ]⟩ φ) } := rfl
    _ ~[emptyModality]~>
        dl![.box]{ (0 <= 5 ⟹ { net := store(net, at(to), select(net, at(to)) - 5) } φ) ∧
            (¬(0 <= 5) ⟹ ⟨[ revert(); ]⟩ φ) } := rfl
    _ ~[revertBox]~>
        dl![.box]{ (0 <= 5 ⟹ { net := store(net, at(to), select(net, at(to)) - 5) } φ) ∧
            (¬(0 <= 5) ⟹ true) } := by
      sol_chain

end Transfer5

/-! ## Example: Symbolic Execution of `to.transfer(x + 2)` -/

namespace TransferSum

variable (φ : Post StandardExample)

/-- `to.transfer(x + 2);` — the amount is nonsimple, so it is captured first
(`transfer_unfold_rightSndArgument`); the guard and the booking read the
capture. -/
def split :
    dl![.box]{ ⟨[ to.transfer(x + 2); ]⟩ φ }
    ~*> dl![.box]{ { pv := x + 2 }
          ((0 <= pv ⟹ { net := store(net, at(to), select(net, at(to)) - pv) } ⟨[ ]⟩ φ) ∧
            (¬(0 <= pv) ⟹ ⟨[ revert(); ]⟩ φ)) } :=
  calc dl![.box]{ ⟨[ to.transfer(x + 2); ]⟩ φ }
    _ ~[transfer_unfold_rightSndArgument]~> dl![.box]{ ⟨[ uint pv = x + 2; to.transfer(pv); ]⟩ φ } := by
      sol_chain
    _ ~*> dl![.box]{ { pv := x + 2 } ⟨[ to.transfer(pv); ]⟩ φ } := by sol_chain
    _ ~[transferNoCallback]~>
        dl![.box]{ { pv := x + 2 }
          ((0 <= pv ⟹ { net := store(net, at(to), select(net, at(to)) - pv) } ⟨[ ]⟩ φ) ∧
            (¬(0 <= pv) ⟹ ⟨[ revert(); ]⟩ φ)) } := by
      sol_chain

/-- `[ to.transfer(x + 2); ] φ`: the box closes the second goal. -/
def box :
    dl![.box]{ ⟨[ to.transfer(x + 2); ]⟩ φ }
    ~*> dl![.box]{ { pv := x + 2 }
          ((0 <= pv ⟹ { net := store(net, at(to), select(net, at(to)) - pv) } φ) ∧
            (¬(0 <= pv) ⟹ true)) } :=
  calc dl![.box]{ ⟨[ to.transfer(x + 2); ]⟩ φ }
    _ ~*> _ := split φ
    _ ~*> _ := by sol_chain

/-- `[ to.transfer(x + 2); ] true`: the box chain's last line, at `true`. -/
theorem box_valid : ⊨ dl!{ [ to.transfer(x + 2); ] true } :=
  (box { fml := dl!{ true } }).valid (by sol_close)

end TransferSum

/-! ## Example: Symbolic Execution of `owner.transfer(5)` -/

namespace TransferOwner

variable (φ : Post StandardExample)

/-- `owner.transfer(5);` — the receiver is the nonsimple part, captured by
`transfer_unfold_leftFstReceiver`; the booking is at the capture. -/
def split :
    dl![.box]{ ⟨[ owner.transfer(5); ]⟩ φ }
    ~*> dl![.box]{ { pv := select(storage, owner) }
          ((0 <= 5 ⟹ { net := store(net, at(pv), select(net, at(pv)) - 5) } ⟨[ ]⟩ φ) ∧
            (¬(0 <= 5) ⟹ ⟨[ revert(); ]⟩ φ)) } :=
  calc dl![.box]{ ⟨[ owner.transfer(5); ]⟩ φ }
    _ ~[transfer_unfold_leftFstReceiver]~> dl![.box]{ ⟨[ uint pv = owner; pv.transfer(5); ]⟩ φ } := by
      sol_chain
    _ ~*> dl![.box]{ { pv := select(storage, owner) } ⟨[ pv.transfer(5); ]⟩ φ } := by sol_chain
    _ ~[transferNoCallback]~>
        dl![.box]{ { pv := select(storage, owner) }
          ((0 <= 5 ⟹ { net := store(net, at(pv), select(net, at(pv)) - 5) } ⟨[ ]⟩ φ) ∧
            (¬(0 <= 5) ⟹ ⟨[ revert(); ]⟩ φ)) } := by
      sol_chain

/-- `[ owner.transfer(5); ] φ`: the box closes the second goal. -/
def box :
    dl![.box]{ ⟨[ owner.transfer(5); ]⟩ φ }
    ~*> dl![.box]{ { pv := select(storage, owner) }
          ((0 <= 5 ⟹ { net := store(net, at(pv), select(net, at(pv)) - 5) } φ) ∧
            (¬(0 <= 5) ⟹ true)) } :=
  calc dl![.box]{ ⟨[ owner.transfer(5); ]⟩ φ }
    _ ~*> _ := split φ
    _ ~*> _ := by sol_chain

/-- `[ owner.transfer(5); ] true`: the box chain's last line, at `true`. -/
theorem box_valid : ⊨ dl!{ [ owner.transfer(5); ] true } :=
  (box { fml := dl!{ true } }).valid (by sol_close)

end TransferOwner

end Solidity.Examples.Chains.Payment
