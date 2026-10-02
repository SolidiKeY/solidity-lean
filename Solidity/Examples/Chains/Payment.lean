import Solidity.Calculus.Chains
import Solidity.Calculus.Close
import Solidity.Calculus.Sequents
import Solidity.FreshNames

/-!
# Payment: `transfer`, as chains

The calculus's four worked examples of `transfer`, each a `calc`
(`Calculus/Chains.lean`).  `transferNoCallback` serves both modalities and
splits on the funds check; the two goals are one formula, `(c ⟹ ψ₁) ∧ (¬c ⟹ ψ₂)`.
Where a chain differs from the printed lines: the rule leaves `⟨[ ]⟩` after
the booking, which `emptyModality` drops; a sequent's context stays outside
the split; a capture `{ pv := x + 2 }` stays in front of both goals instead of
being applied; the receiver's capture is a `uint pv`, not an `address payable`.
Under `.diamond` the context `to >= 0` binds `to`, and a chain's last line is
valid under the funds it assumes (`Fml.Steps.valid_in`).
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

/-- `[ to.transfer(5); ] φ`: under the box the second goal is a revert, which
`revertBox` closes. -/
def box :
    dl![.box]{ ⟨[ to.transfer(5); ]⟩ φ }
    ~*> dl![.box]{ (0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(to), select(net, at(to)) - 5) } φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ true) } :=
  calc dl![.box]{ ⟨[ to.transfer(5); ]⟩ φ }
    _ ~[transferNoCallback]~>
        dl![.box]{ (0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(to), select(net, at(to)) - 5) }
                ⟨[ ]⟩ φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ ⟨[ revert(); ]⟩ φ) } := rfl
    _ ~[emptyModality]~>
        dl![.box]{ (0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(to), select(net, at(to)) - 5) } φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ ⟨[ revert(); ]⟩ φ) } := rfl
    _ ~[revertBox]~>
        dl![.box]{ (0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(to), select(net, at(to)) - 5) } φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ true) } := by
      sol_chain

/-- `5 <= selfBalance ⟹ ⟨ to.transfer(5); ⟩ φ`: the split is the same, and with
`5 <= selfBalance` the `false` that `revertDiamond` leaves is provable, its
antecedent contradicting itself.  `to >= 0` binds `to`. -/
def diamond :
    dl![.diamond]{ to >= 0, 5 <= selfBalance ⟹ ⟨[ to.transfer(5); ]⟩ φ }
    ~*> dl![.diamond]{ to >= 0, 5 <= selfBalance ⟹
          (0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(to), select(net, at(to)) - 5) } φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ false) } :=
  calc dl![.diamond]{ to >= 0, 5 <= selfBalance ⟹ ⟨[ to.transfer(5); ]⟩ φ }
    _ ~[transferNoCallback]~>
        dl![.diamond]{ to >= 0, 5 <= selfBalance ⟹
          (0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(to), select(net, at(to)) - 5) }
                ⟨[ ]⟩ φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ ⟨[ revert(); ]⟩ φ) } := rfl
    _ ~[emptyModality]~>
        dl![.diamond]{ to >= 0, 5 <= selfBalance ⟹
          (0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(to), select(net, at(to)) - 5) } φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ ⟨[ revert(); ]⟩ φ) } := rfl
    _ ~[revertDiamond]~>
        dl![.diamond]{ to >= 0, 5 <= selfBalance ⟹
          (0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(to), select(net, at(to)) - 5) } φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ false) } := by
      sol_chain

/-- The funded diamond is valid: its chain's last line, at `true`. -/
theorem diamond_valid :
    ⊨ dl!{ to >= 0 → 5 <= selfBalance → ⟨ to.transfer(5); ⟩ true } :=
  (diamond { fml := dl!{ true } }).valid (by sol_close)

end Transfer5

/-! ## Example: Symbolic Execution of `to.transfer(x + 2)` -/

namespace TransferSum

variable (m : Modality) (φ : Post StandardExample)

/-- `to.transfer(x + 2);` — the amount is nonsimple, so it is captured first
(`transfer_unfold_rightSndArgument`); the split reads the capture into the
funds check.  The trace is the same under each modality. -/
def split :
    dl![m]{ ⟨[ to.transfer(x + 2); ]⟩ φ }
    ~*> dl![m]{ { pv := x + 2 }
          ((0 <= pv <= selfBalance ⟹
              { selfBalance := selfBalance - pv ‖ net := store(net, at(to), select(net, at(to)) - pv) }
                ⟨[ ]⟩ φ) ∧
            (¬(0 <= pv <= selfBalance) ⟹ ⟨[ revert(); ]⟩ φ)) } :=
  calc dl![m]{ ⟨[ to.transfer(x + 2); ]⟩ φ }
    _ ~[transfer_unfold_rightSndArgument]~> dl![m]{ ⟨[ uint pv = x + 2; to.transfer(pv); ]⟩ φ } := by
      sol_chain
    _ ~*> dl![m]{ { pv := x + 2 } ⟨[ to.transfer(pv); ]⟩ φ } := by sol_chain
    _ ~[transferNoCallback]~>
        dl![m]{ { pv := x + 2 }
          ((0 <= pv <= selfBalance ⟹
              { selfBalance := selfBalance - pv ‖ net := store(net, at(to), select(net, at(to)) - pv) }
                ⟨[ ]⟩ φ) ∧
            (¬(0 <= pv <= selfBalance) ⟹ ⟨[ revert(); ]⟩ φ)) } := by
      sol_chain

/-- `[ to.transfer(x + 2); ] φ`: the box closes the second goal. -/
def box :
    dl![.box]{ ⟨[ to.transfer(x + 2); ]⟩ φ }
    ~*> dl![.box]{ { pv := x + 2 }
          ((0 <= pv <= selfBalance ⟹
              { selfBalance := selfBalance - pv ‖ net := store(net, at(to), select(net, at(to)) - pv) } φ) ∧
            (¬(0 <= pv <= selfBalance) ⟹ true)) } :=
  calc dl![.box]{ ⟨[ to.transfer(x + 2); ]⟩ φ }
    _ ~*> _ := split .box φ
    _ ~*> _ := by sol_chain

/-- `⟨ to.transfer(x + 2); ⟩ φ`: the diamond is left with
`¬(0 <= x + 2 <= selfBalance) ⟹ false`, under the capture. -/
def diamond :
    dl![.diamond]{ ⟨[ to.transfer(x + 2); ]⟩ φ }
    ~*> dl![.diamond]{ { pv := x + 2 }
          ((0 <= pv <= selfBalance ⟹
              { selfBalance := selfBalance - pv ‖ net := store(net, at(to), select(net, at(to)) - pv) } φ) ∧
            (¬(0 <= pv <= selfBalance) ⟹ false)) } :=
  calc dl![.diamond]{ ⟨[ to.transfer(x + 2); ]⟩ φ }
    _ ~*> _ := split .diamond φ
    _ ~*> _ := by sol_chain

/-- `[ to.transfer(x + 2); ] true`: the box chain's last line, at `true`. -/
theorem box_valid : ⊨ dl!{ [ to.transfer(x + 2); ] true } :=
  (box { fml := dl!{ true } }).valid (by sol_close)

/-- `⟨ to.transfer(x + 2); ⟩ true`, funded: the diamond chain's last line at
`true`, closed under the funds check `0 <= x + 2 <= selfBalance` (and
`to >= 0`, which binds `to`). -/
theorem diamond_valid :
    ⊨ dl!{ to >= 0, 0 <= x + 2 <= selfBalance ⟹ ⟨ to.transfer(x + 2); ⟩ true } :=
  (diamond { fml := dl!{ true } }).valid_in
    [.pre dl!{ to >= 0 }, .pre dl!{ 0 <= x + 2 <= selfBalance }] (by sol_close)

end TransferSum

/-! ## Example: Symbolic Execution of `owner.transfer(5)` -/

namespace TransferOwner

variable (m : Modality) (φ : Post StandardExample)

/-- `owner.transfer(5);` — the receiver is the nonsimple part, captured by
`transfer_unfold_leftFstReceiver`; the funds check does not mention it. -/
def split :
    dl![m]{ ⟨[ owner.transfer(5); ]⟩ φ }
    ~*> dl![m]{ { pv := select(storage, owner) }
          ((0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(pv), select(net, at(pv)) - 5) }
                ⟨[ ]⟩ φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ ⟨[ revert(); ]⟩ φ)) } :=
  calc dl![m]{ ⟨[ owner.transfer(5); ]⟩ φ }
    _ ~[transfer_unfold_leftFstReceiver]~> dl![m]{ ⟨[ uint pv = owner; pv.transfer(5); ]⟩ φ } := by
      sol_chain
    _ ~*> dl![m]{ { pv := select(storage, owner) } ⟨[ pv.transfer(5); ]⟩ φ } := by sol_chain
    _ ~[transferNoCallback]~>
        dl![m]{ { pv := select(storage, owner) }
          ((0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(pv), select(net, at(pv)) - 5) }
                ⟨[ ]⟩ φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ ⟨[ revert(); ]⟩ φ)) } := by
      sol_chain

/-- `[ owner.transfer(5); ] φ`: the box closes the second goal. -/
def box :
    dl![.box]{ ⟨[ owner.transfer(5); ]⟩ φ }
    ~*> dl![.box]{ { pv := select(storage, owner) }
          ((0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(pv), select(net, at(pv)) - 5) } φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ true)) } :=
  calc dl![.box]{ ⟨[ owner.transfer(5); ]⟩ φ }
    _ ~*> _ := split .box φ
    _ ~*> _ := by sol_chain

/-- `⟨ owner.transfer(5); ⟩ φ`: the diamond is left with the funds
obligation, under the capture. -/
def diamond :
    dl![.diamond]{ ⟨[ owner.transfer(5); ]⟩ φ }
    ~*> dl![.diamond]{ { pv := select(storage, owner) }
          ((0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(pv), select(net, at(pv)) - 5) } φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ false)) } :=
  calc dl![.diamond]{ ⟨[ owner.transfer(5); ]⟩ φ }
    _ ~*> _ := split .diamond φ
    _ ~*> _ := by sol_chain

/-- `[ owner.transfer(5); ] true`: the box chain's last line, at `true`. -/
theorem box_valid : ⊨ dl!{ [ owner.transfer(5); ] true } :=
  (box { fml := dl!{ true } }).valid (by sol_close)

/-- `⟨ owner.transfer(5); ⟩ true`, funded: the diamond chain's last line at
`true`, under `5 <= selfBalance`; `owner >= 0` says the storage holds a number
at `owner`, which the capture reads. -/
theorem diamond_valid :
    ⊨ dl!{ owner >= 0, 5 <= selfBalance ⟹ ⟨ owner.transfer(5); ⟩ true } :=
  (diamond { fml := dl!{ true } }).valid_in
    [.pre dl!{ owner >= 0 }, .pre dl!{ 5 <= selfBalance }] (by sol_close)

end TransferOwner

/-! ## Example: An Unfunded Transfer

Nothing is known of `selfBalance`.  The box is `Transfer5.box` at `true`; the
diamond, at `true`, isolates the funding: the booking goal is trivial, and the
revert goal is the funds obligation, which no rule closes. -/

namespace Unfunded

/-- `[ to.transfer(5); ] true`: the revert goal closes, and execution goes on
at the booking goal alone. -/
def box :
    dl![.box]{ ⟨[ to.transfer(5); ]⟩ true }
    ~*> dl![.box]{ (0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(to), select(net, at(to)) - 5) } true) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ true) } := by
  sol_chain

/-- `⟨ to.transfer(5); ⟩ true`, to the funds obligation. -/
def diamond :
    dl!{ ⟨ to.transfer(5); ⟩ true }
    ~*> dl!{ (0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(to), select(net, at(to)) - 5) } true) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ false) } := by
  sol_chain

/-- With `3` wei the obligation is false, and so is the formula, `to` bound. -/
example : ¬ (⊨ dl!{ to == 1 → ⟨ to.transfer(5); ⟩ true }) := fun h =>
  h (({ Semantics.State.exampleStore with selfBalance := 3 } : Semantics.State).setEnv (.user "to")
      (.val (.int 1)))
    (holds_eqD_iff.2 ⟨_, rfl, rfl⟩)

end Unfunded

end Solidity.Examples.Chains.Payment
