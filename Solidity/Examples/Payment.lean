import Solidity.Calculus.Chains
import Solidity.Calculus.Close

/-!
# Payment: `transfer`, in the calculus's lines

`sadr.transfer(se);` has one rule for both modalities, `transferNoCallback`,
whose guard is the EVM's value-transfer check: where
`0 <= se <= selfBalance` the booking
`{ selfBalance := selfBalance - se ‖ net := store(net, at(sadr), select(net, at(sadr)) - se) }`,
and where not a `revert();`.  The modalities part company only at that
revert: the box closes it to `true` (`revertBox`), the diamond to `false`
(`revertDiamond`), the *sufficient funds* obligation.

Each worked example is a chain here (`Calculus/Chains.lean`), for any
postcondition `φ` and, where `⟨[ ]⟩` is written, any modality `m`.  The
two goals `S₁ ; S₂` are one formula, the two sequent lines
`(c ⟹ ψ₁) ∧ (¬c ⟹ ψ₂)` (`Notation.lean`: a line `Γ ⟹ ψ` is `a₁ → … → ψ`, and
prints with `→`).  Where the Lean line differs:

* the rule leaves `⟨[ ]⟩` after the booking, which `emptyModality` drops, one
  more step;
* a sequent's context stays outside the split: the
  `5 ≤ selfBalance, 0 ≤ 5 ≤ selfBalance ⟹ …` is
  `5 <= selfBalance ⟹ (0 <= 5 <= selfBalance ⟹ …) ∧ …`, and a capture
  `{ se1 := x + 2 }` stays in front of both goals, instead of being applied
  (`0 ≤ x + 2 ≤ selfBalance`, and `pv` merged into the booking);
* the fresh local is the rules' `se1`, a `uint` also for
  the receiver (not an `address payable`);
* past the split a line is at `.box` or `.diamond`, not `m`: the revert is
  the one rule that looks at it.

**Valid means every state.**  A free local may be unbound (a program
variable of KeY always has a value), and the booking's `at(to)` is stuck
where `to` is: so the funded diamond is valid with `to >= 0` among its
assumptions, which binds `to` to a number.  The box needs nothing.

The frame of a transfer and the ledger's runs are `Net.lean`'s; the
callback rules are `Callback.lean`'s.
-/

namespace Solidity.Examples.Payment

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

section Lines
variable (m : Modality) (φ : Post StandardExample)

/-! ## 2 · `to.transfer(5);` -/

/-- `to.transfer(5);`: one rule under either modality, two goals. -/
theorem transfer5 :
    dl![m]{ ⟨[ to.transfer(5); ]⟩ φ }
      ~[transferNoCallback]~>
        dl![m]{ (0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(to), select(net, at(to)) - 5) }
                ⟨[ ]⟩ φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ ⟨[ revert(); ]⟩ φ) } := rfl

/-- `[ to.transfer(5); ] φ`: the second goal is a revert, which `revertBox`
closes.  It is also the unfunded transfer under the box: nothing is
known of `selfBalance`, and the box never has to establish it. -/
def transfer5Box :
    dl![.box]{ ⟨[ to.transfer(5); ]⟩ φ }
    ~*> dl![.box]{ (0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(to), select(net, at(to)) - 5) } φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ true) } :=
  calc dl![.box]{ ⟨[ to.transfer(5); ]⟩ φ }
    _ ~[transferNoCallback]~>
        dl![.box]{ (0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(to), select(net, at(to)) - 5) }
                ⟨[ ]⟩ φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ ⟨[ revert(); ]⟩ φ) } := transfer5 .box φ
    _ ~[emptyModality]~>
        dl![.box]{ (0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(to), select(net, at(to)) - 5) } φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ ⟨[ revert(); ]⟩ φ) } := rfl
    _ ~[revertBox]~>
        dl![.box]{ (0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(to), select(net, at(to)) - 5) } φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ true) } := by
      sol_chain

/-- `[ to.transfer(5); ] true` as a walk: one rule, two goals. -/
theorem transferBox : ⊢ dl!{ [ to.transfer(5); ] true } := by
  apply guard .transferNoCallback
  · -- dl{ 0 <= 5 ∧ 5 <= selfBalance, { selfBalance := selfBalance - 5 ‖ … } ⟹ [ ] true }
    apply empty
    refine close ?_
    sol_symex
    sol_close
  · -- dl{ ¬(0 <= 5 ∧ 5 <= selfBalance) ⟹ [ revert(); ] true }
    apply done .revertBox
    refine close ?_
    sol_symex
    sol_close

/-- `5 <= selfBalance ⟹ ⟨ to.transfer(5); ⟩ φ`: the split is the same, and
with `5 <= selfBalance` the `false` that `revertDiamond` leaves is provable,
its antecedent contradicting itself.  `to >= 0` binds `to`. -/
def transfer5Diamond :
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
theorem transfer5Diamond_valid :
    ⊨ dl!{ to >= 0 → 5 <= selfBalance → ⟨ to.transfer(5); ⟩ true } :=
  (transfer5Diamond { fml := dl!{ true } }).valid (by sol_close)

/-! ## 3 · `to.transfer(x + 2);` — a nonsimple amount

The amount is captured first (`transfer_unfold_rightSndArgument`), under
either modality, and so is the split; the funds check reads the capture. -/

/-- `⟨[ to.transfer(x + 2); ]⟩ φ`, to the split. -/
def transferSum :
    dl![m]{ ⟨[ to.transfer(x + 2); ]⟩ φ }
    ~*> dl![m]{ { se1 := x + 2 }
          ((0 <= se1 <= selfBalance ⟹
              { selfBalance := selfBalance - se1 ‖ net := store(net, at(to), select(net, at(to)) - se1) }
                ⟨[ ]⟩ φ) ∧
            (¬(0 <= se1 <= selfBalance) ⟹ ⟨[ revert(); ]⟩ φ)) } :=
  calc dl![m]{ ⟨[ to.transfer(x + 2); ]⟩ φ }
    _ ~[transfer_unfold_rightSndArgument]~> dl![m]{ ⟨[ uint se1 = x + 2; to.transfer(se1); ]⟩ φ } := by
      sol_chain
    _ ~*> dl![m]{ { se1 := x + 2 } ⟨[ to.transfer(se1); ]⟩ φ } := by sol_chain
    _ ~[transferNoCallback]~>
        dl![m]{ { se1 := x + 2 }
          ((0 <= se1 <= selfBalance ⟹
              { selfBalance := selfBalance - se1 ‖ net := store(net, at(to), select(net, at(to)) - se1) }
                ⟨[ ]⟩ φ) ∧
            (¬(0 <= se1 <= selfBalance) ⟹ ⟨[ revert(); ]⟩ φ)) } := by
      sol_chain

/-- `[ to.transfer(x + 2); ] φ`: the box closes the second goal. -/
def transferSumBox :
    dl![.box]{ ⟨[ to.transfer(x + 2); ]⟩ φ }
    ~*> dl![.box]{ { se1 := x + 2 }
          ((0 <= se1 <= selfBalance ⟹
              { selfBalance := selfBalance - se1 ‖ net := store(net, at(to), select(net, at(to)) - se1) } φ) ∧
            (¬(0 <= se1 <= selfBalance) ⟹ true)) } :=
  calc dl![.box]{ ⟨[ to.transfer(x + 2); ]⟩ φ }
    _ ~*> _ := transferSum .box φ
    _ ~*> _ := by sol_chain

/-- `⟨ to.transfer(x + 2); ⟩ φ`: the diamond is left with
`¬(0 <= x + 2 <= selfBalance) ⟹ false`, under the capture. -/
def transferSumDiamond :
    dl![.diamond]{ ⟨[ to.transfer(x + 2); ]⟩ φ }
    ~*> dl![.diamond]{ { se1 := x + 2 }
          ((0 <= se1 <= selfBalance ⟹
              { selfBalance := selfBalance - se1 ‖ net := store(net, at(to), select(net, at(to)) - se1) } φ) ∧
            (¬(0 <= se1 <= selfBalance) ⟹ false)) } :=
  calc dl![.diamond]{ ⟨[ to.transfer(x + 2); ]⟩ φ }
    _ ~*> _ := transferSum .diamond φ
    _ ~*> _ := by sol_chain

/--
trace: ⊢ ⊨
    dl{
      { se1 := x + 2 }
        (((0 <= se1 ∧ se1 <= selfBalance) →
                { selfBalance := selfBalance - se1 ‖ net := store(net, at(to), net(to) - se1) } true) ∧
            (¬(0 <= se1 ∧ se1 <= selfBalance) → true)) }
-/
#guard_msgs in
/-- `[ to.transfer(x + 2); ] true`, by the strategy. -/
theorem transferCapturedAmount : ⊨ dl!{ [ to.transfer(x + 2); ] true } := by
  sol_symex
  trace_state
  sol_close

/-! ## 4 · `owner.transfer(5);` — a storage receiver

The receiver is the nonsimple part (`transfer_unfold_leftFstReceiver`).  The
funds check does not mention it, so capturing it changes nothing on the
revert goal. -/

/-- `⟨[ owner.transfer(5); ]⟩ φ`, to the split. -/
def transferOwner :
    dl![m]{ ⟨[ owner.transfer(5); ]⟩ φ }
    ~*> dl![m]{ { se1 := select(storage, owner) }
          ((0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(se1), select(net, at(se1)) - 5) }
                ⟨[ ]⟩ φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ ⟨[ revert(); ]⟩ φ)) } :=
  calc dl![m]{ ⟨[ owner.transfer(5); ]⟩ φ }
    _ ~[transfer_unfold_leftFstReceiver]~> dl![m]{ ⟨[ uint se1 = owner; se1.transfer(5); ]⟩ φ } := by
      sol_chain
    _ ~*> dl![m]{ { se1 := select(storage, owner) } ⟨[ se1.transfer(5); ]⟩ φ } := by sol_chain
    _ ~[transferNoCallback]~>
        dl![m]{ { se1 := select(storage, owner) }
          ((0 <= 5 <= selfBalance ⟹
              { selfBalance := selfBalance - 5 ‖ net := store(net, at(se1), select(net, at(se1)) - 5) }
                ⟨[ ]⟩ φ) ∧
            (¬(0 <= 5 <= selfBalance) ⟹ ⟨[ revert(); ]⟩ φ)) } := by
      sol_chain

/-- trace: ⊢ ⊨ dl{ [ uint se1 = owner; se1 .transfer(5); ] true } -/
#guard_msgs in
/-- `[ owner.transfer(5); ] true`, by the strategy. -/
theorem transferStorageReceiver : ⊨ dl!{ [ owner.transfer(5); ] true } := by
  sol_step
  trace_state
  sol_symex
  sol_close

end Lines

/-! ## 5 · An unfunded transfer

Nothing is known of `selfBalance`.  The box is `transfer5Box`.  The
diamond, at the postcondition `true`, isolates the funding: the booking goal
is trivial, and the revert goal is the funds obligation, which no rule
closes. -/

/-- `⟨ to.transfer(5); ⟩ true`, to the funds obligation. -/
def unfundedDiamond :
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

/-! ## 6 · What the box proves

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

end Solidity.Examples.Payment
