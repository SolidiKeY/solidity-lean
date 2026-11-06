import Solidity.Source.World
import Solidity.Source.MonetaryLaws

/-! Explicit monetary range on both the current world and saved journal
accounts. This is not a theorem of whole Source/EVM reachability. -/
namespace Solidity.Source
open Solidity.Roadmap (Address Word)
variable {D : Layout} {L T : Address → SPath → STy}

def World.BalancesFit (world : World D L) : Prop :=
  ∀ address, Monetary.Fits (world.accounts address).balance

def Entry.BalanceFits : Entry D L T → Prop
  | .account _ old => Monetary.Fits old.balance
  | .transient _ _ => True

def ExecState.BalancesFit (state : ExecState D L T) : Prop :=
  state.world.BalancesFit ∧ ∀ entry, entry ∈ state.journal → entry.BalanceFits

theorem World.wordView_exact (world : World D L) (fit : world.BalancesFit) (address : Address) :
    (Monetary.wordView (world.accounts address).balance).val = (world.accounts address).balance :=
  Monetary.wordView_exact _ (fit address)

theorem World.set_balancesFit (world : World D L) (address : Address) (account : Account D (L address))
    (old : world.BalancesFit) (new : Monetary.Fits account.balance) :
    (world.set address account).BalancesFit := by
  intro other
  by_cases equal : other = address
  · subst other
    rw [World.set_get]
    exact new
  · rw [World.set_other world equal]
    exact old other

theorem ExecState.apply_balanceFits (state : ExecState D L T) (address : Address)
    (balance : Monetary.Balance) (old : state.BalancesFit) (new : Monetary.Fits balance) :
    (state.apply (.account address (fun account => account.withBalance balance))).BalancesFit := by
  refine ⟨World.set_balancesFit _ _ _ old.1 new, ?_⟩
  intro entry member
  change entry ∈ .account address (state.world.accounts address) :: state.journal at member
  rcases List.mem_cons.mp member with equal | previous
  · cases equal
    exact old.1 address
  · exact old.2 entry previous

theorem ExecState.undo_balancesFit (state : ExecState D L T) (fit : state.BalancesFit) :
    state.undo.BalancesFit := by
  rcases state with ⟨world,transient,journal⟩
  rcases fit with ⟨current,saved⟩
  cases journal with
  | nil => exact ⟨current,saved⟩
  | cons entry rest =>
    have tailFit : ∀ item, item ∈ rest → item.BalanceFits :=
      fun item member => saved item (List.mem_cons_of_mem _ member)
    cases entry with
    | account address old =>
      exact ⟨World.set_balancesFit _ _ _ current
        (saved _ (List.mem_cons_self)),tailFit⟩
    | transient address old => exact ⟨current,tailFit⟩

theorem ExecState.undoN_balancesFit (state : ExecState D L T) (count : Nat) (fit : state.BalancesFit) :
    (state.undoN count).BalancesFit := by
  induction count generalizing state with
  | zero => exact fit
  | succ count previous => exact previous state.undo (state.undo_balancesFit fit)

theorem CallFrame.rollback_balancesFit (frame : CallFrame) (state : ExecState D L T)
    (fit : state.BalancesFit) : (frame.rollback state).BalancesFit :=
  state.undoN_balancesFit _ fit

theorem ExecState.endTx_balancesFit (state : ExecState D L T) (fit : state.BalancesFit) :
    state.endTx.BalancesFit := by
  refine ⟨fit.1, ?_⟩
  intro entry impossible
  cases impossible

/-- Successful transfers preserve current and saved-account range. The sender
range is an explicit input; recipient range follows from the actual guard. -/
theorem ExecState.transferNat_balancesFit (state result : ExecState D L T)
    (src dst : Address) (amount : Monetary.Balance) (fit : state.BalancesFit)
    (execution : state.transferNat src dst amount = some result) : result.BalancesFit := by
  simp only [ExecState.transferNat] at execution
  split at execution
  · split at execution
    · cases execution
      exact fit
    · cases execution
  · split at execution
    next guard =>
      cases execution
      exact ExecState.apply_balanceFits _ _ _
        (state.apply_balanceFits src _ fit
          (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (fit.1 src))) guard.2
    next => cases execution

/-- Existing word-valued calls use the same actual natural transfer. -/
theorem ExecState.transfer_balancesFit (state result : ExecState D L T)
    (src dst : Address) (value : Word) (fit : state.BalancesFit)
    (execution : state.transfer src dst value = some result) : result.BalancesFit :=
  state.transferNat_balancesFit result src dst value.val fit execution

/-- Exact account money can represent the first value outside the word range. -/
theorem Account.wide_balance (layout : SPath → STy) :
    ((Account.empty (D := D) layout).withBalance Monetary.wide).balance = 2 ^ 256 := rfl

/-- A present in-range world can have an out-of-range saved account. This
control prevents treating the current-world predicate as a rollback invariant. -/
def savedWide (address : Address) : ExecState D L T :=
  ⟨⟨fun a => Account.empty (L a)⟩, Transient.empty,
    [.account address ((Account.empty (L address)).withBalance Monetary.wide)]⟩

theorem savedWide_current_fit (address : Address) :
    (savedWide (D := D) (L := L) (T := T) address).world.BalancesFit := by
  intro other
  exact (by decide : Monetary.Fits 0)

theorem savedWide_undo_not_fit (address : Address) :
    ¬ (savedWide (D := D) (L := L) (T := T) address).undo.world.BalancesFit := by
  intro fit
  have atAddress := fit address
  change Monetary.Fits ((World.set _ address _).accounts address).balance at atAddress
  rw [World.set_get] at atAddress
  exact Monetary.wide_not_fits atAddress

end Solidity.Source

/-- info: 'Solidity.Source.World.wordView_exact' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.World.wordView_exact

/-- info: 'Solidity.Source.World.set_balancesFit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.World.set_balancesFit

/-- info: 'Solidity.Source.ExecState.apply_balanceFits' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.ExecState.apply_balanceFits

/-- info: 'Solidity.Source.ExecState.undo_balancesFit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.ExecState.undo_balancesFit

/-- info: 'Solidity.Source.ExecState.undoN_balancesFit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.ExecState.undoN_balancesFit

/-- info: 'Solidity.Source.CallFrame.rollback_balancesFit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.CallFrame.rollback_balancesFit

/-- info: 'Solidity.Source.ExecState.endTx_balancesFit' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.ExecState.endTx_balancesFit

/-- info: 'Solidity.Source.ExecState.transferNat_balancesFit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.ExecState.transferNat_balancesFit

/-- info: 'Solidity.Source.ExecState.transfer_balancesFit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.ExecState.transfer_balancesFit

/-- info: 'Solidity.Source.Account.wide_balance' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Account.wide_balance

/-- info: 'Solidity.Source.savedWide_current_fit' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.savedWide_current_fit

/-- info: 'Solidity.Source.savedWide_undo_not_fit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.savedWide_undo_not_fit
