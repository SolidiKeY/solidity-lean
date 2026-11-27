import Solidity.Source.Semantics
import Solidity.Source.MonetaryStorage
import Solidity.Source.MonetaryAuthoritySource


namespace Solidity.Source
open Solidity.Roadmap (Address Word)
variable {D : Layout} {L T : Address → SPath → STy}


example (balance : Monetary.Balance) :
    (Monetary.wordView balance).val = balance ↔ Monetary.Fits balance :=
  ⟨fun equal => equal ▸ (Monetary.wordView balance).isLt, Monetary.wordView_exact balance⟩

theorem ExecState.apply_account_balancesFit (state : ExecState D L T) (address : Address)
    (update : Account D (L address) → Account D (L address)) (fit : state.BalancesFit)
    (new : Monetary.Fits (update (state.world.accounts address)).balance) :
    (state.apply (.account address update)).BalancesFit := by
  refine ⟨World.set_balancesFit _ _ _ fit.1 new, ?_⟩
  intro entry member
  change entry ∈ .account address (state.world.accounts address) :: state.journal at member
  rcases List.mem_cons.mp member with same | previous
  · cases same
    exact fit.1 address
  · exact fit.2 entry previous

theorem ExecState.apply_sameBalance_balancesFit (state : ExecState D L T) (address : Address)
    (update : Account D (L address) → Account D (L address))
    (same : ∀ account, (update account).balance = account.balance) (fit : state.BalancesFit) :
    (state.apply (.account address update)).BalancesFit :=
  state.apply_account_balancesFit address update fit
    (by rw [same]; exact fit.1 address)

theorem ExecState.apply_wordBalance_balancesFit (state : ExecState D L T) (address : Address)
    (amount : Word) (fit : state.BalancesFit) :
    (state.apply (.account address fun account => account.withBalance amount.val)).BalancesFit :=
  state.apply_balanceFits address amount.val fit amount.isLt

theorem ExecState.empty_balancesFit :
    (⟨⟨fun a => Account.empty (L a)⟩, Transient.empty, []⟩ : ExecState D L T).BalancesFit := by
  refine ⟨fun _ => (by decide : Monetary.Fits 0), ?_⟩
  intro entry impossible
  cases impossible


theorem St.init_balancesFit (E : Env) : (St.init E).ex.BalancesFit :=
  ExecState.empty_balancesFit

theorem deploy_open_balancesFit {E : Env} (state : ExecState E.layout E.lay E.lay)
    (addr : Address) (value : Word) (fit : state.BalancesFit)
    (guard : (state.world.accounts addr).balance + value.val < 2 ^ 256) :
    (state.apply (.account addr fun _ =>
      { balance := (state.world.accounts addr).balance + value.val, nonce := 1, code := none,
        storage := Storage.empty })).BalancesFit :=
  state.apply_account_balancesFit addr _ fit guard

theorem deploy_code_balancesFit {E : Env} (state : ExecState E.layout E.lay E.lay)
    (addr : Address) (code : Option Nat) (fit : state.BalancesFit) :
    (state.apply (.account addr fun x => { x with code := code })).BalancesFit :=
  state.apply_sameBalance_balancesFit addr _ (fun _ => rfl) fit

example {E : Env} (state : ExecState E.layout E.lay E.lay)
    (addr : Address) (code : Option Nat) :
    ((state.apply (.account addr fun account => { account with code := code })).world.accounts addr).balance =
      (state.world.accounts addr).balance := by
  simp only [ExecState.apply, World.set_get]

end Solidity.Source

namespace Solidity.Source.Monetary
open Solidity.Roadmap (Address Word)
open Solidity.Source (ExecState Layout SPath STy)


def Authority.Fit (authority : Authority) : Prop := BalancesFit authority.balance

theorem Authority.writeSource_balancesFit {D : Layout} {L T : Address → SPath → STy}
    (authority : Authority) (state : ExecState D L T) (address : Address)
    (fit : state.BalancesFit) (amount : Fits (authority.balance address)) :
    (authority.writeSource state address).BalancesFit :=
  state.apply_balanceFits address _ fit amount

theorem Authority.writeSource_fit {D : Layout} {L T : Address → SPath → STy}
    (authority : Authority) (state : ExecState D L T) (address : Address)
    (fit : state.BalancesFit) (range : authority.Fit) :
    (authority.writeSource state address).BalancesFit :=
  authority.writeSource_balancesFit state address fit (range address)

def Authority.writeSourceChecked? {D : Layout} {L T : Address → SPath → STy}
    (authority : Authority) (state : ExecState D L T) (address : Address) :
    Option (ExecState D L T) :=
  if Fits (authority.balance address) then some (authority.writeSource state address) else none

example {D : Layout} {L T : Address → SPath → STy}
    (authority : Authority) (state : ExecState D L T) (address : Address)
    (amount : ¬ Fits (authority.balance address)) :
    authority.writeSourceChecked? state address = none := by
  simp only [Authority.writeSourceChecked?, amount, if_false]

theorem Authority.writeSourceChecked?_balancesFit {D : Layout} {L T : Address → SPath → STy}
    (authority : Authority) (state result : ExecState D L T) (address : Address)
    (fit : state.BalancesFit) (execution : authority.writeSourceChecked? state address = some result) :
    result.BalancesFit := by
  unfold Authority.writeSourceChecked? at execution
  split at execution
  · next amount =>
    cases execution
    exact authority.writeSource_balancesFit state address fit amount
  · cases execution

theorem Authority.writeSourceChecked?_of_fits {D : Layout} {L T : Address → SPath → STy}
    (authority : Authority) (state : ExecState D L T) (address : Address)
    (amount : Fits (authority.balance address)) :
    authority.writeSourceChecked? state address = some (authority.writeSource state address) := by
  simp only [Authority.writeSourceChecked?, amount, if_true]

theorem Authority.set_fit (authority : Authority) (address : Address) (amount : Balance)
    (range : authority.Fit) (new : Fits amount) : (authority.set address amount).Fit := by
  intro other
  unfold Authority.set
  dsimp only
  split
  · exact new
  · exact range other

end Solidity.Source.Monetary

namespace Solidity.Source
open Solidity.Roadmap (Address Word)


private abbrev wL : Address → SPath → STy := fun _ _ => .bool
private abbrev wD : Layout := ⟨fun _ => [], fun _ => 0, fun _ => .bool⟩

def edgeState : ExecState wD wL wL :=
  ExecState.apply ⟨⟨fun a => Account.empty (wL a)⟩, Transient.empty, []⟩
    (.account 0 fun x => x.withBalance (2 ^ 256 - 1))

theorem edgeState_fit : edgeState.BalancesFit :=
  ExecState.apply_balanceFits _ 0 _ ExecState.empty_balancesFit (by decide)

theorem edgeState_balance : (edgeState.world.accounts 0).balance = 2 ^ 256 - 1 := by
  simp only [edgeState, ExecState.apply, World.set_get, Account.withBalance]

theorem transferNat_hypotheses_satisfiable :
    ∃ (state result : ExecState wD wL wL), state.BalancesFit ∧
      state.transferNat 0 1 (2 ^ 256 - 1) = some result ∧ result.BalancesFit := by
  have hne : (0 : Address) ≠ 1 := by decide
  have bd : (edgeState.world.accounts 1).balance = 0 := by
    simp only [edgeState, ExecState.apply, World.set_other _ (Ne.symm hne)]; rfl
  have execution : edgeState.transferNat 0 1 (2 ^ 256 - 1) =
      some ((edgeState.apply (.account 0 fun x => x.withBalance (2 ^ 256 - 1 - (2 ^ 256 - 1)))).apply
        (.account 1 fun x => x.withBalance (0 + (2 ^ 256 - 1)))) := by
    simp only [ExecState.transferNat, hne, if_false, edgeState_balance, bd]
    rfl
  exact ⟨edgeState, _, edgeState_fit, execution,
    ExecState.transferNat_balancesFit _ _ 0 1 _ edgeState_fit execution⟩

theorem unguarded_write_breaks :
    edgeState.BalancesFit ∧
      ¬ (edgeState.apply (.account 0 fun x => x.withBalance Monetary.wide)).BalancesFit := by
  refine ⟨edgeState_fit, ?_⟩
  intro fit
  have atZero := fit.1 0
  simp only [ExecState.apply, World.set_get, Account.withBalance] at atZero
  exact Monetary.wide_not_fits atZero

theorem wideAuthority_writeSource_breaks :
    ¬ (Monetary.wideAuthority.writeSource edgeState 0).BalancesFit ∧
      Monetary.wideAuthority.writeSourceChecked? edgeState 0 = none := by
  refine ⟨?_, ?_⟩
  · intro fit
    have atZero := fit.1 0
    rw [Monetary.Authority.source_amount] at atZero
    exact Monetary.wide_not_fits atZero
  · simp only [Monetary.Authority.writeSourceChecked?]
    exact if_neg Monetary.wide_not_fits

end Solidity.Source

/-- info: 'Solidity.Source.St.init_balancesFit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.St.init_balancesFit

/-- info: 'Solidity.Source.ExecState.apply_account_balancesFit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.ExecState.apply_account_balancesFit

/-- info: 'Solidity.Source.ExecState.apply_sameBalance_balancesFit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.ExecState.apply_sameBalance_balancesFit

/-- info: 'Solidity.Source.ExecState.apply_wordBalance_balancesFit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.ExecState.apply_wordBalance_balancesFit

/-- info: 'Solidity.Source.ExecState.empty_balancesFit' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.ExecState.empty_balancesFit

/-- info: 'Solidity.Source.deploy_open_balancesFit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.deploy_open_balancesFit

/-- info: 'Solidity.Source.deploy_code_balancesFit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.deploy_code_balancesFit

/-- info: 'Solidity.Source.Monetary.Authority.writeSource_balancesFit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.Authority.writeSource_balancesFit

/-- info: 'Solidity.Source.Monetary.Authority.writeSource_fit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.Authority.writeSource_fit

/-- info: 'Solidity.Source.Monetary.Authority.writeSourceChecked?_balancesFit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.Authority.writeSourceChecked?_balancesFit

/-- info: 'Solidity.Source.Monetary.Authority.writeSourceChecked?_of_fits' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.Authority.writeSourceChecked?_of_fits

/-- info: 'Solidity.Source.Monetary.Authority.set_fit' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.Monetary.Authority.set_fit

/-- info: 'Solidity.Source.edgeState_fit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.edgeState_fit

/-- info: 'Solidity.Source.transferNat_hypotheses_satisfiable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.transferNat_hypotheses_satisfiable

/-- info: 'Solidity.Source.unguarded_write_breaks' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.unguarded_write_breaks

/-- info: 'Solidity.Source.wideAuthority_writeSource_breaks' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Source.wideAuthority_writeSource_breaks
