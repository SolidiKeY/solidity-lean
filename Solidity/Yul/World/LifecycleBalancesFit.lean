import Solidity.Yul.World.Lifecycle
import Solidity.Source.MonetaryFit

/-!
# BalancesFit through the EIP-6780 lifecycle writers

The lifecycle's balance writers keep `ExecState.BalancesFit`
(`Source/MonetaryFit.lean` lists the Source writers): the self-beneficiary
burn writes `0`, the destruct transfer is the guarded `transferNat`, and
finalization erases accounts to empty ones and clears the journal.
-/
namespace Solidity.Yul.World
open Solidity.Roadmap (Address Word)
open Solidity.Source
variable {D : Layout} {L T : Address → SPath → STy}

theorem selfBeneficiary_balancesFit (s : ExecState D L T) (created : Bool) (a : Address)
    (fit : s.BalancesFit) : (selfBeneficiary s created a).BalancesFit := by
  unfold selfBeneficiary
  split
  · exact s.apply_account_balancesFit a _ fit (by decide : Monetary.Fits 0)
  · exact fit

theorem destructTransfer_balancesFit (s out : ExecState D L T) (created : Bool)
    (a beneficiary : Address) (fit : s.BalancesFit)
    (h : destructTransfer s created a beneficiary = some out) : out.BalancesFit := by
  unfold destructTransfer at h
  split at h
  · cases h
    exact selfBeneficiary_balancesFit s created a fit
  · exact s.transferNat_balancesFit out a beneficiary _ fit h

theorem finish_balancesFit (s : Lifecycle D L T) (fit : s.execution.BalancesFit) :
    s.finish.execution.BalancesFit := by
  refine ⟨?_, ?_⟩
  · intro a
    change Monetary.Fits (if s.created a && s.doomed a then Account.empty (L a)
      else s.execution.world.accounts a).balance
    split
    · exact (by decide : Monetary.Fits 0)
    · exact fit.1 a
  · intro entry impossible
    cases impossible

end Solidity.Yul.World

/-- info: 'Solidity.Yul.World.destructTransfer_balancesFit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.World.destructTransfer_balancesFit

/-- info: 'Solidity.Yul.World.selfBeneficiary_balancesFit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.World.selfBeneficiary_balancesFit

/-- info: 'Solidity.Yul.World.finish_balancesFit' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Yul.World.finish_balancesFit
