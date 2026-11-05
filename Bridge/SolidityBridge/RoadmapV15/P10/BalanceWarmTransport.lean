import SolidityBridge.RoadmapV15.P10.BalanceEnvironmentConsumer
import Batteries.Data.RBMap.Lemmas

/-! Account-access warmth after the actual pinned BALANCE read. These laws
preserve ledger observations; they do not assert that a following opcode supplies
the same address, or prove arbitrary account/world execution. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem balance_warms_account (s : EvmYul.State .EVM) (key : UInt256) :
    (EvmYul.State.balance s key).1.substate.accessedAccounts.contains
      (AccountAddress.ofUInt256 key) = true := by
  change (s.substate.accessedAccounts.insert (AccountAddress.ofUInt256 key)).contains
    (AccountAddress.ofUInt256 key) = true
  letI : Std.TransCmp (α := AccountAddress) compare :=
    (inferInstance : Std.TransCmp (compareOn (fun a : AccountAddress => a.val)))
  exact Batteries.RBSet.contains_iff.mpr (Batteries.RBSet.mem_insert_self _ _)

theorem balance_accounts_preserved (s : EvmYul.State .EVM) (key : UInt256) :
    (EvmYul.State.balance s key).1.accountMap = s.accountMap := by rfl

theorem balance_reads_preserved (s : EvmYul.State .EVM) (key probe : UInt256) :
    (EvmYul.State.balance (EvmYul.State.balance s key).1 probe).2 =
      (EvmYul.State.balance s probe).2 := by rfl

theorem balance_warm_probe_cost (s : EVM.State) (key : UInt256) (tail : List UInt256) :
    EVM.C' {s with toState := (EvmYul.State.balance s.toState key).1,stack := key::tail} .BALANCE = 100 := by
  change (if (EvmYul.State.balance s.toState key).1.substate.accessedAccounts.contains
    (AccountAddress.ofUInt256 key) then 100 else 2600) = 100
  rw [balance_warms_account]
  rfl

theorem balance_frame_preserved (frame : Backend.Environment.Frame)
    (s : EvmYul.State .EVM) (key : UInt256) :
    balanceFrame frame (EvmYul.State.balance s key).1 = balanceFrame frame s := by rfl

/-- Probe accounts with the same actual low160 address share warmth. -/
theorem balance_alias_probe_cost :
    ∀ (s : EVM.State) (key probe : UInt256) (tail : List UInt256), AccountAddress.ofUInt256 probe = AccountAddress.ofUInt256 key → EVM.C' {s with toState := (EvmYul.State.balance s.toState key).1,stack := probe::tail} .BALANCE = 100
    := by
  intro s key probe tail sameAccount
  change (if (EvmYul.State.balance s.toState key).1.substate.accessedAccounts.contains
    (AccountAddress.ofUInt256 probe) then 100 else 2600) = 100
  rw [sameAccount,balance_warms_account]
  rfl

/-- The actual fetched read supplies the warmed state and preserved ledger.
The next-cost observation explicitly reinstalls the input key. -/
theorem balance_resource_frame :
    ∀ (frame : Backend.Environment.Frame) (site : Site .BALANCE) (key : UInt256) (tail : List UInt256) (_room : tail.length+1 ≤ 1024) (_gas : EVM.C' (slotReadSite site key tail).state .BALANCE ≤ site.seed.gasAvailable.toNat) (fuel : Nat),
     let input := (slotReadSite site key tail).state
     let cost := EVM.C' input .BALANCE
     let read := EvmYul.State.balance input.toState key
     let next := ({Assembly.chargedPrepare input cost with toState := read.1}).replaceStackAndIncrPC (read.2::tail)
     Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧ EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next ∧ EVM.C' {next with stack := key::tail} .BALANCE = 100 ∧ balanceFrame frame next.toState = balanceFrame frame input.toState ∧ next.accountMap = input.accountMap ∧ next.memory = input.memory ∧ next.returnData = input.returnData ∧ next.H_return = input.H_return
    := by
  intro frame site key tail room gas fuel
  dsimp only
  have h := balance_agreement frame site key tail room gas fuel
  dsimp only at h
  refine ⟨h.2.1,h.2.2,?_,rfl,rfl,rfl,rfl,rfl⟩
  exact balance_warm_probe_cost (slotReadSite site key tail).state key tail

#print axioms balance_alias_probe_cost
#print axioms balance_resource_frame

#print axioms balance_warm_probe_cost
#print axioms balance_frame_preserved

#print axioms balance_warms_account
#print axioms balance_accounts_preserved
#print axioms balance_reads_preserved
end SolidityBridge.RoadmapV15.P10
