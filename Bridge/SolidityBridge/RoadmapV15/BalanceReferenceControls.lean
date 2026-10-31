import SolidityBridge.RoadmapV15.BalanceReference

/-! Actual numeric account lookup and accessed-account effects. No caller
execution, transaction fee/rollback or gas sufficiency is inferred. -/
namespace SolidityBridge.RoadmapV15.BalanceReferenceControls
open Solidity Solidity.Backend
private def frame : EvmYul.EVM.State :=
  { (default : EvmYul.EVM.State) with
    accountMap := ((∅ : EvmYul.AccountMap .EVM).insert (.ofNat 7)
      { (default : EvmYul.Account .EVM) with balance := .ofNat 29 }).insert (.ofNat 11)
      { (default : EvmYul.Account .EVM) with balance := .ofNat 31 } }
private def high : EvmYul.UInt256 := .ofNat (2 ^ 160 + 7)
private def operands : List EvmYul.UInt256 := [high, .ofNat 11, .ofNat 19, .ofNat (2 ^ 256 - 1)]
example : operands.map (fun w => (EvmYul.State.balance frame.toState w).2.toNat) =
    [29, 31, 0, 0] := by decide +kernel
example : (EvmYul.State.balance frame.toState high).2.toNat ≠ 0 := by decide +kernel
example : (EvmYul.State.balance frame.toState high).2.toNat ≠ 31 := by decide +kernel
example : (EvmYul.State.balance frame.toState high).1.substate.accessedAccounts.contains (.ofNat 7) = true := by decide +kernel
example : frame.substate.accessedAccounts.contains (.ofNat 7) = false := by decide +kernel
example : (EvmYul.State.balance frame.toState high).1.accountMap = frame.accountMap := rfl
example : (EvmYul.State.balance frame.toState (.ofNat 19)).1.substate.accessedAccounts.contains (.ofNat 19) = true := by decide +kernel
example : Solidity.Backend.Environment.step (environmentReferenceFrame frame) (.op .BALANCE) [] = none := rfl
example (fuel : Nat) : EvmYul.EVM.step (fuel + 1) 0 (some (.BALANCE, none))
    {frame with stack := []} = .error .StackUnderflow := rfl
example : EvmYul.EVM.step 0 0 (some (.BALANCE, none))
    {frame with stack := [high]} = .error .OutOfFuel := rfl
example (fuel : Nat) :
    let p := Solidity.Evm.External.Memory.prepare {frame with stack := [high, .ofNat 258, .ofNat 513]}
    let pair := EvmYul.State.balance p.toState high
    EvmYul.EVM.step (fuel + 1) 0 (some (.BALANCE, none))
      {frame with stack := [high, .ofNat 258, .ofNat 513]} =
      .ok ({p with toState := pair.1}.replaceStackAndIncrPC [.ofNat 29, .ofNat 258, .ofNat 513]) := by
  have h := environment_balance_reference frame high [.ofNat 258, .ofNat 513] fuel
  exact h
example : Solidity.Backend.Environment.step (environmentReferenceFrame frame) (.op .BALANCE)
    [environmentReferenceWord high, environmentReferenceWord (.ofNat 258), environmentReferenceWord (.ofNat 513)] =
    some [environmentReferenceWord (.ofNat 29), environmentReferenceWord (.ofNat 258), environmentReferenceWord (.ofNat 513)] := by
  rw [environment_balance_backend]
  decide +kernel
#print axioms environment_balance_value
#print axioms environment_balance_backend
#print axioms environment_balance_reference
end SolidityBridge.RoadmapV15.BalanceReferenceControls
