import SolidityBridge.RoadmapV15.P10.DecoderAgreement
import SolidityBridge.RoadmapV15.P10.StorageReadConsumer

/-! Native fetched external-code observation. No G31 source admission is added. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem extcodesize_cost (site : Site .EXTCODESIZE) (key : UInt256) (tail : List UInt256) :
    EVM.C' (slotReadSite site key tail).state .EXTCODESIZE =
      if site.seed.substate.accessedAccounts.contains (AccountAddress.ofUInt256 key)
      then 100 else 2600 := by rfl

theorem extcodesize_cost_bound (site : Site .EXTCODESIZE) (key : UInt256) (tail : List UInt256) :
    EVM.C' (slotReadSite site key tail).state .EXTCODESIZE ≤ 2600 := by
  rw [extcodesize_cost]
  split <;> decide

private theorem extcodesize_gate (s : EVM.State) (gas : EVM.C' s .EXTCODESIZE ≤ s.gasAvailable.toNat)
    (enough : 1 ≤ s.stack.length) (room : s.stack.length ≤ 1024) :
    Assembly.driverGate #[] s .EXTCODESIZE = .ok (s,EVM.C' s .EXTCODESIZE) := by
  have expansion : EVM.memoryExpansionCost s .EXTCODESIZE = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have capacity : s.stack.length-1+1 ≤ 1024 := by omega
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [EVM.δ,EVM.α,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge enough),if_neg (Nat.not_lt_of_ge capacity)]
  cases s.executionEnv.perm <;> rfl

/-- Actual fetched lookup, charging and warm-account update. Complete caller,
account, storage, memory, log and return-byte state remains observed. -/
theorem extcodesize_agreement (site : Site .EXTCODESIZE)
    (key : UInt256) (tail : List UInt256) (room : tail.length+1 ≤ 1024)
    (gas : EVM.C' (slotReadSite site key tail).state .EXTCODESIZE ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (slotReadSite site key tail).state
    let read := EvmYul.State.extCodeSize input.toState key
    let cost := EVM.C' input .EXTCODESIZE
    let next := ({Assembly.chargedPrepare input cost with toState := read.1}).replaceStackAndIncrPC (read.2::tail)
    Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  let input := (slotReadSite site key tail).state
  let cost := EVM.C' input .EXTCODESIZE
  have gate : Assembly.driverGate #[] input .EXTCODESIZE = .ok (input,cost) := by
    apply extcodesize_gate input gas
    · change 1 ≤ (key::tail).length
      simp only [List.length_cons];omega
    · change (key::tail).length ≤ 1024
      exact room
  have step : EVM.step (fuel+1) cost (some (.EXTCODESIZE,none)) input =
      .ok (({Assembly.chargedPrepare input cost with toState := (EvmYul.State.extCodeSize input.toState key).1}).replaceStackAndIncrPC ((EvmYul.State.extCodeSize input.toState key).2::tail)) := by rfl
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.EXTCODESIZE,none) :=
    DecoderAgreement.decode_all (slotReadSite site key tail)
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel #[] input input _ (.EXTCODESIZE,none) cost
      decoded gate step (by unfold Assembly.NonhaltingOpcode;decide)

theorem extcodesize_read_shape (s : EVM.State) (key : UInt256) (tail : List UInt256) (cost : Nat) :
    ({Assembly.chargedPrepare s cost with toState := (EvmYul.State.extCodeSize s.toState key).1}).replaceStackAndIncrPC ((EvmYul.State.extCodeSize s.toState key).2::tail) =
    {s with
      pc := s.pc + .ofNat 1,gasAvailable := s.gasAvailable - .ofNat cost,
      execLength := s.execLength+1,stack := (EvmYul.State.extCodeSize s.toState key).2::tail,
      substate := s.substate.addAccessedAccount (AccountAddress.ofUInt256 key)} := by rfl


/-- Precisely the pinned account-code observation, not account execution. -/
theorem extcodesize_value (s : EvmYul.State .EVM) (key : UInt256) :
    (s.extCodeSize key).2 =
      (s.lookupAccount (AccountAddress.ofUInt256 key)).option (UInt256.ofNat 0)
        (fun account => UInt256.ofNat account.code.size) := rfl

#print axioms extcodesize_cost
#print axioms extcodesize_cost_bound
#print axioms extcodesize_agreement
#print axioms extcodesize_read_shape
#print axioms extcodesize_value
end SolidityBridge.RoadmapV15.P10
