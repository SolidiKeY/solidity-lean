import SolidityBridge.RoadmapV15.P10.DecoderAgreement
import SolidityBridge.RoadmapV15.P10.Modular

/-! Charged fetched POP at arbitrary emitted sites and represented Scalar tails.
The jump-array parameter is arbitrary; compiler/frame origin and Osaka approval
are separate. Input stack legality is explicit even though POP shrinks it. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem pop_gate (valid : Array UInt256) (s : EVM.State)
    (gas : 2 ≤ s.gasAvailable.toNat) (enough : 1 ≤ s.stack.length)
    (room : s.stack.length ≤ 1024) :
    Assembly.driverGate valid s .POP = .ok (s,2) := by
  have expansion : EVM.memoryExpansionCost s .POP = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  have cost : EVM.C' s .POP = 2 := rfl
  have outputRoom : s.stack.length-1 ≤ 1024 := by omega
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost,EVM.δ,EVM.α,Option.getD_some,Nat.add_zero,
    if_neg (Nat.not_lt_zero _),if_neg (Nat.not_lt_of_ge gas),
    if_neg (Nat.not_lt_of_ge enough),if_neg (Nat.not_lt_of_ge outputRoom)]
  cases s.executionEnv.perm <;> rfl

theorem pop_agreement (valid : Array UInt256) (site : Site .POP)
    (a : Scalar.Word) (tail : Scalar.Stack) (room : tail.length+1 ≤ 1024)
    (gas : 2 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::tail)).state
    let next := (Assembly.chargedPrepare input 2).replaceStackAndIncrPC
      (tail.map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .POP) (a::tail) = some tail ∧
      Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
      EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::tail)).state
  have gate : Assembly.driverGate valid input .POP = .ok (input,2) := by
    apply pop_gate valid input gas
    · change 1 ≤ ((a::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::tail).map (fun w => UInt256.mk w.toFin)).length ≤ 1024
      simpa only [List.length_map,List.length_cons] using room
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.POP,none) :=
    DecoderAgreement.decode_all (modularSite site (a::tail))
  have step : EVM.step (fuel+1) 2 (some (.POP,none)) input =
      .ok ((Assembly.chargedPrepare input 2).replaceStackAndIncrPC
        (tail.map (fun w => UInt256.mk w.toFin))) := by rfl
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel valid input input _ (.POP,none) 2 decoded gate step
      (by unfold Assembly.NonhaltingOpcode;decide)

#print axioms pop_gate
#print axioms pop_agreement
end SolidityBridge.RoadmapV15.P10
