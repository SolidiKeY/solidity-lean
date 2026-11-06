import SolidityBridge.RoadmapV15.P10.SignedLeWord
import SolidityBridge.RoadmapV15.P10.DecoderAgreement

/-! Actual charged fetched SGT at arbitrary represented sites, as a producer
for the selected intLe two-instruction consumer. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem sgt_gate (s : EVM.State) (gas : 3 ≤ s.gasAvailable.toNat)
    (enough : 2 ≤ s.stack.length) (room : s.stack.length-2+1 ≤ 1024) :
    Assembly.driverGate #[] s .SGT = .ok (s,3) := by
  have expansion : EVM.memoryExpansionCost s .SGT = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  have cost : EVM.C' s .SGT = 3 := rfl
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost,EVM.δ,EVM.α,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge enough),if_neg (Nat.not_lt_of_ge room)]
  cases s.executionEnv.perm <;> rfl

theorem signed_gt_agreement (site : Site .SGT) (a b : Scalar.Word)
    (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let result := Scalar.flag (decide (b.toInt < a.toInt))
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((result::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .SGT) (a::b::tail) = some (result::tail) ∧
    Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
    EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::tail)).state
  have gate : Assembly.driverGate #[] input .SGT = .ok (input,3) := by
    apply sgt_gate input gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 3 (some (.SGT,none)) input =
      .ok ((Assembly.chargedPrepare input 3).replaceStackAndIncrPC
        (((Scalar.flag (decide (b.toInt < a.toInt)))::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := signed_gt_word a b
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.SGT,none) :=
    DecoderAgreement.decode_all (modularSite site (a::b::tail))
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel #[] input input _ (.SGT,none) 3 decoded gate step
      (by unfold Assembly.NonhaltingOpcode;decide)


#print axioms signed_gt_agreement
end SolidityBridge.RoadmapV15.P10
