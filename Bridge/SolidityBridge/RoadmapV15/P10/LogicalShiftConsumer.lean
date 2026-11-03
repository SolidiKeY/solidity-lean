import SolidityBridge.RoadmapV15.P10.LogicalShiftWords
import SolidityBridge.RoadmapV15.P10.DecoderAgreement

/-! Charged fetched SHL/SHR at arbitrary represented sites. Operand stack is
count/value here; the actual selected source emitter's SWAP is composed separately. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem logical_gate (s : EVM.State) (op : Operation .EVM)
    (allowed : op = .SHL ∨ op = .SHR) (gas : 3 ≤ s.gasAvailable.toNat)
    (enough : 2 ≤ s.stack.length) (room : s.stack.length-2+1 ≤ 1024) :
    Assembly.driverGate #[] s op = .ok (s,3) := by
  have expansion : EVM.memoryExpansionCost s op = 0 := by
    rcases allowed with rfl|rfl <;> simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have cost : EVM.C' s op = 3 := by rcases allowed with rfl|rfl <;> rfl
  have delta : EVM.δ op = some 2 := by rcases allowed with rfl|rfl <;> rfl
  have alpha : EVM.α op = some 1 := by rcases allowed with rfl|rfl <;> rfl
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost,delta,alpha,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge enough),if_neg (Nat.not_lt_of_ge room)]
  rcases allowed with rfl|rfl <;> cases s.executionEnv.perm <;> rfl

theorem logical_shl_agreement (site : Site .SHL) (count value : Scalar.Word)
    (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (count::value::tail)).state
    let result := if count.toNat < 256 then value <<< count.toNat else 0
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((result::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .SHL) (count::value::tail) = some (result::tail) ∧
    Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
    EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (count::value::tail)).state
  have gate : Assembly.driverGate #[] input .SHL = .ok (input,3) := by
    apply logical_gate input .SHL (Or.inl rfl) gas
    · change 2 ≤ ((count::value::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((count::value::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 3 (some (.SHL,none)) input =
      .ok ((Assembly.chargedPrepare input 3).replaceStackAndIncrPC
        (((if count.toNat < 256 then value <<< count.toNat else 0)::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := logical_shl_word count value
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.SHL,none) :=
    DecoderAgreement.decode_all (modularSite site (count::value::tail))
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel #[] input input _ (.SHL,none) 3 decoded gate step
      (by unfold Assembly.NonhaltingOpcode;decide)

theorem logical_shr_agreement (site : Site .SHR) (count value : Scalar.Word)
    (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (count::value::tail)).state
    let result := if count.toNat < 256 then value >>> count.toNat else 0
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((result::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .SHR) (count::value::tail) = some (result::tail) ∧
    Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
    EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (count::value::tail)).state
  have gate : Assembly.driverGate #[] input .SHR = .ok (input,3) := by
    apply logical_gate input .SHR (Or.inr rfl) gas
    · change 2 ≤ ((count::value::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((count::value::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 3 (some (.SHR,none)) input =
      .ok ((Assembly.chargedPrepare input 3).replaceStackAndIncrPC
        (((if count.toNat < 256 then value >>> count.toNat else 0)::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := logical_shr_word count value
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.SHR,none) :=
    DecoderAgreement.decode_all (modularSite site (count::value::tail))
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel #[] input input _ (.SHR,none) 3 decoded gate step
      (by unfold Assembly.NonhaltingOpcode;decide)

#print axioms logical_shl_agreement
#print axioms logical_shr_agreement
end SolidityBridge.RoadmapV15.P10
