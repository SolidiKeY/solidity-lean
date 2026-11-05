import SolidityBridge.RoadmapV15.P10.BitwiseWords
import SolidityBridge.RoadmapV15.P10.DecoderAgreement

/-! Charged fetched AND/OR/XOR consumers of the actual pinned transition.
All decoder/gate/dispatcher clauses are discharged below; source/compiler origin
and whole-program Osaka/resource correspondence remain separate. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem bitwise_gate (s : EVM.State) (op : Operation .EVM)
    (allowed : op = .AND ∨ op = .OR ∨ op = .XOR) (gas : 3 ≤ s.gasAvailable.toNat)
    (enough : 2 ≤ s.stack.length) (room : s.stack.length-2+1 ≤ 1024) :
    Assembly.driverGate #[] s op = .ok (s,3) := by
  have expansion : EVM.memoryExpansionCost s op = 0 := by
    rcases allowed with rfl|rfl|rfl <;>
      simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have cost : EVM.C' s op = 3 := by rcases allowed with rfl|rfl|rfl <;> rfl
  have delta : EVM.δ op = some 2 := by rcases allowed with rfl|rfl|rfl <;> rfl
  have alpha : EVM.α op = some 1 := by rcases allowed with rfl|rfl|rfl <;> rfl
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [cost,delta,alpha,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge enough),if_neg (Nat.not_lt_of_ge room)]
  rcases allowed with rfl|rfl|rfl <;> cases s.executionEnv.perm <;> rfl

private theorem bitwise_checked (input next : EVM.State) (op : Operation .EVM) (fuel : Nat)
    (decoded : EVM.decode input.executionEnv.code input.pc = some (op,none))
    (gate : Assembly.driverGate #[] input op = .ok (input,3))
    (step : EVM.step (fuel+1) 3 (some (op,none)) input = .ok next)
    (nonhalting : Assembly.NonhaltingOpcode op) :
    Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
    EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel #[] input input next (op,none) 3 decoded gate step nonhalting

/-- Actual AND and intrinsic result, preserving the complete charged State. -/
theorem bitwise_and_agreement (site : Site .AND) (a b : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      (((a &&& b)::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .AND) (a::b::tail) = some ((a &&& b)::tail) ∧
      Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::tail)).state
  have gate : Assembly.driverGate #[] input .AND = .ok (input,3) := by
    apply bitwise_gate input .AND (Or.inl rfl) gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 3 (some (.AND,none)) input =
      .ok ((Assembly.chargedPrepare input 3).replaceStackAndIncrPC
        (((a &&& b)::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := bitwise_and_word a b
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.AND,none) :=
    DecoderAgreement.decode_all (modularSite site (a::b::tail))
  exact bitwise_checked input _ .AND fuel decoded gate step
    (by unfold Assembly.NonhaltingOpcode;decide)

/-- Actual OR and intrinsic result, preserving the complete charged State. -/
theorem bitwise_or_agreement (site : Site .OR) (a b : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      (((a ||| b)::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .OR) (a::b::tail) = some ((a ||| b)::tail) ∧
      Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::tail)).state
  have gate : Assembly.driverGate #[] input .OR = .ok (input,3) := by
    apply bitwise_gate input .OR (Or.inr (Or.inl rfl)) gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 3 (some (.OR,none)) input =
      .ok ((Assembly.chargedPrepare input 3).replaceStackAndIncrPC
        (((a ||| b)::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := bitwise_or_word a b
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.OR,none) :=
    DecoderAgreement.decode_all (modularSite site (a::b::tail))
  exact bitwise_checked input _ .OR fuel decoded gate step
    (by unfold Assembly.NonhaltingOpcode;decide)

/-- Actual XOR and intrinsic result, preserving the complete charged State. -/
theorem bitwise_xor_agreement (site : Site .XOR) (a b : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      (((a ^^^ b)::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .XOR) (a::b::tail) = some ((a ^^^ b)::tail) ∧
      Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::tail)).state
  have gate : Assembly.driverGate #[] input .XOR = .ok (input,3) := by
    apply bitwise_gate input .XOR (Or.inr (Or.inr rfl)) gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 3 (some (.XOR,none)) input =
      .ok ((Assembly.chargedPrepare input 3).replaceStackAndIncrPC
        (((a ^^^ b)::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := bitwise_xor_word a b
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.XOR,none) :=
    DecoderAgreement.decode_all (modularSite site (a::b::tail))
  exact bitwise_checked input _ .XOR fuel decoded gate step
    (by unfold Assembly.NonhaltingOpcode;decide)

#print axioms bitwise_and_agreement
#print axioms bitwise_or_agreement
#print axioms bitwise_xor_agreement
end SolidityBridge.RoadmapV15.P10
