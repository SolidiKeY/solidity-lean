import SolidityBridge.RoadmapV15.P10.WrappingArithmeticWords
import SolidityBridge.RoadmapV15.P10.DecoderAgreement

/-! Charged fetched ADD/SUB/MUL consumers of the actual selected certificates.
All source values are already evaluated; source/frame origin remains open. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem arithmetic_gate (valid : Array UInt256) (s : EVM.State)
    (op : Operation .EVM) (cost : Nat) (allowed : op = .ADD ∨ op = .SUB ∨ op = .MUL)
    (chargeCost : EVM.C' s op = cost) (gas : cost ≤ s.gasAvailable.toNat)
    (enough : 2 ≤ s.stack.length) (room : s.stack.length-2+1 ≤ 1024) :
    Assembly.driverGate valid s op = .ok (s,cost) := by
  have expansion : EVM.memoryExpansionCost s op = 0 := by
    rcases allowed with rfl|rfl|rfl <;>
      simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have delta : EVM.δ op = some 2 := by rcases allowed with rfl|rfl|rfl <;> rfl
  have alpha : EVM.α op = some 1 := by rcases allowed with rfl|rfl|rfl <;> rfl
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [chargeCost,delta,alpha,Option.getD_some,if_neg (Nat.not_lt_zero _),
    if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge enough),if_neg (Nat.not_lt_of_ge room)]
  rcases allowed with rfl|rfl|rfl <;> cases s.executionEnv.perm <;> rfl

/-- Actual charged ADD, with top word as the left operand. -/
theorem wrapping_add_agreement (valid : Array UInt256) (site : Site .ADD)
    (a b : Scalar.Word) (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      (((a + b)::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .ADD) (a::b::tail) = some ((a + b)::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
    EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::tail)).state
  have gate : Assembly.driverGate valid input .ADD = .ok (input,3) := by
    apply arithmetic_gate valid input .ADD 3 (Or.inl rfl) (by rfl) gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 3 (some (.ADD,none)) input =
      .ok ((Assembly.chargedPrepare input 3).replaceStackAndIncrPC
        (((a + b)::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := wrapping_add_word a b
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.ADD,none) :=
    DecoderAgreement.decode_all (modularSite site (a::b::tail))
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel valid input input _ (.ADD,none) 3 decoded gate step
      (by unfold Assembly.NonhaltingOpcode;decide)

theorem wrapping_add_code (site : Site .ADD) :
    site.state.executionEnv.code.data.toList =
      Backend.encode (site.before ++ Scalar.wrappingAdd.code ++ site.after) := by
  simpa only [Scalar.wrappingAdd,List.append_assoc,List.singleton_append] using Site.code_bytes site

theorem selected_wrapping_add_agreement (valid : Array UInt256) (site : Site .ADD)
    (a b : PrimTy.uint.Denote) (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      (((Scalar.encodeValue .uint a + Scalar.encodeValue .uint b)::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.run Scalar.wrappingAdd.code (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::tail) =
      (BinOp.addW.evalT (p := .uint) rfl a b).map (fun r => Scalar.encodeValue .uint r::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
    EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  exact ⟨Scalar.wrappingAdd.correct a b tail,
    (wrapping_add_agreement valid site (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail room gas fuel).2⟩

/-- Actual charged SUB, with top word as the left operand. -/
theorem wrapping_sub_agreement (valid : Array UInt256) (site : Site .SUB)
    (a b : Scalar.Word) (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      (((a - b)::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .SUB) (a::b::tail) = some ((a - b)::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
    EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::tail)).state
  have gate : Assembly.driverGate valid input .SUB = .ok (input,3) := by
    apply arithmetic_gate valid input .SUB 3 (Or.inr (Or.inl rfl)) (by rfl) gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 3 (some (.SUB,none)) input =
      .ok ((Assembly.chargedPrepare input 3).replaceStackAndIncrPC
        (((a - b)::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := wrapping_sub_word a b
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.SUB,none) :=
    DecoderAgreement.decode_all (modularSite site (a::b::tail))
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel valid input input _ (.SUB,none) 3 decoded gate step
      (by unfold Assembly.NonhaltingOpcode;decide)

theorem wrapping_sub_code (site : Site .SUB) :
    site.state.executionEnv.code.data.toList =
      Backend.encode (site.before ++ Scalar.wrappingSub.code ++ site.after) := by
  simpa only [Scalar.wrappingSub,List.append_assoc,List.singleton_append] using Site.code_bytes site

theorem selected_wrapping_sub_agreement (valid : Array UInt256) (site : Site .SUB)
    (a b : PrimTy.uint.Denote) (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      (((Scalar.encodeValue .uint a - Scalar.encodeValue .uint b)::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.run Scalar.wrappingSub.code (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::tail) =
      (BinOp.subW.evalT (p := .uint) rfl a b).map (fun r => Scalar.encodeValue .uint r::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
    EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  exact ⟨Scalar.wrappingSub.correct a b tail,
    (wrapping_sub_agreement valid site (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail room gas fuel).2⟩

/-- Actual charged MUL, with top word as the left operand. -/
theorem wrapping_mul_agreement (valid : Array UInt256) (site : Site .MUL)
    (a b : Scalar.Word) (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 5 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      (((a * b)::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .MUL) (a::b::tail) = some ((a * b)::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
    EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::tail)).state
  have gate : Assembly.driverGate valid input .MUL = .ok (input,5) := by
    apply arithmetic_gate valid input .MUL 5 (Or.inr (Or.inr rfl)) (by rfl) gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 5 (some (.MUL,none)) input =
      .ok ((Assembly.chargedPrepare input 5).replaceStackAndIncrPC
        (((a * b)::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := wrapping_mul_word a b
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.MUL,none) :=
    DecoderAgreement.decode_all (modularSite site (a::b::tail))
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel valid input input _ (.MUL,none) 5 decoded gate step
      (by unfold Assembly.NonhaltingOpcode;decide)

theorem wrapping_mul_code (site : Site .MUL) :
    site.state.executionEnv.code.data.toList =
      Backend.encode (site.before ++ Scalar.wrappingMul.code ++ site.after) := by
  simpa only [Scalar.wrappingMul,List.append_assoc,List.singleton_append] using Site.code_bytes site

theorem selected_wrapping_mul_agreement (valid : Array UInt256) (site : Site .MUL)
    (a b : PrimTy.uint.Denote) (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 5 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::tail)).state
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      (((Scalar.encodeValue .uint a * Scalar.encodeValue .uint b)::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.run Scalar.wrappingMul.code (Scalar.encodeValue .uint a::Scalar.encodeValue .uint b::tail) =
      (BinOp.mulW.evalT (p := .uint) rfl a b).map (fun r => Scalar.encodeValue .uint r::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
    EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  exact ⟨Scalar.wrappingMul.correct a b tail,
    (wrapping_mul_agreement valid site (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b) tail room gas fuel).2⟩

#print axioms wrapping_add_agreement
#print axioms wrapping_add_code
#print axioms selected_wrapping_add_agreement
#print axioms wrapping_sub_agreement
#print axioms wrapping_sub_code
#print axioms selected_wrapping_sub_agreement
#print axioms wrapping_mul_agreement
#print axioms wrapping_mul_code
#print axioms selected_wrapping_mul_agreement
end SolidityBridge.RoadmapV15.P10
