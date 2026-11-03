import SolidityBridge.RoadmapV15.P10.EqualityConsumer

/-! Actual charged fetched unsigned LT/GT consumers. Existing word and Scalar
comparison definitions are read-only; source/compiler origin remains open. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

theorem unsigned_lt_word (a b : Scalar.Word) :
    UInt256.lt ⟨a.toFin⟩ ⟨b.toFin⟩ = ⟨(Scalar.flag (decide (a.toNat < b.toNat))).toFin⟩ := by
  first | rfl | (change Bool.toUInt256 (decide (a.toNat < b.toNat)) = _; cases decide (a.toNat < b.toNat) <;> rfl)

private theorem unsigned_lt_gate (valid : Array UInt256) (s : EVM.State)
    (gas : 3 ≤ s.gasAvailable.toNat) (enough : 2 ≤ s.stack.length)
    (room : s.stack.length-2+1 ≤ 1024) :
    Assembly.driverGate valid s .LT = .ok (s,3) := by
  have expansion : EVM.memoryExpansionCost s .LT = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  change (if s.gasAvailable.toNat < 3 then _ else _) = _
  rw [if_neg (Nat.not_lt_of_ge gas)]
  simp only [EVM.δ,EVM.α,Option.getD_some,if_neg (Nat.not_lt_of_ge enough),
    if_neg (Nat.not_lt_of_ge room)]
  cases s.executionEnv.perm <;> rfl

/-- Actual fetched LT, preserving the complete charged State and continuation. -/
theorem unsigned_lt_agreement (valid : Array UInt256) (site : Site .LT)
    (a b : Scalar.Word) (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      (((Scalar.flag (decide (a.toNat < b.toNat)))::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .LT) (a::b::tail) = some ((Scalar.flag (decide (a.toNat < b.toNat)))::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
    EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::tail)).state
  have gate : Assembly.driverGate valid input .LT = .ok (input,3) := by
    apply unsigned_lt_gate valid input gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 3 (some (.LT,none)) input =
      .ok ((Assembly.chargedPrepare input 3).replaceStackAndIncrPC
        (((Scalar.flag (decide (a.toNat < b.toNat)))::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := unsigned_lt_word a b
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.LT,none) :=
    DecoderAgreement.decode_all (modularSite site (a::b::tail))
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel valid input input _ (.LT,none) 3 decoded gate step
      (by unfold Assembly.NonhaltingOpcode;decide)


theorem selected_unsigned_lt_agreement (valid : Array UInt256) (site : Site .LT)
    (a b : PrimTy.uint.Denote) (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let aw := Scalar.encodeValue .uint a
    let bw := Scalar.encodeValue .uint b
    let input := (modularSite site (aw::bw::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((Scalar.flag (decide (aw.toNat < bw.toNat))::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.run (Scalar.uintLt).code (aw::bw::tail) =
      (BinOp.lt.evalT (p := .uint) rfl a b).map
        (fun result => Scalar.encodeValue .bool result::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
    EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  exact ⟨(Scalar.uintLt).correct a b tail,
    (unsigned_lt_agreement valid site (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b)
      tail room gas fuel).2⟩


theorem unsigned_gt_word (a b : Scalar.Word) :
    UInt256.gt ⟨a.toFin⟩ ⟨b.toFin⟩ = ⟨(Scalar.flag (decide (b.toNat < a.toNat))).toFin⟩ := by
  first | rfl | (change Bool.toUInt256 (decide (b.toNat < a.toNat)) = _; cases decide (b.toNat < a.toNat) <;> rfl)

private theorem unsigned_gt_gate (valid : Array UInt256) (s : EVM.State)
    (gas : 3 ≤ s.gasAvailable.toNat) (enough : 2 ≤ s.stack.length)
    (room : s.stack.length-2+1 ≤ 1024) :
    Assembly.driverGate valid s .GT = .ok (s,3) := by
  have expansion : EVM.memoryExpansionCost s .GT = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  change (if s.gasAvailable.toNat < 3 then _ else _) = _
  rw [if_neg (Nat.not_lt_of_ge gas)]
  simp only [EVM.δ,EVM.α,Option.getD_some,if_neg (Nat.not_lt_of_ge enough),
    if_neg (Nat.not_lt_of_ge room)]
  cases s.executionEnv.perm <;> rfl

/-- Actual fetched GT, preserving the complete charged State and continuation. -/
theorem unsigned_gt_agreement (valid : Array UInt256) (site : Site .GT)
    (a b : Scalar.Word) (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      (((Scalar.flag (decide (b.toNat < a.toNat)))::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .GT) (a::b::tail) = some ((Scalar.flag (decide (b.toNat < a.toNat)))::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
    EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::tail)).state
  have gate : Assembly.driverGate valid input .GT = .ok (input,3) := by
    apply unsigned_gt_gate valid input gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 3 (some (.GT,none)) input =
      .ok ((Assembly.chargedPrepare input 3).replaceStackAndIncrPC
        (((Scalar.flag (decide (b.toNat < a.toNat)))::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := unsigned_gt_word a b
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  have decoded : EVM.decode input.executionEnv.code input.pc = some (.GT,none) :=
    DecoderAgreement.decode_all (modularSite site (a::b::tail))
  constructor
  · simp only [Assembly.driverSteps]
    rw [decoded]
    dsimp only [Option.option,bind,Except.bind]
    rw [gate]
    dsimp only
    rw [step]
  · exact Assembly.X_continue fuel valid input input _ (.GT,none) 3 decoded gate step
      (by unfold Assembly.NonhaltingOpcode;decide)


theorem selected_unsigned_gt_agreement (valid : Array UInt256) (site : Site .GT)
    (a b : PrimTy.uint.Denote) (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024)
    (gas : 3 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let aw := Scalar.encodeValue .uint a
    let bw := Scalar.encodeValue .uint b
    let input := (modularSite site (aw::bw::tail)).state
    let next := (Assembly.chargedPrepare input 3).replaceStackAndIncrPC
      ((Scalar.flag (decide (bw.toNat < aw.toNat))::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.run (Scalar.uintGt).code (aw::bw::tail) =
      (BinOp.gt.evalT (p := .uint) rfl a b).map
        (fun result => Scalar.encodeValue .bool result::tail) ∧
    Assembly.driverSteps 1 (fuel+2) valid input = .ok next ∧
    EVM.X (fuel+2) valid input = EVM.X (fuel+1) valid next := by
  exact ⟨(Scalar.uintGt).correct a b tail,
    (unsigned_gt_agreement valid site (Scalar.encodeValue .uint a) (Scalar.encodeValue .uint b)
      tail room gas fuel).2⟩


#print axioms unsigned_lt_word
#print axioms unsigned_lt_agreement
#print axioms selected_unsigned_lt_agreement
#print axioms unsigned_gt_word
#print axioms unsigned_gt_agreement
#print axioms selected_unsigned_gt_agreement
end SolidityBridge.RoadmapV15.P10
