import SolidityBridge.RoadmapV15.P10.Modular

/-! Unsigned DIV/MOD transport from the actual reference words to the intrinsic
Scalar slice and charged fetched step. Zero division succeeds with zero here;
this is not a Solidity guard or a compiler-origin/Osaka approval theorem. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

private theorem unsigned_zero (b : Scalar.Word) : (b == 0) = decide (b.toNat = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq,BitVec.toNat_eq]
  rfl

theorem unsigned_div_word (a b : Scalar.Word) :
    UInt256.div ⟨a.toFin⟩ ⟨b.toFin⟩ =
      ⟨(if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat / b.toNat)).toFin⟩ := by
  apply congrArg UInt256.mk
  apply Fin.ext
  change a.toNat / b.toNat = (if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat / b.toNat)).toNat
  rw [unsigned_zero]
  by_cases zero : b.toNat = 0
  · simp only [zero,Nat.div_zero,decide_true,if_true]
    rfl
  · simp only [zero,decide_false]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt)).symm

theorem unsigned_mod_word (a b : Scalar.Word) :
    UInt256.mod ⟨a.toFin⟩ ⟨b.toFin⟩ =
      ⟨(if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat % b.toNat)).toFin⟩ := by
  have zero : (b.toFin == 0) = (b == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,Fin.ext_iff,BitVec.toNat_eq]
    rfl
  unfold UInt256.mod
  rw [zero]
  split
  · rfl
  · apply congrArg UInt256.mk
    apply Fin.ext
    change a.toNat % b.toNat = (a.toNat % b.toNat) % 2^256
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) a.isLt)).symm

private theorem unsigned_byte {op : Backend.Op} (site : Site op) :
    site.state.executionEnv.code.get? (Backend.encode site.before).length = some op.code := by
  change (Backend.encode (site.before ++ .op op :: site.after)).toArray[(Backend.encode site.before).length]? = _
  rw [List.getElem?_toArray]
  simp only [Backend.encode_append,Backend.encode_cons,Instr.encode,List.singleton_append]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self,List.getElem?_cons_zero]

private theorem unsigned_gate (s : EVM.State) (op : Operation .EVM)
    (allowed : op = .DIV ∨ op = .MOD) (gas : 5 ≤ s.gasAvailable.toNat)
    (enough : 2 ≤ s.stack.length) (room : s.stack.length-2+1 ≤ 1024) :
    Assembly.driverGate #[] s op = .ok (s,5) := by
  have expansion : EVM.memoryExpansionCost s op = 0 := by
    rcases allowed with rfl|rfl <;>
      simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have cost : EVM.C' s op = 5 := by rcases allowed with rfl|rfl <;> rfl
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

private theorem unsigned_checked (input next : EVM.State) (op : Operation .EVM) (fuel : Nat)
    (decoded : EVM.decode input.executionEnv.code input.pc = some (op,none))
    (gate : Assembly.driverGate #[] input op = .ok (input,5))
    (step : EVM.step (fuel+1) 5 (some (op,none)) input = .ok next)
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
  · exact Assembly.X_continue fuel #[] input input next (op,none) 5 decoded gate step nonhalting

theorem decode_div (site : Site .DIV) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (.DIV,none) := by
  have byte := unsigned_byte site
  simp only [EVM.decode,Site.pc_nat,byte]
  rfl

theorem div_agreement (site : Site .DIV) (a b : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) (gas : 5 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      (((if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat / b.toNat))::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .DIV) (a::b::tail) = some ((if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat / b.toNat))::tail) ∧
      Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::tail)).state
  have gate : Assembly.driverGate #[] input .DIV = .ok (input,5) := by
    apply unsigned_gate input .DIV (Or.inl rfl) gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 5 (some (.DIV,none)) input =
      .ok ((Assembly.chargedPrepare input 5).replaceStackAndIncrPC
        (((if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat / b.toNat))::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := unsigned_div_word a b
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  exact unsigned_checked input _ .DIV fuel (decode_div _) gate step
    (by unfold Assembly.NonhaltingOpcode;decide)

theorem decode_mod (site : Site .MOD) :
    EVM.decode site.state.executionEnv.code site.state.pc = some (.MOD,none) := by
  have byte := unsigned_byte site
  simp only [EVM.decode,Site.pc_nat,byte]
  rfl

theorem mod_agreement (site : Site .MOD) (a b : Scalar.Word) (tail : Scalar.Stack)
    (room : tail.length+2 ≤ 1024) (gas : 5 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (modularSite site (a::b::tail)).state
    let next := (Assembly.chargedPrepare input 5).replaceStackAndIncrPC
      (((if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat % b.toNat))::tail).map (fun w => UInt256.mk w.toFin))
    Scalar.step (.op .MOD) (a::b::tail) = some ((if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat % b.toNat))::tail) ∧
      Assembly.driverSteps 1 (fuel+2) #[] input = .ok next ∧
      EVM.X (fuel+2) #[] input = EVM.X (fuel+1) #[] next := by
  dsimp only
  refine ⟨rfl,?_⟩
  let input := (modularSite site (a::b::tail)).state
  have gate : Assembly.driverGate #[] input .MOD = .ok (input,5) := by
    apply unsigned_gate input .MOD (Or.inr rfl) gas
    · change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
      simp only [List.length_map,List.length_cons];omega
    · change ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1 ≤ 1024
      simp only [List.length_map,List.length_cons];omega
  have step : EVM.step (fuel+1) 5 (some (.MOD,none)) input =
      .ok ((Assembly.chargedPrepare input 5).replaceStackAndIncrPC
        (((if b == 0 then (0 : Scalar.Word) else BitVec.ofNat 256 (a.toNat % b.toNat))::tail).map (fun w => UInt256.mk w.toFin))) := by
    have word := unsigned_mod_word a b
    simp only [input,modularSite,Site.state,List.map_cons]
    rw [←word]
    rfl
  exact unsigned_checked input _ .MOD fuel (decode_mod _) gate step
    (by unfold Assembly.NonhaltingOpcode;decide)


/-- Actual capacity refusal after adequate gas and available operands. -/
theorem div_capacity_refusal (site : Site .DIV) (a b : Scalar.Word) (tail : Scalar.Stack)
    (gas : 5 ≤ site.seed.gasAvailable.toNat) (over : 1024 < tail.length+1) (fuel : Nat) :
    Assembly.driverSteps 1 (fuel+2) #[] (modularSite site (a::b::tail)).state = .error .StackOverflow := by
  let input := (modularSite site (a::b::tail)).state
  have expansion : EVM.memoryExpansionCost input .DIV = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : input.gasAvailable-UInt256.ofNat 0 = input.gasAvailable := by
    change UInt256.mk (input.gasAvailable.val-0) = input.gasAvailable
    rw [sub_zero]
  have enough : 2 ≤ input.stack.length := by
    change 2 ≤ ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length
    simp only [List.length_map,List.length_cons];omega
  have capacity : 1024 < input.stack.length-2+1 := by
    change 1024 < ((a::b::tail).map (fun w => UInt256.mk w.toFin)).length-2+1
    simp only [List.length_map,List.length_cons];omega
  have budget : 5 ≤ input.gasAvailable.toNat := gas
  have gate : Assembly.driverGate #[] input .DIV = .error .StackOverflow := by
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    have cost : EVM.C' input .DIV = 5 := rfl
    simp only [cost,if_neg (Nat.not_lt_zero _),if_neg (Nat.not_lt_of_ge budget),
      EVM.δ,EVM.α,Option.getD_some,if_neg (Nat.not_lt_of_ge enough),if_pos capacity]
    rfl
  simp only [Assembly.driverSteps]
  rw [decode_div]
  dsimp only [Option.option,bind,Except.bind]
  have refused : Assembly.driverGate #[] (modularSite site (a::b::tail)).state .DIV =
      .error .StackOverflow := gate
  rw [refused]


#print axioms div_capacity_refusal
#print axioms unsigned_div_word
#print axioms unsigned_mod_word
#print axioms decode_div
#print axioms decode_mod
#print axioms div_agreement
#print axioms mod_agreement
end SolidityBridge.RoadmapV15.P10
