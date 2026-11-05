import SolidityBridge.RoadmapV15.P10.ExponentConsumer

/-! EXP full-State and exponent-byte controls. All expected ordered buffers,
caller/account context and spill are retained. No source-profile closure. -/
namespace SolidityBridge.RoadmapV15.P10.PowerControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
private def u (n : Nat) : UInt256 := .ofNat n
private def maximum : Scalar.Word := BitVec.ofNat 256 (2^256-1)
private def spill : Scalar.Stack := [258,513]
private def seed (gas : Nat) : EVM.State :=
  {(default : EVM.State) with
    execLength := 41,gasAvailable := u gas,activeWords := u 1
    memory := ⟨#[0xaa,0xbb]⟩,returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7,source := .ofNat 11,sender := .ofNat 19,perm := false}
    accountMap := ((∅ : AccountMap .EVM).insert (.ofNat 7)
      {(default : Account .EVM) with nonce := u 3,balance := u 29}).insert (.ofNat 11)
      {(default : Account .EVM) with nonce := u 5,balance := u 41}}
private def site (gas : Nat) (words : Scalar.Stack) : Site .EXP :=
  modularSite ⟨seed gas,[.push ⟨1,by decide⟩ #v[0x0a],.op .POP],[.op .STOP],by decide⟩ words
private def expected (input : Site .EXP) (words : Scalar.Stack) : EVM.State :=
  {input.state with
    pc := u 4,gasAvailable := u 0,execLength := 42
    stack := words.map (fun w => UInt256.mk w.toFin)}

private theorem small_cost (budget : Nat) (a b : Scalar.Word) (tail : Scalar.Stack)
    (small : b.toNat < 256) (nonzero : UInt256.eq0 ⟨b.toFin⟩ = false) :
    EVM.C' (site budget (a::b::tail)).state .EXP = 60 := by
  unfold site
  rw [power_cost,nonzero,Nat.log_of_lt small]
  rfl

private theorem wide_cost (budget : Nat) (a : Scalar.Word) (tail : Scalar.Stack) :
    EVM.C' (site budget (a::256::tail)).state .EXP = 110 := by
  unfold site
  rw [power_cost]
  change 10+50*(1+Nat.log 256 256) = 110
  rw [show Nat.log 256 256 = 1 by simpa only [Nat.pow_one] using Nat.log_pow (by decide : 1 < 256) 1]

private theorem max_log : Nat.log 256 maximum.toNat = 31 := by
  apply (Nat.log_eq_iff (Or.inl (by decide : (31 : Nat) ≠ 0))).2
  constructor <;> decide +kernel

private theorem max_cost (tail : Scalar.Stack) :
    EVM.C' (site 1610 (1::maximum::tail)).state .EXP = 1610 := by
  unfold site
  rw [power_cost]
  have nonzero : UInt256.eq0 ⟨maximum.toFin⟩ = false := by decide +kernel
  rw [nonzero,max_log]
  rfl

private theorem execute (budget : Nat) (a b value : Scalar.Word) (tail : Scalar.Stack)
    (fits : budget < UInt256.size) (room : tail.length+2 ≤ 1024)
    (cost : EVM.C' (site budget (a::b::tail)).state .EXP = budget)
    (result : BitVec.ofNat 256 (a.toNat ^ b.toNat) = value) :
    Assembly.driverSteps 1 2 #[] (site budget (a::b::tail)).state =
      .ok (expected (site budget (a::b::tail)) (value::tail)) := by
  let base : Site .EXP := ⟨seed budget,[.push ⟨1,by decide⟩ #v[0x0a],.op .POP],[.op .STOP],by decide⟩
  have actualCost : EVM.C' (modularSite base (a::b::tail)).state .EXP = budget := cost
  have gas : EVM.C' (modularSite base (a::b::tail)).state .EXP ≤ base.seed.gasAvailable.toNat := by
    rw [actualCost]
    change budget ≤ budget % UInt256.size
    rw [Nat.mod_eq_of_lt fits]
  have h := (power_agreement base a b tail room gas 0).2.1
  rw [actualCost,result] at h
  have zero : UInt256.ofNat budget-UInt256.ofNat budget = UInt256.ofNat 0 := by
    change UInt256.mk ((UInt256.ofNat budget).val-(UInt256.ofNat budget).val) = _
    rw [sub_self]
    rfl
  simpa only [base,expected,site,modularSite,Site.state,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,List.map_cons,seed,u,zero] using h

theorem nonzero_power :
    Assembly.driverSteps 1 2 #[] (site 60 (2::3::spill)).state =
      .ok (expected (site 60 (2::3::spill)) (8::spill)) := by
  apply execute 60 2 3 (8) spill (by decide +kernel) (by decide +kernel)
  · exact small_cost _ _ _ _ (by decide +kernel) (by decide +kernel)
  · rfl

theorem zero_to_zero :
    Assembly.driverSteps 1 2 #[] (site 10 (0::0::spill)).state =
      .ok (expected (site 10 (0::0::spill)) (1::spill)) := by
  apply execute 10 0 0 (1) spill (by decide +kernel) (by decide +kernel)
  · rfl
  · rfl

theorem last_nonzero_bit :
    Assembly.driverSteps 1 2 #[] (site 60 (2::255::spill)).state =
      .ok (expected (site 60 (2::255::spill)) (BitVec.ofNat 256 (2^255)::spill)) := by
  apply execute 60 2 255 (BitVec.ofNat 256 (2^255)) spill (by decide +kernel) (by decide +kernel)
  · exact small_cost _ _ _ _ (by decide +kernel) (by decide +kernel)
  · rfl

theorem first_word_wrap :
    Assembly.driverSteps 1 2 #[] (site 110 (2::256::spill)).state =
      .ok (expected (site 110 (2::256::spill)) (0::spill)) := by
  apply execute 110 2 256 (0) spill (by decide +kernel) (by decide +kernel)
  · exact wide_cost _ _ _
  · rfl

theorem maximum_square :
    Assembly.driverSteps 1 2 #[] (site 60 (maximum::2::spill)).state =
      .ok (expected (site 60 (maximum::2::spill)) (1::spill)) := by
  apply execute 60 maximum 2 (1) spill (by decide +kernel) (by decide +kernel)
  · exact small_cost _ _ _ _ (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem boundary_tail (tail : Scalar.Stack) (length : tail.length = 1022) :
    Assembly.driverSteps 1 2 #[] (site 60 (2::3::tail)).state =
      .ok (expected (site 60 (2::3::tail)) (8::tail)) := by
  apply execute 60 2 3 8 tail (by decide +kernel) (by rw [length])
  · exact small_cost _ _ _ _ (by decide +kernel) (by decide +kernel)
  · rfl

theorem stack_boundary :
    let tail : Scalar.Stack := List.replicate 1022 513
    Assembly.driverSteps 1 2 #[] (site 60 (2::3::tail)).state =
      .ok (expected (site 60 (2::3::tail)) (8::tail)) :=
  boundary_tail _ List.length_replicate

theorem maximum_exponent_cost : EVM.C' (site 1610 (1::maximum::spill)).state .EXP = 1610 :=
  max_cost spill

theorem maximum_exponent_one :
    Assembly.driverSteps 1 2 #[] (site 1610 (1::maximum::spill)).state =
      .ok (expected (site 1610 (1::maximum::spill)) (1::spill)) := by
  apply execute 1610 1 maximum 1 spill (by decide +kernel) (by decide +kernel) (max_cost spill)
  simp only [show (1 : Scalar.Word).toNat = 1 from rfl,Nat.one_pow]
  rfl

private def combination : Site .EXP :=
  modularSite ⟨seed 68,[.push ⟨1,by decide⟩ #v[0x0a],.op .POP],
    [.op .ADDMOD,.op .STOP],by decide⟩ (2::3::1::7::spill)

theorem fetched_combination :
    Scalar.run [.op .EXP,.op .ADDMOD] (2::3::1::7::spill) = some (2::spill) ∧
    Assembly.driverSteps 2 3 #[] combination.state =
      .ok {combination.state with
        pc := u 5,gasAvailable := u 0,execLength := 43
        stack := (2::spill).map (fun w => UInt256.mk w.toFin)} := by
  constructor
  · rfl
  · let base : Site .EXP := ⟨seed 68,[.push ⟨1,by decide⟩ #v[0x0a],.op .POP],[.op .ADDMOD,.op .STOP],by decide⟩
    have cost : EVM.C' combination.state .EXP = 60 := by
      change EVM.C' (modularSite base (2::3::1::7::spill)).state .EXP = 60
      rw [power_cost]
      change 10+50*(1+Nat.log 256 3) = 60
      rw [Nat.log_of_lt (by decide : 3 < 256)]
    have gas : EVM.C' (modularSite base (2::3::1::7::spill)).state .EXP ≤ base.seed.gasAvailable.toNat := by
      change EVM.C' combination.state .EXP ≤ 68
      rw [cost]; decide
    have first := (power_agreement base 2 3 (1::7::spill) (by decide +kernel) gas 1).2.1
    have actualCost : EVM.C' (modularSite base (2::3::1::7::spill)).state .EXP = 60 := cost
    rw [actualCost] at first
    have first' : Assembly.driverSteps 1 3 #[] combination.state =
        .ok ((Assembly.chargedPrepare combination.state 60).replaceStackAndIncrPC
          ((8::1::7::spill).map (fun w => UInt256.mk w.toFin))) := by
      simpa only [combination,base] using first
    rw [fetched_steps_cons 1 1 #[] combination.state,first']
    rfl

-- Use exact actual gas formulas before reducing the real exceptional gate.
private theorem wrong_charge (budget : Nat) (words : Scalar.Stack)
    (cost : EVM.C' (site budget words).state .EXP > budget) (fits : budget < UInt256.size) :
    Assembly.driverSteps 1 2 #[] (site budget words).state = .error .OutOfGass := by
  let image := site budget words
  have expansion : EVM.memoryExpansionCost image.state .EXP = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : image.state.gasAvailable-UInt256.ofNat 0 = image.state.gasAvailable := by
    change UInt256.mk ((UInt256.ofNat budget).val-0) = UInt256.ofNat budget
    rw [sub_zero]
  have low : image.state.gasAvailable.toNat < EVM.C' image.state .EXP := by
    change budget % UInt256.size < EVM.C' (site budget words).state .EXP
    rw [Nat.mod_eq_of_lt fits]
    exact cost
  have gate : Assembly.driverGate #[] image.state .EXP = .error .OutOfGass := by
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    simp only [if_neg (Nat.not_lt_zero _),if_pos low,bind,Except.bind]
    rfl
  change Assembly.driverSteps 1 2 #[] image.state = _
  simp only [Assembly.driverSteps]
  rw [decode_exp image]
  dsimp only [Option.option,bind,Except.bind]
  rw [gate]

theorem wrong_byte_charge :
    Assembly.driverSteps 1 2 #[] (site 109 (2::256::spill)).state = .error .OutOfGass := by
  apply wrong_charge _ _ _ (by decide +kernel)
  rw [wide_cost]; decide

-- Actual output-capacity failure, outside the admitted initial stack bound.
private theorem overflow_tail (tail : Scalar.Stack) (length : tail.length = 1024) :
    Assembly.driverSteps 1 2 #[] (site 60 (2::3::tail)).state = .error .StackOverflow := by
  let image := site 60 (2::3::tail)
  have count : image.state.stack.length = 1026 := by
    change ((2::3::tail).map (fun w : Scalar.Word => UInt256.mk w.toFin)).length = 1026
    simp only [List.length_map,List.length_cons,length]
  have expansion : EVM.memoryExpansionCost image.state .EXP = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : image.state.gasAvailable-UInt256.ofNat 0 = image.state.gasAvailable := by
    change UInt256.mk ((u 60).val-0) = u 60
    rw [sub_zero]
  have cost : EVM.C' image.state .EXP = 60 :=
    small_cost _ _ _ _ (by decide +kernel) (by decide +kernel)
  have gate : Assembly.driverGate #[] image.state .EXP = .error .StackOverflow := by
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    simp only [cost,EVM.δ,EVM.α,Option.getD_some,count]
    rfl
  change Assembly.driverSteps 1 2 #[] image.state = _
  simp only [Assembly.driverSteps]
  rw [decode_exp image]
  dsimp only [Option.option,bind,Except.bind]
  rw [gate]

theorem fetched_stack_overflow :
    Assembly.driverSteps 1 2 #[] (site 60 (2::3::List.replicate 1024 513)).state = .error .StackOverflow :=
  overflow_tail _ List.length_replicate

theorem wrong_operand_order : Scalar.step (.op .EXP) [2,3] ≠ some [9] := by decide +kernel
example : Assembly.driverSteps 1 2 #[] (site 9 []).state = .error .OutOfGass := by rfl
example : Assembly.driverSteps 1 2 #[] (site 10 []).state = .error .StackUnderflow := by rfl
example : Assembly.driverSteps 1 1 #[] (site 110 [2,256]).state = .error .OutOfFuel := by rfl
example : Assembly.driverSteps 1 2 #[] (site 59 [2,255]).state = .error .OutOfGass := by
  apply wrong_charge _ _ _ (by decide +kernel)
  rw [small_cost _ _ _ _ (by decide +kernel) (by decide +kernel)]; decide

#print axioms nonzero_power
#print axioms zero_to_zero
#print axioms last_nonzero_bit
#print axioms first_word_wrap
#print axioms maximum_square
#print axioms stack_boundary
#print axioms maximum_exponent_cost
#print axioms maximum_exponent_one
#print axioms fetched_combination
#print axioms wrong_byte_charge
#print axioms wrong_operand_order
#print axioms fetched_stack_overflow
end SolidityBridge.RoadmapV15.P10.PowerControls
