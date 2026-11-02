import SolidityBridge.RoadmapV15.P10.StackFamilyConsumer

/-! Every legal family index has an inhabited ordered whole-State client.
Charged gas/stack/fuel failures use the actual fetched driver. -/
namespace SolidityBridge.RoadmapV15.P10.StackFamilyControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
private def u (n : Nat) : UInt256 := .ofNat n
private def spill : Scalar.Stack := [258,513]
private def middle : Scalar.Stack := [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
private def seed (gas : Nat) : EVM.State :=
  {(default : EVM.State) with
    execLength := 41,gasAvailable := u gas,activeWords := u 1
    memory := ⟨#[0xaa,0xbb]⟩,returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7,source := .ofNat 11,sender := .ofNat 19,perm := false}
    accountMap := ((∅ : AccountMap .EVM).insert (.ofNat 7)
      {(default : Account .EVM) with nonce := u 3,balance := u 29}).insert (.ofNat 11)
      {(default : Account .EVM) with nonce := u 5,balance := u 41}}
private def site (op : Backend.Op) (gas : Nat) (words : Scalar.Stack) : Site op :=
  modularSite ⟨seed gas,[.push ⟨1,by decide⟩ #v[0x80],.op .POP],[.op .STOP],by decide⟩ words
private def expected {op : Backend.Op} (input : Site op) (words : Scalar.Stack) : EVM.State :=
  {input.state with
    pc := u 4,gasAvailable := u 0,execLength := 42
    stack := words.map (fun w => UInt256.mk w.toFin)}
private def leadingWords (n : Fin 16) : Scalar.Stack :=
  (List.range n.val).map (fun i => BitVec.ofNat 256 (i+1))

private theorem execute_dup (n : Fin 16) (pre tail : Scalar.Stack) (a : Scalar.Word)
    (depth : pre.length = n.val) (room : pre.length+tail.length+2 ≤ 1024) :
    Assembly.driverSteps 1 2 #[] (site (.DUP n) 3 (pre ++ a::tail)).state =
      .ok (expected (site (.DUP n) 3 (pre ++ a::tail)) (a::(pre ++ a::tail))) := by
  let base : Site (.DUP n) := ⟨seed 3,[.push ⟨1,by decide⟩ #v[0x80],.op .POP],[.op .STOP],by decide⟩
  have h := (dup_family_agreement n base pre tail a depth room (by change 3 ≤ 3; decide) 0).2.1
  simpa only [base,site,expected,modularSite,Site.state,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,seed,u] using h

private theorem execute_swap (n : Fin 16) (pre tail : Scalar.Stack) (a b : Scalar.Word)
    (depth : pre.length = n.val) (room : pre.length+tail.length+2 ≤ 1024) :
    Assembly.driverSteps 1 2 #[] (site (.SWAP n) 3 (a::(pre ++ b::tail))).state =
      .ok (expected (site (.SWAP n) 3 (a::(pre ++ b::tail))) (b::(pre ++ a::tail))) := by
  let base : Site (.SWAP n) := ⟨seed 3,[.push ⟨1,by decide⟩ #v[0x80],.op .POP],[.op .STOP],by decide⟩
  have h := (swap_family_agreement n base pre tail a b depth room (by change 3 ≤ 3; decide) 0).2.1
  simpa only [base,site,expected,modularSite,Site.state,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,seed,u] using h

/-- Nonuniform increasing leadingWords, distinct selected/top/spill words, populated
inherited-static State, at every one of the16 legal family indices. -/
theorem every_depth_populated (n : Fin 16) :
    Assembly.driverSteps 1 2 #[] (site (.DUP n) 3 (leadingWords n ++ 511::spill)).state =
      .ok (expected (site (.DUP n) 3 (leadingWords n ++ 511::spill)) (511::(leadingWords n ++ 511::spill))) ∧
    Assembly.driverSteps 1 2 #[] (site (.SWAP n) 3 (1025::(leadingWords n ++ 511::spill))).state =
      .ok (expected (site (.SWAP n) 3 (1025::(leadingWords n ++ 511::spill))) (511::(leadingWords n ++ 1025::spill))) := by
  have depth : (leadingWords n).length = n.val := by simp only [leadingWords,List.length_map,List.length_range]
  have room : (leadingWords n).length+spill.length+2 ≤ 1024 := by rw [depth];change n.val+2+2 ≤ 1024;omega
  exact ⟨execute_dup n _ _ _ depth room,execute_swap n _ _ _ _ depth room⟩

theorem dup_first :
    Assembly.driverSteps 1 2 #[] (site (.DUP 0) 3 (511::spill)).state =
      .ok (expected (site (.DUP 0) 3 (511::spill)) (511::511::spill)) := by
  exact execute_dup 0 [] spill 511 rfl (by decide +kernel)

theorem swap_last :
    Assembly.driverSteps 1 2 #[] (site (.SWAP 15) 3 (1025::(middle ++ 511::spill))).state =
      .ok (expected (site (.SWAP 15) 3 (1025::(middle ++ 511::spill))) (511::(middle ++ 1025::spill))) := by
  exact execute_swap 15 middle spill 1025 511 rfl (by decide +kernel)

theorem dup_capacity_boundary :
    Assembly.driverSteps 1 2 #[] (site (.DUP 15) 3 (middle ++ 511::List.replicate 1007 513)).state =
      .ok (expected (site (.DUP 15) 3 (middle ++ 511::List.replicate 1007 513))
        (511::(middle ++ 511::List.replicate 1007 513))) := by
  apply execute_dup 15 middle _ 511 rfl
  simp only [middle,List.length_cons,List.length_nil,List.length_replicate];decide

theorem swap_capacity_boundary :
    Assembly.driverSteps 1 2 #[] (site (.SWAP 15) 3 (1025::(middle ++ 511::List.replicate 1007 513))).state =
      .ok (expected (site (.SWAP 15) 3 (1025::(middle ++ 511::List.replicate 1007 513)))
        (511::(middle ++ 1025::List.replicate 1007 513))) := by
  apply execute_swap 15 middle _ 1025 511 rfl
  simp only [middle,List.length_cons,List.length_nil,List.length_replicate];decide

private theorem dup_overflow (tail : Scalar.Stack) (length : tail.length = 1008) :
    Assembly.driverSteps 1 2 #[] (site (.DUP 15) 3 (middle ++ 511::tail)).state = .error .StackOverflow := by
  let image := site (.DUP 15) 3 (middle ++ 511::tail)
  have count : image.state.stack.length = 1024 := by
    change ((middle ++ 511::tail).map (fun w : Scalar.Word => UInt256.mk w.toFin)).length = 1024
    simp only [List.length_map,List.length_append,List.length_cons,length,middle,List.length_nil]
  have expansion : EVM.memoryExpansionCost image.state .DUP16 = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : image.state.gasAvailable-UInt256.ofNat 0 = image.state.gasAvailable := by
    change UInt256.mk ((u 3).val-0) = u 3
    rw [sub_zero]
  have gate : Assembly.driverGate #[] image.state .DUP16 = .error .StackOverflow := by
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    simp only [EVM.δ,EVM.α,Option.getD_some,count]
    rfl
  change Assembly.driverSteps 1 2 #[] image.state = _
  simp only [Assembly.driverSteps]
  rw [decode_dup_family 15 image]
  dsimp only [Option.option,bind,Except.bind]
  have mappedGate : Assembly.driverGate #[] image.state (dupCode 15) = .error .StackOverflow := gate
  rw [mappedGate]

theorem dup_actual_overflow :
    Assembly.driverSteps 1 2 #[] (site (.DUP 15) 3 (middle ++ 511::List.replicate 1008 513)).state =
      .error .StackOverflow := dup_overflow _ List.length_replicate

theorem depth_specific_underflow :
    Assembly.driverSteps 1 2 #[] (site (.DUP 15) 3 middle).state = .error .StackUnderflow ∧
    Assembly.driverSteps 1 2 #[] (site (.SWAP 15) 3 (511::middle)).state = .error .StackUnderflow := by
  constructor <;> rfl

theorem gas_before_arity :
    Assembly.driverSteps 1 2 #[] (site (.SWAP 15) 2 []).state = .error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (site (.SWAP 15) 3 []).state = .error .StackUnderflow := by
  constructor <;> rfl

theorem zero_step_fuel :
    Assembly.driverSteps 1 1 #[] (site (.DUP 0) 3 (511::spill)).state = .error .OutOfFuel := by rfl

theorem wrong_depth :
    Scalar.step (.op (.DUP 15)) (middle ++ 511::spill) ≠ some (1::(middle ++ 511::spill)) := by
  decide +kernel

theorem wrong_swap_order :
    Scalar.step (.op (.SWAP 15)) (1025::(middle ++ 511::spill)) ≠
      some (511::(middle.reverse ++ 1025::spill)) := by decide +kernel

theorem opcode_family_distinct :
    (Backend.Op.DUP 15).code = 0x8f ∧ (Backend.Op.SWAP 15).code = 0x9f ∧
    EVM.decode (site (.DUP 15) 3 (middle ++ 511::spill)).state.executionEnv.code
      (site (.DUP 15) 3 (middle ++ 511::spill)).state.pc ≠ some (.SWAP16,none) := by
  decide +kernel

private def combination : Site (.DUP 15) :=
  modularSite ⟨seed 6,[.push ⟨1,by decide⟩ #v[0x80],.op .POP],
    [.op (.SWAP 0),.op .STOP],by decide⟩ (middle ++ 511::spill)
private def afterSwap : Scalar.Stack := [1,511,2,3,4,5,6,7,8,9,10,11,12,13,14,15,511,258,513]

theorem fetched_combination :
    Scalar.run [.op (.DUP 15),.op (.SWAP 0)] (middle ++ 511::spill) = some afterSwap ∧
    Assembly.driverSteps 2 3 #[] combination.state =
      .ok {combination.state with
        pc := u 5,gasAvailable := u 0,execLength := 43
        stack := afterSwap.map (fun w => UInt256.mk w.toFin)} := by
  constructor
  · rfl
  · let base : Site (.DUP 15) := ⟨seed 6,[.push ⟨1,by decide⟩ #v[0x80],.op .POP],
      [.op (.SWAP 0),.op .STOP],by decide⟩
    have first := (dup_family_agreement 15 base middle spill 511 rfl (by decide +kernel)
      (by change 3 ≤ 6; decide) 1).2.1
    have first' : Assembly.driverSteps 1 3 #[] combination.state =
        .ok ((Assembly.chargedPrepare combination.state 3).replaceStackAndIncrPC
          ((511::(middle ++ 511::spill)).map (fun w => UInt256.mk w.toFin))) := by
      simpa only [combination,base] using first
    rw [fetched_steps_cons 1 1 #[] combination.state,first']
    rfl

#print axioms fetched_combination
#print axioms every_depth_populated
#print axioms dup_first
#print axioms swap_last
#print axioms dup_capacity_boundary
#print axioms swap_capacity_boundary
#print axioms dup_actual_overflow
#print axioms depth_specific_underflow
#print axioms gas_before_arity
#print axioms zero_step_fuel
#print axioms wrong_depth
#print axioms wrong_swap_order
#print axioms opcode_family_distinct
end SolidityBridge.RoadmapV15.P10.StackFamilyControls
