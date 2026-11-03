import SolidityBridge.RoadmapV15.P10.BlockMetadata
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Populated native metadata controls paired with unchanged source-slice
refusals. No source/consensus reachability or randomness-generation claim. -/
namespace SolidityBridge.RoadmapV15.P10.BlockMetadataControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed u accounts spill before after)

def entry (op : Backend.Op) (gas : Nat) (perm : Bool) (number : Nat)
    (words : Scalar.Stack) : Site op :=
  ⟨{seed gas perm with
    stack := words.map (fun w => UInt256.mk w.toFin)
    executionEnv := {(seed gas perm).executionEnv with
      weiValue := u 37,gasPrice := 61
      header := {(seed gas perm).executionEnv.header with
        beneficiary := .ofNat 23,number := number,prevRandao := u 43,
        difficulty := 13,gasLimit := 30000000,baseFeePerGas := 59,timestamp := 513}}},
    before,after,by decide⟩
def observed (op : Backend.Op) (perm : Bool) (number : Nat) (words : Scalar.Stack)
    (value : UInt256) : EVM.State :=
  {(entry op 9 perm number words).state with
    pc := u 4,gasAvailable := u 7,execLength := 42
    stack := value::words.map (fun w => UInt256.mk w.toFin)}

private theorem expected_state (op : Backend.Op) (perm : Bool) (number : Nat)
    (words : Scalar.Stack) (value : UInt256) :
    (Assembly.chargedPrepare (entry op 9 perm number words).state 2).replaceStackAndIncrPC
      (value::(entry op 9 perm number words).state.stack) = observed op perm number words value := by
  change ({(entry op 9 perm number words).state with
    pc := u 3+u 1,gasAvailable := u 9-u 2,execLength := 42,
    stack := value::words.map (fun w => UInt256.mk w.toFin)} : EVM.State) = _
  have pc : u 3+u 1=u 4 := by rfl
  have gas : u 9-u 2=u 7 := by rfl
  rw [pc,gas]
  rfl

theorem coinbase_client (perm : Bool) (words : Scalar.Stack) (room : words.length+1 ≤ 1024) :
    Assembly.driverSteps 1 2 #[] (entry .COINBASE 9 perm 257 words).state =
      .ok (observed .COINBASE perm 257 words (u 23)) := by
  have capacity : (entry .COINBASE 9 perm 257 words).state.stack.length+1 ≤ 1024 := by
    simpa only [entry,Site.state,List.length_map] using room
  have h := (coinbase_fetched #[] (entry .COINBASE 9 perm 257 words) 0
    (by change 2 ≤ 9;decide) capacity).1
  rw [expected_state] at h
  exact h

theorem number_client (perm : Bool) (number : Nat) (words : Scalar.Stack) (room : words.length+1 ≤ 1024) :
    Assembly.driverSteps 1 2 #[] (entry .NUMBER 9 perm number words).state =
      .ok (observed .NUMBER perm number words (u number)) := by
  have capacity : (entry .NUMBER 9 perm number words).state.stack.length+1 ≤ 1024 := by
    simpa only [entry,Site.state,List.length_map] using room
  have h := (number_fetched #[] (entry .NUMBER 9 perm number words) 0
    (by change 2 ≤ 9;decide) capacity).1
  rw [expected_state] at h
  exact h

theorem prevrandao_client (perm : Bool) (words : Scalar.Stack) (room : words.length+1 ≤ 1024) :
    Assembly.driverSteps 1 2 #[] (entry .PREVRANDAO 9 perm 257 words).state =
      .ok (observed .PREVRANDAO perm 257 words (u 43)) := by
  have capacity : (entry .PREVRANDAO 9 perm 257 words).state.stack.length+1 ≤ 1024 := by
    simpa only [entry,Site.state,List.length_map] using room
  have h := (prevrandao_fetched #[] (entry .PREVRANDAO 9 perm 257 words) 0
    (by change 2 ≤ 9;decide) capacity).1
  rw [expected_state] at h
  exact h

theorem gaslimit_client (perm : Bool) (words : Scalar.Stack) (room : words.length+1 ≤ 1024) :
    Assembly.driverSteps 1 2 #[] (entry .GASLIMIT 9 perm 257 words).state =
      .ok (observed .GASLIMIT perm 257 words (u 30000000)) := by
  have capacity : (entry .GASLIMIT 9 perm 257 words).state.stack.length+1 ≤ 1024 := by
    simpa only [entry,Site.state,List.length_map] using room
  have h := (gaslimit_fetched #[] (entry .GASLIMIT 9 perm 257 words) 0
    (by change 2 ≤ 9;decide) capacity).1
  rw [expected_state] at h
  exact h

theorem basefee_client (perm : Bool) (words : Scalar.Stack) (room : words.length+1 ≤ 1024) :
    Assembly.driverSteps 1 2 #[] (entry .BASEFEE 9 perm 257 words).state =
      .ok (observed .BASEFEE perm 257 words (u 59)) := by
  have capacity : (entry .BASEFEE 9 perm 257 words).state.stack.length+1 ≤ 1024 := by
    simpa only [entry,Site.state,List.length_map] using room
  have h := (basefee_fetched #[] (entry .BASEFEE 9 perm 257 words) 0
    (by change 2 ≤ 9;decide) capacity).1
  rw [expected_state] at h
  exact h

/-- A supplied table need not be correct for future branches to read this field. -/
theorem arbitrary_table_client :
    Assembly.driverSteps 1 2 #[u 99] (entry .PREVRANDAO 9 false 257 spill).state =
      .ok (observed .PREVRANDAO false 257 spill (u 43)) := by
  have h := (prevrandao_fetched #[u 99] (entry .PREVRANDAO 9 false 257 spill) 0
    (by decide) (by decide)).1
  rw [expected_state] at h
  exact h

theorem legal_capacity :
    Assembly.driverSteps 1 2 #[] (entry .COINBASE 9 false 257 []).state =
      .ok (observed .COINBASE false 257 [] (u 23)) ∧
    Assembly.driverSteps 1 2 #[] (entry .BASEFEE 9 true 257 (List.replicate 1023 513)).state =
      .ok (observed .BASEFEE true 257 (List.replicate 1023 513) (u 59)) := by
  exact ⟨coinbase_client _ _ (by decide),basefee_client _ _ (by simp only [List.length_replicate];decide)⟩

/-- Raw Nat-to-word conversion only, not a source or consensus profile extension. -/
theorem number_modulo :
    Assembly.driverSteps 1 2 #[] (entry .NUMBER 9 true (2^256+513) spill).state =
      .ok (observed .NUMBER true (2^256+513) spill (u 513)) := by
  have word : u (2^256+513)=u 513 := by rfl
  have h := number_client true (2^256+513) spill (by decide)
  rw [word] at h
  exact h

private theorem fee_overflow (site : Site .BASEFEE)
    (gas : 2 ≤ site.state.gasAvailable.toNat) (full : site.state.stack.length=1024) :
    Assembly.driverSteps 1 2 #[] site.state = .error .StackOverflow := by
  have expansion : EVM.memoryExpansionCost site.state .BASEFEE=0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : site.state.gasAvailable-UInt256.ofNat 0=site.state.gasAvailable := by
    change UInt256.mk (site.state.gasAvailable.val-0)=site.state.gasAvailable
    rw [sub_zero]
  have cost : EVM.C' site.state .BASEFEE=2 := rfl
  have decoded := DecoderAgreement.decode_all site
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind]
  simp only [Assembly.driverGate,DecoderAgreement.referenceOp]
  rw [expansion,charge]
  simp only [cost,EVM.δ,EVM.α,Option.getD_some,Nat.sub_zero,
    if_neg (Nat.not_lt_zero _),if_neg (Nat.not_lt_of_ge gas),full]
  rfl

theorem resource_order :
    Assembly.driverSteps 1 2 #[] (entry .COINBASE 1 false 257 spill).state = .error .OutOfGass ∧
    Assembly.driverSteps 1 1 #[] (entry .NUMBER 0 true 257 spill).state = .error .OutOfFuel ∧
    Assembly.driverSteps 1 2 #[] (entry .BASEFEE 9 false 257 (List.replicate 1024 513)).state = .error .StackOverflow ∧
    Assembly.driverSteps 1 2 #[] (entry .BASEFEE 1 true 257 (List.replicate 1024 513)).state = .error .OutOfGass := by
  exact ⟨rfl,rfl,fee_overflow (entry .BASEFEE 9 false 257 (List.replicate 1024 513))
    (by change 2 ≤ 9;decide) (by simp only [entry,Site.state,List.length_map,List.length_replicate]),rfl⟩

theorem distinct_fields :
    (observed .COINBASE false 257 spill (u 23)).stack ≠ [u 7,u 258,u 513] ∧
    (observed .NUMBER false 257 spill (u 257)).stack ≠ [u 513,u 258,u 513] ∧
    (observed .PREVRANDAO false 257 spill (u 43)).stack ≠ [u 13,u 258,u 513] ∧
    (observed .BASEFEE false 257 spill (u 59)).stack ≠ [u 61,u 258,u 513] ∧
    (observed .BASEFEE false 257 spill (u 59)).stack ≠ [u 37,u 258,u 513] ∧
    (observed .GASLIMIT false 257 spill (u 30000000)).stack ≠ [u 7,u 258,u 513] := by
  decide

theorem source_refusal_clients (frame : Backend.Environment.Frame) (tail : List Backend.Environment.Word) :
    (Backend.Environment.admittedOp .COINBASE=false ∧ Backend.Environment.step frame (.op .COINBASE) tail=none) ∧
    (Backend.Environment.admittedOp .NUMBER=false ∧ Backend.Environment.step frame (.op .NUMBER) tail=none) ∧
    (Backend.Environment.admittedOp .PREVRANDAO=false ∧ Backend.Environment.step frame (.op .PREVRANDAO) tail=none) ∧
    (Backend.Environment.admittedOp .GASLIMIT=false ∧ Backend.Environment.step frame (.op .GASLIMIT) tail=none) ∧
    (Backend.Environment.admittedOp .BASEFEE=false ∧ Backend.Environment.step frame (.op .BASEFEE) tail=none) := by
  exact ⟨metadata_source_refusal _ (Or.inl rfl) frame tail,
    metadata_source_refusal _ (Or.inr (Or.inl rfl)) frame tail,
    metadata_source_refusal _ (Or.inr (Or.inr (Or.inl rfl))) frame tail,
    metadata_source_refusal _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) frame tail,
    metadata_source_refusal _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) frame tail⟩

theorem complete_ordered_observation :
    (observed .PREVRANDAO false 257 spill (u 43)).stack = [u 43,u 258,u 513] ∧
    (observed .PREVRANDAO false 257 spill (u 43)).stack ≠ [u 513,u 258,u 43] ∧
    (observed .PREVRANDAO false 257 spill (u 43)).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x44,0x00] ∧
    (observed .PREVRANDAO false 257 spill (u 43)).pc=u 4 ∧
    (observed .PREVRANDAO false 257 spill (u 43)).gasAvailable=u 7 ∧
    (observed .PREVRANDAO false 257 spill (u 43)).execLength=42 ∧
    (observed .PREVRANDAO false 257 spill (u 43)).executionEnv.header.beneficiary.val=23 ∧
    (observed .PREVRANDAO false 257 spill (u 43)).executionEnv.header.number=257 ∧
    (observed .PREVRANDAO false 257 spill (u 43)).executionEnv.header.prevRandao=u 43 ∧
    (observed .PREVRANDAO false 257 spill (u 43)).executionEnv.header.difficulty=13 ∧
    (observed .PREVRANDAO false 257 spill (u 43)).executionEnv.header.gasLimit=30000000 ∧
    (observed .PREVRANDAO false 257 spill (u 43)).executionEnv.header.baseFeePerGas=59 ∧
    (observed .PREVRANDAO false 257 spill (u 43)).executionEnv.header.timestamp=513 ∧
    (observed .PREVRANDAO false 257 spill (u 43)).memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    (observed .PREVRANDAO false 257 spill (u 43)).activeWords=u 1 ∧
    (observed .PREVRANDAO false 257 spill (u 43)).returnData.data.toList=[0xcc,0xdd] ∧
    (observed .PREVRANDAO false 257 spill (u 43)).H_return.data.toList=[0xee,0xff] ∧
    (observed .PREVRANDAO false 257 spill (u 43)).executionEnv.calldata.data.toList=[0x11,0x22,0x33] ∧
    (observed .PREVRANDAO false 257 spill (u 43)).accountMap=accounts ∧
    (observed .PREVRANDAO false 257 spill (u 43)).σ₀=accounts ∧
    (observed .PREVRANDAO false 257 spill (u 43)).substate=(seed 9 false).substate := by
  exact ⟨rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms coinbase_client
#print axioms number_client
#print axioms prevrandao_client
#print axioms gaslimit_client
#print axioms basefee_client
#print axioms arbitrary_table_client
#print axioms legal_capacity
#print axioms number_modulo
#print axioms resource_order
#print axioms distinct_fields
#print axioms source_refusal_clients
#print axioms complete_ordered_observation
end SolidityBridge.RoadmapV15.P10.BlockMetadataControls
