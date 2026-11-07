import SolidityBridge.RoadmapV15.P10.HeaderEnvironment
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Populated raw-native observations, not source/world reachability witnesses.
Header wrapping and absent-account cases keep the actual reference definition. -/
namespace SolidityBridge.RoadmapV15.P10.HeaderEnvironmentControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed u accounts spill before after)

def entry (op : Backend.Op) (gas : Nat) (perm : Bool) (time : Nat)
    (ledger : AccountMap .EVM) (words : Scalar.Stack) : Site op :=
  ⟨{seed gas perm with
    accountMap := ledger
    stack := words.map (fun w => UInt256.mk w.toFin)
    executionEnv := {(seed gas perm).executionEnv with
      weiValue := u 37
      header := {(seed gas perm).executionEnv.header with timestamp := time}}},
    before,after,by decide⟩
def observed (op : Backend.Op) (perm : Bool) (time : Nat) (ledger : AccountMap .EVM)
    (words : Scalar.Stack) (value : UInt256) (remaining : Nat) : EVM.State :=
  {(entry op 9 perm time ledger words).state with
    pc := u 4,gasAvailable := u remaining,execLength := 42
    stack := value::words.map (fun w => UInt256.mk w.toFin)}

private theorem expected_state (op : Backend.Op) (perm : Bool) (time : Nat)
    (ledger : AccountMap .EVM) (words : Scalar.Stack) (value : UInt256)
    (cost : Nat) (allowed : cost=2 ∨ cost=5) :
    (Assembly.chargedPrepare (entry op 9 perm time ledger words).state cost).replaceStackAndIncrPC
      (value::(entry op 9 perm time ledger words).state.stack) =
      observed op perm time ledger words value (9-cost) := by
  change ({(entry op 9 perm time ledger words).state with
    pc := u 3 + u 1,gasAvailable := u 9-u cost,execLength := 42,
    stack := value::words.map (fun w => UInt256.mk w.toFin)} : EVM.State) = _
  have pc : u 3+u 1=u 4 := by rfl
  rw [pc]
  rcases allowed with rfl|rfl
  · have gas : u 9-u 2=u 7 := by rfl
    rw [gas]
    rfl
  · have gas : u 9-u 5=u 4 := by rfl
    rw [gas]
    rfl

theorem timestamp_client (perm : Bool) (time : Nat) (words : Scalar.Stack)
    (room : words.length+1 ≤ 1024) :
    Assembly.driverSteps 1 2 #[] (entry .TIMESTAMP 9 perm time accounts words).state =
      .ok (observed .TIMESTAMP perm time accounts words (u time) 7) := by
  have capacity : (entry .TIMESTAMP 9 perm time accounts words).state.stack.length+1 ≤ 1024 := by
    simpa only [entry,Site.state,List.length_map] using room
  have h := (timestamp_fetched (entry .TIMESTAMP 9 perm time accounts words) 0
    (by change 2 ≤ 9;decide) capacity).1
  rw [expected_state _ _ _ _ _ _ 2 (Or.inl rfl)] at h
  exact h

theorem selfbalance_client (perm : Bool) (words : Scalar.Stack)
    (room : words.length+1 ≤ 1024) :
    Assembly.driverSteps 1 2 #[] (entry .SELFBALANCE 9 perm 260 accounts words).state =
      .ok (observed .SELFBALANCE perm 260 accounts words (u 29) 4) := by
  have capacity : (entry .SELFBALANCE 9 perm 260 accounts words).state.stack.length+1 ≤ 1024 := by
    simpa only [entry,Site.state,List.length_map] using room
  have h := (selfbalance_fetched (entry .SELFBALANCE 9 perm 260 accounts words) 0
    (by change 5 ≤ 9;decide) capacity).1
  rw [expected_state _ _ _ _ _ _ 5 (Or.inr rfl)] at h
  exact h

/-- Logical native missing-account behavior, not a supplied-code reachability claim. -/
theorem selfbalance_absent :
    Assembly.driverSteps 1 2 #[] (entry .SELFBALANCE 9 false 260 ∅ spill).state =
      .ok (observed .SELFBALANCE false 260 ∅ spill (u 0) 4) := by
  have h := (selfbalance_fetched (entry .SELFBALANCE 9 false 260 ∅ spill) 0
    (by change 5 ≤ 9;decide) (by decide)).1
  rw [expected_state _ _ _ _ _ _ 5 (Or.inr rfl)] at h
  exact h

theorem legal_capacity :
    Assembly.driverSteps 1 2 #[] (entry .TIMESTAMP 9 false 260 accounts []).state =
      .ok (observed .TIMESTAMP false 260 accounts [] (u 260) 7) ∧
    Assembly.driverSteps 1 2 #[] (entry .SELFBALANCE 9 true 260 accounts (List.replicate 1023 513)).state =
      .ok (observed .SELFBALANCE true 260 accounts (List.replicate 1023 513) (u 29) 4) := by
  exact ⟨timestamp_client _ _ _ (by decide),selfbalance_client _ _ (by simp only [List.length_replicate];decide)⟩

/-- A raw Nat header can exceed the word size; no source or consensus admission is added. -/
theorem timestamp_modulo :
    Assembly.driverSteps 1 2 #[] (entry .TIMESTAMP 9 true (2^256+513) accounts spill).state =
      .ok (observed .TIMESTAMP true (2^256+513) accounts spill (u 513) 7) := by
  have word : u (2^256+513)=u 513 := by rfl
  have h := timestamp_client true (2^256+513) spill (by decide)
  rw [word] at h
  exact h

private theorem balance_overflow (site : Site .SELFBALANCE)
    (gas : 5 ≤ site.state.gasAvailable.toNat) (full : site.state.stack.length=1024) :
    Assembly.driverSteps 1 2 #[] site.state = .error .StackOverflow := by
  have expansion : EVM.memoryExpansionCost site.state .SELFBALANCE = 0 := by
    simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : site.state.gasAvailable-UInt256.ofNat 0=site.state.gasAvailable := by
    change UInt256.mk (site.state.gasAvailable.val-0)=site.state.gasAvailable
    rw [sub_zero]
  have cost : EVM.C' site.state .SELFBALANCE=5 := rfl
  have decoded := DecoderAgreement.decode_all site
  simp only [Assembly.driverSteps,decoded,Option.option,bind,Except.bind]
  simp only [Assembly.driverGate,DecoderAgreement.referenceOp]
  rw [expansion,charge]
  simp only [cost,EVM.δ,EVM.α,Option.getD_some,Nat.sub_zero,
    if_neg (Nat.not_lt_zero _),if_neg (Nat.not_lt_of_ge gas),full]
  rfl

theorem resource_order :
    Assembly.driverSteps 1 2 #[] (entry .TIMESTAMP 1 false 260 accounts spill).state = .error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (entry .SELFBALANCE 4 true 260 accounts spill).state = .error .OutOfGass ∧
    Assembly.driverSteps 1 1 #[] (entry .SELFBALANCE 0 false 260 accounts spill).state = .error .OutOfFuel ∧
    Assembly.driverSteps 1 2 #[] (entry .SELFBALANCE 9 false 260 accounts (List.replicate 1024 513)).state = .error .StackOverflow := by
  exact ⟨rfl,rfl,rfl,balance_overflow (entry .SELFBALANCE 9 false 260 accounts (List.replicate 1024 513))
    (by change 5 ≤ 9;decide) (by simp only [entry,Site.state,List.length_map,List.length_replicate])⟩

theorem identities_and_costs :
    (observed .SELFBALANCE false 260 accounts spill (u 29) 4).stack ≠ [u 41,u 258,u 513] ∧
    (observed .SELFBALANCE false 260 accounts spill (u 29) 4).stack ≠ [u 37,u 258,u 513] ∧
    (observed .SELFBALANCE false 260 accounts spill (u 29) 4).stack ≠ [u 4,u 258,u 513] ∧
    (observed .TIMESTAMP false 260 accounts spill (u 260) 7).stack ≠ [u 4,u 258,u 513] := by
  decide

theorem complete_ordered_observation :
    (observed .SELFBALANCE false 260 accounts spill (u 29) 4).stack = [u 29,u 258,u 513] ∧
    (observed .SELFBALANCE false 260 accounts spill (u 29) 4).stack ≠ [u 513,u 258,u 29] ∧
    (observed .SELFBALANCE false 260 accounts spill (u 29) 4).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x47,0x00] ∧
    (observed .SELFBALANCE false 260 accounts spill (u 29) 4).pc = u 4 ∧
    (observed .SELFBALANCE false 260 accounts spill (u 29) 4).gasAvailable = u 4 ∧
    (observed .SELFBALANCE false 260 accounts spill (u 29) 4).execLength = 42 ∧
    (observed .SELFBALANCE false 260 accounts spill (u 29) 4).executionEnv.header.timestamp = 260 ∧
    (observed .SELFBALANCE false 260 accounts spill (u 29) 4).memory.data.toList = [0xaa,0xbb]++List.replicate 30 0 ∧
    (observed .SELFBALANCE false 260 accounts spill (u 29) 4).activeWords = u 1 ∧
    (observed .SELFBALANCE false 260 accounts spill (u 29) 4).returnData.data.toList = [0xcc,0xdd] ∧
    (observed .SELFBALANCE false 260 accounts spill (u 29) 4).H_return.data.toList = [0xee,0xff] ∧
    (observed .SELFBALANCE false 260 accounts spill (u 29) 4).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (observed .SELFBALANCE false 260 accounts spill (u 29) 4).accountMap = accounts ∧
    (observed .SELFBALANCE false 260 accounts spill (u 29) 4).σ₀ = accounts ∧
    (observed .SELFBALANCE false 260 accounts spill (u 29) 4).substate = (seed 9 false).substate := by
  exact ⟨rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms timestamp_client
#print axioms selfbalance_client
#print axioms selfbalance_absent
#print axioms legal_capacity
#print axioms timestamp_modulo
#print axioms resource_order
#print axioms identities_and_costs
#print axioms complete_ordered_observation
end SolidityBridge.RoadmapV15.P10.HeaderEnvironmentControls
