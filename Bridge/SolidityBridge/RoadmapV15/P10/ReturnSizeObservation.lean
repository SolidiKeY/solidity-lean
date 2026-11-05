import SolidityBridge.RoadmapV15.P10.FrozenWitness
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Charged RETURNDATASIZE consumer of the published frozen fetched API.
The returnData buffer is distinct from H_return, calldata and physical memory.
No call-origin, copy/read-value, allocator or world/source adequacy is supplied. -/
namespace SolidityBridge.RoadmapV15.P10.ReturnSizeObservation
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed before after u spill)

theorem gate_classification (valid : Array UInt256) (s : EVM.State) :
    Assembly.driverGate valid s .RETURNDATASIZE=
      if s.gasAvailable.toNat<2 then .error .OutOfGass
      else if 1024<s.stack.length+1 then .error .StackOverflow
      else .ok (s,2) := by
  first
  | solve | rfl
  | solve | decide
  | solve | omega
  | solve | simp only []
  | have expansion : EVM.memoryExpansionCost s .RETURNDATASIZE=0 := by
      simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
    have charge : s.gasAvailable-UInt256.ofNat 0=s.gasAvailable := by
      change UInt256.mk (s.gasAvailable.val-0)=s.gasAvailable
      rw [sub_zero]
    have cost : EVM.C' s .RETURNDATASIZE=2 := rfl
    have notCopy : (Operation.RETURNDATASIZE : Operation .EVM)≠.RETURNDATACOPY := by decide
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    simp only [cost,EVM.δ,EVM.α,Option.getD_some,if_neg (Nat.not_lt_zero _),Nat.sub_zero,notCopy,false_and,if_false]
    by_cases gas : s.gasAvailable.toNat<2
    · simp only [if_pos gas,bind,Except.bind,pure,Except.pure,reduceCtorEq,false_and,if_false]
    · simp only [if_neg gas,bind,Except.bind,pure,Except.pure,reduceCtorEq,false_and,if_false]
      by_cases full : 1024<s.stack.length+1
      · simp only [if_pos full]
      · simp only [if_neg full]
        cases s.executionEnv.perm <;> rfl

theorem agreement (valid : Array UInt256) (site : Site .RETURNDATASIZE) (fuel : Nat)
    (gas : 2≤site.state.gasAvailable.toNat) (room : site.state.stack.length+1≤1024) :
    let next := (Assembly.chargedPrepare site.state 2).replaceStackAndIncrPC
      (UInt256.ofNat site.state.returnData.size::site.state.stack)
    Assembly.driverSteps 1 (fuel+2) valid site.state=.ok next ∧
    EVM.X (fuel+2) valid site.state=EVM.X (fuel+1) valid next ∧
    next.toState=site.state.toState ∧ next.memory=site.state.memory ∧
    next.returnData=site.state.returnData ∧ next.H_return=site.state.H_return := by
  have gate : Assembly.driverGate valid site.state .RETURNDATASIZE=.ok (site.state,2) := by
    rw [gate_classification,if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge room)]
  have step := FrozenV1.api.charged.checked_return_size site valid fuel
  rw [gate] at step
  dsimp only at step ⊢
  have continuation := FrozenV1.api.continuation.x_return_size site valid fuel
  rw [step] at continuation
  exact ⟨step,continuation,rfl,rfl,rfl,rfl⟩

theorem word_observation (site : Site .RETURNDATASIZE) :
    (UInt256.ofNat site.state.returnData.size).toNat=site.state.returnData.size%UInt256.size := by
  rfl

def entry (gas : Nat) (perm : Bool) (words : Scalar.Stack) (bytes : ByteArray) : Site .RETURNDATASIZE :=
  ⟨{seed gas perm with
    stack := words.map (fun w=>UInt256.mk w.toFin)
    returnData := bytes
    executionEnv := {(seed gas perm).executionEnv with calldata:=⟨#[0x11,0x22,0x33,0x44]⟩}},before,after,by decide⟩
def populated : ByteArray := ⟨#[0xcc,0xdd,0]⟩
def observed (perm : Bool) (words : Scalar.Stack) (bytes : ByteArray) : EVM.State :=
  {(entry 9 perm words bytes).state with
    stack:=UInt256.ofNat bytes.size::words.map (fun w=>UInt256.mk w.toFin)
    pc:=u 4,gasAvailable:=u 7,execLength:=42}

theorem client (perm : Bool) (words : Scalar.Stack) (bytes : ByteArray) (room : words.length+1≤1024) :
    Assembly.driverSteps 1 2 #[u 37,u 99] (entry 9 perm words bytes).state=.ok (observed perm words bytes) := by
  have actual := (agreement #[u 37,u 99] (entry 9 perm words bytes) 0 (by change 2≤9;decide)
    (by simpa only [entry,Site.state,List.length_map] using room)).1
  have shape : (Assembly.chargedPrepare (entry 9 perm words bytes).state 2).replaceStackAndIncrPC
      (UInt256.ofNat (entry 9 perm words bytes).state.returnData.size::(entry 9 perm words bytes).state.stack)=observed perm words bytes := by
    first
    | solve | rfl
    | solve | simp only []
    | simp only [entry,observed,Site.state,Assembly.chargedPrepare,EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,seed,u]
      rfl
  rw [shape] at actual
  exact actual

theorem complete_observation (perm : Bool) :
    let out := observed perm spill populated
    out.stack=[u 3,u 258,u 513] ∧ out.stack≠[u 2,u 258,u 513] ∧
    out.stack≠[u 4,u 258,u 513] ∧ out.stack≠[u 3,u 513,u 258] ∧
    out.returnData.data.toList=[0xcc,0xdd,0] ∧ out.H_return.data.toList=[0xee,0xff] ∧
    out.executionEnv.calldata.data.toList=[0x11,0x22,0x33,0x44] ∧
    out.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    out.executionEnv.code.data.toList=[0x60,0x7f,0x50,0x3d,0] ∧
    out.pc=u 4 ∧ out.gasAvailable=u 7 ∧ out.execLength=42 ∧
    out.toState=(entry 9 perm spill populated).state.toState := by
  refine ⟨rfl,?_,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · change [u 3,u 258,u 513]≠[u 2,u 258,u 513];decide
  · change [u 3,u 258,u 513]≠[u 4,u 258,u 513];decide
  · change [u 3,u 258,u 513]≠[u 3,u 513,u 258];decide

theorem empty_and_capacity (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (entry 9 perm [] .empty).state=.ok (observed perm [] .empty) ∧
    Assembly.driverSteps 1 2 #[] (entry 9 perm (List.replicate 1023 513) populated).state=
      .ok (observed perm (List.replicate 1023 513) populated) ∧
    (observed perm [] .empty).stack=[u 0] := by
  have empty := client perm [] .empty (by decide)
  have full := client perm (List.replicate 1023 513) populated (by simp only [List.length_replicate];decide)
  -- Observation does not inspect the supplied jump table; use the same concrete table.
  simpa only [FrozenV1.api.charged.checked_return_size,gate_classification] using
    (show Assembly.driverSteps 1 2 #[u 37,u 99] (entry 9 perm [] .empty).state=.ok (observed perm [] .empty) ∧
      Assembly.driverSteps 1 2 #[u 37,u 99] (entry 9 perm (List.replicate 1023 513) populated).state=
        .ok (observed perm (List.replicate 1023 513) populated) ∧
      (observed perm [] .empty).stack=[u 0] from ⟨empty,full,rfl⟩)

theorem failure_order (perm : Bool) :
    Assembly.driverSteps 1 2 #[] (entry 1 perm (List.replicate 1024 513) populated).state=.error .OutOfGass ∧
    Assembly.driverSteps 1 2 #[] (entry 9 perm (List.replicate 1024 513) populated).state=.error .StackOverflow ∧
    Assembly.driverSteps 1 1 #[] (entry 0 perm [] populated).state=.error .OutOfFuel := by
  have shortGas : Assembly.driverGate #[] (entry 1 perm (List.replicate 1024 513) populated).state .RETURNDATASIZE=.error .OutOfGass := by
    rw [gate_classification]
    change (if 1<2 then _ else _)=_
    rw [if_pos (by decide : 1<2)]
  have overflow : Assembly.driverGate #[] (entry 9 perm (List.replicate 1024 513) populated).state .RETURNDATASIZE=.error .StackOverflow := by
    rw [gate_classification]
    have n : (entry 9 perm (List.replicate 1024 513) populated).state.stack.length+1=1025 := by
      simp only [entry,Site.state,List.length_map,List.length_replicate]
    rw [n]
    change (if 9<2 then _ else if 1024<1025 then _ else _)=_
    rw [if_neg (by decide : ¬9<2),if_pos (by decide : 1024<1025)]
  have low := FrozenV1.api.charged.checked_return_size (entry 1 perm (List.replicate 1024 513) populated) #[] 0
  have high := FrozenV1.api.charged.checked_return_size (entry 9 perm (List.replicate 1024 513) populated) #[] 0
  rw [shortGas] at low
  rw [overflow] at high
  exact ⟨low,high,rfl⟩

#print axioms empty_and_capacity
#print axioms failure_order
#print axioms gate_classification
#print axioms agreement
#print axioms word_observation
#print axioms client
#print axioms complete_observation
end SolidityBridge.RoadmapV15.P10.ReturnSizeObservation
