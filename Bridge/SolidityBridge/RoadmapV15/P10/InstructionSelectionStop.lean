import SolidityBridge.RoadmapV15.P10.InstructionSelectionSequence

/-! Terminal STOP consumer for the concrete fetched ADD/MUL sequence.
This retains the pinned returnData clearing policy and separate H_return buffer.
No source/frame origin, account execution, transaction or Osaka adequacy is inferred. -/
namespace SolidityBridge.RoadmapV15.P10.InstructionSelectionStop
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open InstructionSelectionSequence
open WordPushFixtures (u spill)

def finished (a b c : Scalar.Word) (tail : Scalar.Stack) (perm : Bool) : EVM.State :=
  {expected a b c tail perm with execLength:=44,returnData:=.empty}

private theorem stop_gate (valid : Array UInt256) (s : EVM.State) (room : s.stack.length≤1024) :
    Assembly.driverGate valid s .STOP=.ok (s,0) := by
  first
  | solve | rfl
  | solve | simp only []
  | have expansion : EVM.memoryExpansionCost s .STOP=0 := by
      simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
    have charge : s.gasAvailable-UInt256.ofNat 0=s.gasAvailable := by
      change UInt256.mk (s.gasAvailable.val-0)=s.gasAvailable
      rw [sub_zero]
    have cost : EVM.C' s .STOP=0 := rfl
    simp only [Assembly.driverGate]
    rw [expansion,charge]
    simp only [cost,EVM.δ,EVM.α,Option.getD_some,if_neg (Nat.not_lt_zero _),
      Nat.sub_zero,Nat.add_zero,if_neg (Nat.not_lt_of_ge room)]
    cases s.executionEnv.perm <;> rfl

private theorem room_at_stop (a b c : Scalar.Word) (tail : Scalar.Stack) (perm : Bool)
    (room : tail.length+3≤1024) : (expected a b c tail perm).stack.length≤1024 := by
  change ((((a+b)*c)::tail).map (fun w=>UInt256.mk w.toFin)).length≤1024
  simp only [List.length_map,List.length_cons]
  omega

theorem decoded_stop (a b c : Scalar.Word) (tail : Scalar.Stack) (perm : Bool) :
    EVM.decode (expected a b c tail perm).executionEnv.code (expected a b c tail perm).pc=some (.STOP,none) := by
  rfl

/-- Real reference termination, not just the arithmetic-prefix continuation. -/
theorem terminates (valid : Array UInt256) (a b c : Scalar.Word) (tail : Scalar.Stack)
    (perm : Bool) (room : tail.length+3≤1024) :
    EVM.X 4 valid (input a b c tail perm)=.ok (.success (finished a b c tail perm) .empty) := by
  let m : Solidity.Evm.Machine := {Solidity.Evm.Machine.init with stack:=Selection.irStack (a::b::c::tail)}
  have arithmeticRun := InstructionSelectionSequence.sequence valid a b c tail perm m rfl room
  rw [arithmeticRun.2.2.2.2.2.1]
  have gate := stop_gate valid (expected a b c tail perm) (room_at_stop a b c tail perm room)
  have result := Assembly.X_stop 0 valid (expected a b c tail perm) (expected a b c tail perm) 0
    (by rw [decoded_stop];rfl) gate
  have shape : Assembly.stopAfter (expected a b c tail perm) 0=finished a b c tail perm := by
    first
    | solve | rfl
    | solve | simp only []
    | have charge : (expected a b c tail perm).gasAvailable-UInt256.ofNat 0=(expected a b c tail perm).gasAvailable := by
        change UInt256.mk ((expected a b c tail perm).gasAvailable.val-0)=(expected a b c tail perm).gasAvailable
        rw [sub_zero]
      simp only [Assembly.stopAfter,Assembly.chargedPrepare,charge,finished]
      rfl
  rw [shape] at result
  exact result

/-- Fuel one can reach the STOP gate but cannot run its instruction. -/
theorem stop_short_fuel (valid : Array UInt256) (a b c : Scalar.Word) (tail : Scalar.Stack)
    (perm : Bool) (room : tail.length+3≤1024) :
    EVM.X 1 valid (expected a b c tail perm)=.error .OutOfFuel := by
  rw [Assembly.X_unfold,decoded_stop]
  simp only [Option.getD_some]
  have gate := stop_gate valid (expected a b c tail perm) (room_at_stop a b c tail perm room)
  rw [gate]
  rfl

theorem complete_observation (perm : Bool) :
    let out := finished 7 3 5 spill perm
    out.stack=[u 50,u 258,u 513] ∧ out.stack≠[u 50,u 513,u 258] ∧
    out.pc=u 5 ∧ out.pc≠u 6 ∧ out.gasAvailable=u 4 ∧ out.execLength=44 ∧
    out.returnData.data.toList=[] ∧ out.returnData.data.toList≠[0xcc,0xdd] ∧
    out.H_return.data.toList=[0xee,0xff] ∧
    out.memory.data.toList=[0xaa,0xbb]++List.replicate 30 0 ∧
    out.activeWords=u 1 ∧ out.toState=(input 7 3 5 spill perm).toState := by
  refine ⟨rfl,?_,rfl,?_,rfl,rfl,rfl,?_,rfl,rfl,rfl,rfl⟩
  · change [u 50,u 258,u 513]≠[u 50,u 513,u 258];decide
  · change u 5≠u 6;decide
  · change ([]:List UInt8)≠[0xcc,0xdd];decide

theorem nonzero_client (perm : Bool) :
    EVM.X 4 #[u 37,u 99] (input 7 3 5 spill perm)=.ok (.success (finished 7 3 5 spill perm) .empty) := by
  exact terminates _ _ _ _ _ _ (by decide)

#print axioms decoded_stop
#print axioms terminates
#print axioms stop_short_fuel
#print axioms complete_observation
#print axioms nonzero_client
end SolidityBridge.RoadmapV15.P10.InstructionSelectionStop
