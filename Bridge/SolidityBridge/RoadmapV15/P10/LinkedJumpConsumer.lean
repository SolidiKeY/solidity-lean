import SolidityBridge.RoadmapV15.P10.JumpMemberConsumer

/-! Consume the published linked-program reference/scanner certificate to
supply an actual JUMPI destination. Code alignment and resources stay explicit;
no membership, decoder or desired-execution conclusion is an input premise.
The certified array is not asserted equal to opaque upstream D_J. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

local instance : ReflBEq UInt256 where
  rfl {a} := by
    cases a with
    | mk a => change (a == a) = true; exact BEq.rfl

theorem linked_reference_member {code : List Solidity.Evm.Instr}
    (program : Assembly.LinkedProgram code) (n : Nat) (reference : n ∈ program.checked.image.refs) :
    program.validJumps.contains (UInt256.ofNat n) = true := by
  have facts := program.reference n reference
  apply Array.contains_eq_true_of_mem
  simpa only [Assembly.LinkedProgram.validJumps,List.mem_toArray] using facts.2.1

theorem linked_reference_jumpi {code : List Solidity.Evm.Instr}
    (program : Assembly.LinkedProgram code) (n : Nat) (reference : n ∈ program.checked.image.refs)
    (site : Site .JUMPI)
    (aligned : site.state.executionEnv.code = program.frame.executionEnv.code)
    (condition : UInt256) (tail : List UInt256) (room : tail.length+2 ≤ 1024)
    (gas : 10 ≤ site.seed.gasAvailable.toNat) (fuel : Nat) :
    let input := (jumpMemberSite site (UInt256.ofNat n) condition tail).state
    let next := {Assembly.chargedPrepare input 10 with
      pc := if condition != (⟨0⟩ : UInt256) then UInt256.ofNat n else input.pc + ⟨1⟩
      stack := tail}
    (UInt256.ofNat n).toNat = n ∧
      EVM.decode input.executionEnv.code (UInt256.ofNat n) = some (.JUMPDEST,none) ∧
      Assembly.driverSteps 1 (fuel+2) program.validJumps input = .ok next ∧
      EVM.X (fuel+2) program.validJumps input = EVM.X (fuel+1) program.validJumps next := by
  have facts := program.reference n reference
  have member := linked_reference_member program n reference
  have execution := jump_member_agreement program.validJumps site (UInt256.ofNat n) condition tail member room gas fuel
  dsimp only
  refine ⟨facts.1,?_,execution.1,execution.2⟩
  change EVM.decode site.state.executionEnv.code (UInt256.ofNat n) = _
  rw [aligned]
  exact facts.2.2

#print axioms linked_reference_member
#print axioms linked_reference_jumpi
end SolidityBridge.RoadmapV15.P10
