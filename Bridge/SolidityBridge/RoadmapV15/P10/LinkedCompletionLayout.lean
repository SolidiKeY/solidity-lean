import SolidityBridge.RoadmapV15.P10.LinkedJumpFixtures
import SolidityBridge.RoadmapV15.P10.UnsignedCleanupLayout

/-! Actual represented entry and observations for the linked exit suffix.
These are native State records, not a new transition relation. The entry code
is fixed, but caller accounts/memory/environment, gas and tail are arbitrary. -/
namespace SolidityBridge.RoadmapV15.P10
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

def linkedCompletionSite (seed : EVM.State) : Site .JUMPI :=
  ⟨seed,LinkedJumpFixtures.before,LinkedJumpFixtures.after,by decide⟩
def linkedCompletionInput (seed : EVM.State) (tail : List UInt256) : EVM.State :=
  (jumpMemberSite (linkedCompletionSite seed) (.ofNat 72) (.ofNat 1) tail).state
def linkedCompletionJump (seed : EVM.State) (tail : List UInt256) : EVM.State :=
  {Assembly.chargedPrepare (linkedCompletionInput seed tail) 10 with pc := .ofNat 72,stack := tail}
def linkedCompletionStop (seed : EVM.State) (tail : List UInt256) : EVM.State :=
  (Assembly.chargedPrepare (linkedCompletionJump seed tail) 1).incrPC
def linkedCompletionOutput (seed : EVM.State) (tail : List UInt256) : EVM.State :=
  Assembly.stopAfter (linkedCompletionStop seed tail) 0

/-- Actual destination/STOP gate, including capacity and both permissions. -/
theorem completion_terminal_gate (valid : Array UInt256) (s : EVM.State)
    (op : Operation .EVM) (cost : Nat)
    (allowed : (op = .JUMPDEST ∧ cost = 1) ∨ (op = .STOP ∧ cost = 0))
    (gas : cost ≤ s.gasAvailable.toNat) (room : s.stack.length ≤ 1024) :
    Assembly.driverGate valid s op = .ok (s,cost) := by
  have expansion : EVM.memoryExpansionCost s op = 0 := by
    rcases allowed with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      simp only [EVM.memoryExpansionCost,EVM.memoryExpansionCost.μᵢ',Nat.sub_self]
  have charge : s.gasAvailable-UInt256.ofNat 0 = s.gasAvailable := by
    change UInt256.mk (s.gasAvailable.val-0) = s.gasAvailable
    rw [sub_zero]
  have price : EVM.C' s op = cost := by rcases allowed with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rfl
  have delta : EVM.δ op = some 0 := by rcases allowed with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rfl
  have alpha : EVM.α op = some 0 := by rcases allowed with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rfl
  simp only [Assembly.driverGate]
  rw [expansion,charge]
  simp only [price,delta,alpha,Option.getD_some,Nat.sub_zero,Nat.add_zero,
    if_neg (Nat.not_lt_zero _),if_neg (Nat.not_lt_of_ge gas),if_neg (Nat.not_lt_of_ge room)]
  rcases allowed with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> cases s.executionEnv.perm <;> rfl

#print axioms completion_terminal_gate
end SolidityBridge.RoadmapV15.P10
