import Solidity.Evm.MemoryLoopHorizonObjectPrefix

/-! Explicit reached-turn construction-cost bounds supply strong finite room.
Every genuine successful prefix costs at most count*perTurn, and the next true
turn is included even when its body later reverts. The strong initial allocation
input for horizon*perTurn remains explicit; no physical capacity, termination
proof, resource-budget change or legacy cost equivalence is fabricated. -/
namespace Solidity.Evm.Memory.Construction
variable {C : Contract} {Γ Δ : Ctx}

theorem CountedLoopPrefix.cost_le_turns {c : Val C Γ .bool} {body : Prog C Γ Δ} {σ : State C Γ}
    {o : Solidity.Out C σ.H Γ} {cost count perTurn : Nat}
    (hp : CountedLoopPrefix c body σ o cost count)
    (bounded : ∀ (reached : Solidity.Out C σ.H Γ) (prior turns : Nat),
      CountedLoopPrefix c body σ reached prior turns → c.evalT reached.st=.ok true →
      allocationCostProg body reached.st ≤ perTurn) : cost ≤ count*perTurn := by
  induction hp with
  | start => exact Nat.zero_le _
  | next previous condition step ih =>
    have current := bounded _ _ _ previous condition
    simp only [Nat.succ_mul]
    omega

theorem finiteLoopRoom_of_turn_bound {b frame : Nat} {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {base : Nat → Fin W} {initial : Machine} {horizon perTurn : Nat}
    (bounded : ∀ (reached : Solidity.Out C σ.H Γ) (prior turns : Nat),
      CountedLoopPrefix c body σ reached prior turns → c.evalT reached.st=.ok true →
      allocationCostProg body reached.st ≤ perTurn)
    (demand : Objects.AllocationInput b frame (horizon*perTurn) σ base initial) :
    FiniteLoopRoom b frame c body σ base initial horizon := by
  intro o cost turns hp before condition
  have prior := hp.cost_le_turns bounded
  have current := bounded o cost turns hp condition
  have total : cost+allocationCostProg body o.st ≤ (turns+1)*perTurn := by
    rw [Nat.succ_mul]
    omega
  have product := Nat.mul_le_mul_right perTurn (show turns+1 ≤ horizon by omega)
  exact demand.of_le (Nat.le_trans total product)

end Solidity.Evm.Memory.Construction
