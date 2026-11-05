import Solidity.Evm.MemoryLoopFiniteHorizon

/-! A proved per-turn demand bound supplies the existing finite-room contract
from the owner's initial AllocationInput. The bound quantifies only genuine
counted true-condition prefixes; the next body cost is included even if that
body later reverts. This changes no physical capacity predicate or execution
resource limit and supplies no bound without its explicit proof/input. -/
namespace Solidity.Evm.Memory
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
    (demand : AllocationInput b frame (horizon*perTurn) σ base initial) :
    FiniteLoopRoom b frame c body σ base initial horizon := by
  intro o cost turns hp before condition
  have prior := hp.cost_le_turns bounded
  have current := bounded o cost turns hp condition
  have total : cost+allocationCostProg body o.st ≤ (turns+1)*perTurn := by
    rw [Nat.succ_mul]
    omega
  have product := Nat.mul_le_mul_right perTurn (show turns+1 ≤ horizon by omega)
  exact demand.of_le (Nat.le_trans total product)

end Solidity.Evm.Memory
