import Solidity.Evm.MemoryLoopHorizonTurnBound

/-! A real source empty-array declaration allocates one cell per reached turn.
For arbitrary horizons its finite-room certificate consumes the owner's actual
initial AllocationInput for that many cells. This does not fabricate a physical
allocator witness, a compiler certificate, or unconditional capacity. -/
namespace Solidity.Evm.Memory.HorizonTurnBoundControls

def body {C : Contract} {Γ : Ctx} : Prog C Γ (.mem (.array (.prim .uint))::Γ) :=
  .cons (.declMem (.array (.prim .uint)) (.user "fresh")
    (some (.newArr (.lit 0 rfl) rfl)) rfl rfl) .nil

theorem body_cost {C : Contract} {Γ : Ctx} (state : State C Γ) : allocationCostProg body state=1 := by
  rfl

theorem allocating_room {C : Contract} {Γ : Ctx} {b frame : Nat}
    {σ : State C Γ} {base : Nat → Fin W} {initial : Machine} (horizon : Nat)
    (demand : AllocationInput b frame horizon σ base initial) :
    FiniteLoopRoom b frame (.simple (.bool true)) body σ base initial horizon := by
  apply finiteLoopRoom_of_turn_bound (perTurn:=1)
  · intro reached prior turns hp condition
    exact Nat.le_of_eq (body_cost reached.st)
  · simpa only [Nat.mul_one] using demand

end Solidity.Evm.Memory.HorizonTurnBoundControls
