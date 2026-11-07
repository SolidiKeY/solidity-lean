import Solidity.Evm.MemoryLoopHorizonPrefixCapacity
import Solidity.Evm.MemoryLoopHorizonTurnBoundControls

/-! Actual empty-array allocation constructs a reached one-turn prefix. Its
finite-room certificate therefore supplies the incurred one-cell owner capacity
input. The test does not assume a reached prefix or fabricate an allocator;
the loop owner's representation remains StructAllocatorRepr. -/
namespace Solidity.Evm.Memory.HorizonPrefixCapacityControls

theorem body_run {C : Contract} {Γ : Ctx} (state : State C Γ) :
    HorizonTurnBoundControls.body.run state=
      .ok ⟨state.allocPush (defaultArray .uint ⟨0,W_pos⟩),List.prefix_append _ _⟩ := by
  have allocated : (Stmt.declMem (.array (.prim .uint)) (.user "fresh")
      (some (.newArr (.lit 0 rfl) rfl)) rfl rfl).run state=
      .ok ⟨state.allocPush (defaultArray .uint ⟨0,W_pos⟩),List.prefix_append _ _⟩ :=
    newArray_decl state .uint (.lit 0 rfl) ⟨0,W_pos⟩ rfl
  unfold HorizonTurnBoundControls.body
  rw [Prog.run_cons_ok allocated]
  rfl

theorem allocating_input {C : Contract} {Γ : Ctx} {b frame : Nat}
    {σ : State C Γ} {base : Nat → Fin W} {initial : Machine}
    (room : FiniteLoopRoom b frame (.simple (.bool true)) HorizonTurnBoundControls.body σ base initial 1) :
    AllocationInput b frame 1 σ base initial := by
  have hp := CountedLoopPrefix.next (c:= (.simple (.bool true))) .start
    (show (Val.simple (.bool true) : Val C Γ .bool).evalT σ=.ok true from rfl) (body_run σ)
  exact room.prefix_input hp (by decide)

end Solidity.Evm.Memory.HorizonPrefixCapacityControls
