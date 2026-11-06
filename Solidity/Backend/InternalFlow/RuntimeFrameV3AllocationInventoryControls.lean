import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDescentControls

/-! Populated zero/one/two actual prefixes with the complete new-object inventory.
Every object is observed from the same reached state and address map. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocationInventory.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent

theorem prefixes (steps : Nat) (small : steps≤2) :
 ∃ (τ : State C (Frame A)) (e : ScalarAllocatingDescent.Controls.σ.H <+: τ.H) (after : Machine) (addresses : Nat → Fin W),
 loopIterN (run guardCompiled.code) (run (AllocatingScalarTurn.code 8)) steps ScalarAllocatingDescent.Controls.input=.inl after ∧
 StateRepr 1 2 16 F τ addresses after ∧
 Heap.Keeps e ScalarAllocatingDescent.Controls.σ.heap τ.heap ∧
 τ.H.length=2+steps ∧ Holds 2 steps 22 τ addresses ∧
 (∀ i j,i<steps → j<steps → i≠j → addresses (2+i)≠addresses (2+j)) ∧
 (∀ j,j<steps → [after.mem (22+4*j),after.mem (23+4*j),after.mem (24+4*j),after.mem (25+4*j)]=[w[3],w[0],w[0],w[0]]) := by
 have repr : StateRepr 1 2 16 F ScalarAllocatingDescent.Controls.σ CountdownWitness.P.base
     ScalarAllocatingDescent.Controls.input :=
   reserved_write AllocatingScalarTarget.represented 7 (by decide) (by decide) w[10]
 have owned : StructAllocatorRepr ScalarAllocatingDescent.Controls.σ.heap CountdownWitness.P.base 16
     (⟨22,by decide⟩ : Fin W) ScalarAllocatingDescent.Controls.input :=
   AllocatingScalarTarget.ownership.localWrite 7 (by decide) (by decide) w[10]
 have counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) ScalarAllocatingDescent.Controls.σ.env=
     countValue ((2-steps)+steps) (by have h : 2<W := (by decide);omega) := by
   apply Subtype.ext
   change (2:Int)=(((2-steps)+steps:Nat):Int)
   omega
 obtain ⟨τ,e,after,addresses,actual,represented,env,size,kept,owner,extension,growth,stack,position,history,words,inventory⟩ :=
   running_with_inventory steps (2-steps) ScalarAllocatingDescent.Controls.σ (by have h : 2<W := (by decide);omega)
     CountdownWitness.P.r0 rfl counter rfl CountdownWitness.P.base ScalarAllocatingDescent.Controls.input repr
     (⟨22,by decide⟩ : Fin W) owned (by have h : 30<W := (by decide);change 22+4*steps<W;omega)
     8 8 10 (by decide) (by decide) (by decide) (by decide) (by omega) (by decide)
     (by have h : 16<W := (by decide);omega) rfl
 refine ⟨τ,e,after,addresses,actual,represented,kept,size,inventory,(fun i j hi hj different => distinct inventory i j hi hj different),?_⟩
 intro j small
 have physical := observe inventory represented.heap j small
 simpa only [show 22+4*j+1=23+4*j from by omega,show 22+4*j+2=24+4*j from by omega,
   show 22+4*j+3=25+4*j from by omega] using physical

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocationInventory.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocationInventory.Controls.prefixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.ScalarAllocationInventory.Controls.prefixes
