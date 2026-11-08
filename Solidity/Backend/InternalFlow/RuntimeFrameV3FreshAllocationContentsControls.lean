import Solidity.Backend.InternalFlow.RuntimeFrameV3FreshAllocationContents
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDescentControls

/-! First newly allocated object observed after one or two actual turns.
The header and element negatives reject swapped length/payload observations. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.FreshAllocationContents.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent

theorem prefixes (steps : Nat) (small : steps≤1) :
 let σ := ScalarAllocatingDescent.Controls.σ
 let first := AllocatingScalarSource.allocated σ
 let fresh : HRef first.H (.array (.prim .bool)) := (σ.alloc (defaultArray .bool AllocatingScalarSource.size)).2
 ∃ (τ : State C (Frame A)) (e : first.H <+: τ.H) (after : Machine) (addresses : Nat → Fin W),
 loopIterN (run guardCompiled.code) (run (AllocatingScalarTurn.code 8)) (steps+1) ScalarAllocatingDescent.Controls.input=.inl after ∧
 StateRepr 1 2 16 F τ addresses after ∧
 τ.heap.get (fresh.wk e)=defaultArray .bool AllocatingScalarSource.size ∧
 addresses (fresh.wk e).id=wmod 22 ∧
 [after.mem 22,after.mem 23,after.mem 24,after.mem 25]=[w[3],w[0],w[0],w[0]] ∧
 after.mem 22≠w[0] ∧ after.mem 23≠w[3] := by
 simp only []
 have repr : StateRepr 1 2 16 F ScalarAllocatingDescent.Controls.σ CountdownWitness.P.base
     ScalarAllocatingDescent.Controls.input :=
   reserved_write AllocatingScalarTarget.represented 7 (by decide) (by decide) w[10]
 have owned : StructAllocatorRepr ScalarAllocatingDescent.Controls.σ.heap CountdownWitness.P.base 16
     (⟨22,by decide⟩ : Fin W) ScalarAllocatingDescent.Controls.input :=
   AllocatingScalarTarget.ownership.localWrite 7 (by decide) (by decide) w[10]
 have counter : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) ScalarAllocatingDescent.Controls.σ.env=
     countValue ((1-steps)+steps+1) (by have h : 2<W  := (by decide);omega) := by
   apply Subtype.ext
   change (2:Int)=(((1-steps)+steps+1:Nat):Int)
   omega
 obtain ⟨τ,e,after,addresses,actual,represented,kept,contents,address,observed⟩ :=
   reached steps (1-steps) ScalarAllocatingDescent.Controls.σ (by have h : 2<W  := (by decide);omega)
     CountdownWitness.P.r0 rfl counter rfl CountdownWitness.P.base ScalarAllocatingDescent.Controls.input repr
     (⟨22,by decide⟩ : Fin W) owned (by have h : 30<W  := (by decide);change 22+4*(steps+1)<W;omega)
     8 8 10 (by decide) (by decide) (by decide) (by decide) (by omega) (by decide)
     (by have h : 16<W  := (by decide);omega) rfl
 have header : after.mem 22=w[3] := congrArg (fun xs : List Word => xs[0]!) observed
 have firstElement : after.mem 23=w[0] := congrArg (fun xs : List Word => xs[1]!) observed
 refine ⟨τ,e,after,addresses,actual,represented,contents,address,observed,?_,?_⟩
 · rw [header]
   intro bad
   have impossible : (3:Nat)=0 := congrArg Fin.val (Word.val.inj bad)
   omega
 · rw [firstElement]
   intro bad
   have impossible : (0:Nat)=3 := congrArg Fin.val (Word.val.inj bad)
   omega

end Solidity.Backend.InternalFlow.RuntimeFrame.FreshAllocationContents.Controls

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.FreshAllocationContents.Controls.prefixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.FreshAllocationContents.Controls.prefixes
