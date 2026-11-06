import Solidity.Backend.InternalFlow.RuntimeFrameV3NativeDescentHeap
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDescentControls

/-! Populated complete heap identity with the genuine descent/native local
boundary retained: the source returns two while the active child holds zero. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.NativeDescentHeap.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent

theorem actual :
 ∃ (out : Solidity.Out C ScalarAllocatingDescent.Controls.σ.H (Frame A))
   (τ : State C (Frame A)) (after : Machine) (addresses : Nat → Fin W),
 (AllocatingScalarSource.body A (by rfl) 3).run ScalarAllocatingDescent.Controls.σ=.ok out ∧
 loopIterN (run guardCompiled.code) (run (AllocatingScalarTurn.code 8)) 2 ScalarAllocatingDescent.Controls.input=.inl after ∧
 StateRepr 1 2 16 F τ addresses after ∧ out.st.H=τ.H ∧ HEq out.st.heap τ.heap ∧
 TEnv.get (.here : Idx (Frame A) (.val .uint)) out.st.env=countValue 2 (by decide) ∧
 after.mem 4=w[0] ∧
 ¬ReprV .uint (TEnv.get (.here : Idx (Frame A) (.val .uint)) out.st.env) (after.mem 4) := by
 have repr : StateRepr 1 2 16 F ScalarAllocatingDescent.Controls.σ CountdownWitness.P.base ScalarAllocatingDescent.Controls.input :=
   reserved_write AllocatingScalarTarget.represented 7 (by decide) (by decide) w[10]
 have owned : StructAllocatorRepr ScalarAllocatingDescent.Controls.σ.heap CountdownWitness.P.base 16
     (⟨22,by decide⟩ : Fin W) ScalarAllocatingDescent.Controls.input :=
   AllocatingScalarTarget.ownership.localWrite 7 (by decide) (by decide) w[10]
 obtain ⟨out,τ,e,after,addresses,source,target,represented,typing,heap,inventory,kept,value⟩ :=
   heap_matches 3 2 ScalarAllocatingDescent.Controls.σ (by decide) CountdownWitness.P.r0
     rfl rfl rfl CountdownWitness.P.base ScalarAllocatingDescent.Controls.input repr
     (⟨22,by decide⟩ : Fin W) owned (by decide) 8 8 10
     (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl (by decide)
 obtain ⟨other,e',seen,base',setup,otherRun,otherRepr,env,size,otherKeeps,owner,extension,history,observed⟩ :=
   ScalarAllocatingDescent.Controls.available 2 (by decide)
 have same : after=seen := Sum.inl.inj (target.symm.trans otherRun)
 have zero : after.mem 4=w[0] := same ▸ congrArg (fun t : List Word × List Word => t.2[3]!) observed
 refine ⟨out,τ,after,addresses,source,target,represented,typing,heap,value,zero,?_⟩
 rw [value,zero]
 intro bad
 have words : (w[0] : Word)=w[2] := Restore.uint_unique bad (ReprV.uint_of rfl)
 have impossible : (0:Nat)=2 := congrArg Fin.val (Word.val.inj words)
 omega

end Solidity.Backend.InternalFlow.RuntimeFrame.NativeDescentHeap.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.NativeDescentHeap.Controls.actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.NativeDescentHeap.Controls.actual
