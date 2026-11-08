import Solidity.Backend.InternalFlow.RuntimeFrameV3NativeReturnRepresentation
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDescentControls
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarReturn

/-! Populated actual native-output representation and a complete ordered
20-word target observation vector. Old fixtures and vectors are unchanged. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.NativeReturnRepresentation.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent

theorem complete :
 ∃ (out : Solidity.Out C ScalarAllocatingDescent.Controls.σ.H (Frame A)) (last : Machine) (addresses : Nat → Fin W),
 (AllocatingScalarSource.body A (by rfl) 3).run ScalarAllocatingDescent.Controls.σ=.ok out ∧
 run (ScalarPairedTransport.image guardCompiled 8 7) ScalarAllocatingDescent.Controls.input=.ok last 0 ∧
 StateRepr 1 2 16 F out.st addresses last ∧
 (last.stack,[last.mem 0,last.mem 2,last.mem 3,last.mem 4,last.mem 7,last.mem 8,last.mem 9,
   last.mem 16,last.mem 17,last.mem 18,last.mem 20,last.mem 21,
   last.mem 22,last.mem 23,last.mem 24,last.mem 25,last.mem 26,last.mem 27,last.mem 28,last.mem 29])=
 ([w[77]],[w[30],w[16],w[2],w[2],w[10],w[10],w[99],w[2],w[7],w[9],w[1],w[4],w[3],w[0],w[0],w[0],w[3],w[0],w[0],w[0]]) ∧
 last.mem 0≠w[34] ∧ last.mem 2≠w[20] ∧
 run (ScalarPairedTransport.image guardCompiled 8 7) ScalarAllocatingDescent.Controls.input≠.revert := by
 have repr : StateRepr 1 2 16 F ScalarAllocatingDescent.Controls.σ CountdownWitness.P.base ScalarAllocatingDescent.Controls.input :=
   reserved_write AllocatingScalarTarget.represented 7 (by decide) (by decide) w[10]
 have owned : StructAllocatorRepr ScalarAllocatingDescent.Controls.σ.heap CountdownWitness.P.base 16
     (⟨22,by decide⟩ : Fin W) ScalarAllocatingDescent.Controls.input :=
   AllocatingScalarTarget.ownership.localWrite 7 (by decide) (by decide) w[10]
 obtain ⟨out,last,addresses,source,target,represented,kept,extended,growth,owner,stack,pointer,reference,inventory,words⟩ :=
   endpoint 3 2 ScalarAllocatingDescent.Controls.σ (by decide) CountdownWitness.P.r0 rfl rfl rfl
     CountdownWitness.P.base ScalarAllocatingDescent.Controls.input repr (⟨22,by decide⟩ : Fin W) owned (by decide)
     8 8 7 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl
     (by decide) (by decide) (by decide) rfl (by decide)
 have native := AllocatingScalarSource.two_return (C:=C) (R:=A) (by rfl) ScalarAllocatingDescent.Controls.σ 0 CountdownWitness.P.r0 rfl rfl
 have exactOutput := Except.ok.inj (source.symm.trans native)
 have resultValue : TEnv.get (.here : Idx (Frame A) (.val .uint)) out.st.env=countValue 2 (by decide) := by rw [exactOutput];rfl
 have counterValue : TEnv.get (.there .here : Idx (Frame A) (.val .uint)) out.st.env=countValue 2 (by decide) := by rw [exactOutput];rfl
 have resultRepr := represented.core.vals (.here : Idx (Frame A) (.val .uint))
 change ReprV .uint (TEnv.get (.here : Idx (Frame A) (.val .uint)) out.st.env) (last.mem 4) at resultRepr
 rw [resultValue] at resultRepr
 have resultWord : last.mem 4=w[2] := Restore.uint_unique resultRepr (ReprV.uint_of rfl)
 have counterRepr := represented.core.vals (.there .here : Idx (Frame A) (.val .uint))
 change ReprV .uint (TEnv.get (.there .here : Idx (Frame A) (.val .uint)) out.st.env) (last.mem 3) at counterRepr
 rw [counterValue] at counterRepr
 have counterWord : last.mem 3=w[2] := Restore.uint_unique counterRepr (ReprV.uint_of rfl)
 have cursor : last.mem 0=w[30] := owner.arrays.free.cell
 have bottom : last.mem 7=w[10] := words 7 (by decide) (by decide) (by decide) (.inl (by decide))
 have sentinel : last.mem 9=w[99] := words 9 (by decide) (by decide) (by decide) (.inl (by decide))
 have first := AllocatingPrefixes.old_array out.ext kept extended represented.heap CountdownWitness.P.r0
 have other := AllocatingPrefixes.old_array out.ext kept extended represented.heap CompileExamples.r1
 have firstLength := first.length
 have otherLength := other.length
 rw [show ScalarAllocatingDescent.Controls.σ.heap.len CountdownWitness.P.r0 .dyn=2 from HeapDomain.Checks.length_zero] at firstLength
 rw [show ScalarAllocatingDescent.Controls.σ.heap.len CompileExamples.r1 .dyn=1 from HeapDomain.Checks.length_one] at otherLength
 change last.mem 16=w[2] at firstLength
 change last.mem 20=w[1] at otherLength
 have word7 : last.mem 17=w[7] := Restore.uint_unique (first.elements 0 (CountdownWitness.P.uint 7 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
 have word9 : last.mem 18=w[9] := Restore.uint_unique (first.elements 1 (CountdownWitness.P.uint 9 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
 have word4 : last.mem 21=w[4] := Restore.uint_unique (other.elements 0 (CountdownWitness.P.uint 4 (by decide)) (by with_unfolding_all rfl)) (ReprV.uint_of rfl)
 have fresh0 := ScalarAllocationInventory.observe inventory represented.heap 0 (by decide)
 have fresh1 := ScalarAllocationInventory.observe inventory represented.heap 1 (by decide)
 have f0 : last.mem 22=w[3] := congrArg (fun xs : List Word => xs[0]!) fresh0
 have f1 : last.mem 23=w[0] := congrArg (fun xs : List Word => xs[1]!) fresh0
 have f2 : last.mem 24=w[0] := congrArg (fun xs : List Word => xs[2]!) fresh0
 have f3 : last.mem 25=w[0] := congrArg (fun xs : List Word => xs[3]!) fresh0
 have g0 : last.mem 26=w[3] := congrArg (fun xs : List Word => xs[0]!) fresh1
 have g1 : last.mem 27=w[0] := congrArg (fun xs : List Word => xs[1]!) fresh1
 have g2 : last.mem 28=w[0] := congrArg (fun xs : List Word => xs[2]!) fresh1
 have g3 : last.mem 29=w[0] := congrArg (fun xs : List Word => xs[3]!) fresh1
 refine ⟨out,last,addresses,source,target,represented,?_,?_,?_,?_⟩
 · rw [stack,cursor,reference,counterWord,resultWord,bottom,pointer,sentinel,firstLength,word7,word9,otherLength,word4,f0,f1,f2,f3,g0,g1,g2,g3]
   rfl
 · rw [cursor];decide
 · rw [reference];decide
 · rw [target];intro bad;cases bad

end Solidity.Backend.InternalFlow.RuntimeFrame.NativeReturnRepresentation.Controls
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.NativeReturnRepresentation.Controls.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.NativeReturnRepresentation.Controls.complete
