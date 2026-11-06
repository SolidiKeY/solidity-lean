import Solidity.Backend.InternalFlow.RuntimeFrameV3NativeScalarAgreement
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDescentControls

/-! Populated native/target scalar agreement and genuine insufficient native
quotation. A source exhaustion has no output State and is not target divergence. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.NativeScalarAgreement.Controls
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource ScalarAllocatingDescent

theorem coupled : ∃ (out : Solidity.Out C ScalarAllocatingDescent.Controls.σ.H (Frame A)) (last : Machine),
 (AllocatingScalarSource.body A (by rfl) 3).run ScalarAllocatingDescent.Controls.σ=.ok out ∧
 run (ScalarPairedTransport.image guardCompiled 8 7) ScalarAllocatingDescent.Controls.input=.ok last 0 ∧
 TEnv.get (.here : Idx (Frame A) (.val .uint)) out.st.env=countValue 2 (by decide) ∧
 last.mem 4=w[2] ∧
 (AllocatingScalarSource.body A (by rfl) 2).run ScalarAllocatingDescent.Controls.σ=.error .exhausted ∧
 run (ScalarPairedTransport.image guardCompiled 8 7) ScalarAllocatingDescent.Controls.input≠.revert := by
 have repr : StateRepr 1 2 16 F ScalarAllocatingDescent.Controls.σ CountdownWitness.P.base
     ScalarAllocatingDescent.Controls.input :=
   reserved_write AllocatingScalarTarget.represented 7 (by decide) (by decide) w[10]
 have owned : StructAllocatorRepr ScalarAllocatingDescent.Controls.σ.heap CountdownWitness.P.base 16
     (⟨22,by decide⟩ : Fin W) ScalarAllocatingDescent.Controls.input :=
   AllocatingScalarTarget.ownership.localWrite 7 (by decide) (by decide) w[10]
 obtain ⟨out,last,source,target,value,observed,size,stack,pointer,reference⟩ :=
   agreement guardCompiled producer 3 2 ScalarAllocatingDescent.Controls.σ (by decide) CountdownWitness.P.r0
     rfl rfl rfl CountdownWitness.P.base ScalarAllocatingDescent.Controls.input repr
     (⟨22,by decide⟩ : Fin W) owned (by decide) 8 8 7 10
     (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
     (by decide) rfl (by decide) (by decide) (by decide) rfl (by decide)
 rw [value] at observed
 have word : last.mem 4=w[2] := Restore.uint_unique observed (ReprV.uint_of rfl)
 have short := AllocatingScalarSource.exhaustion (C:=C) (R:=A) (by rfl) 2 ScalarAllocatingDescent.Controls.σ
   2 (by decide) CountdownWitness.P.r0 rfl rfl (by decide)
 refine ⟨out,last,source,target,value,word,short,?_⟩
 rw [target]
 intro impossible
 cases impossible

end Solidity.Backend.InternalFlow.RuntimeFrame.NativeScalarAgreement.Controls

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.NativeScalarAgreement.Controls.coupled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.NativeScalarAgreement.Controls.coupled
