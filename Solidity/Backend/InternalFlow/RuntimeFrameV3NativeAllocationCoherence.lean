import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarReturn
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarOutcomes

/-! Sufficient native quotation indices have the same actual complete output,
including newly allocated heap contents. This is source execution coherence,
not equality with a separately represented target descent heap. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.NativeAllocationCoherence
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource AllocatingScalarSource

theorem stable {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (depth other : Nat) (σ : State C (Frame R)) (n : Nat) (fit : n<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue n fit)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref)
 (enough : n<depth) (otherEnough : n<other) :
 (AllocatingScalarSource.body R hm depth).run σ=(AllocatingScalarSource.body R hm other).run σ := by
 induction n generalizing depth other σ with
 | zero =>
   cases depth with
   | zero => omega
   | succ depth =>
     cases other with
     | zero => omega
     | succ other => rw [AllocatingScalarSource.source_zero hm σ depth counter,AllocatingScalarSource.source_zero hm σ other counter]
 | succ n ih =>
   cases depth with
   | zero => omega
   | succ depth =>
     cases other with
     | zero => omega
     | succ other =>
       let child := entered (allocated σ) n (by omega) (ref.wk (extension σ))
       have same := ih depth other child (by omega) (ref.wk (extension σ)) rfl rfl (by omega) (by omega)
       obtain ⟨out,actual,size,env,kept⟩ := AllocatingScalarSource.success hm depth child n (by omega) (ref.wk (extension σ)) rfl rfl (by omega)
       have value : TEnv.get (.here : Idx (Frame R) (.val .uint)) out.st.env=countValue n (by omega) := by
         rw [env,TEnv.get_set]
       have otherRun : (AllocatingScalarSource.body R hm other).run child=.ok out := same.symm.trans actual
       have first := AllocatingScalarSource.return_turn hm σ depth n fit ref counter alias out actual value
       have second := AllocatingScalarSource.return_turn hm σ other n fit ref counter alias out otherRun value
       exact first.trans second.symm

theorem common_output {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (depth other : Nat) (σ : State C (Frame R)) (n : Nat) (fit : n<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue n fit)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref)
 (enough : n<depth) (otherEnough : n<other) :
 ∃ out, (AllocatingScalarSource.body R hm depth).run σ=.ok out ∧ (AllocatingScalarSource.body R hm other).run σ=.ok out ∧
 TEnv.get (.here : Idx (Frame R) (.val .uint)) out.st.env=countValue n fit ∧
 out.st.H.length=σ.H.length+n ∧ Heap.Keeps out.ext σ.heap out.st.heap := by
 obtain ⟨out,actual,size,env,kept⟩ := AllocatingScalarSource.success hm depth σ n fit ref counter alias enough
 have same := stable hm depth other σ n fit ref counter alias enough otherEnough
 refine ⟨out,actual,same.symm.trans actual,?_,size,kept⟩
 rw [env,TEnv.get_set]

end Solidity.Backend.InternalFlow.RuntimeFrame.NativeAllocationCoherence

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.NativeAllocationCoherence.stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.NativeAllocationCoherence.stable

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.NativeAllocationCoherence.common_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.NativeAllocationCoherence.common_output
