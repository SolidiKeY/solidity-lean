import Solidity.Backend.InternalFlow.RuntimeFrameV3StateShell
import Solidity.Backend.InternalFlow.RuntimeFrameV3TypedHeapExtensionality
import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingScalarReturn

/-! Exact new-object contents of the actual native allocating recursive run.
The quotation index is not an admission cutoff; every sufficient index is
covered. No target simulation or desired heap equality is assumed. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.NativeHeapProfile
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource TypedHeapExtensionality

theorem success_with_context {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (depth : Nat) (σ : State C (Frame R)) (n : Nat) (fit : n<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue n fit)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref)
 (enough : n<depth) :
 ∃ out, (AllocatingScalarSource.body R hm depth).run σ=.ok out ∧
 TEnv.get (.here : Idx (Frame R) (.val .uint)) out.st.env=countValue n fit ∧
 out.st.H.length=σ.H.length+n ∧ Heap.Keeps out.ext σ.heap out.st.heap ∧
 Defaults σ.H.length out.st.heap ∧ StateShell.Same σ out.st := by
 induction n generalizing depth σ with
 | zero =>
   cases depth with
   | zero => omega
   | succ depth =>
     refine ⟨⟨finished σ 0 fit,List.prefix_refl _⟩,AllocatingScalarSource.source_zero hm σ depth counter,rfl,?_,Heap.Keeps.refl σ.heap,?_,?_⟩
     · change σ.H.length=σ.H.length+0;omega
     · intro S r fresh
       have bound : r.id<σ.H.length := (List.getElem?_eq_some_iff.mp r.get?).1
       omega
     · exact StateShell.refl σ
 | succ n ih =>
   cases depth with
   | zero => omega
   | succ depth =>
     let parent := AllocatingScalarSource.allocated σ
     let firstExt := AllocatingScalarSource.extension σ
     let child := entered parent n (by omega) (ref.wk firstExt)
     obtain ⟨out,childRun,value,size,kept,defaults,context⟩ := ih depth child (by omega) (ref.wk firstExt) rfl rfl (by omega)
     let arguments : TEnv C parent.H (Parameters R) := (countValue n (by omega),(some (ref.wk firstExt),()))
     let returned := exported (result R) Ext.refl parent arguments out
     let finalOut : Solidity.Out C σ.H (Frame R) :=
       ⟨finished returned.st (n+1) fit,firstExt.trans returned.ext⟩
     have actual : (AllocatingScalarSource.body R hm (depth+1)).run σ=.ok finalOut :=
       AllocatingScalarSource.return_turn hm σ depth n fit ref counter alias out childRun value
     have initialKept : Heap.Keeps firstExt σ.heap child.heap := Heap.keeps_alloc σ.heap (defaultArray .bool AllocatingScalarSource.size)
     have tail : Defaults (σ.H.length+1) out.st.heap := by
       intro S r fresh
       apply defaults r
       change (σ.H++([.array (.prim .bool)] : HTy)).length≤r.id
       simpa only [List.length_append,List.length_singleton] using fresh
     have profile : Defaults σ.H.length out.st.heap := prepend_defaults σ.heap out.ext out.st.heap kept tail
     refine ⟨finalOut,actual,rfl,?_,initialKept.trans kept,profile,?_⟩
     · change out.st.H.length=(σ.H++([.array (.prim .bool)] : HTy)).length+n at size
       change out.st.H.length=σ.H.length+(n+1)
       simp only [List.length_append,List.length_singleton] at size
       omega
     · exact StateShell.trans (show StateShell.Same σ child from ⟨rfl,rfl,rfl,rfl⟩) context

theorem success {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (depth : Nat) (σ : State C (Frame R)) (n : Nat) (fit : n<W) (ref : HRef σ.H R)
 (counter : TEnv.get (.there .here : Idx (Frame R) (.val .uint)) σ.env=countValue n fit)
 (alias : TEnv.get (.there (.there .here) : Idx (Frame R) (.mem R)) σ.env=some ref)
 (enough : n<depth) :
 ∃ out, (AllocatingScalarSource.body R hm depth).run σ=.ok out ∧
 TEnv.get (.here : Idx (Frame R) (.val .uint)) out.st.env=countValue n fit ∧
 out.st.H.length=σ.H.length+n ∧ Heap.Keeps out.ext σ.heap out.st.heap ∧
 Defaults σ.H.length out.st.heap := by
 obtain ⟨out,actual,value,size,kept,defaults,context⟩ := success_with_context hm depth σ n fit ref counter alias enough
 exact ⟨out,actual,value,size,kept,defaults⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.NativeHeapProfile
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.NativeHeapProfile.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.NativeHeapProfile.success

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.NativeHeapProfile.success_with_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.NativeHeapProfile.success_with_context
