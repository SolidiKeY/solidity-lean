import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarPlan

/-! Universal frozen return and bare-revert transport for the selected scalar
family. Actual source success supplies the count and sufficient quotation;
these are derived, not extra admission or target-simulation premises. General
source selection and approved-domain coverage remain separate obligations. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarClaims
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

theorem source_revert {C : Contract} {Γ : Ctx} {R : RefTy}
 (hm : (Ty.ref R).mapFree=true) (reference : Idx Γ (.mem R)) (count : Val C Γ .uint)
 (destination : Idx Γ (.val .uint)) (f : Name) (depth : Nat) (caller : State C Γ)
 (failed : count.evalT caller=.error .revert) :
 (DisjointScalarReturn.call hm reference count destination f depth).run caller=.error .revert := by
 change TRun.call (DisjointScalarEntry.args hm reference count) (.val .uint (.user "result") (some destination))
   (ScalarRecursiveSource.body R hm depth).ext (ScalarRecursiveSource.body R hm depth).runR caller=_
 have args : (DisjointScalarEntry.args hm reference count).evalT caller=.error .revert := by
   cases alias : TEnv.get reference caller.env <;>
     simp only [DisjointScalarEntry.args,Args.evalT,MPath.mvalT,alias,failed,ok_bind,error_bind,pure_bind]
 unfold TRun.call
 simp only [args,error_bind]

theorem source_value {C : Contract} {Γ : Ctx} {R : RefTy}
 (hm : (Ty.ref R).mapFree=true) (reference : Idx Γ (.mem R)) (count : Val C Γ .uint)
 (destination : Idx Γ (.val .uint)) (f : Name) (depth : Nat) (caller : State C Γ)
 (ref : HRef caller.H R) (alias : TEnv.get reference caller.env=some ref)
 (value : PrimTy.uint.Denote) (evaluated : count.evalT caller=.ok value) :
 (DisjointScalarReturn.call hm reference count destination f depth).run caller=
 if value.word.val<depth then
   .ok ⟨caller.setLocal destination (countValue value.word.val value.word.isLt),List.prefix_refl _⟩
 else .error .exhausted := by
 have normalized : value=countValue value.word.val value.word.isLt := Subtype.ext (word_val value).symm
 have args : (DisjointScalarEntry.args hm reference count).evalT caller=
     .ok (countValue value.word.val value.word.isLt,(some ref,())) := by
   simp only [DisjointScalarEntry.args,Args.evalT,MPath.mvalT,alias,evaluated,ok_bind]
   rw [←normalized]
   rfl
 exact call_all_horizons hm f (DisjointScalarEntry.args hm reference count) destination depth caller
   value.word.val value.word.isLt ref args

theorem returns {C : Contract} {Γ : Ctx} {R : RefTy}
 {b c selectedFrame pointer bottom : Nat} {F : Frag Γ} {count : Val C Γ .uint}
 (emitted : ScalarEmitter.Emission b c selectedFrame pointer bottom F count)
 (below : bottom<pointer) (hm : (Ty.ref R).mapFree=true)
 (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint)) (f : Name) (depth : Nat) :
 InterfaceV1.ReturnClaim b F (DisjointScalarReturn.call hm reference count destination f depth)
   ((ScalarPlan.plan emitted reference destination).at depth) := by
 intro L frame caller base before start entry out source
 have checked := emitted.value.cert.correct entry.represented
 rcases checked with ⟨value,word,evaluated,encoded,executed⟩ | ⟨failed,executed⟩
 · obtain ⟨ref,alias,pointerWord⟩ := entry.represented.pointers reference
   have actual := source_value hm reference count destination f depth caller ref alias value evaluated
   by_cases enough : value.word.val<depth
   · rw [if_pos enough] at actual
     have same := Except.ok.inj (source.symm.trans actual)
     subst out
     have normalized : value=countValue value.word.val value.word.isLt := Subtype.ext (word_val value).symm
     rw [normalized] at evaluated
     exact ScalarPlan.returned_of_eval emitted below hm reference destination entry value.word.val value.word.isLt evaluated enough
   · rw [if_neg enough] at actual
     rw [actual] at source
     cases source
 · rw [source_revert hm reference count destination f depth caller failed] at source
   cases source

theorem bare_revert {C : Contract} {Γ : Ctx} {R : RefTy}
 {b c selectedFrame pointer bottom : Nat} {F : Frag Γ} {count : Val C Γ .uint}
 (emitted : ScalarEmitter.Emission b c selectedFrame pointer bottom F count)
 (below : bottom<pointer) (hm : (Ty.ref R).mapFree=true)
 (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint)) (f : Name) (depth : Nat) :
 InterfaceV1.BareRevertClaim b F (DisjointScalarReturn.call hm reference count destination f depth)
   ((ScalarPlan.plan emitted reference destination).at depth) := by
 intro L frame caller base before start entry source
 have checked := emitted.value.cert.correct entry.represented
 rcases checked with ⟨value,word,evaluated,encoded,executed⟩ | ⟨failed,executed⟩
 · obtain ⟨ref,alias,pointerWord⟩ := entry.represented.pointers reference
   have actual := source_value hm reference count destination f depth caller ref alias value evaluated
   split at actual <;> rw [actual] at source <;> cases source
 · have pointerBound : pointer<frame := entry.pointerBelow
   let actual : ScalarEmitter.Emission b c frame pointer bottom F count :=
     ⟨emitted.value,emitted.geometry.1,emitted.geometry.2.1,pointerBound,
      emitted.geometry.2.2.2.1,by omega,by omega⟩
   simpa only [List.append_nil] using
     ScalarEmitter.argument_revert actual hm caller reference destination failed base before entry.represented []

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarClaims
