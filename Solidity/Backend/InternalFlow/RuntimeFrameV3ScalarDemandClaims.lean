import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDemand

/-! Universal frozen scalar claims for actual-count demand. Source execution
keeps its original observation index. The entry bridges reuse checked capacity
proofs for the SAME target image; no source observation is substituted and no
simulation or approved-domain premise is inserted. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarDemand
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

theorem returns {C : Contract} {Γ : Ctx} {R : RefTy}
 {b c selectedFrame pointer bottom : Nat} {F : Frag Γ} {count : Val C Γ .uint}
 (emitted : ScalarEmitter.Emission b c selectedFrame pointer bottom F count)
 (below : bottom<pointer) (hm : (Ty.ref R).mapFree=true)
 (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint)) (f : Name) (depth : Nat) :
 InterfaceV1.ReturnClaim b F (DisjointScalarReturn.call hm reference count destination f depth)
   ((plan emitted reference destination).at depth) := by
 intro L frame caller base before start entry out source
 have checked := emitted.value.cert.correct entry.represented
 rcases checked with ⟨value,word,evaluated,encoded,executed⟩ | ⟨failed,executed⟩
 · obtain ⟨ref,alias,pointerWord⟩ := entry.represented.pointers reference
   have compatible := success_entry emitted reference destination entry value evaluated
   have actual := ScalarClaims.source_value hm reference count destination f depth caller ref alias value evaluated
   by_cases enough : value.word.val<depth
   · rw [if_pos enough] at actual
     have same := Except.ok.inj (source.symm.trans actual)
     subst out
     have normalized : value=countValue value.word.val value.word.isLt := Subtype.ext (word_val value).symm
     rw [normalized] at evaluated
     exact ScalarPlan.returned_of_eval emitted below hm reference destination compatible value.word.val value.word.isLt evaluated (Nat.lt_succ_self _)
   · rw [if_neg enough] at actual
     rw [actual] at source
     cases source
 · rw [ScalarClaims.source_revert hm reference count destination f depth caller failed] at source
   cases source

theorem bare_revert {C : Contract} {Γ : Ctx} {R : RefTy}
 {b c selectedFrame pointer bottom : Nat} {F : Frag Γ} {count : Val C Γ .uint}
 (emitted : ScalarEmitter.Emission b c selectedFrame pointer bottom F count)
 (below : bottom<pointer) (hm : (Ty.ref R).mapFree=true)
 (reference : Idx Γ (.mem R)) (destination : Idx Γ (.val .uint)) (f : Name) (depth : Nat) :
 InterfaceV1.BareRevertClaim b F (DisjointScalarReturn.call hm reference count destination f depth)
   ((plan emitted reference destination).at depth) := by
 intro L frame caller base before start entry source
 have checked := emitted.value.cert.correct entry.represented
 rcases checked with ⟨value,word,evaluated,encoded,executed⟩ | ⟨failed,executed⟩
 · obtain ⟨ref,alias,pointerWord⟩ := entry.represented.pointers reference
   have actual := ScalarClaims.source_value hm reference count destination f depth caller ref alias value evaluated
   split at actual <;> rw [actual] at source <;> cases source
 · have compatible := failure_entry emitted reference destination entry .revert failed
   exact ScalarClaims.bare_revert emitted below hm reference destination f 0
     L frame caller base before start compatible
     (ScalarClaims.source_revert hm reference count destination f 0 caller failed)

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarDemand
