import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingFailure

/-! Caller-local reconstruction over actual reached global and heap fields.
Old address identity and local words do not imply old heap contents or fragile
storage-alias liveness. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.CallerReframe
open Evm Evm.Memory

theorem reframe {C : Contract} {Γ Δ : Ctx} {L b child frame : Nat} {F : Frag Γ} {G : Frag Δ}
 (caller : State C Γ) (post : State C Δ) (e : caller.H <+: post.H)
 (base addresses : Nat → Fin W) (before after : Machine)
 (initial : StateRepr L b frame F caller base before)
 (reached : StateRepr L child frame G post addresses after)
 (extended : BaseExtends caller.H base addresses)
 (words : ∀ {t : LTy} (i : Idx Γ t), after.mem (cellOf b i)=before.mem (cellOf b i))
 (notFragile : ∀ {R : RefTy} (i : Idx Γ (.alias R)), F.get i≠.fragile) :
 StateRepr L b frame F (post.withEnv (TEnv.wk e Γ caller.env)) addresses after := by
 constructor
 · refine ⟨reached.core.store,?_,?_,reached.core.net,reached.core.netSelf,initial.core.bound,?_,
     reached.core.env,reached.core.funds,reached.core.oracle⟩
   · intro p i
     change ReprV p (Look.ofTEnv (TEnv.wk e Γ caller.env) i) (after.mem (cellOf b i))
     rw [Look.ofTEnv_wk,words i]
     exact initial.core.vals i
   · intro R i flag
     obtain ⟨r,slot,value,word,path⟩ := initial.core.aliases i flag
     refine ⟨r,slot,?_,(words i).trans word,path⟩
     exact (Look.ofTEnv_wk e caller.env i).trans value
   · intro R i flag
     exact (notFragile i flag).elim
 · exact reached.heap
 · intro R i
   obtain ⟨r,value,word⟩ := initial.pointers i
   refine ⟨r.wk e,?_,?_⟩
   · change TEnv.get i (TEnv.wk e Γ caller.env)=some (r.wk e)
     rw [TEnv.get_wk,value]
     rfl
   · exact (words i).trans (word.trans (congrArg Word.val (extended r).symm))
 · exact initial.locals
 · exact reached.structs
 · exact reached.separated
 · exact reached.refs

namespace Checks
open CountdownWitness RecursiveSource
abbrev Γ : Ctx := [.val .uint,.mem A,.mem A]
abbrev F := Frag.init Γ
def caller := callee.withEnv (Δ:=Γ) (countValue 2 (by decide),(some P.r0,(some P.r0,())))
abbrev before := ParentPrefixes.Checks.input
noncomputable abbrev last := AllocatingReturn.Checks.machine
noncomputable abbrev addresses := AllocatingReturn.Checks.addresses

theorem initial : StateRepr 1 1 16 F caller P.base before := by
 have h := ParentPrefixes.Checks.initial
 refine ⟨⟨h.core.store,?_,?_,h.core.net,h.core.netSelf,h.core.bound,?_,h.core.env,h.core.funds,h.core.oracle⟩,
   h.heap,?_,by decide,h.structs,h.separated,h.refs⟩
 · intro p i
   cases i with
   | here => exact h.core.vals .here
   | there i => cases i with | there i => cases i with | there i => cases i
 · intro R i flag
   cases i with | there i => cases i with | there i => cases i with | there i => cases i
 · intro R i flag
   cases i with | there i => cases i with | there i => cases i with | there i => cases i
 · intro R i
   cases i with
   | there i => cases i with
     | here => exact ⟨P.r0,rfl,rfl⟩
     | there i => cases i with
       | here => exact ⟨P.r0,rfl,rfl⟩
       | there i => cases i

def args : Args P.C Γ (Parameters A) := entryArgs A rfl (.there .here) .here

theorem arguments : args.evalT caller=.ok callee.env := by rfl

noncomputable def output : Solidity.Out P.C caller.H Γ :=
 exported (ps:=Parameters A) (CallRet.none : CallRet Γ [] Γ) Ext.refl caller callee.env AllocatingReturn.Checks.output

def call : Stmt P.C Γ Γ := InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step 3

theorem source : call.run caller=.ok output :=
 call_return args .none .refl (AllocatingActivation.body 3).runR caller callee.env arguments AllocatingReturn.Checks.output AllocatingReturn.Checks.specification.1

/-- Every sufficient native quotation returns this same actual caller output;
the target image does not depend on the quotation index. -/
theorem source_all (depth : Nat) (enough : 2<depth) :
 (InterfaceV1.recursiveSource "allocatingCountdown" args .none AllocatingActivation.step depth).run caller=.ok output := by
 have same : AllocatingResume.Checks.returned=AllocatingReturn.Checks.output :=
   Except.ok.inj (AllocatingResume.Checks.source_result.symm.trans AllocatingReturn.Checks.specification.1)
 have body := AllocatingResume.Checks.source_all depth enough
 rw [same] at body
 exact call_return args .none .refl (AllocatingActivation.body depth).runR caller callee.env arguments AllocatingReturn.Checks.output body

/-- Full old caller cells, including the additional older alias, follow from
actual low exterior and returned active reference/counter observations. -/
theorem caller_words : ∀ {t : LTy} (i : Idx Γ t), last.mem (cellOf 1 i)=before.mem (cellOf 1 i) := by
 intro t i
 rcases AllocatingReturn.Checks.facts with ⟨stack,cursor,oldAlias,reference,counter,rest⟩
 cases i with
 | here => exact counter
 | there i => cases i with
   | here => exact reference
   | there i => cases i with
     | here => exact oldAlias
     | there i => cases i

theorem represented : StateRepr 1 1 16 F output.st addresses last := by
 have h := reframe caller AllocatingReturn.Checks.output.st AllocatingReturn.Checks.output.ext P.base addresses before last
   initial AllocatingReturn.Checks.specification.2.2.1 AllocatingReturn.Checks.specification.2.2.2.2.1 caller_words
   (by intro R i;cases i with | there i => cases i with | there i => cases i with | there i => cases i)
 exact h

/-- Allocator transport follows the same successful heap, not whole-caller
memory equality or an assumed failed-state reconstruction. -/
theorem growth : GrowsAllocator 1 16 8 caller P.base before output.st addresses last := by
 intro cursor positive owned room
 exact AllocatingReturn.Checks.specification.2.2.2.2.2.1 cursor (by decide) owned room

theorem ownership : StructAllocatorRepr caller.heap P.base 16 (⟨22,by decide⟩ : Fin W) before :=
 ParentPrefixes.Checks.ownership

theorem capacity : AllocationInput 1 16 8 caller P.base before :=
 .inr ⟨by decide,⟨22,by decide⟩,ownership,by decide⟩

theorem returned_ownership : StructAllocatorRepr output.st.heap addresses 16 (⟨30,by decide⟩ : Fin W) last :=
 growth ⟨22,by decide⟩ (by decide) ownership (by decide)

theorem endpoint : call.run caller=.ok output ∧
 run (AllocatingReturn.image (C:=P.C) 2 CountdownWitness.F 8 7) before=.ok last 0 ∧
 StateRepr 1 1 16 F output.st addresses last ∧ last.stack=before.stack ∧
 BaseExtends caller.H P.base addresses ∧ GrowsAllocator 1 16 8 caller P.base before output.st addresses last :=
 ⟨source,AllocatingReturn.Checks.specification.2.1,represented,AllocatingReturn.Checks.specification.2.2.2.1,
   AllocatingReturn.Checks.specification.2.2.2.2.1,growth⟩

theorem observations :
 (last.stack,[last.mem 0,last.mem 1,last.mem 2,last.mem 3,last.mem 7,last.mem 8,last.mem 9,
 last.mem 10,last.mem 11,last.mem 12,last.mem 13,last.mem 16,last.mem 17,last.mem 18,last.mem 20,last.mem 21])=
 ([w[77]],[w[30],w[16],w[16],w[2],w[10],w[10],w[99],w[16],w[2],w[16],w[1],w[2],w[7],w[9],w[1],w[4]]) :=
 AllocatingReturn.Checks.observations

theorem wrong_alias : last.mem 1≠w[20] := by
 have word : last.mem 1=w[16] := caller_words (.there (.there .here))
 rw [word]
 decide

theorem wrong_scalar : last.mem 3≠w[0] := by
 have word : last.mem 3=w[2] := caller_words (.here : Idx Γ (.val .uint))
 rw [word]
 decide

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.CallerReframe
