import Solidity.Backend.InternalFlow.RuntimeFrameV3CallerReframe

/-! Caller restoration including fragile storage aliases when the ACTUAL
reached source storage is unchanged. Old pointer identity does not imply old
heap contents; no Heap.Keeps or storage liveness assumption is introduced.
The old non-fragile reframe theorem is unchanged. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame
open Evm Evm.Memory

theorem reframe {C : Contract} {Γ Δ : Ctx} {L b child frame : Nat} {F : Frag Γ} {G : Frag Δ}
 (caller : State C Γ) (post : State C Δ) (e : caller.H <+: post.H)
 (base addresses : Nat → Fin W) (before after : Machine)
 (initial : StateRepr L b frame F caller base before)
 (reached : StateRepr L child frame G post addresses after)
 (extended : BaseExtends caller.H base addresses)
 (words : ∀ {t : LTy} (i : Idx Γ t),after.mem (cellOf b i)=before.mem (cellOf b i))
 (storage : post.storage=caller.storage) :
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
     exact ⟨r,slot,(Look.ofTEnv_wk e caller.env i).trans value,(words i).trans word,path⟩
   · intro R i flag
     obtain ⟨r,slot,value,word,path,live⟩ := initial.core.fragile i flag
     refine ⟨r,slot,(Look.ofTEnv_wk e caller.env i).trans value,(words i).trans word,path,?_⟩
     change ∃ v,post.storage.findLive r=some v
     simpa only [storage] using live
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

end Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.reframe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.CallerStorageFrame.reframe
