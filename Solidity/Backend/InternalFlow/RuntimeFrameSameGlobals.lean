import Solidity.Backend.InternalFlow.RuntimeFrameV3CallerReframe

/-! Restore an entire caller context over a reached state with the SAME source
globals and heap, at a different frame base. Fragile slots retain their actual
original liveness because the source store is identical, not because an
arbitrary mutating callee or heap extension is presumed to preserve them. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.SameGlobals
open Evm Evm.Memory

theorem reframe {C : Contract} {Γ Δ : Ctx} {L b child frame : Nat} {F : Frag Γ} {G : Frag Δ}
 (σ : State C Γ) (locals : TEnv C σ.H Δ)
 (base addresses : Nat → Fin W) (before after : Machine)
 (initial : StateRepr L b frame F σ base before)
 (reached : StateRepr L child frame G (σ.withEnv locals) addresses after)
 (extended : BaseExtends σ.H base addresses)
 (words : ∀ {t : LTy} (i : Idx Γ t),after.mem (cellOf b i)=before.mem (cellOf b i)) :
 StateRepr L b frame F σ addresses after := by
 constructor
 · refine ⟨reached.core.store,?_,?_,reached.core.net,reached.core.netSelf,initial.core.bound,?_,
     reached.core.env,reached.core.funds,reached.core.oracle⟩
   · intro p index
     change ReprV p (Look.ofTEnv σ.env index) (after.mem (cellOf b index))
     rw [words index]
     exact initial.core.vals index
   · intro R index flag
     obtain ⟨reference,slot,value,word,path⟩ := initial.core.aliases index flag
     exact ⟨reference,slot,value,(words index).trans word,path⟩
   · intro R index flag
     obtain ⟨reference,slot,value,word,path,live⟩ := initial.core.fragile index flag
     exact ⟨reference,slot,value,(words index).trans word,path,live⟩
 · exact reached.heap
 · intro R index
   obtain ⟨reference,value,word⟩ := initial.pointers index
   exact ⟨reference,value,(words index).trans (word.trans (congrArg Word.val (extended reference).symm))⟩
 · exact initial.locals
 · exact reached.structs
 · exact reached.separated
 · exact reached.refs

end Solidity.Backend.InternalFlow.RuntimeFrame.SameGlobals
