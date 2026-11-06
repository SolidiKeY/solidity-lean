import Solidity.Backend.InternalFlow.RuntimeFrameSameGlobals
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarReturn

/-! Real memory/scalar argument execution into a disjoint private frame.
The published value certificate supplies the scalar evaluation, while actual
caller pointers supply reference identity. All old caller locals, including
fragile slots in the unchanged source store, remain represented. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.DisjointScalarEntry
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

def args {C : Contract} {Γ : Ctx} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (reference : Idx Γ (.mem R)) (count : Val C Γ .uint) : Args C Γ (Parameters R) :=
 .snoc (.snocMemory .nil R (.user "alias") (.var reference hm)) .uint (.user "count") count

def code {C : Contract} {Γ : Ctx} {R : RefTy} {F : Frag Γ} {count : Val C Γ .uint}
 (b c : Nat) (reference : Idx Γ (.mem R)) (value : CompiledVal b F count) : List Instr :=
 [.mload (cellOf b reference),.mstore c] ++
 (value.code ++ [.mstore (c+1),.push w[0],.mstore (c+2)])

theorem entered {C : Contract} {Γ : Ctx} {R : RefTy} {L b c frame : Nat} {F : Frag Γ}
 (hm : (Ty.ref R).mapFree=true) (σ : State C Γ) (reference : Idx Γ (.mem R))
 (count : Val C Γ .uint) (value : CompiledVal b F count) (n : Nat) (bound : n<W)
 (evaluated : count.evalT σ=.ok (countValue n bound))
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (disjoint : b+Γ.length≤c) (space : c+3≤frame) :
 ∃ (ref : HRef σ.H R) (after : Machine),
 (args hm reference count).evalT σ=.ok (countValue n bound,(some ref,())) ∧
 run (code b c reference value) before=.ok after 0 ∧
 StateRepr L c frame (Frag.init (Frame R))
   ((σ.withEnv (Δ:=Parameters R) (countValue n bound,(some ref,()))).push (t:=.val .uint) (PrimTy.dflt .uint)) base after ∧
 StateRepr L b frame F σ base after ∧ after.stack=before.stack ∧
 after.mem c=before.mem (cellOf b reference) ∧
 (∀ x,x≠c → x≠c+1 → x≠c+2 → after.mem x=before.mem x) ∧
 GrowsAllocator b frame 0 σ base before
   ((σ.withEnv (Δ:=Parameters R) (countValue n bound,(some ref,()))).push (t:=.val .uint) (PrimTy.dflt .uint)) base after := by
 obtain ⟨ref,alias,pointer⟩ := repr.pointers reference
 let first := writeMachine before c (before.mem (cellOf b reference))
 have firstRepr : StateRepr L b frame F σ base first :=
   reserved_write repr c disjoint (by omega) _
 have compiled := value.cert.correct firstRepr
 rcases compiled with ⟨v,w,source,word,executed⟩ | ⟨source,executed⟩
 · have same : v=countValue n bound := Except.ok.inj (source.symm.trans evaluated)
   subst v
   let mid := writeMachine first (c+1) w
   let after := writeMachine mid (c+2) w[0]
   have oldRepr : StateRepr L b frame F σ base after :=
     reserved_write (reserved_write firstRepr (c+1) (by omega) (by omega) w) (c+2) (by omega) (by omega) w[0]
   have child : StateRepr L c frame (Frag.init (Frame R))
       ((σ.withEnv (Δ:=Parameters R) (countValue n bound,(some ref,()))).push (t:=.val .uint) (PrimTy.dflt .uint)) base after := by
     constructor
     · refine ⟨oldRepr.core.store,?_,?_,oldRepr.core.net,oldRepr.core.netSelf,oldRepr.core.bound,?_,
         oldRepr.core.env,oldRepr.core.funds,oldRepr.core.oracle⟩
       · intro p index
         cases index with
         | here =>
           change ReprV .uint (PrimTy.dflt .uint) (upd mid.mem (c+2) w[0] (c+2))
           rw [upd_same]
           exact ReprV.dflt_zero .uint
         | there index => cases index with
           | here =>
             change ReprV .uint (countValue n bound) (upd mid.mem (c+2) w[0] (c+1))
             rw [upd_other _ _ (by omega)]
             change ReprV .uint (countValue n bound) (upd first.mem (c+1) w (c+1))
             rw [upd_same]
             exact word
           | there index => cases index with | there index => cases index
       · intro T index flag
         cases index with | there index => cases index with | there index => cases index with | there index => cases index
       · intro T index flag
         cases index with | there index => cases index with | there index => cases index with | there index => cases index
     · exact oldRepr.heap
     · intro T index
       cases index with | there index => cases index with | there index => cases index with
         | here =>
           refine ⟨ref,rfl,?_⟩
           change upd (upd (upd before.mem c (before.mem (cellOf b reference))) (c+1) w) (c+2) w[0] c=_
           simp only [upd,if_neg (show c≠c+2 from by omega),if_neg (show c≠c+1 from by omega),if_true]
           exact pointer
         | there index => cases index
     · exact space
     · exact oldRepr.structs
     · exact oldRepr.separated
     · exact oldRepr.refs
   refine ⟨ref,after,?_,?_,child,oldRepr,rfl,?_,?_,?_⟩
   · simp only [args,Args.evalT,MPath.mvalT,alias,evaluated,ok_bind]
     rfl
   · unfold code
     have loaded : run [.mload (cellOf b reference),.mstore c] before=.ok first 0 := rfl
     rw [run_append_ok loaded,run_append_ok executed]
     rfl
   · exact (upd_other mid.mem w[0] (by omega)).trans
       ((upd_other first.mem w (by omega)).trans (upd_same _ _ _))
   · intro x h0 h1 h2
     exact (upd_other mid.mem w[0] h2).trans
       ((upd_other first.mem w h1).trans (upd_other before.mem _ h0))
   · intro cursor positive owner free
     simpa only [Nat.add_zero] using
       ((owner.localWrite c (by omega) (by omega) _).localWrite (c+1) (by omega) (by omega) w).localWrite
         (c+2) (by omega) (by omega) w[0]
 · rw [evaluated] at source
   cases source

/-- A checked failing argument absorbs EVERY continuation of this exact
entry prefix. No failed state, rollback or effect-absence fact is produced. -/
theorem revert {C : Contract} {Γ : Ctx} {R : RefTy} {L b c frame : Nat} {F : Frag Γ}
 (hm : (Ty.ref R).mapFree=true) (σ : State C Γ) (reference : Idx Γ (.mem R))
 (count : Val C Γ .uint) (value : CompiledVal b F count)
 (failed : count.evalT σ=.error .revert)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F σ base before)
 (disjoint : b+Γ.length≤c) (space : c+3≤frame) :
 (args hm reference count).evalT σ=.error .revert ∧
 (∀ suffix,run (code b c reference value ++ suffix) before=.revert) := by
 obtain ⟨ref,alias,pointer⟩ := repr.pointers reference
 let first := writeMachine before c (before.mem (cellOf b reference))
 have firstRepr : StateRepr L b frame F σ base first := reserved_write repr c disjoint (by omega) _
 have compiled := value.cert.correct firstRepr
 rcases compiled with ⟨v,w,source,word,executed⟩ | ⟨source,executed⟩
 · rw [failed] at source
   cases source
 · have prefixRun : run (code b c reference value) before=.revert := by
     unfold code
     have loaded : run [.mload (cellOf b reference),.mstore c] before=.ok first 0 := rfl
     rw [run_append_ok loaded]
     exact run_append_revert executed
   refine ⟨?_,fun suffix => run_append_revert prefixRun⟩
   simp only [args,Args.evalT,MPath.mvalT,alias,failed,ok_bind,error_bind, pure_bind]

end Solidity.Backend.InternalFlow.RuntimeFrame.DisjointScalarEntry
