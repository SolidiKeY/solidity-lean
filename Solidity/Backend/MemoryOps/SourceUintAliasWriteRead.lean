import Solidity.Backend.MemoryOps.SourceUintAliasWrite
import Solidity.Backend.MemoryOps.SourceCalldataUintBinding

/-! Actual reached array read into a scalar, with strong Objects framing.
Existing read and local-assignment certificates supply the word program. -/
namespace Solidity.Backend.MemoryOps

/-- The published read path followed by the published scalar store. -/
def uintReadIntoCode {C : Contract} {Δ : Ctx} (b : Nat)
    (root : Idx Δ (.mem (.array (.prim .uint)))) (index result : Idx Δ (.val .uint)) : List Evm.Instr :=
  Evm.Memory.readLocalCode b root (.simple (.local index) : Val C Δ .uint)++[.mstore (Evm.cellOf b result)]

/-- Actual initial contents derive the read value. Result/index/RHS locals may
alias: the store follows the read and does not require unequal scalar indices. -/
theorem source_uint_read_into_objects_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fs : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (σ : State C Δ) (r : HRef σ.H (.array (.prim .uint))) (address : Nat)
    (hr : SourceUintMemoryAt y address σ.heap r .dyn)
    (sr : Source.Idx Γ SourceUintArrayTy) (si result : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.array (.prim .uint)))) (index targetResult : Idx Δ (.val .uint)) (k : PrimTy.uint.Denote)
    (hsr : y.1.get sr=.memRef rfl address) (hsi : y.1.get si=sourceUint k)
    (htr : TEnv.get root σ.env=some r) (hti : TEnv.get index σ.env=k)
    (hk : k.1.toNat<σ.heap.len r .dyn) (SH : Source.HeapTy) (mok : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (repr : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (allocator : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m) (hb : 0<b)
    (hin : Evm.valIn F (.simple (.local index) : Val C Δ .uint)=true) :
    let value := (MObj.elems .dyn (σ.heap.get r))[k.1.toNat]'hk
    let z : Source.EMState E Γ := (y.1.set result (sourceUint value),y.2)
    ∃ target : Evm.Machine,
      (Source.evalE G Fs (fuel+2) (.indexArray (.local sr) (.local si) rfl)).run y=(.ok (.val (sourceUint value)),y) ∧
      (Source.evalE G Fs (fuel+3) (sourceUintReadInto sr si result)).run y=(.ok (.val (sourceUint value)),z) ∧
      Stmt.run σ (.assignLocal targetResult (.readMem (.index .dyn (.var root rfl) (.simple (.local index)))))=
        .ok ⟨σ.setLocal targetResult value,List.prefix_refl _⟩ ∧
      Evm.run (uintReadIntoCode (C := C) b root index targetResult) m=.ok target 0 ∧
      SourceUintMemoryAt z address σ.heap r .dyn ∧ Source.MemOK E SH z ∧
      Evm.Memory.Objects.StateRepr L b frame F (σ.setLocal targetResult value) base target ∧
      Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor target ∧
      Evm.Memory.Objects.KeepsAllocator b frame σ base m (σ.setLocal targetResult value) target ∧
      z.1.get result=sourceUint value ∧ TEnv.get targetResult (σ.setLocal targetResult value).env=value ∧
      z.2=y.2 ∧ (∀ τ (i : Source.Idx Γ τ),result.toNat≠i.toNat → z.1.get i=y.1.get i) ∧
      target.stack=m.stack ∧ target.mem 0=m.mem 0 := by
  first
  | solve | simp only [] | omega
  | dsimp only
    let value := (MObj.elems .dyn (σ.heap.get r))[k.1.toNat]'hk
    let z : Source.EMState E Γ := (y.1.set result (sourceUint value),y.2)
    have sourceRead := hr.eval_index G Fs fuel sr si k hsr hsi hk
    have source := source_uint_read_into_of_run G Fs fuel y sr si result value sourceRead
    have readSome : σ.heap.readAddr (.index r .dyn k)=some value := List.getElem?_eq_getElem hk
    let e : Val C Δ .uint := .readMem (.index .dyn (.var root rfl) (.simple (.local index)))
    have eval : e.evalT σ=.ok value := by
      simp only [e,Val.evalT,MLoc.addrT,MPath.mvalT,Simple.evalT,htr,hti,readSome,
        TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have native : Stmt.run σ (.assignLocal targetResult e)=.ok ⟨σ.setLocal targetResult value,List.prefix_refl _⟩ := by
      change TRun.assignLocal targetResult e σ=_
      simp only [TRun.assignLocal,eval,bind,Except.bind,pure,Except.pure]
    have readCert := Evm.Memory.Objects.PtrFrag.readPrimitive repr
      (Evm.Memory.Objects.PtrFrag.local (C := C) root rfl) (.dyn : ArrTy (.array (.prim .uint)) (.prim .uint))
      (.simple (.local index) : Val C Δ .uint) hin
    have cert := Evm.Memory.Objects.assignValue_correct repr targetResult e
      (Evm.Memory.readLocalCode b root (.simple (.local index) : Val C Δ .uint)) readCert
    unfold Evm.Memory.Objects.ResultRepr at cert
    rw [show TRun.assignLocal targetResult e σ=.ok ⟨σ.setLocal targetResult value,List.prefix_refl _⟩ from native] at cert
    rcases cert with ⟨o,target,equal,code,finalRepr,stack,keep⟩ | ⟨bad,_⟩
    · cases Except.ok.inj equal
      have finalOK : Source.MemOK E SH z :=
        ⟨⟨mok.1.1,Source.LocalsOK.set y.1 result mok.1.2 (Source.Val.refOK_of_loc rfl _)⟩,mok.2⟩
      have finalAllocator := keep cursor hb allocator
      exact ⟨target,sourceRead,source,native,code,hr,finalOK,finalRepr,finalAllocator,keep,
        source_locals_get_set _ _ _,TEnv.get_set _ _ _,rfl,
        (fun τ i ne => source_locals_get_set_other y.1 result i _ ne),stack,finalAllocator.free.cell.trans allocator.free.cell.symm⟩
    · cases bad

/-- info: 'Solidity.Backend.MemoryOps.source_uint_read_into_objects_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_read_into_objects_word
/-- One alias/write/scalar-read program. The scalar may overwrite its own
index or RHS after reading; the value/bound/representation come from the actual
first write, not a supplied desired reached relation or successful suffix. -/
theorem source_uint_alias_write_read_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fs : Source.Fr) (fuel : Nat)
    (y : Source.EMState E Γ) (sdst ssrc : Source.Idx Γ SourceUintArrayTy)
    (si sv sresult : Source.Idx Γ (.int .u256)) (address : Nat) (k value : PrimTy.uint.Denote)
    (hsrc : y.1.get ssrc=.memRef rfl address) (hsi : y.1.get si=sourceUint k) (hsv : y.1.get sv=sourceUint value)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    (σ : State C Δ) (dst src : Idx Δ (.mem (.array (.prim .uint)))) (index rhs result : Idx Δ (.val .uint))
    (r : HRef σ.H (.array (.prim .uint))) (htsrc : TEnv.get src σ.env=some r)
    (hti : TEnv.get index σ.env=k) (htv : TEnv.get rhs σ.env=value)
    (hr : SourceUintMemoryAt y address σ.heap r .dyn) (hk : k.1.toNat<σ.heap.len r .dyn)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m) (hb : 0<b)
    (hindex : Evm.valIn F (.simple (.local index) : Val C Δ .uint)=true)
    (hvalue : Evm.valIn F (.simple (.local rhs) : Val C Δ .uint)=true) :
    let alias : Source.EMState E Γ := (y.1.set sdst (.memRef rfl address),y.2)
    let σm := σ.setLocal dst (some r)
    ∃ (mid : Heap σ.H) (changed : Source.EMState E Γ) (mm target : Evm.Machine),
      let z : Source.EMState E Γ := (changed.1.set sresult (sourceUint value),changed.2)
      (Source.evalE G Fs (fuel+5) (sourceLocalAlias sdst ssrc)).run y=(.ok (.val (.memRef rfl address)),alias) ∧
      (Source.evalE G Fs (fuel+4) (sourceUintIndexedAssign sdst si sv)).run alias=(.ok (.val (sourceUint value)),changed) ∧
      (Source.evalE G Fs (fuel+2) (.indexArray (.local sdst) (.local si) rfl)).run changed=(.ok (.val (sourceUint value)),changed) ∧
      (Source.evalE G Fs (fuel+3) (sourceUintReadInto sdst si sresult)).run changed=(.ok (.val (sourceUint value)),z) ∧
      (Source.execItems G Fs (fuel+7) Γ.length none
        (.stmt (.expr (sourceLocalAlias sdst ssrc)) (.stmt (.expr (sourceUintIndexedAssign sdst si sv))
          (.stmt (.expr (sourceUintReadInto sdst si sresult)) .nil)) : Source.RItems E [] false .body Γ Γ)
          y.1).run (.nil,y.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run σ (.cons (.rebindMem dst (.alias (.var src rfl)))
        (.cons (.assignMem (.index .dyn (.var dst rfl) (.simple (.local index))) (.val (.simple (.local rhs))))
          (.cons (.assignLocal result (.readMem (.index .dyn (.var dst rfl) (.simple (.local index))))) .nil)))=
        .ok ⟨(σm.withHeap mid).setLocal result value,List.prefix_refl _⟩ ∧
      Evm.run (Evm.Memory.aliasLocalCode b dst src++uintAliasWriteCode (C := C) b dst index rhs) m=.ok mm 0 ∧
      Evm.run (uintReadIntoCode (C := C) b dst index result) mm=.ok target 0 ∧
      Evm.run ((Evm.Memory.aliasLocalCode b dst src++uintAliasWriteCode (C := C) b dst index rhs)++uintReadIntoCode (C := C) b dst index result) m=.ok target 0 ∧
      σ.heap.writeAddr (.index r .dyn k) value=some mid ∧ mid.readAddr (.index r .dyn k)=some value ∧
      SourceUintMemoryAt changed address mid r .dyn ∧ SourceUintMemoryAt z address mid r .dyn ∧
      Source.MemOK E SH changed ∧ Source.MemOK E SH z ∧
      Evm.Memory.Objects.StateRepr L b frame F ((σm.withHeap mid).setLocal result value) base target ∧
      Evm.Memory.Objects.AllocatorRepr mid base frame cursor target ∧
      Evm.Memory.Objects.KeepsAllocator b frame σ base m ((σm.withHeap mid).setLocal result value) target ∧
      target.stack=m.stack ∧ target.mem 0=m.mem 0 ∧
      MObj.elems .dyn (mid.get r)=(MObj.elems .dyn (σ.heap.get r)).set k.1.toNat value ∧
      changed.1=alias.1 ∧ z.1.get sresult=sourceUint value ∧
      TEnv.get result ((σm.withHeap mid).setLocal result value).env=value ∧
      z.2=changed.2 ∧
      (∀ τ (i : Source.Idx Γ τ),sdst.toNat≠i.toNat → sresult.toNat≠i.toNat → z.1.get i=y.1.get i) ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),r.id≠q.id → mid.get q=σ.heap.get q) ∧
      (∀ a,a≠address → z.2.heap.get a=y.2.heap.get a) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve | simp only [] | omega
  | obtain ⟨mid,changed,mm,first,second,pair,aliasNative,writeNative,prefixNative,write,newAlias,new,mok,
      aliasCode,writeCode,prefixCode,repr,alloc,keep,stack,free,values,locals,rootS,rootT,sourceOther,frames,sourceFrames,ex,events,logs,fn⟩ :=
      source_uint_alias_assign_word G Fs (fuel+1) y sdst ssrc si sv address k value hsrc hsi hsv SH hmem
        σ dst src index rhs r htsrc hti htv hr hk hm ha hb hindex hvalue
    dsimp only
    let alias : Source.EMState E Γ := (y.1.set sdst (.memRef rfl address),y.2)
    let σm := σ.setLocal dst (some r)
    have sourceNe : sdst.toNat≠si.toNat := by intro same;cases source_idx_type_of_position sdst si same
    have targetNe : dst.toNat≠index.toNat := by
      intro same
      have hd := dst.getElem?_toNat
      rw [same,index.getElem?_toNat] at hd
      cases hd
    have sourceIndex : changed.1.get si=sourceUint k := (sourceOther _ si sourceNe).trans hsi
    have targetIndex : TEnv.get index (σm.withHeap mid).env=k := (TEnv.get_set_ne dst index _ σ.env targetNe).trans hti
    have nextBound : k.1.toNat<mid.len r .dyn := by
      change k.1.toNat<(MObj.elems .dyn (mid.get r)).length
      rw [values,List.length_set]
      exact hk
    have changedValue : mid.readAddr (.index r .dyn k)=some value := by
      change (MObj.elems .dyn (mid.get r))[k.1.toNat]?=some value
      rw [values]
      exact List.getElem?_set_self hk
    have actualValue : (MObj.elems .dyn (mid.get r))[k.1.toNat]'nextBound=value :=
      Option.some.inj ((List.getElem?_eq_getElem nextBound).symm.trans changedValue)
    have suffix := source_uint_read_into_objects_word G Fs fuel changed (σm.withHeap mid) r address new
      sdst si sresult dst index result k rootS sourceIndex rootT targetIndex nextBound SH mok repr alloc hb hindex
    dsimp only at suffix
    change (MObj.elems .dyn ((σm.withHeap mid).heap.get r))[k.1.toNat]'nextBound=value at actualValue
    rw [actualValue] at suffix
    obtain ⟨target,readSource,third,readNative,readCode,final,finalOK,finalRepr,finalAlloc,keepRead,
      resultSource,resultTarget,globals,readOther,finalStack,finalFree⟩ := suffix
    let z : Source.EMState E Γ := (changed.1.set sresult (sourceUint value),changed.2)
    have firstStmt := source_expr_statement_run G Fs (fuel+5) Γ.length _ y alias _ first
    have secondStmt := source_expr_statement_run G Fs (fuel+4) Γ.length _ alias changed _ second
    have thirdStmt := source_expr_statement_run G Fs (fuel+3) Γ.length _ changed z _ third
    have tail := source_items_pair_run G Fs fuel Γ.length _ _ alias changed z secondStmt thirdStmt
    have items := source_items_cons_run G Fs (fuel+6) Γ.length _ _ y alias z firstStmt tail
    have prog : Prog.run σ (.cons (.rebindMem dst (.alias (.var src rfl)))
        (.cons (.assignMem (.index .dyn (.var dst rfl) (.simple (.local index))) (.val (.simple (.local rhs))))
          (.cons (.assignLocal result (.readMem (.index .dyn (.var dst rfl) (.simple (.local index))))) .nil)))=
        .ok ⟨(σm.withHeap mid).setLocal result value,List.prefix_refl _⟩ := by
      rw [Prog.run_cons_ok aliasNative,Prog.run_cons_ok writeNative,Prog.run_cons_ok readNative,Prog.run_nil]
      rfl
    refine ⟨mid,changed,mm,target,first,second,readSource,third,items,prog,prefixCode,readCode,?_,write,
      changedValue,new,final,mok,finalOK,finalRepr,finalAlloc,?_,finalStack.trans stack,finalFree.trans free,
      values,locals,resultSource,resultTarget,globals,?_,(fun q ne => frames _ q ne),sourceFrames,ex,events,logs,fn⟩
    · rw [Evm.run_append_ok prefixCode,readCode]
    · intro c positive initial
      exact keepRead c positive (keep c positive initial)
    · intro τ i rootNe resultNe
      rw [readOther τ i resultNe]
      exact sourceOther τ i rootNe

/-- info: 'Solidity.Backend.MemoryOps.source_uint_alias_write_read_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_alias_write_read_word
end Solidity.Backend.MemoryOps
