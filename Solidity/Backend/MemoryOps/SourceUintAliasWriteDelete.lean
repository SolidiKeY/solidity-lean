import Solidity.Backend.MemoryOps.SourceUintAliasWrite
import Solidity.Backend.MemoryOps.SourceUintAliasDelete

/-! Reached write/delete composition with strong Objects representations.
The primitive delete adapter consumes existing Source/default-write semantics;
no alternative interpreter, compiler, allocator or final-state oracle. -/
namespace Solidity.Backend.MemoryOps

/-- Strong numeric deletion from the actual independent Source/native write.
This operation-side adapter retains the complete Objects representation. -/
theorem source_uint_delete_objects_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fs : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (σ : State C Δ) (r : HRef σ.H (.array (.prim .uint))) (address : Nat)
    (hr : SourceUintMemoryAt y address σ.heap r .dyn)
    (sr : Source.Idx Γ SourceUintArrayTy) (si : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.array (.prim .uint)))) (index : Idx Δ (.val .uint)) (k : PrimTy.uint.Denote)
    (hsr : y.1.get sr=.memRef rfl address) (hsi : y.1.get si=sourceUint k)
    (htr : TEnv.get root σ.env=some r) (hti : TEnv.get index σ.env=k)
    (hk : k.1.toNat<σ.heap.len r .dyn) (SH : Source.HeapTy) (mok : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (repr : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (allocator : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m) (hb : 0<b)
    (hin : Evm.valIn F (.simple (.local index) : Val C Δ .uint)=true) :
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      (Source.evalE G Fs (fuel+3) (sourceUintIndexedDelete sr si)).run y=(.ok Source.RVal.unit,z) ∧
      Stmt.run σ (.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local index)))) rfl)=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (uintAliasDeleteCode (C := C) b root index) m=.ok target 0 ∧
      SourceUintMemoryAt z address out r .dyn ∧ Source.MemOK E SH z ∧
      Evm.Memory.Objects.StateRepr L b frame F (σ.withHeap out) base target ∧
      Evm.Memory.Objects.AllocatorRepr out base frame cursor target ∧
      Evm.Memory.Objects.KeepsAllocator b frame σ base m (σ.withHeap out) target ∧
      σ.heap.writeAddr (.index r .dyn k) (PrimTy.dflt .uint)=some out ∧
      MObj.elems .dyn (out.get r)=(MObj.elems .dyn (σ.heap.get r)).set k.1.toNat (PrimTy.dflt .uint) ∧
      z.1=y.1 ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),r.id≠q.id → out.get q=σ.heap.get q) ∧
      (∀ a,a≠address → z.2.heap.get a=y.2.heap.get a) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals ∧
      target.stack=m.stack ∧ target.mem 0=m.mem 0 := by
  first
  | solve | simp only [] | omega
  | obtain ⟨out,z,write,sourceWrite,new,memOK,values,frames,sourceFrames,locals,ex,events,logs,fn⟩ :=
      hr.write_observed Fs (fuel+2) k (PrimTy.dflt .uint) hk SH mok
    have sourceDelete : (Source.deleteLoc (E := E) (Γ := Γ) Fs (fuel+2) (τ := .int .u256)
      (.mem address k.1.toNat)).run y=(.ok (),z) := sourceWrite
    have source := hr.eval_delete_of_run G Fs fuel sr si k hsr hsi hk sourceDelete
    let iv : Val C Δ .uint := .simple (.local index)
    let rv : Val C Δ .uint := Evm.Memory.deleteDefaultValue .uint
    have nativeAssign : TRun.assignMem (.index .dyn (.var root rfl) iv) (.val rv) σ=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
      simp only [iv,TRun.assignMem,MLoc.addrT,MSrc.mvalT,MPath.mvalT,Simple.evalT,Val.evalT,
        htr,hti,show rv.evalT σ=.ok (PrimTy.dflt .uint) from Evm.Memory.deleteDefaultValue_eval σ .uint,
        write,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have native : Stmt.run σ (.deleteMem (.loc (.index .dyn (.var root rfl) iv)) rfl)=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
      change TRun.deleteMem (.loc (.index .dyn (.var root rfl) iv)) σ=_
      rw [Evm.Memory.deleteMem_primitive_eq_assign]
      exact nativeAssign
    have pointer : Evm.Memory.Objects.PtrFrag (C := C) b F (.var root rfl) [.mload (Evm.cellOf b root)] := .local root rfl
    have valueCode : Evm.Memory.Objects.SrcFrag b F (.val rv) (Evm.compileVal b rv) := .val rv _ (.core rv rfl)
    have cert := Evm.Memory.Objects.PtrFrag.write repr (.dyn : ArrTy (.array (.prim .uint)) (.prim .uint)) pointer valueCode iv hin
    unfold Evm.Memory.Objects.ResultRepr at cert
    rw [nativeAssign] at cert
    rcases cert with ⟨o,target,equal,code,finalRepr,stack,keep⟩ | ⟨bad,_⟩
    · cases Except.ok.inj equal
      have finalAllocator := keep cursor hb allocator
      exact ⟨out,z,target,source,native,code,new,memOK,finalRepr,finalAllocator,keep,write,
        values,locals,(fun q hq => frames _ q hq),sourceFrames,ex,events,logs,fn,stack,finalAllocator.free.cell.trans allocator.free.cell.symm⟩
    · cases bad

/-- info: 'Solidity.Backend.MemoryOps.source_uint_delete_objects_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_delete_objects_word
/-- Actual three-operation composition. Both writes consume the reached
alias-selected object. All second-write prerequisites follow the first update;
no intermediate relation, execution or desired final result is assumed. -/
theorem source_uint_alias_write_delete_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fs : Source.Fr) (fuel : Nat)
    (y : Source.EMState E Γ) (sdst ssrc : Source.Idx Γ SourceUintArrayTy)
    (si sv : Source.Idx Γ (.int .u256)) (address : Nat) (k value : PrimTy.uint.Denote)
    (hsrc : y.1.get ssrc=.memRef rfl address) (hsi : y.1.get si=sourceUint k) (hsv : y.1.get sv=sourceUint value)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    (σ : State C Δ) (dst src : Idx Δ (.mem (.array (.prim .uint)))) (index rhs : Idx Δ (.val .uint))
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
    ∃ (mid out : Heap σ.H) (changed z : Source.EMState E Γ) (mm target : Evm.Machine),
      (Source.evalE G Fs (fuel+5) (sourceLocalAlias sdst ssrc)).run y=(.ok (.val (.memRef rfl address)),alias) ∧
      (Source.evalE G Fs (fuel+4) (sourceUintIndexedAssign sdst si sv)).run alias=(.ok (.val (sourceUint value)),changed) ∧
      (Source.evalE G Fs (fuel+3) (sourceUintIndexedDelete sdst si)).run changed=(.ok Source.RVal.unit,z) ∧
      (Source.execItems G Fs (fuel+7) Γ.length none
        (.stmt (.expr (sourceLocalAlias sdst ssrc)) (.stmt (.expr (sourceUintIndexedAssign sdst si sv))
          (.stmt (.expr (sourceUintIndexedDelete sdst si)) .nil)) : Source.RItems E [] false .body Γ Γ)
          y.1).run (.nil,y.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run σ (.cons (.rebindMem dst (.alias (.var src rfl)))
        (.cons (.assignMem (.index .dyn (.var dst rfl) (.simple (.local index))) (.val (.simple (.local rhs))))
          (.cons (.deleteMem (.loc (.index .dyn (.var dst rfl) (.simple (.local index)))) rfl) .nil)))=
        .ok ⟨σm.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (Evm.Memory.aliasLocalCode b dst src++uintAliasWriteCode (C := C) b dst index rhs) m=.ok mm 0 ∧
      Evm.run (uintAliasDeleteCode (C := C) b dst index) mm=.ok target 0 ∧
      Evm.run ((Evm.Memory.aliasLocalCode b dst src++uintAliasWriteCode (C := C) b dst index rhs)++uintAliasDeleteCode (C := C) b dst index) m=.ok target 0 ∧
      σ.heap.writeAddr (.index r .dyn k) value=some mid ∧
      mid.writeAddr (.index r .dyn k) (PrimTy.dflt .uint)=some out ∧
      mid.readAddr (.index r .dyn k)=some value ∧
      SourceUintMemoryAt changed address mid r .dyn ∧ SourceUintMemoryAt z address out r .dyn ∧
      Source.MemOK E SH changed ∧ Source.MemOK E SH z ∧
      Evm.Memory.Objects.StateRepr L b frame F (σm.withHeap mid) base mm ∧
      Evm.Memory.Objects.StateRepr L b frame F (σm.withHeap out) base target ∧
      Evm.Memory.Objects.AllocatorRepr mid base frame cursor mm ∧
      Evm.Memory.Objects.AllocatorRepr out base frame cursor target ∧
      Evm.Memory.Objects.KeepsAllocator b frame σ base m (σm.withHeap out) target ∧
      target.stack=m.stack ∧ target.mem 0=m.mem 0 ∧
      MObj.elems .dyn (mid.get r)=(MObj.elems .dyn (σ.heap.get r)).set k.1.toNat value ∧
      MObj.elems .dyn (out.get r)=((MObj.elems .dyn (σ.heap.get r)).set k.1.toNat value).set k.1.toNat (PrimTy.dflt .uint) ∧
      changed.1=alias.1 ∧ z.1=changed.1 ∧
      (∀ τ (i : Source.Idx Γ τ),sdst.toNat≠i.toNat → z.1.get i=y.1.get i) ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),r.id≠q.id → out.get q=σ.heap.get q) ∧
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
    have targetIndex : TEnv.get index (σm.withHeap mid).env=k :=
      (TEnv.get_set_ne dst index _ σ.env targetNe).trans hti
    have nextBound : k.1.toNat<mid.len r .dyn := by
      change k.1.toNat<(MObj.elems .dyn (mid.get r)).length
      rw [values,List.length_set]
      exact hk
    have changedValue : mid.readAddr (.index r .dyn k)=some value := by
      change (MObj.elems .dyn (mid.get r))[k.1.toNat]?=some value
      rw [values]
      exact List.getElem?_set_self hk
    obtain ⟨out,z,target,third,deleteNative,deleteCode,final,finalOK,finalRepr,finalAlloc,keepDelete,deleteWrite,
      finalValues,finalLocals,finalFrames,finalSourceFrames,finalEx,finalEvents,finalLogs,finalFn,finalStack,finalFree⟩ :=
      source_uint_delete_objects_word G Fs fuel changed (σm.withHeap mid) r address new sdst si dst index k
        rootS sourceIndex rootT targetIndex nextBound SH mok repr alloc hb hindex
    have firstStmt := source_expr_statement_run G Fs (fuel+5) Γ.length _ y alias _ first
    have secondStmt := source_expr_statement_run G Fs (fuel+4) Γ.length _ alias changed _ second
    have thirdStmt := source_expr_statement_run G Fs (fuel+3) Γ.length _ changed z Source.RVal.unit third
    have tail := source_items_pair_run G Fs fuel Γ.length _ _ alias changed z secondStmt thirdStmt
    have items := source_items_cons_run G Fs (fuel+6) Γ.length _ _ y alias z firstStmt tail
    have prog : Prog.run σ (.cons (.rebindMem dst (.alias (.var src rfl)))
        (.cons (.assignMem (.index .dyn (.var dst rfl) (.simple (.local index))) (.val (.simple (.local rhs))))
          (.cons (.deleteMem (.loc (.index .dyn (.var dst rfl) (.simple (.local index)))) rfl) .nil)))=
        .ok ⟨σm.withHeap out,List.prefix_refl _⟩ := by
      rw [Prog.run_cons_ok aliasNative,Prog.run_cons_ok writeNative,Prog.run_cons_ok deleteNative,Prog.run_nil]
      rfl
    refine ⟨mid,out,changed,z,mm,target,first,second,third,items,prog,prefixCode,deleteCode,?_,write,
      deleteWrite,changedValue,new,final,mok,finalOK,repr,finalRepr,alloc,finalAlloc,?_,
      finalStack.trans stack,finalFree.trans free,values,?_,locals,finalLocals,?_,?_,?_,
      finalEx.trans ex,finalEvents.trans events,finalLogs.trans logs,finalFn.trans fn⟩
    · rw [Evm.run_append_ok prefixCode,deleteCode]
    · intro c positive initial
      exact keepDelete c positive (keep c positive initial)
    · change MObj.elems .dyn (out.get r)=(MObj.elems .dyn (mid.get r)).set k.1.toNat (PrimTy.dflt .uint) at finalValues
      rw [finalValues,values]
    · intro τ i ne
      rw [finalLocals]
      exact sourceOther τ i ne
    · intro Q q ne
      exact (finalFrames q ne).trans (frames Q q ne)
    · intro a ne
      exact (finalSourceFrames a ne).trans (sourceFrames a ne)

/-- info: 'Solidity.Backend.MemoryOps.source_uint_alias_write_delete_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_alias_write_delete_word
end Solidity.Backend.MemoryOps
