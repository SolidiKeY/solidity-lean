import Solidity.Backend.MemoryOps.SourceUintAliasWriteRead

/-! A fourth actual statement rejects through its reached overwritten index.
Only successful prefixes have returned states/machines; failure is not rollback. -/
namespace Solidity.Backend.MemoryOps

/-- Prepending an actual successful statement to a reached failing Items tail.
This uses the existing interpreter, with its actual one-step fuel consumption. -/
theorem source_items_cons_error {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n nps : Nat)
    (s : Source.RStmt E [] false .body Γ Γ) (rest : Source.RItems E [] false .body Γ Γ)
    (y mid failed : Source.EMState E Γ) (halt : Source.Halt)
    (first : (Source.execS G F n nps none s y.1).run (.nil,y.2)=(.ok (.normal mid.1),(.nil,mid.2)))
    (tail : (Source.execItems G F n nps none rest mid.1).run (.nil,mid.2)=(.error halt,(.nil,failed.2))) :
    (Source.execItems G F (n+1) nps none (.stmt s rest) y.1).run (.nil,y.2)=(.error halt,(.nil,failed.2)) := by
  first
  | solve | simp only [] | omega
  | rw [Source.execItems,Source.Hoare.run_bind,first]
    change (Source.execItems G F n nps none rest mid.1 >>= fun o => Source.EM.lift (o.up Γ)).run (.nil,mid.2)=_
    rw [Source.Hoare.run_bind,tail]

/-- RHS failure precedes the local write. The given run is consumed by the
assignment clause, not assumed as an execution of the whole statement. -/
theorem source_uint_read_into_error_of_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (y z : Source.EMState E Γ)
    (root : Source.Idx Γ SourceUintArrayTy) (index result : Source.Idx Γ (.int .u256)) (halt : Source.Halt)
    (read : (Source.evalE G F (n+2) (.indexArray (.local root) (.local index) rfl)).run y=(.error halt,z)) :
    (Source.evalE G F (n+3) (sourceUintReadInto root index result)).run y=(.error halt,z) := by
  first
  | solve | simp only [] | omega
  | rw [sourceUintReadInto,Source.evalE,Source.Hoare.run_bind,read]

/-- A written out-of-range value becomes the real index through the third
statement. The fourth read-assignment fails in ONE Source/native/word program.
No reached relation, desired failure/run or post-revert state is a premise. -/
theorem source_uint_alias_write_read_reject_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fs : Source.Fr) (fuel : Nat)
    (y : Source.EMState E Γ) (sdst ssrc : Source.Idx Γ SourceUintArrayTy)
    (si sv sfail : Source.Idx Γ (.int .u256)) (address : Nat) (k value : PrimTy.uint.Denote)
    (hsrc : y.1.get ssrc=.memRef rfl address) (hsi : y.1.get si=sourceUint k) (hsv : y.1.get sv=sourceUint value)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    (σ : State C Δ) (dst src : Idx Δ (.mem (.array (.prim .uint)))) (index rhs failedResult : Idx Δ (.val .uint))
    (r : HRef σ.H (.array (.prim .uint))) (htsrc : TEnv.get src σ.env=some r)
    (hti : TEnv.get index σ.env=k) (htv : TEnv.get rhs σ.env=value)
    (hr : SourceUintMemoryAt y address σ.heap r .dyn) (hk : k.1.toNat<σ.heap.len r .dyn)
    (outside : σ.heap.len r .dyn≤value.1.toNat)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m) (hb : 0<b)
    (hindex : Evm.valIn F (.simple (.local index) : Val C Δ .uint)=true)
    (hvalue : Evm.valIn F (.simple (.local rhs) : Val C Δ .uint)=true) :
    let alias : Source.EMState E Γ := (y.1.set sdst (.memRef rfl address),y.2)
    let σm := σ.setLocal dst (some r)
    ∃ (mid : Heap σ.H) (changed : Source.EMState E Γ) (mm target : Evm.Machine),
      let z : Source.EMState E Γ := (changed.1.set si (sourceUint value),changed.2)
      let τ := (σm.withHeap mid).setLocal index value
      (Source.evalE G Fs (fuel+6) (sourceLocalAlias sdst ssrc)).run y=(.ok (.val (.memRef rfl address)),alias) ∧
      (Source.evalE G Fs (fuel+5) (sourceUintIndexedAssign sdst si sv)).run alias=(.ok (.val (sourceUint value)),changed) ∧
      (Source.evalE G Fs (fuel+4) (sourceUintReadInto sdst si si)).run changed=(.ok (.val (sourceUint value)),z) ∧
      (Source.execItems G Fs (fuel+8) Γ.length none
        (.stmt (.expr (sourceLocalAlias sdst ssrc)) (.stmt (.expr (sourceUintIndexedAssign sdst si sv))
          (.stmt (.expr (sourceUintReadInto sdst si si)) .nil)) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.evalE G Fs (fuel+3) (sourceUintReadInto sdst si sfail)).run z=(.error (.revert (Source.panicData .index)),z) ∧
      (Source.execItems G Fs (fuel+8) Γ.length none
        (.stmt (.expr (sourceLocalAlias sdst ssrc)) (.stmt (.expr (sourceUintIndexedAssign sdst si sv))
          (.stmt (.expr (sourceUintReadInto sdst si si)) (.stmt (.expr (sourceUintReadInto sdst si sfail)) .nil))) :
            Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.error (.revert (Source.panicData .index)),(.nil,z.2)) ∧
      Prog.run σ (.cons (.rebindMem dst (.alias (.var src rfl)))
        (.cons (.assignMem (.index .dyn (.var dst rfl) (.simple (.local index))) (.val (.simple (.local rhs))))
          (.cons (.assignLocal index (.readMem (.index .dyn (.var dst rfl) (.simple (.local index))))) .nil)))=
        .ok ⟨τ,List.prefix_refl _⟩ ∧
      Prog.run σ (.cons (.rebindMem dst (.alias (.var src rfl)))
        (.cons (.assignMem (.index .dyn (.var dst rfl) (.simple (.local index))) (.val (.simple (.local rhs))))
          (.cons (.assignLocal index (.readMem (.index .dyn (.var dst rfl) (.simple (.local index)))))
            (.cons (.assignLocal failedResult (.readMem (.index .dyn (.var dst rfl) (.simple (.local index))))) .nil))))=.error .revert ∧
      Evm.run (Evm.Memory.aliasLocalCode b dst src++uintAliasWriteCode (C := C) b dst index rhs) m=.ok mm 0 ∧
      Evm.run (uintReadIntoCode (C := C) b dst index index) mm=.ok target 0 ∧
      Evm.run ((Evm.Memory.aliasLocalCode b dst src++uintAliasWriteCode (C := C) b dst index rhs)++uintReadIntoCode (C := C) b dst index index) m=.ok target 0 ∧
      Evm.run (uintReadIntoCode (C := C) b dst index failedResult) target=.revert ∧
      Evm.run (((Evm.Memory.aliasLocalCode b dst src++uintAliasWriteCode (C := C) b dst index rhs)++uintReadIntoCode (C := C) b dst index index)++uintReadIntoCode (C := C) b dst index failedResult) m=.revert ∧
      SourceUintMemoryAt z address mid r .dyn ∧ Source.MemOK E SH z ∧
      Evm.Memory.Objects.StateRepr L b frame F τ base target ∧
      Evm.Memory.Objects.AllocatorRepr mid base frame cursor target ∧
      σ.heap.writeAddr (.index r .dyn k) value=some mid ∧ mid.readAddr (.index r .dyn k)=some value ∧
      MObj.elems .dyn (mid.get r)=(MObj.elems .dyn (σ.heap.get r)).set k.1.toNat value ∧
      z.1.get si=sourceUint value ∧ TEnv.get index τ.env=value ∧
      target.stack=m.stack ∧ target.mem 0=m.mem 0 ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),r.id≠q.id → mid.get q=σ.heap.get q) ∧
      (∀ a,a≠address → z.2.heap.get a=y.2.heap.get a) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve | simp only [] | omega
  | obtain ⟨mid,changed,mm,first,second,pair,aliasNative,writeNative,pairNative,write,newAlias,new,mok,
      aliasCode,writeCode,pairCode,repr,alloc,keep,stack,free,values,locals,rootS,rootT,sourceOther,frames,sourceFrames,ex,events,logs,fn⟩ :=
      source_uint_alias_assign_word G Fs (fuel+2) y sdst ssrc si sv address k value hsrc hsi hsv SH hmem
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
    have hit : mid.readAddr (.index r .dyn k)=some value := by
      change (MObj.elems .dyn (mid.get r))[k.1.toNat]?=some value
      rw [values]
      exact List.getElem?_set_self hk
    have actualValue : (MObj.elems .dyn ((σm.withHeap mid).heap.get r))[k.1.toNat]'nextBound=value :=
      Option.some.inj ((List.getElem?_eq_getElem nextBound).symm.trans hit)
    have suffix := source_uint_read_into_objects_word G Fs (fuel+1) changed (σm.withHeap mid) r address new
      sdst si si dst index index k rootS sourceIndex rootT targetIndex nextBound SH mok repr alloc hb hindex
    dsimp only at suffix
    rw [actualValue] at suffix
    obtain ⟨target,readSource,third,readNative,readCode,final,finalOK,finalRepr,finalAlloc,keepRead,
      resultSource,resultTarget,globals,readOther,finalStack,finalFree⟩ := suffix
    let z : Source.EMState E Γ := (changed.1.set si (sourceUint value),changed.2)
    let τ := (σm.withHeap mid).setLocal index value
    have outside' : mid.len r .dyn≤value.1.toNat := by
      change (MObj.elems .dyn (mid.get r)).length≤value.1.toNat
      rw [values,List.length_set]
      exact outside
    have sourceRoot : z.1.get sdst=.memRef rfl address :=
      (source_locals_get_set_other changed.1 si sdst _ (Ne.symm sourceNe)).trans rootS
    have targetRoot : TEnv.get dst τ.env=some r :=
      (TEnv.get_set_ne index dst _ (σm.withHeap mid).env (Ne.symm targetNe)).trans rootT
    have failedRead := final.eval_read_bounds G Fs fuel sdst si value sourceRoot resultSource outside'
    have fourth := source_uint_read_into_error_of_run G Fs fuel z z sdst si sfail _ failedRead
    have firstStmt := source_expr_statement_run G Fs (fuel+6) Γ.length _ y alias _ first
    have secondStmt := source_expr_statement_run G Fs (fuel+5) Γ.length _ alias changed _ second
    have thirdStmt := source_expr_statement_run G Fs (fuel+4) Γ.length _ changed z _ third
    have fourthStmt := source_expr_statement_error G Fs (fuel+3) Γ.length _ z z _ fourth
    have pairTail := source_items_pair_run G Fs (fuel+1) Γ.length _ _ alias changed z secondStmt thirdStmt
    have prefixItems := source_items_cons_run G Fs (fuel+7) Γ.length _ _ y alias z firstStmt pairTail
    have badTail := source_items_pair_error G Fs fuel Γ.length _ _ changed z z _ thirdStmt fourthStmt
    have badRest := source_items_cons_error G Fs (fuel+6) Γ.length _ _ alias changed z _ secondStmt badTail
    have failedItems := source_items_cons_error G Fs (fuel+7) Γ.length _ _ y alias z _ firstStmt badRest
    let e : Val C Δ .uint := .readMem (.index .dyn (.var dst rfl) (.simple (.local index)))
    have reachedIndex : TEnv.get index τ.env=value := resultTarget
    have noRead : τ.heap.readAddr (.index r .dyn value)=none := List.getElem?_eq_none outside'
    have invalid : e.evalT τ=.error .revert := by
      simp only [e,Val.evalT,MLoc.addrT,MPath.mvalT,Simple.evalT,targetRoot,reachedIndex,noRead,
        TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have invalidAssign : Stmt.run τ (.assignLocal failedResult e)=.error .revert := by
      change TRun.assignLocal failedResult e τ=_
      simp only [TRun.assignLocal,invalid,bind,Except.bind]
    have tailFail : Prog.run τ (.cons (.assignLocal failedResult e) .nil)=.error .revert := by
      change TRun.seq _ _ τ=_
      change TRun.assignLocal failedResult e τ=.error .revert at invalidAssign
      simp only [TRun.seq]
      rw [invalidAssign]
    have prefixProg : Prog.run σ (.cons (.rebindMem dst (.alias (.var src rfl)))
        (.cons (.assignMem (.index .dyn (.var dst rfl) (.simple (.local index))) (.val (.simple (.local rhs))))
          (.cons (.assignLocal index e) .nil)))=.ok ⟨τ,List.prefix_refl _⟩ := by
      rw [Prog.run_cons_ok aliasNative,Prog.run_cons_ok writeNative,Prog.run_cons_ok readNative,Prog.run_nil]
      rfl
    have failedProg : Prog.run σ (.cons (.rebindMem dst (.alias (.var src rfl)))
        (.cons (.assignMem (.index .dyn (.var dst rfl) (.simple (.local index))) (.val (.simple (.local rhs))))
          (.cons (.assignLocal index e) (.cons (.assignLocal failedResult e) .nil))))=.error .revert := by
      rw [Prog.run_cons_ok aliasNative,Prog.run_cons_ok writeNative,Prog.run_cons_ok readNative,tailFail]
      rfl
    have readCert := Evm.Memory.Objects.PtrFrag.readPrimitive finalRepr
      (Evm.Memory.Objects.PtrFrag.local dst rfl) (.dyn : ArrTy (.array (.prim .uint)) (.prim .uint))
      (.simple (.local index) : Val C Δ .uint) hindex
    have readRevert : Evm.run (Evm.Memory.readLocalCode b dst (.simple (.local index) : Val C Δ .uint)) target=.revert := by
      change Evm.ValOutT .uint _ (Evm.run (Evm.Memory.readLocalCode b dst (.simple (.local index) : Val C Δ .uint)) target) target at readCert
      rw [invalid] at readCert
      rcases readCert with ⟨v,w,bad,_⟩ | ⟨_,revert⟩
      · cases bad
      · exact revert
    have lastCode : Evm.run (uintReadIntoCode (C := C) b dst index failedResult) target=.revert :=
      Evm.run_append_revert readRevert
    have prefixCode : Evm.run ((Evm.Memory.aliasLocalCode b dst src++uintAliasWriteCode (C := C) b dst index rhs)++uintReadIntoCode (C := C) b dst index index) m=.ok target 0 := by
      rw [Evm.run_append_ok pairCode,readCode]
    refine ⟨mid,changed,mm,target,first,second,third,prefixItems,fourth,failedItems,prefixProg,failedProg,
      pairCode,readCode,prefixCode,lastCode,?_,final,finalOK,finalRepr,finalAlloc,write,hit,values,
      resultSource,resultTarget,finalStack.trans stack,finalFree.trans free,(fun q ne => frames _ q ne),
      sourceFrames,ex,events,logs,fn⟩
    rw [Evm.run_append_ok prefixCode,lastCode]

/-- info: 'Solidity.Backend.MemoryOps.source_items_cons_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_items_cons_error
/-- info: 'Solidity.Backend.MemoryOps.source_uint_read_into_error_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_read_into_error_of_run
/-- info: 'Solidity.Backend.MemoryOps.source_uint_alias_write_read_reject_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_alias_write_read_reject_word
end Solidity.Backend.MemoryOps
