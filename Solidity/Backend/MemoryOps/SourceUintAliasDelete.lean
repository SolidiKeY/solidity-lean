import Solidity.Backend.MemoryOps.SourceUintAlias
import Solidity.Backend.MemoryOps.SourceUintDelete
import Solidity.Backend.MemoryOps.SourceCalldataUintMutation

/-! Actual dynamic uint alias followed by primitive deletion. The strong
Objects write certificate realizes the existing intrinsic default-write identity;
Source deletion independently supplies unit and its real heap update. -/
namespace Solidity.Backend.MemoryOps

/-- Existing delete program, not a replacement pointer compiler. -/
def uintAliasDeleteCode {C : Contract} {Δ : Ctx} (b : Nat)
    (dst : Idx Δ (.mem (.array (.prim .uint)))) (index : Idx Δ (.val .uint)) : List Evm.Instr :=
  Evm.Memory.deleteLocalCode b dst (Evm.compileVal b (.simple (.local index) : Val C Δ .uint))

/-- INITIAL correspondence derives the reached child, actual delete and whole
program; the final representation, contents and frames are consequences. -/
theorem source_uint_alias_delete_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
    (y : Source.EMState E Γ) (sdst ssrc : Source.Idx Γ SourceUintArrayTy)
    (si : Source.Idx Γ (.int .u256)) (address : Nat) (k : PrimTy.uint.Denote)
    (hsrc : y.1.get ssrc=.memRef rfl address) (hsi : y.1.get si=sourceUint k)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    (σ : State C Δ) (dst src : Idx Δ (.mem (.array (.prim .uint)))) (index : Idx Δ (.val .uint))
    (r : HRef σ.H (.array (.prim .uint))) (htsrc : TEnv.get src σ.env=some r)
    (hti : TEnv.get index σ.env=k)
    (hr : SourceUintMemoryAt y address σ.heap r .dyn) (hk : k.1.toNat<σ.heap.len r .dyn)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m) (hb : 0<b)
    (hindex : Evm.valIn F (.simple (.local index) : Val C Δ .uint)=true) :
    let mid : Source.EMState E Γ := (y.1.set sdst (.memRef rfl address),y.2)
    let σm := σ.setLocal dst (some r)
    let mm := Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base r.id))
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      (Source.evalE G Fsrc (horizon+4) (sourceLocalAlias sdst ssrc)).run y=(.ok (.val (.memRef rfl address)),mid) ∧
      (Source.evalE G Fsrc (horizon+3) (sourceUintIndexedDelete sdst si)).run mid=(.ok Source.RVal.unit,z) ∧
      (Source.execItems G Fsrc (horizon+6) Γ.length none
        (.stmt (.expr (sourceLocalAlias sdst ssrc))
          (.stmt (.expr (sourceUintIndexedDelete sdst si)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
      Stmt.run σ (.rebindMem dst (.alias (.var src rfl)))=.ok ⟨σm,List.prefix_refl _⟩ ∧
      Stmt.run σm (.deleteMem (.loc (.index .dyn (.var dst rfl) (.simple (.local index)))) rfl)=
        .ok ⟨σm.withHeap out,List.prefix_refl _⟩ ∧
      Prog.run σ (.cons (.rebindMem dst (.alias (.var src rfl)))
        (.cons (.deleteMem (.loc (.index .dyn (.var dst rfl) (.simple (.local index)))) rfl) .nil))=
        .ok ⟨σm.withHeap out,List.prefix_refl _⟩ ∧
      σ.heap.writeAddr (.index r .dyn k) (PrimTy.dflt .uint)=some out ∧
      SourceUintMemoryAt mid address σm.heap r .dyn ∧ SourceUintMemoryAt z address out r .dyn ∧
      Source.MemOK E SH z ∧
      Evm.run (Evm.Memory.aliasLocalCode b dst src) m=.ok mm 0 ∧
      Evm.run (uintAliasDeleteCode (C := C) b dst index) mm=.ok target 0 ∧
      Evm.run (Evm.Memory.aliasLocalCode b dst src++uintAliasDeleteCode (C := C) b dst index) m=.ok target 0 ∧
      Evm.Memory.Objects.StateRepr L b frame F (σm.withHeap out) base target ∧
      Evm.Memory.Objects.AllocatorRepr out base frame cursor target ∧
      Evm.Memory.Objects.KeepsAllocator b frame σ base m (σm.withHeap out) target ∧
      target.stack=m.stack ∧ target.mem 0=m.mem 0 ∧
      MObj.elems .dyn (out.get r)=(MObj.elems .dyn (σ.heap.get r)).set k.1.toNat (PrimTy.dflt .uint) ∧
      z.1=mid.1 ∧ z.1.get sdst=.memRef rfl address ∧ TEnv.get dst (σm.withHeap out).env=some r ∧
      (∀ τ (i : Source.Idx Γ τ),sdst.toNat≠i.toNat → z.1.get i=y.1.get i) ∧
      (∀ Q (q : HRef σ.H Q),r.id≠q.id → out.get q=σ.heap.get q) ∧
      (∀ a,a≠address → z.2.heap.get a=y.2.heap.get a) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve | simp only [] | omega
  | obtain ⟨first,firstStmt,aliasNative,aliasCode,selected,mok,repr,alloc,keepAlias,rootS,rootT,globals,heap,stackAlias,free,sourceOther,targetOther,allObjects,allSource⟩ :=
      source_uint_alias_word G Fsrc (horizon+2) y sdst ssrc address hsrc SH hmem σ dst src r htsrc hr hm ha hb
    dsimp only
    let mid : Source.EMState E Γ := (y.1.set sdst (.memRef rfl address),y.2)
    let σm := σ.setLocal dst (some r)
    let mm := Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base r.id))
    have sourceNe : ∀ (i : Source.Idx Γ (.int .u256)),sdst.toNat≠i.toNat := by
      intro i same
      cases source_idx_type_of_position sdst i same
    have targetNe : ∀ (i : Idx Δ (.val .uint)),dst.toNat≠i.toNat := by
      intro i same
      have hd := dst.getElem?_toNat
      rw [same,i.getElem?_toNat] at hd
      cases hd
    have indexS : mid.1.get si=sourceUint k := (sourceOther si (sourceNe si)).trans hsi
    have indexT : TEnv.get index σm.env=k := (targetOther index (targetNe index)).trans hti
    have rootTarget : TEnv.get dst σm.env=some r := rootT
    obtain ⟨out,z,write,sourceWrite,new,memOK,values,frames,sourceFrames,locals,ex,events,logs,fn⟩ :=
      selected.write_observed Fsrc (horizon+2) k (PrimTy.dflt .uint) hk SH mok
    have sourceDelete : (Source.deleteLoc (E := E) (Γ := Γ) Fsrc (horizon+2) (τ := .int .u256)
      (.mem address k.1.toNat)).run mid=(.ok (),z) := sourceWrite
    have second := selected.eval_delete_of_run G Fsrc horizon sdst si k rootS indexS hk sourceDelete
    have secondStmt := source_expr_statement_run G Fsrc (horizon+3) Γ.length _ mid z _ second
    have nativeWrite : σm.heap.writeAddr (.index r .dyn k) (PrimTy.dflt .uint)=some out := write
    let iv : Val C Δ .uint := .simple (.local index)
    let rv : Val C Δ .uint := Evm.Memory.deleteDefaultValue .uint
    have nativeAssign : TRun.assignMem (.index .dyn (.var dst rfl) iv) (.val rv) σm=
        .ok ⟨σm.withHeap out,List.prefix_refl _⟩ := by
      simp only [iv,TRun.assignMem,MLoc.addrT,MSrc.mvalT,MPath.mvalT,Simple.evalT,Val.evalT,
        rootTarget,indexT,show rv.evalT σm=.ok (PrimTy.dflt .uint) from Evm.Memory.deleteDefaultValue_eval σm .uint,
        nativeWrite,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have native : Stmt.run σm (.deleteMem (.loc (.index .dyn (.var dst rfl) iv)) rfl)=
        .ok ⟨σm.withHeap out,List.prefix_refl _⟩ := by
      change TRun.deleteMem (.loc (.index .dyn (.var dst rfl) iv)) σm=_
      rw [Evm.Memory.deleteMem_primitive_eq_assign]
      exact nativeAssign
    have pointer : Evm.Memory.Objects.PtrFrag (C := C) b F (.var dst rfl) [.mload (Evm.cellOf b dst)] := .local dst rfl
    have valueCode : Evm.Memory.Objects.SrcFrag b F (.val rv) (Evm.compileVal b rv) := .val rv _ (.core rv rfl)
    have cert := Evm.Memory.Objects.PtrFrag.write repr (.dyn : ArrTy (.array (.prim .uint)) (.prim .uint)) pointer valueCode iv hindex
    unfold Evm.Memory.Objects.ResultRepr at cert
    rw [show TRun.assignMem (.index .dyn (.var dst rfl) iv) (.val rv) σm=.ok ⟨σm.withHeap out,List.prefix_refl _⟩ from nativeAssign] at cert
    rcases cert with ⟨o,target,equal,code,finalRepr,stack,keepWrite⟩ | ⟨bad,_⟩
    · cases Except.ok.inj equal
      have codeRun : Evm.run (uintAliasDeleteCode (C := C) b dst index) mm=.ok target 0 := code
      have keepWhole : Evm.Memory.Objects.KeepsAllocator b frame σ base m (σm.withHeap out) target := by
        intro c positive initial
        exact keepWrite c positive (keepAlias c positive initial)
      have finalAlloc := keepWhole cursor hb ha
      have prog : Prog.run σ (.cons (.rebindMem dst (.alias (.var src rfl)))
          (.cons (.deleteMem (.loc (.index .dyn (.var dst rfl) iv)) rfl) .nil))=
          .ok ⟨σm.withHeap out,List.prefix_refl _⟩ := by
        rw [Prog.run_cons_ok aliasNative,Prog.run_cons_ok native,Prog.run_nil]
        rfl
      refine ⟨out,z,target,first,second,source_items_pair_run G Fsrc horizon Γ.length _ _ y mid z firstStmt secondStmt,
        aliasNative,native,prog,write,selected,new,memOK,aliasCode,codeRun,?_,finalRepr,finalAlloc,keepWhole,
        stack.trans stackAlias,finalAlloc.free.cell.trans ha.free.cell.symm,values,locals,?_,rootT,?_,frames,sourceFrames,ex,events,logs,fn⟩
      · rw [Evm.run_append_ok aliasCode,codeRun]
      · rw [locals];exact rootS
      · intro τ i ne
        rw [locals];exact sourceOther i ne
    · cases bad

/-- info: 'Solidity.Backend.MemoryOps.source_uint_alias_delete_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_alias_delete_word
/-- The reached selected capacity rejects deletion after a successful alias.
Only the successful prefix has a machine/relation; the failed program exposes
Source panic bytes and native/word reversion at their own actual boundaries. -/
theorem source_uint_alias_delete_bounds_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
    (y : Source.EMState E Γ) (sdst ssrc : Source.Idx Γ SourceUintArrayTy)
    (si : Source.Idx Γ (.int .u256)) (address : Nat) (k : PrimTy.uint.Denote)
    (hs : y.1.get ssrc=.memRef rfl address) (hsi : y.1.get si=sourceUint k)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    (σ : State C Δ) (dst src : Idx Δ (.mem (.array (.prim .uint)))) (index : Idx Δ (.val .uint))
    (r : HRef σ.H (.array (.prim .uint))) (ht : TEnv.get src σ.env=some r)
    (hti : TEnv.get index σ.env=k) (hr : SourceUintMemoryAt y address σ.heap r .dyn)
    (outside : σ.heap.len r .dyn≤k.1.toNat)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m) (hb : 0<b) :
    let mid : Source.EMState E Γ := (y.1.set sdst (.memRef rfl address),y.2)
    let σm := σ.setLocal dst (some r)
    let mm := Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base r.id))
    (Source.evalE G Fsrc (horizon+4) (sourceLocalAlias sdst ssrc)).run y=
      (.ok (.val (.memRef rfl address)),mid) ∧
    Evm.run (Evm.Memory.aliasLocalCode b dst src) m=.ok mm 0 ∧
    (Source.evalE G Fsrc (horizon+3) (sourceUintIndexedDelete sdst si)).run mid=
      (.error (.revert (Source.panicData .index)),mid) ∧
    (Source.execItems G Fsrc (horizon+6) Γ.length none
      (.stmt (.expr (sourceLocalAlias sdst ssrc)) (.stmt (.expr (sourceUintIndexedDelete sdst si)) .nil) :
        Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.error (.revert (Source.panicData .index)),(.nil,mid.2)) ∧
    Stmt.run σm (.deleteMem (.loc (.index .dyn (.var dst rfl) (.simple (.local index)))) rfl)=.error .revert ∧
    Prog.run σ (.cons (.rebindMem dst (.alias (.var src rfl)))
      (.cons (.deleteMem (.loc (.index .dyn (.var dst rfl) (.simple (.local index)))) rfl) .nil))=.error .revert ∧
    Evm.run (uintAliasDeleteCode (C := C) b dst index) mm=.revert ∧
    Evm.run (Evm.Memory.aliasLocalCode b dst src++uintAliasDeleteCode (C := C) b dst index) m=.revert ∧
    SourceUintMemoryAt mid address σm.heap r .dyn ∧ Source.MemOK E SH mid ∧
    Evm.Memory.Objects.StateRepr L b frame F σm base mm ∧
    Evm.Memory.Objects.AllocatorRepr σm.heap base frame cursor mm ∧
    mm.stack=m.stack ∧ mm.mem 0=m.mem 0 := by
  first
  | solve | simp only [] | omega
  | obtain ⟨first,firstStmt,native,word,new,mok,repr,allocator,keeps,selected,targetSelected,globals,heap,stack,free,sourceOther,targetOther,allObjects,allSource⟩ :=
      source_uint_alias_word G Fsrc (horizon+2) y sdst ssrc address hs SH hmem σ dst src r ht hr hm ha hb
    dsimp only
    let mid : Source.EMState E Γ := (y.1.set sdst (.memRef rfl address),y.2)
    let σm := σ.setLocal dst (some r)
    have sourceNe : sdst.toNat≠si.toNat := by intro same;cases source_idx_type_of_position sdst si same
    have targetNe : dst.toNat≠index.toNat := by
      intro same
      have hd := dst.getElem?_toNat
      rw [same,index.getElem?_toNat] at hd
      cases hd
    have indexSource := (sourceOther si sourceNe).trans hsi
    have indexTarget : TEnv.get index σm.env=k := (targetOther index targetNe).trans hti
    obtain ⟨second,revert⟩ := resolved_uint_delete_word_bounds G Fsrc horizon σm r new sdst si dst index k
      selected indexSource targetSelected indexTarget outside repr.legacy
    have secondStmt := source_expr_statement_error G Fsrc (horizon+3) Γ.length _ mid mid _ second
    have targetRoot : TEnv.get dst σm.env=some r := targetSelected
    have noWrite : σm.heap.writeAddr (.index r .dyn k) (PrimTy.dflt .uint)=none := by
      simp only [Heap.writeAddr,Heap.setIndex,show ¬k.1.toNat<(MObj.elems .dyn (σm.heap.get r)).length from Nat.not_lt.mpr outside,↓reduceIte]
    have invalid : Stmt.run σm (.deleteMem (.loc (.index .dyn (.var dst rfl) (.simple (.local index)))) rfl)=.error .revert := by
      change TRun.deleteMem (.loc (.index .dyn (.var dst rfl) (.simple (.local index)))) σm=_
      simp only [TRun.deleteMem,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,targetRoot,indexTarget,
        bind,Except.bind,pure,Except.pure,TRun.clearT,noWrite,TRes.ofOpt]
    refine ⟨first,word,second,source_items_pair_error G Fsrc horizon Γ.length _ _ y mid mid _ firstStmt secondStmt,
      invalid,?_,revert,?_,new,mok,repr,allocator,stack,free⟩
    · have tail : Prog.run σm (.cons (.deleteMem (.loc (.index .dyn (.var dst rfl) (.simple (.local index)))) rfl) .nil)=.error .revert := by
        change TRun.seq _ _ σm=_
        change TRun.deleteMem (.loc (.index .dyn (.var dst rfl) (.simple (.local index)))) σm=.error .revert at invalid
        simp only [TRun.seq]
        rw [invalid]
      rw [Prog.run_cons_ok native,tail]
      rfl
    · rw [Evm.run_append_ok word]
      exact revert

/-- info: 'Solidity.Backend.MemoryOps.source_uint_alias_delete_bounds_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_alias_delete_bounds_word
end Solidity.Backend.MemoryOps
