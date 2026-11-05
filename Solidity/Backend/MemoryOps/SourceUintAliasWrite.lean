import Solidity.Backend.MemoryOps.SourceUintAlias
import Solidity.Backend.MemoryOps.SourceCalldataUintMutation

/-! Dynamic alias followed by an actual primitive write. Existing strong
Objects pointer/value write certificates supply the whole word sequence;
no replacement allocator, path compiler, semantics or target relation. -/
namespace Solidity.Backend.MemoryOps

/-- Literal program of the published strong pointer/value write certificate. -/
def uintAliasWriteCode {C : Contract} {Δ : Ctx} (b : Nat)
    (dst : Idx Δ (.mem (.array (.prim .uint)))) (index rhs : Idx Δ (.val .uint)) : List Evm.Instr :=
  Evm.compileVal b (.simple (.local rhs) : Val C Δ .uint) ++ [.mload (Evm.cellOf b dst)] ++
    Evm.compileVal b (.simple (.local index) : Val C Δ .uint) ++
    Evm.Memory.Objects.writeCode (.dyn : ArrTy (.array (.prim .uint)) (.prim .uint))

/-- All suffix premises follow the actual alias certificate and INITIAL
bounds/scalars/contents. The changed native and Source heap are the same
ones consumed by the strong target write, not independent successful runs. -/
theorem source_uint_alias_assign_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
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
    let mid : Source.EMState E Γ := (y.1.set sdst (.memRef rfl address),y.2)
    let σm := σ.setLocal dst (some r)
    let mm := Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base r.id))
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      (Source.evalE G Fsrc (horizon+4) (sourceLocalAlias sdst ssrc)).run y=(.ok (.val (.memRef rfl address)),mid) ∧
      (Source.evalE G Fsrc (horizon+3) (sourceUintIndexedAssign sdst si sv)).run mid=(.ok (.val (sourceUint value)),z) ∧
      (Source.execItems G Fsrc (horizon+6) Γ.length none
        (.stmt (.expr (sourceLocalAlias sdst ssrc))
          (.stmt (.expr (sourceUintIndexedAssign sdst si sv)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
      Stmt.run σ (.rebindMem dst (.alias (.var src rfl)))=.ok ⟨σm,List.prefix_refl _⟩ ∧
      Stmt.run σm (.assignMem (.index .dyn (.var dst rfl) (.simple (.local index))) (.val (.simple (.local rhs))))=
        .ok ⟨σm.withHeap out,List.prefix_refl _⟩ ∧
      Prog.run σ (.cons (.rebindMem dst (.alias (.var src rfl)))
        (.cons (.assignMem (.index .dyn (.var dst rfl) (.simple (.local index))) (.val (.simple (.local rhs)))) .nil))=
        .ok ⟨σm.withHeap out,List.prefix_refl _⟩ ∧
      σ.heap.writeAddr (.index r .dyn k) value=some out ∧
      SourceUintMemoryAt mid address σm.heap r .dyn ∧ SourceUintMemoryAt z address out r .dyn ∧
      Source.MemOK E SH z ∧
      Evm.run (Evm.Memory.aliasLocalCode b dst src) m=.ok mm 0 ∧
      Evm.run (uintAliasWriteCode (C := C) b dst index rhs) mm=.ok target 0 ∧
      Evm.run (Evm.Memory.aliasLocalCode b dst src++uintAliasWriteCode (C := C) b dst index rhs) m=.ok target 0 ∧
      Evm.Memory.Objects.StateRepr L b frame F (σm.withHeap out) base target ∧
      Evm.Memory.Objects.AllocatorRepr out base frame cursor target ∧
      Evm.Memory.Objects.KeepsAllocator b frame σ base m (σm.withHeap out) target ∧
      target.stack=m.stack ∧ target.mem 0=m.mem 0 ∧
      MObj.elems .dyn (out.get r)=(MObj.elems .dyn (σ.heap.get r)).set k.1.toNat value ∧
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
    have valueS : mid.1.get sv=sourceUint value := (sourceOther sv (sourceNe sv)).trans hsv
    have indexT : TEnv.get index σm.env=k := (targetOther index (targetNe index)).trans hti
    have valueT : TEnv.get rhs σm.env=value := (targetOther rhs (targetNe rhs)).trans htv
    have rootTarget : TEnv.get dst σm.env=some r := rootT
    obtain ⟨out,z,write,sourceWrite,new,memOK,values,frames,sourceFrames,locals,ex,events,logs,fn⟩ :=
      selected.write_observed Fsrc (horizon+2) k value hk SH mok
    have second := selected.eval_assign_of_run G Fsrc horizon sdst si sv k value rootS indexS valueS hk sourceWrite
    have secondStmt := source_expr_statement_run G Fsrc (horizon+3) Γ.length _ mid z _ second
    have nativeWrite : σm.heap.writeAddr (.index r .dyn k) value=some out := write
    have native : Stmt.run σm (.assignMem (.index .dyn (.var dst rfl) (.simple (.local index))) (.val (.simple (.local rhs))))=
        .ok ⟨σm.withHeap out,List.prefix_refl _⟩ := by
      change TRun.assignMem (.index .dyn (.var dst rfl) (.simple (.local index))) (.val (.simple (.local rhs))) σm=_
      simp only [TRun.assignMem,MLoc.addrT,MSrc.mvalT,MPath.mvalT,Simple.evalT,Val.evalT,
        rootTarget,indexT,valueT,nativeWrite,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    let iv : Val C Δ .uint := .simple (.local index)
    let rv : Val C Δ .uint := .simple (.local rhs)
    have pointer : Evm.Memory.Objects.PtrFrag (C := C) b F (.var dst rfl) [.mload (Evm.cellOf b dst)] := .local dst rfl
    have valueCode : Evm.Memory.Objects.SrcFrag b F (.val rv) (Evm.compileVal b rv) := .val rv _ (.core rv hvalue)
    have cert := Evm.Memory.Objects.PtrFrag.write repr (.dyn : ArrTy (.array (.prim .uint)) (.prim .uint)) pointer valueCode iv hindex
    unfold Evm.Memory.Objects.ResultRepr at cert
    rw [show TRun.assignMem (.index .dyn (.var dst rfl) iv) (.val rv) σm=.ok ⟨σm.withHeap out,List.prefix_refl _⟩ from native] at cert
    rcases cert with ⟨o,target,equal,code,finalRepr,stack,keepWrite⟩ | ⟨bad,_⟩
    · cases Except.ok.inj equal
      have codeRun : Evm.run (uintAliasWriteCode (C := C) b dst index rhs) mm=.ok target 0 := code
      have keepWhole : Evm.Memory.Objects.KeepsAllocator b frame σ base m (σm.withHeap out) target := by
        intro c positive initial
        exact keepWrite c positive (keepAlias c positive initial)
      have finalAlloc := keepWhole cursor hb ha
      have prog : Prog.run σ (.cons (.rebindMem dst (.alias (.var src rfl)))
          (.cons (.assignMem (.index .dyn (.var dst rfl) iv) (.val rv)) .nil))=
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

/-- info: 'Solidity.Backend.MemoryOps.source_uint_alias_assign_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_alias_assign_word
end Solidity.Backend.MemoryOps
