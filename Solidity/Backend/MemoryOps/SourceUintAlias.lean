import Solidity.Backend.MemoryOps.SourceCalldataUintBinding
import Solidity.Evm.MemoryObjectStatements

/-! Actual dynamic uint reference rebinding with initial Source contents and
strong Objects representation. No constructor, pointer compiler, copy algorithm
or new semantics is introduced. Array capacities may differ at runtime. -/
namespace Solidity.Backend.MemoryOps

/-- Initial contents accompany the same actual Source/native pointer through
rebinding. Strong Objects/allocator facts and complete old-object frames are
retained; this is aliasing an existing object, not copying or allocation. -/
theorem source_uint_alias_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
    (y : Source.EMState E Γ) (sdst ssrc : Source.Idx Γ SourceUintArrayTy)
    (address : Nat) (hs : y.1.get ssrc=.memRef rfl address) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    (σ : State C Δ) (dst src : Idx Δ (.mem (.array (.prim .uint))))
    (r : HRef σ.H (.array (.prim .uint))) (ht : TEnv.get src σ.env=some r)
    (hr : SourceUintMemoryAt y address σ.heap r .dyn)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m) (hb : 0<b) :
    let z : Source.EMState E Γ := (y.1.set sdst (.memRef rfl address),y.2)
    let σ' := σ.setLocal dst (some r)
    let m' := Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base r.id))
    (Source.evalE G Fsrc (horizon+2) (sourceLocalAlias sdst ssrc)).run y=(.ok (.val (.memRef rfl address)),z) ∧
    (Source.execS G Fsrc (horizon+3) Γ.length none
      (.expr (sourceLocalAlias sdst ssrc) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
    Stmt.run σ (.rebindMem dst (.alias (.var src rfl)))=.ok ⟨σ',List.prefix_refl _⟩ ∧
    Evm.run (Evm.Memory.aliasLocalCode b dst src) m=.ok m' 0 ∧
    SourceUintMemoryAt z address σ'.heap r .dyn ∧ Source.MemOK E SH z ∧
    Evm.Memory.Objects.StateRepr L b frame F σ' base m' ∧
    Evm.Memory.Objects.AllocatorRepr σ'.heap base frame cursor m' ∧
    Evm.Memory.Objects.KeepsAllocator b frame σ base m σ' m' ∧
    z.1.get sdst=.memRef rfl address ∧ TEnv.get dst σ'.env=some r ∧
    z.2=y.2 ∧ σ'.heap=σ.heap ∧ m'.stack=m.stack ∧ m'.mem 0=m.mem 0 ∧
    (∀ {τ : Source.STy} (q : Source.Idx Γ τ),sdst.toNat≠q.toNat → z.1.get q=y.1.get q) ∧
    (∀ {t : LTy} (q : Idx Δ t),dst.toNat≠q.toNat → TEnv.get q σ'.env=TEnv.get q σ.env) ∧
    (∀ {Q : RefTy} (q : HRef σ.H Q),σ'.heap.get q=σ.heap.get q) ∧
    (∀ a,z.2.heap.get a=y.2.heap.get a) := by
  first
  | solve | rfl | simp only [] | omega
  | dsimp only
    have he := source_local_alias_run G Fsrc horizon y sdst ssrc (.memRef rfl address) hs
    have hsstmt := source_expr_statement_run G Fsrc (horizon+2) Γ.length _ y
      (y.1.set sdst (.memRef rfl address),y.2) (.val (.memRef rfl address)) he
    have hmk := source_local_alias_memOK Fsrc (horizon+1) y sdst ssrc SH hmem
    rw [hs] at hmk
    have hi : TRun.rebindMem dst (.alias (.var src rfl)) σ=.ok ⟨σ.setLocal dst (some r),List.prefix_refl _⟩ := by
      simp only [TRun.rebindMem,MRhs.evalT,MPath.mvalT,ht,bind,Except.bind,pure,Except.pure]
    have cert := Evm.Memory.Objects.PtrFrag.rebind hm (.local src rfl) dst
    unfold Evm.Memory.Objects.ResultRepr at cert
    rw [hi] at cert
    obtain ⟨q,hq,hptr⟩ := hm.pointers src
    have hqr : q=r := Option.some.inj (hq.symm.trans ht)
    subst q
    have hcode : Evm.run (Evm.Memory.aliasLocalCode b dst src) m=
        .ok (Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base r.id))) 0 := by
      simp only [Evm.run,Evm.Memory.aliasLocalCode,Evm.exec_cons_zero,Evm.Instr.step,Evm.Machine.next,
        Evm.Out.ok_bind,hptr,Evm.exec_nil,Evm.Memory.writeMachine]
    rcases cert with ⟨o,target,ho,hc,hm',hstack,halloc⟩ | ⟨hbad,_⟩
    · cases Except.ok.inj ho
      have htgt : target=Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base r.id)) := (Evm.Out.ok.inj (hc.symm.trans hcode)).1
      subst target
      have ha' := halloc cursor hb ha
      refine ⟨he,hsstmt,hi,hcode,hr,hmk,hm',ha',halloc,source_locals_get_set _ _ _,TEnv.get_set _ _ _,rfl,rfl,rfl,
        ha'.free.cell.trans ha.free.cell.symm,?_,?_,fun _ => rfl,fun _ => rfl⟩
      · intro τ q hn
        exact source_locals_get_set_other y.1 sdst q _ hn
      · intro t q hn
        exact TEnv.get_set_ne dst q _ σ.env hn
    · cases hbad

/-- Rebinding to a different-capacity existing array derives the suffix
bounds failure at the reached pointer. Actual Source Items and whole existing
word append reject; only the successful alias prefix has a machine result. -/
theorem source_uint_alias_read_bounds_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
    (y : Source.EMState E Γ) (sdst ssrc : Source.Idx Γ SourceUintArrayTy)
    (si : Source.Idx Γ (.int .u256)) (address : Nat) (k : PrimTy.uint.Denote)
    (hs : y.1.get ssrc=.memRef rfl address) (hsi : y.1.get si=sourceUint k)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    (σ : State C Δ) (dst src : Idx Δ (.mem (.array (.prim .uint)))) (index : Idx Δ (.val .uint))
    (r : HRef σ.H (.array (.prim .uint))) (ht : TEnv.get src σ.env=some r) (hti : TEnv.get index σ.env=k)
    (hr : SourceUintMemoryAt y address σ.heap r .dyn) (outside : σ.heap.len r .dyn≤k.1.toNat)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m) (hb : 0<b)
    (hin : Evm.valIn F (.simple (.local index) : Val C Δ .uint)=true) :
    let z : Source.EMState E Γ := (y.1.set sdst (.memRef rfl address),y.2)
    let σ' := σ.setLocal dst (some r)
    let m' := Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base r.id))
    (Source.evalE G Fsrc (horizon+4) (sourceLocalAlias sdst ssrc)).run y=(.ok (.val (.memRef rfl address)),z) ∧
    Stmt.run σ (.rebindMem dst (.alias (.var src rfl)))=.ok ⟨σ',List.prefix_refl _⟩ ∧
    Evm.run (Evm.Memory.aliasLocalCode b dst src) m=.ok m' 0 ∧
    (Source.evalE G Fsrc (horizon+3) (.indexArray (.local sdst) (.local si) rfl)).run z=
      (.error (.revert (Source.panicData .index)),z) ∧
    (Source.execItems G Fsrc (horizon+6) Γ.length none
      (.stmt (.expr (sourceLocalAlias sdst ssrc))
        (.stmt (.expr (.indexArray (.local sdst) (.local si) rfl)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.error (.revert (Source.panicData .index)),(.nil,z.2)) ∧
    (Val.readMem (.index .dyn (.var dst rfl) (.simple (.local index))) : Val C Δ .uint).evalT σ'=.error .revert ∧
    Evm.run (Evm.Memory.readLocalCode b dst (.simple (.local index) : Val C Δ .uint)) m'=.revert ∧
    Evm.run (Evm.Memory.aliasLocalCode b dst src++Evm.Memory.readLocalCode b dst (.simple (.local index) : Val C Δ .uint)) m=.revert ∧
    SourceUintMemoryAt z address σ'.heap r .dyn ∧ Source.MemOK E SH z ∧
    Evm.Memory.Objects.StateRepr L b frame F σ' base m' ∧
    Evm.Memory.Objects.AllocatorRepr σ'.heap base frame cursor m' ∧
    Evm.Memory.Objects.KeepsAllocator b frame σ base m σ' m' ∧
    z.2=y.2 ∧ σ'.heap=σ.heap ∧ m'.stack=m.stack ∧ m'.mem 0=m.mem 0 := by
  first
  | solve | simp only [] | omega
  | have aliasRun := source_uint_alias_word G Fsrc (horizon+2) y sdst ssrc address hs SH hmem σ dst src r ht hr hm ha hb
    obtain ⟨first,firstStmt,native,word,new,mok,repr,allocator,keeps,selected,targetSelected,globals,heap,stack,free,sourceOther,targetOther,allObjects,allSource⟩ := aliasRun
    dsimp only
    let z : Source.EMState E Γ := (y.1.set sdst (.memRef rfl address),y.2)
    let σ' := σ.setLocal dst (some r)
    let m' := Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base r.id))
    have sourceNe : sdst.toNat≠si.toNat := by
      intro same
      cases source_idx_type_of_position sdst si same
    have indexSource := (sourceOther si sourceNe).trans hsi
    have second := new.eval_read_bounds G Fsrc (horizon+1) sdst si k selected indexSource outside
    have secondStmt := source_expr_statement_error G Fsrc (horizon+3) Γ.length _ z z _ second
    have targetNe : dst.toNat≠index.toNat := by
      intro same
      have hd := dst.getElem?_toNat
      rw [same,index.getElem?_toNat] at hd
      cases hd
    have indexTarget : TEnv.get index σ'.env=k := (targetOther index targetNe).trans hti
    have readNone : σ'.heap.readAddr (.index r .dyn k)=none := List.getElem?_eq_none outside
    have targetRoot : TEnv.get dst σ'.env=some r := targetSelected
    have invalid : (Val.readMem (.index .dyn (.var dst rfl) (.simple (.local index))) : Val C Δ .uint).evalT σ'=.error .revert := by
      simp only [Val.evalT,MLoc.addrT,MPath.mvalT,Simple.evalT,indexTarget,targetRoot,readNone,
        TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have cert := Evm.Memory.Objects.PtrFrag.readPrimitive repr
      (Evm.Memory.Objects.PtrFrag.local dst rfl) (.dyn : ArrTy (.array (.prim .uint)) (.prim .uint))
      (.simple (.local index) : Val C Δ .uint) hin
    have readCode : Evm.run (Evm.Memory.readLocalCode b dst (.simple (.local index) : Val C Δ .uint)) m'=.revert := by
      change Evm.ValOutT .uint _ (Evm.run (Evm.Memory.readLocalCode b dst (.simple (.local index) : Val C Δ .uint)) m') m' at cert
      rw [invalid] at cert
      rcases cert with ⟨v,w,bad,_⟩ | ⟨_,revert⟩
      · cases bad
      · exact revert
    refine ⟨first,native,word,second,source_items_pair_error G Fsrc horizon Γ.length _ _ y z z _ firstStmt secondStmt,
      invalid,readCode,?_,new,mok,repr,allocator,keeps,globals,heap,stack,free⟩
    rw [Evm.run_append_ok word,readCode]

/-- info: 'Solidity.Backend.MemoryOps.source_uint_alias_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_alias_word
/-- info: 'Solidity.Backend.MemoryOps.source_uint_alias_read_bounds_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_alias_read_bounds_word
end Solidity.Backend.MemoryOps
