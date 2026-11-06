import Solidity.Backend.MemoryOps.SourceUintFixedRefsTarget
import Solidity.Evm.MemoryDelete

/-! Actual primitive delete through a fixed child and the published default
word/pointer/index/store program, with strong representation and allocator frames. -/
namespace Solidity.Backend.MemoryOps

def uintFixedChildDeleteCode {C : Contract} {Δ : Ctx} {n : Nat} (b : Nat)
    (root : Idx Δ (.mem (UintFixedRefsRef n))) (i j : Idx Δ (.val .uint)) : List Evm.Instr :=
  Evm.compileVal b (Evm.Memory.deleteDefaultValue .uint : Val C Δ .uint) ++
    ([.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local i) : Val C Δ .uint) ++ Evm.Memory.Objects.readCode (.dyn : ArrTy (UintFixedRefsRef n) (.ref (.fixed (.prim .uint) n)))) ++
    Evm.compileVal b (.simple (.local j) : Val C Δ .uint) ++ Evm.Memory.Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))

theorem SourceUintFixedRefsAt.resolved_delete_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} (G : Source.Glob E) (Fs : Source.Fr) (horizon nps : Nat)
    (σ : State C Δ) (r : HRef σ.H (UintFixedRefsRef n)) (address : Nat → Nat)
    (hr : SourceUintFixedRefsAt y a σ.heap r address)
    (sr : Source.Idx Γ (SourceUintFixedRefsTy n)) (si sj : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (UintFixedRefsRef n))) (i j : Idx Δ (.val .uint))
    (k l : PrimTy.uint.Denote) (q : HRef σ.H (.fixed (.prim .uint) n))
    (hsr : y.1.get sr=.memRef rfl a) (hsi : y.1.get si=sourceUint k) (hsj : y.1.get sj=sourceUint l)
    (htr : TEnv.get root σ.env=some r) (hti : TEnv.get i σ.env=k) (htj : TEnv.get j σ.env=l)
    (hq : σ.heap.index r .dyn k=some q)
    (separate : ∀ t∈MObj.elems .dyn (σ.heap.get r),t.id≠q.id → address t.id≠address q.id)
    (hl : l.1.toNat<n) (SH : Source.HeapTy) (memOK : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m) :
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      σ.heap.writeAddr (.index q .fixed l) (PrimTy.dflt .uint)=some out ∧
      (Source.evalE G Fs (horizon+4) (sourceUintFixedNestedDelete sr si sj)).run y=(.ok Source.RVal.unit,z) ∧
      (Source.execS G Fs (horizon+5) nps none
        (.expr (sourceUintFixedNestedDelete sr si sj) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      Stmt.run σ (.deleteMem (.loc (.index .fixed (uintFixedChildPath root i) (.simple (.local j)))) rfl)=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (uintFixedChildDeleteCode (C := C) b root i j) m=.ok target 0 ∧
      SourceUintFixedRefsAt z a out r address ∧ Source.MemOK E SH z ∧
      Evm.Memory.Objects.StateRepr L b frame F (σ.withHeap out) base target ∧
      z.1=y.1 ∧ z.2.heap.next=y.2.heap.next ∧ out.get r=σ.heap.get r ∧
      (∀ {Q : RefTy} (t : HRef σ.H Q),q.id≠t.id → out.get t=σ.heap.get t) ∧
      (∀ d,d≠address q.id → z.2.heap.get d=y.2.heap.get d) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals ∧
      target.stack=m.stack ∧ Evm.Memory.Objects.KeepsAllocator b frame σ base m (σ.withHeap out) target := by
  first
  | solve | simp only [] | omega
  | obtain ⟨out,z,typed,expr,stmt,reached,preserved,locals,next,parent,objects,addresses,world,events,logs,fnLocals⟩ :=
      hr.resolved_delete G Fs horizon nps sr si sj k l q hsr hsi hsj hq separate hl SH memOK
    have selected : (uintFixedChildPath (C := C) root i).mvalT σ=.ok q := by
      simp only [uintFixedChildPath,MPath.mvalT,MLoc.addrT,Val.evalT,Simple.evalT,htr,hti,
        Heap.readAddr,hq,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have intrinsic : TRun.assignMem (.index .fixed (uintFixedChildPath root i) (.simple (.local j))) (.val (Evm.Memory.deleteDefaultValue .uint)) σ=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
      simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,selected,Evm.Memory.deleteDefaultValue_eval,Val.evalT,Simple.evalT,htj,
        typed,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have clear : Stmt.run σ (.deleteMem (.loc (.index .fixed (uintFixedChildPath root i) (.simple (.local j)))) rfl)=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
      change TRun.deleteMem (.loc (.index .fixed (uintFixedChildPath root i) (.simple (.local j)))) σ=_
      rw [Evm.Memory.deleteMem_primitive_eq_assign]
      exact intrinsic
    have pointer : Evm.Memory.Objects.PtrFrag b F (uintFixedChildPath (C := C) root i)
        ([.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local i) : Val C Δ .uint) ++ Evm.Memory.Objects.readCode (.dyn : ArrTy (UintFixedRefsRef n) (.ref (.fixed (.prim .uint) n)))) :=
      .index .dyn _ _ (.local root rfl) (.simple (.local i)) rfl
    have code := Evm.Memory.Objects.PtrFrag.write hm (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))
      pointer (.val _ _ (.core (Evm.Memory.deleteDefaultValue .uint) rfl)) (.simple (.local j)) rfl
    unfold Evm.Memory.Objects.ResultRepr at code
    rw [intrinsic] at code
    rcases code with ⟨o,target,eq,run,representation,stack,allocator⟩ | ⟨bad,_⟩
    · cases Except.ok.inj eq
      exact ⟨out,z,target,typed,expr,stmt,clear,run,reached,preserved,representation,
        locals,next,parent,objects,addresses,world,events,logs,fnLocals,stack,allocator⟩
    · cases bad

theorem SourceUintFixedRefsAt.resolved_write_delete_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} (G : Source.Glob E) (Fs : Source.Fr) (horizon nps : Nat)
    (σ : State C Δ) (r : HRef σ.H (UintFixedRefsRef n)) (address : Nat → Nat)
    (hr : SourceUintFixedRefsAt y a σ.heap r address)
    (sr : Source.Idx Γ (SourceUintFixedRefsTy n)) (si sj sv : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (UintFixedRefsRef n))) (i j rhs : Idx Δ (.val .uint))
    (k l v : PrimTy.uint.Denote) (q : HRef σ.H (.fixed (.prim .uint) n))
    (hsr : y.1.get sr=.memRef rfl a) (hsi : y.1.get si=sourceUint k) (hsj : y.1.get sj=sourceUint l) (hsv : y.1.get sv=sourceUint v)
    (htr : TEnv.get root σ.env=some r) (hti : TEnv.get i σ.env=k) (htj : TEnv.get j σ.env=l) (htv : TEnv.get rhs σ.env=v)
    (hq : σ.heap.index r .dyn k=some q)
    (separate : ∀ t∈MObj.elems .dyn (σ.heap.get r),t.id≠q.id → address t.id≠address q.id)
    (hk : k.1.toNat<n) (hl : l.1.toNat<n) (SH : Source.HeapTy) (memOK : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m) :
    ∃ (mid out : Heap σ.H) (ym z : Source.EMState E Γ) (mm target : Evm.Machine),
      σ.heap.writeAddr (.index q .fixed k) v=some mid ∧
      mid.writeAddr (.index q .fixed l) (PrimTy.dflt .uint)=some out ∧
      (Source.execS G Fs (horizon+6) nps none
        (.expr (sourceUintFixedNestedAssign sr si si sv) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS G Fs (horizon+5) nps none
        (.expr (sourceUintFixedNestedDelete sr si sj) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems G Fs (horizon+7) nps none
        (.stmt (.expr (sourceUintFixedNestedAssign sr si si sv))
          (.stmt (.expr (sourceUintFixedNestedDelete sr si sj)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run σ (.cons (.assignMem (.index .fixed (uintFixedChildPath root i) (.simple (.local i))) (.val (.simple (.local rhs))))
        (.cons (.deleteMem (.loc (.index .fixed (uintFixedChildPath root i) (.simple (.local j)))) rfl) .nil))=
          .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (uintFixedChildWriteCode (C := C) b root i i rhs) m=.ok mm 0 ∧
      Evm.run (uintFixedChildDeleteCode (C := C) b root i j) mm=.ok target 0 ∧
      Evm.run (uintFixedChildWriteCode (C := C) b root i i rhs ++ uintFixedChildDeleteCode (C := C) b root i j) m=.ok target 0 ∧
      SourceUintFixedRefsAt ym a mid r address ∧ SourceUintFixedRefsAt z a out r address ∧
      Source.MemOK E SH ym ∧ Source.MemOK E SH z ∧
      Evm.Memory.Objects.StateRepr L b frame F (σ.withHeap mid) base mm ∧
      Evm.Memory.Objects.StateRepr L b frame F (σ.withHeap out) base target ∧
      ym.1=y.1 ∧ z.1=y.1 ∧ z.2.heap.next=y.2.heap.next ∧ out.get r=σ.heap.get r ∧
      (∀ {Q : RefTy} (t : HRef σ.H Q),q.id≠t.id → out.get t=σ.heap.get t) ∧
      (∀ d,d≠address q.id → z.2.heap.get d=y.2.heap.get d) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals ∧
      target.stack=m.stack ∧ Evm.Memory.Objects.KeepsAllocator b frame σ base m (σ.withHeap out) target := by
  first
  | solve | simp only [] | omega
  | obtain ⟨mid,ym,mm,tw,ew,sw,iw,cw,rm,mok,hm',locals,next,parent,objects,addresses,world,events,logs,fnLocals,stack,allocator⟩ :=
      hr.resolved_write_word G Fs (horizon+1) nps σ r address sr si si sv root i i rhs k k v q
        hsr hsi hsi hsv htr hti hti htv hq separate hk SH memOK hm
    have selected : mid.index r .dyn k=some q := by
      change (MObj.elems .dyn (mid.get r))[k.1.toNat]?=some q
      rw [parent];exact hq
    have middleSeparate : ∀ t∈MObj.elems .dyn (mid.get r),t.id≠q.id → address t.id≠address q.id := by
      rw [parent];exact separate
    obtain ⟨out,z,target,td,ed,sd,id,cd,rz,mokz,hz,lz,nz,pz,oz,az,wz,ez,lgz,fz,sz,allocz⟩ :=
      rm.resolved_delete_word G Fs horizon nps (σ.withHeap mid) r address sr si sj root i j k l q
        (by rw [locals];exact hsr) (by rw [locals];exact hsi) (by rw [locals];exact hsj)
        htr hti htj selected middleSeparate hl SH mok hm'
    refine ⟨mid,out,ym,z,mm,target,tw,td,sw,sd,source_items_pair_run G Fs (horizon+1) nps _ _ y ym z sw sd,
      intrinsic_heap_pair_run σ _ _ mid out iw id,cw,cd,?_,rm,rz,mok,mokz,hm',hz,locals,lz.trans locals,
      nz.trans next,pz.trans parent,fun t ht => (oz t ht).trans (objects t ht),
      fun d hd => (az d hd).trans (addresses d hd),wz.trans world,ez.trans events,lgz.trans logs,fz.trans fnLocals,
      sz.trans stack,?_⟩
    · rw [Evm.run_append_ok cw];exact cd
    · intro cursor hb ha
      exact allocz cursor hb (allocator cursor hb ha)


/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.resolved_delete_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.resolved_delete_word
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.resolved_write_delete_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.resolved_write_delete_word
end Solidity.Backend.MemoryOps
