import Solidity.Backend.MemoryOps.SourceUintFixedRefsDelete

/-! Actual nested fixed-child stores using the published Objects pointer/store
certificate. Initial Source and target alignment, not a desired poststate. -/
namespace Solidity.Backend.MemoryOps

def uintFixedChildPath {C : Contract} {Δ : Ctx} {n : Nat}
    (root : Idx Δ (.mem (UintFixedRefsRef n))) (i : Idx Δ (.val .uint)) :
    MPath C Δ (.ref (.fixed (.prim .uint) n)) :=
  .loc (.index .dyn (.var root rfl) (.simple (.local i)))

def uintFixedChildWriteCode {C : Contract} {Δ : Ctx} {n : Nat} (b : Nat)
    (root : Idx Δ (.mem (UintFixedRefsRef n))) (i j rhs : Idx Δ (.val .uint)) : List Evm.Instr :=
  Evm.compileVal b (.simple (.local rhs) : Val C Δ .uint) ++
    ([.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local i) : Val C Δ .uint) ++ Evm.Memory.Objects.readCode (.dyn : ArrTy (UintFixedRefsRef n) (.ref (.fixed (.prim .uint) n)))) ++
    Evm.compileVal b (.simple (.local j) : Val C Δ .uint) ++ Evm.Memory.Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))

theorem SourceUintFixedRefsAt.resolved_write_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {n : Nat}
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
    (hl : l.1.toNat<n) (SH : Source.HeapTy) (memOK : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m) :
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      σ.heap.writeAddr (.index q .fixed l) v=some out ∧
      (Source.evalE G Fs (horizon+4) (sourceUintFixedNestedAssign sr si sj sv)).run y=(.ok (.val (sourceUint v)),z) ∧
      (Source.execS G Fs (horizon+5) nps none
        (.expr (sourceUintFixedNestedAssign sr si sj sv) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      Stmt.run σ (.assignMem (.index .fixed (uintFixedChildPath root i) (.simple (.local j))) (.val (.simple (.local rhs))))=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (uintFixedChildWriteCode (C := C) b root i j rhs) m=.ok target 0 ∧
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
      hr.resolved_write G Fs horizon nps sr si sj sv k l v q hsr hsi hsj hsv hq separate hl SH memOK
    have selected : (uintFixedChildPath (C := C) root i).mvalT σ=.ok q := by
      simp only [uintFixedChildPath,MPath.mvalT,MLoc.addrT,Val.evalT,Simple.evalT,htr,hti,
        Heap.readAddr,hq,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have intrinsic : TRun.assignMem (.index .fixed (uintFixedChildPath root i) (.simple (.local j))) (.val (.simple (.local rhs))) σ=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
      simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,selected,Val.evalT,Simple.evalT,htj,htv,
        typed,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have pointer : Evm.Memory.Objects.PtrFrag b F (uintFixedChildPath (C := C) root i)
        ([.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local i) : Val C Δ .uint) ++ Evm.Memory.Objects.readCode (.dyn : ArrTy (UintFixedRefsRef n) (.ref (.fixed (.prim .uint) n)))) :=
      .index .dyn _ _ (.local root rfl) (.simple (.local i)) rfl
    have code := Evm.Memory.Objects.PtrFrag.write hm (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))
      pointer (.val _ _ (.core (.simple (.local rhs)) rfl)) (.simple (.local j)) rfl
    unfold Evm.Memory.Objects.ResultRepr at code
    rw [intrinsic] at code
    rcases code with ⟨o,target,eq,run,representation,stack,allocator⟩ | ⟨bad,_⟩
    · cases Except.ok.inj eq
      exact ⟨out,z,target,typed,expr,stmt,intrinsic,run,reached,preserved,representation,
        locals,next,parent,objects,addresses,world,events,logs,fnLocals,stack,allocator⟩
    · cases bad

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.resolved_write_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.resolved_write_word
end Solidity.Backend.MemoryOps
