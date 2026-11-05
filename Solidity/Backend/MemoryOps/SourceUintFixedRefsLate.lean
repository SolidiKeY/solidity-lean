import Solidity.Backend.MemoryOps.SourceUintFixedRefsBounds

/-! Actual successful nested-word prefix and reached late bounds failure, with
Source/Prog/word append execution links and no post-revert machine. -/
namespace Solidity.Backend.MemoryOps

theorem SourceUintFixedRefsAt.resolved_write_late_bounds_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {n : Nat}
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
    (hk : k.1.toNat<n) (hl : n≤l.1.toNat) (SH : Source.HeapTy) (memOK : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m) :
    ∃ (mid : Heap σ.H) (ym : Source.EMState E Γ) (mm : Evm.Machine),
      σ.heap.writeAddr (.index q .fixed k) v=some mid ∧
      (Source.execS G Fs (horizon+6) nps none
        (.expr (sourceUintFixedNestedAssign sr si si sv) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.evalE G Fs (horizon+4) (sourceUintFixedNestedAssign sr si sj sv)).run ym=
        (.error (.revert (Source.panicData .index)),ym) ∧
      (Source.execItems G Fs (horizon+7) nps none
        (.stmt (.expr (sourceUintFixedNestedAssign sr si si sv))
          (.stmt (.expr (sourceUintFixedNestedAssign sr si sj sv)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      Stmt.run σ (.assignMem (.index .fixed (uintFixedChildPath root i) (.simple (.local i))) (.val (.simple (.local rhs))))=
        .ok ⟨σ.withHeap mid,List.prefix_refl _⟩ ∧
      Stmt.run (σ.withHeap mid) (.assignMem (.index .fixed (uintFixedChildPath root i) (.simple (.local j))) (.val (.simple (.local rhs))))=.error .revert ∧
      Prog.run σ (.cons (.assignMem (.index .fixed (uintFixedChildPath root i) (.simple (.local i))) (.val (.simple (.local rhs))))
        (.cons (.assignMem (.index .fixed (uintFixedChildPath root i) (.simple (.local j))) (.val (.simple (.local rhs)))) .nil))=.error .revert ∧
      Evm.run (uintFixedChildWriteCode (C := C) b root i i rhs) m=.ok mm 0 ∧
      Evm.run (uintFixedChildWriteCode (C := C) b root i j rhs) mm=.revert ∧
      Evm.run (uintFixedChildWriteCode (C := C) b root i i rhs ++ uintFixedChildWriteCode (C := C) b root i j rhs) m=.revert ∧
      SourceUintFixedRefsAt ym a mid r address ∧ Source.MemOK E SH ym ∧
      Evm.Memory.Objects.StateRepr L b frame F (σ.withHeap mid) base mm ∧
      ym.1=y.1 ∧ ym.2.heap.next=y.2.heap.next ∧ mid.get r=σ.heap.get r ∧
      (∀ {Q : RefTy} (t : HRef σ.H Q),q.id≠t.id → mid.get t=σ.heap.get t) ∧
      (∀ d,d≠address q.id → ym.2.heap.get d=y.2.heap.get d) ∧
      ym.2.ex=y.2.ex ∧ ym.2.events=y.2.events ∧ ym.2.logs=y.2.logs ∧ ym.2.fnLocals=y.2.fnLocals ∧
      mm.stack=m.stack ∧ Evm.Memory.Objects.KeepsAllocator b frame σ base m (σ.withHeap mid) mm := by
  first
  | solve | simp only [] | omega
  | obtain ⟨mid,ym,mm,tw,ew,sw,iw,cw,rm,mok,hm',locals,next,parent,objects,addresses,world,events,logs,fnLocals,stack,allocator⟩ :=
      hr.resolved_write_word G Fs (horizon+1) nps σ r address sr si si sv root i i rhs k k v q
        hsr hsi hsi hsv htr hti hti htv hq separate hk SH memOK hm
    have selected : mid.index r .dyn k=some q := by
      change (MObj.elems .dyn (mid.get r))[k.1.toNat]?=some q
      rw [parent];exact hq
    obtain ⟨failed,ir,cr⟩ := rm.resolved_write_bounds_word G Fs horizon (σ.withHeap mid) r address
      sr si sj sv root i j rhs k l v q
      (by rw [locals];exact hsr) (by rw [locals];exact hsi) (by rw [locals];exact hsj) (by rw [locals];exact hsv)
      htr hti htj htv selected hl hm'
    have second := source_expr_statement_error G Fs (horizon+4) nps _ ym ym _ failed
    refine ⟨mid,ym,mm,tw,sw,failed,source_items_pair_error G Fs (horizon+1) nps _ _ y ym ym _ sw second,
      iw,ir,intrinsic_heap_pair_error σ _ _ mid .revert iw ir,cw,cr,?_,rm,mok,hm',
      locals,next,parent,objects,addresses,world,events,logs,fnLocals,stack,allocator⟩
    rw [Evm.run_append_ok cw]
    exact cr

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.resolved_write_late_bounds_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.resolved_write_late_bounds_word
end Solidity.Backend.MemoryOps
