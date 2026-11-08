import Solidity.Backend.MemoryOps.SourceAssignment

/-! Actual reached-state composition of published Source statements, intrinsic
programs and word code. The second operation consumes the first output. -/
namespace Solidity.Backend.MemoryOps

theorem indexedWrite_elems {H : HTy} {R : RefTy} {E : Ty} (hp out : Heap H)
    (r : HRef H R) (a : ArrTy R E) (i : PrimTy.uint.Denote) (v : MVal H E)
    (hw : hp.writeAddr (.index r a i) v=some out) :
    MObj.elems a (out.get r)=(MObj.elems a (hp.get r)).set i.1.toNat v := by
  change hp.setIndex r a i v=some out at hw
  unfold Heap.setIndex at hw
  split at hw
  · rw [←Option.some.inj hw,Heap.get_set_same,MObj.elems_setElem]
  · cases hw

theorem indexedWrite_frame {H : HTy} {R Q : RefTy} {E : Ty} (hp out : Heap H)
    (r : HRef H R) (a : ArrTy R E) (i : PrimTy.uint.Denote) (v : MVal H E)
    (hw : hp.writeAddr (.index r a i) v=some out) (q : HRef H Q) (hne : r.id≠q.id) :
    out.get q=hp.get q := by
  change hp.setIndex r a i v=some out at hw
  unfold Heap.setIndex at hw
  split at hw
  · rw [←Option.some.inj hw,Heap.get_set_ne _ _ _ hne]
  · cases hw

/-- Existing RItems cons executes its tail at the reached globals and locals. -/
theorem source_items_cons_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (n nps : Nat)
    (s : Source.RStmt E [] false .body Γ Γ) (rest : Source.RItems E [] false .body Γ Γ)
    (y mid out : Source.EMState E Γ)
    (hs : (Source.execS G F n nps none s y.1).run (.nil,y.2)=(.ok (.normal mid.1),(.nil,mid.2)))
    (hr : (Source.execItems G F n nps none rest mid.1).run (.nil,mid.2)=(.ok (.normal out.1),(.nil,out.2))) :
    (Source.execItems G F (n+1) nps none (.stmt s rest) y.1).run (.nil,y.2)=
      (.ok (.normal out.1),(.nil,out.2)) := by
  rw [Source.execItems,Source.Hoare.run_bind,hs]
  change (Source.execItems G F n nps none rest mid.1 >>= fun o => Source.EM.lift (o.up Γ)).run (.nil,mid.2)=_
  rw [Source.Hoare.run_bind,hr]
  rfl

theorem source_items_pair_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (horizon nps : Nat)
    (s t : Source.RStmt E [] false .body Γ Γ) (y mid out : Source.EMState E Γ)
    (hs : (Source.execS G F (horizon+5) nps none s y.1).run (.nil,y.2)=(.ok (.normal mid.1),(.nil,mid.2)))
    (ht : (Source.execS G F (horizon+4) nps none t mid.1).run (.nil,mid.2)=(.ok (.normal out.1),(.nil,out.2))) :
    (Source.execItems G F (horizon+6) nps none (.stmt s (.stmt t .nil)) y.1).run (.nil,y.2)=
      (.ok (.normal out.1),(.nil,out.2)) := by
  have hn : (Source.execItems G F (horizon+4) nps none (.nil : Source.RItems E [] false .body Γ Γ) out.1).run (.nil,out.2)=
      (.ok (.normal out.1),(.nil,out.2)) := rfl
  have htail := source_items_cons_run G F (horizon+4) nps t .nil mid out out ht hn
  exact source_items_cons_run G F (horizon+5) nps s (.stmt t .nil) y mid out hs htail

theorem intrinsic_heap_pair_run {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (s t : Stmt C Γ Γ) (mid out : Heap σ.H)
    (hs : Stmt.run σ s=.ok ⟨σ.withHeap mid,List.prefix_refl _⟩)
    (ht : Stmt.run (σ.withHeap mid) t=.ok ⟨σ.withHeap out,List.prefix_refl _⟩) :
    Prog.run σ (.cons s (.cons t .nil))=.ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
  rw [Prog.run_cons_ok hs,Prog.run_cons_ok ht,Prog.run_nil]
  rfl

/-- INITIAL local alignment and both INITIAL bounds suffice: the second bound
is derived from the first actual write's preserved length. -/
theorem resolved_assign_delete_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (horizon : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .bool)))
    (hr : SourceBoolMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory .bool none)) (si sj : Source.Idx Γ (.int .u256))
    (srhs : Source.Idx Γ .bool) (root : Idx Δ (.mem (.array (.prim .bool))))
    (i j : Idx Δ (.val .uint)) (rhs : Idx Δ (.val .bool)) (k l : PrimTy.uint.Denote) (value : Bool)
    (hsroot : y.1.get sroot=.memRef rfl address) (hsi : y.1.get si=sourceUint k)
    (hsj : y.1.get sj=sourceUint l) (hsrhs : y.1.get srhs=.bool value)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get i σ.env=k)
    (htj : TEnv.get j σ.env=l) (htrhs : TEnv.get rhs σ.env=value)
    (hk : k.1.toNat<σ.heap.len r .dyn) (hl : l.1.toNat<σ.heap.len r .dyn)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) :
    ∃ (mid out : Heap σ.H) (ym z : Source.EMState E Γ) (mm target : Evm.Machine),
      σ.heap.writeAddr (.index r .dyn k) value=some mid ∧ mid.writeAddr (.index r .dyn l) false=some out ∧
      (Source.execS G Fsrc (horizon+5) Γ.length none (.expr (sourceIndexedAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal y.1),(.nil,ym.2)) ∧
      (Source.execS G Fsrc (horizon+4) Γ.length none (.expr (sourceIndexedDelete sroot sj) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
        (.ok (.normal ym.1),(.nil,z.2)) ∧
      (Source.execItems G Fsrc (horizon+6) Γ.length none
        (.stmt (.expr (sourceIndexedAssign sroot si srhs)) (.stmt (.expr (sourceIndexedDelete sroot sj)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal y.1),(.nil,z.2)) ∧
      Prog.run σ (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local i))) (.val (.simple (.local rhs))))
        (.cons (.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local j)))) rfl) .nil))=
          .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs))) m=.ok mm 0 ∧
      Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) mm=.ok target 0 ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs)) ++
        Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) m=.ok target 0 ∧
      SourceBoolMemoryAt ym address mid r .dyn ∧ SourceBoolMemoryAt z address out r .dyn ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap mid) base mm ∧ Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      Source.MemOK E SH ym ∧ Source.MemOK E SH z ∧ ym.1=y.1 ∧ z.1=y.1 ∧ target.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target := by
  obtain ⟨mid,ym,mm,hw1,_,hs1,hi1,hc1,hr1,hm1,hmem1,hy1,hstack1,ha1⟩ :=
    resolved_assign_word G Fsrc (horizon+1) σ r hr sroot si srhs root i rhs k value
      hsroot hsi hsrhs htroot hti htrhs hk hm SH hmem
  have hlen : mid.len r .dyn=σ.heap.len r .dyn := by
    change (MObj.elems .dyn (mid.get r)).length=_
    rw [indexedWrite_elems σ.heap mid r .dyn k value hw1]
    exact List.length_set (as := MObj.elems .dyn (σ.heap.get r)) (i := k.1.toNat) (a := value)
  have hl' : l.1.toNat<(σ.withHeap mid).heap.len r .dyn := by
    change l.1.toNat<mid.len r .dyn
    rw [hlen];exact hl
  obtain ⟨out,z,target,hw2,_,hs2,hi2,hc2,hr2,hm2,hmem2,hy2,hstack2,ha2⟩ :=
    resolved_delete_word G Fsrc horizon (σ.withHeap mid) r hr1 sroot sj root j l
      (by rw [hy1];exact hsroot) (by rw [hy1];exact hsj) htroot htj hl' hm1 SH hmem1
  have hs1' : (Source.execS G Fsrc (horizon+5) Γ.length none (.expr (sourceIndexedAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.ok (.normal ym.1),(.nil,ym.2)) := by simpa only [hy1] using hs1
  have hs2' : (Source.execS G Fsrc (horizon+4) Γ.length none (.expr (sourceIndexedDelete sroot sj) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
      (.ok (.normal z.1),(.nil,z.2)) := by simpa only [hy2] using hs2
  have hseq := source_items_pair_run G Fsrc horizon Γ.length _ _ y ym z hs1' hs2'
  refine ⟨mid,out,ym,z,mm,target,hw1,hw2,hs1,hs2,?_,intrinsic_heap_pair_run σ _ _ mid out hi1 hi2,hc1,hc2,?_,hr1,hr2,hm1,hm2,hmem1,hmem2,hy1,hy2.trans hy1,hstack2.trans hstack1,?_⟩
  · simpa only [hy2,hy1] using hseq
  · rw [Evm.run_append_ok hc1];exact hc2
  · intro cursor hb ha
    exact ha2 cursor hb (ha1 cursor hb ha)

theorem source_expr_statement_error {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (horizon nps : Nat)
    (e : Source.RExpr E Γ τ) (y z : Source.EMState E Γ) (halt : Source.Halt)
    (he : (Source.evalE G F horizon e).run y=(.error halt,z)) :
    (Source.execS G F (horizon+1) nps none (.expr e : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.error halt,(.nil,z.2)) := by
  have hsub : (Source.EM.sub (Γ := []) y.1 (Source.evalE G F horizon e)).run (.nil,y.2)=
      (.error halt,(.nil,z.2)) := by
    unfold Source.EM.sub
    have he' : (Source.evalE (plan := none) (calldataKnown := true) G F horizon e) (y.1,y.2)=(.error halt,z) := he
    cases z
    simp only [ExceptT.run,ExceptT.mk,he']
  rw [Source.execS,Source.Hoare.run_bind,hsub]

theorem source_items_pair_error {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (horizon nps : Nat)
    (s t : Source.RStmt E [] false .body Γ Γ) (y mid out : Source.EMState E Γ) (halt : Source.Halt)
    (hs : (Source.execS G F (horizon+5) nps none s y.1).run (.nil,y.2)=(.ok (.normal mid.1),(.nil,mid.2)))
    (ht : (Source.execS G F (horizon+4) nps none t mid.1).run (.nil,mid.2)=(.error halt,(.nil,out.2))) :
    (Source.execItems G F (horizon+6) nps none (.stmt s (.stmt t .nil)) y.1).run (.nil,y.2)=
      (.error halt,(.nil,out.2)) := by
  have htail : (Source.execItems G F (horizon+5) nps none (.stmt t .nil : Source.RItems E [] false .body Γ Γ) mid.1).run (.nil,mid.2)=
      (.error halt,(.nil,out.2)) := by
    rw [Source.execItems,Source.Hoare.run_bind,ht]
  rw [Source.execItems,Source.Hoare.run_bind,hs]
  change (Source.execItems G F (horizon+5) nps none (.stmt t .nil : Source.RItems E [] false .body Γ Γ) mid.1 >>=
    fun o => Source.EM.lift (o.up Γ)).run (.nil,mid.2)=_
  rw [Source.Hoare.run_bind,htail]

/-- Lower horizon timeout is a reached observation, not a public depth bound. -/
theorem source_indexed_delete_horizon_two {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (root : Source.Idx Γ (.array .memory .bool none)) (index : Source.Idx Γ (.int .u256)) :
    (Source.evalE G F 2 (sourceIndexedDelete root index)).run y=(.error .timeout,y) := by
  rfl

theorem resolved_delete_assign_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (horizon : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .bool)))
    (hr : SourceBoolMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory .bool none)) (si sj : Source.Idx Γ (.int .u256))
    (srhs : Source.Idx Γ .bool) (root : Idx Δ (.mem (.array (.prim .bool))))
    (i j : Idx Δ (.val .uint)) (rhs : Idx Δ (.val .bool)) (k l : PrimTy.uint.Denote) (value : Bool)
    (hsroot : y.1.get sroot=.memRef rfl address) (hsi : y.1.get si=sourceUint k)
    (hsj : y.1.get sj=sourceUint l) (hsrhs : y.1.get srhs=.bool value)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get i σ.env=k)
    (htj : TEnv.get j σ.env=l) (htrhs : TEnv.get rhs σ.env=value)
    (hk : k.1.toNat<σ.heap.len r .dyn) (hl : l.1.toNat<σ.heap.len r .dyn)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) :
    ∃ (mid out : Heap σ.H) (ym z : Source.EMState E Γ) (mm target : Evm.Machine),
      σ.heap.writeAddr (.index r .dyn l) false=some mid ∧ mid.writeAddr (.index r .dyn k) value=some out ∧
      (Source.execS G Fsrc (horizon+5) Γ.length none (.expr (sourceIndexedDelete sroot sj) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal y.1),(.nil,ym.2)) ∧
      (Source.execS G Fsrc (horizon+4) Γ.length none (.expr (sourceIndexedAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
        (.ok (.normal ym.1),(.nil,z.2)) ∧
      (Source.execItems G Fsrc (horizon+6) Γ.length none
        (.stmt (.expr (sourceIndexedDelete sroot sj)) (.stmt (.expr (sourceIndexedAssign sroot si srhs)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal y.1),(.nil,z.2)) ∧
      Prog.run σ (.cons (.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local j)))) rfl)
        (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local i))) (.val (.simple (.local rhs)))) .nil))=
          .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) m=.ok mm 0 ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs))) mm=.ok target 0 ∧
      Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint)) ++
        Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs))) m=.ok target 0 ∧
      SourceBoolMemoryAt ym address mid r .dyn ∧ SourceBoolMemoryAt z address out r .dyn ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap mid) base mm ∧ Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      Source.MemOK E SH ym ∧ Source.MemOK E SH z ∧ ym.1=y.1 ∧ z.1=y.1 ∧ target.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target := by
  obtain ⟨mid,ym,mm,hw1,_,hs1,hi1,hc1,hr1,hm1,hmem1,hy1,hstack1,ha1⟩ :=
    resolved_delete_word G Fsrc (horizon+1) σ r hr sroot sj root j l hsroot hsj htroot htj hl hm SH hmem
  have hlen : mid.len r .dyn=σ.heap.len r .dyn := by
    change (MObj.elems .dyn (mid.get r)).length=_
    rw [indexedWrite_elems σ.heap mid r .dyn l false hw1]
    exact List.length_set (as := MObj.elems .dyn (σ.heap.get r)) (i := l.1.toNat) (a := false)
  have hk' : k.1.toNat<(σ.withHeap mid).heap.len r .dyn := by
    change k.1.toNat<mid.len r .dyn
    rw [hlen];exact hk
  obtain ⟨out,z,target,hw2,_,hs2,hi2,hc2,hr2,hm2,hmem2,hy2,hstack2,ha2⟩ :=
    resolved_assign_word G Fsrc horizon (σ.withHeap mid) r hr1 sroot si srhs root i rhs k value
      (by rw [hy1];exact hsroot) (by rw [hy1];exact hsi) (by rw [hy1];exact hsrhs)
      htroot hti htrhs hk' hm1 SH hmem1
  have hs1' : (Source.execS G Fsrc (horizon+5) Γ.length none (.expr (sourceIndexedDelete sroot sj) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.ok (.normal ym.1),(.nil,ym.2)) := by simpa only [hy1] using hs1
  have hs2' : (Source.execS G Fsrc (horizon+4) Γ.length none (.expr (sourceIndexedAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
      (.ok (.normal z.1),(.nil,z.2)) := by simpa only [hy2] using hs2
  have hseq := source_items_pair_run G Fsrc horizon Γ.length _ _ y ym z hs1' hs2'
  refine ⟨mid,out,ym,z,mm,target,hw1,hw2,hs1,hs2,?_,intrinsic_heap_pair_run σ _ _ mid out hi1 hi2,hc1,hc2,?_,hr1,hr2,hm1,hm2,hmem1,hmem2,hy1,hy2.trans hy1,hstack2.trans hstack1,?_⟩
  · simpa only [hy2,hy1] using hseq
  · rw [Evm.run_append_ok hc1];exact hc2
  · intro cursor hb ha
    exact ha2 cursor hb (ha1 cursor hb ha)

theorem intrinsic_heap_pair_error {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (s t : Stmt C Γ Γ) (mid : Heap σ.H) (halt : THalt)
    (hs : Stmt.run σ s=.ok ⟨σ.withHeap mid,List.prefix_refl _⟩)
    (ht : Stmt.run (σ.withHeap mid) t=.error halt) :
    Prog.run σ (.cons s (.cons t .nil))=.error halt := by
  have htail : Prog.run (σ.withHeap mid) (.cons t .nil)=.error halt := by
    change TRun.seq t.runR (Prog.nil : Prog C Γ Γ).runR (σ.withHeap mid)=_
    simp only [TRun.seq]
    rw [show t.runR (σ.withHeap mid)=.error halt from ht]
  rw [Prog.run_cons_ok hs,htail]
  rfl

theorem resolved_assign_delete_reject {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (horizon : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .bool)))
    (hr : SourceBoolMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory .bool none)) (si sj : Source.Idx Γ (.int .u256))
    (srhs : Source.Idx Γ .bool) (root : Idx Δ (.mem (.array (.prim .bool))))
    (i j : Idx Δ (.val .uint)) (rhs : Idx Δ (.val .bool)) (k l : PrimTy.uint.Denote) (value : Bool)
    (hsroot : y.1.get sroot=.memRef rfl address) (hsi : y.1.get si=sourceUint k)
    (hsj : y.1.get sj=sourceUint l) (hsrhs : y.1.get srhs=.bool value)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get i σ.env=k)
    (htj : TEnv.get j σ.env=l) (htrhs : TEnv.get rhs σ.env=value)
    (hk : k.1.toNat<σ.heap.len r .dyn) (hl : σ.heap.len r .dyn≤l.1.toNat)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) :
    ∃ (mid : Heap σ.H) (ym : Source.EMState E Γ) (mm : Evm.Machine),
      σ.heap.writeAddr (.index r .dyn k) value=some mid ∧
      (Source.execS G Fsrc (horizon+5) Γ.length none (.expr (sourceIndexedAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal y.1),(.nil,ym.2)) ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs))) m=.ok mm 0 ∧
      (Source.execItems G Fsrc (horizon+6) Γ.length none
        (.stmt (.expr (sourceIndexedAssign sroot si srhs)) (.stmt (.expr (sourceIndexedDelete sroot sj)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      Prog.run σ (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local i))) (.val (.simple (.local rhs))))
        (.cons (.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local j)))) rfl) .nil))=.error .revert ∧
      Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) mm=.revert ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs)) ++
        Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) m=.revert ∧
      SourceBoolMemoryAt ym address mid r .dyn ∧ Source.MemOK E SH ym ∧ ym.1=y.1 := by
  obtain ⟨mid,ym,mm,hw1,_,hs1,hi1,hc1,hr1,hm1,hmem1,hy1,hstack1,ha1⟩ :=
    resolved_assign_word G Fsrc (horizon+1) σ r hr sroot si srhs root i rhs k value
      hsroot hsi hsrhs htroot hti htrhs hk hm SH hmem
  have hlen : mid.len r .dyn=σ.heap.len r .dyn := by
    change (MObj.elems .dyn (mid.get r)).length=_
    rw [indexedWrite_elems σ.heap mid r .dyn k value hw1]
    exact List.length_set (as := MObj.elems .dyn (σ.heap.get r)) (i := k.1.toNat) (a := value)
  have hl' : (σ.withHeap mid).heap.len r .dyn≤l.1.toNat := by
    change mid.len r .dyn≤l.1.toNat
    rw [hlen];exact hl
  have hb := resolved_delete_word_bounds G Fsrc horizon (σ.withHeap mid) r hr1 sroot sj root j l
    (by rw [hy1];exact hsroot) (by rw [hy1];exact hsj) htroot htj hl' hm1
  have hs2 := source_expr_statement_error G Fsrc (horizon+3) Γ.length (sourceIndexedDelete sroot sj) ym ym _ hb.1
  have hs1' : (Source.execS G Fsrc (horizon+5) Γ.length none (.expr (sourceIndexedAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.ok (.normal ym.1),(.nil,ym.2)) := by simpa only [hy1] using hs1
  have hseq := source_items_pair_error G Fsrc horizon Γ.length _ _ y ym ym _ hs1' hs2
  have hn := (hr1.delete_bounds Fsrc horizon l hl').2
  have hi2 : Stmt.run (σ.withHeap mid) (.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local j)))) rfl)=.error .revert := by
    change TRun.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local j)))) (σ.withHeap mid)=_
    simp only [TRun.deleteMem,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,State.withHeap,htroot,htj,
      bind,Except.bind,pure,Except.pure,TRun.clearT,hn,TRes.ofOpt]
  refine ⟨mid,ym,mm,hw1,hs1,hc1,hseq,intrinsic_heap_pair_error σ _ _ mid .revert hi1 hi2,hb.2,?_,hr1,hmem1,hy1⟩
  rw [Evm.run_append_ok hc1];exact hb.2

/-- info: 'Solidity.Backend.MemoryOps.indexedWrite_elems' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms indexedWrite_elems
/-- info: 'Solidity.Backend.MemoryOps.indexedWrite_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms indexedWrite_frame
/-- info: 'Solidity.Backend.MemoryOps.source_items_cons_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_items_cons_run
/-- info: 'Solidity.Backend.MemoryOps.source_items_pair_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_items_pair_run
/-- info: 'Solidity.Backend.MemoryOps.intrinsic_heap_pair_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intrinsic_heap_pair_run
/-- info: 'Solidity.Backend.MemoryOps.resolved_assign_delete_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resolved_assign_delete_word
/-- info: 'Solidity.Backend.MemoryOps.source_expr_statement_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_expr_statement_error
/-- info: 'Solidity.Backend.MemoryOps.source_items_pair_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_items_pair_error
/-- info: 'Solidity.Backend.MemoryOps.source_indexed_delete_horizon_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_indexed_delete_horizon_two
/-- info: 'Solidity.Backend.MemoryOps.resolved_delete_assign_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resolved_delete_assign_word
/-- info: 'Solidity.Backend.MemoryOps.intrinsic_heap_pair_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms intrinsic_heap_pair_error
/-- info: 'Solidity.Backend.MemoryOps.resolved_assign_delete_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resolved_assign_delete_reject
end Solidity.Backend.MemoryOps
