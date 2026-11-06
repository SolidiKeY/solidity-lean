import Solidity.Backend.MemoryOps.SourceUintDelete

/-! Actual reached-state numeric assignment/deletion sequencing. Existing
Source RItems, intrinsic Prog and whole published code append only. Second
bounds/locals/representation/allocator are derived from the real first output. -/
namespace Solidity.Backend.MemoryOps

theorem resolved_uint_assign_delete_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (horizon : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .uint)))
    (hr : SourceUintMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) none)) (si sj : Source.Idx Γ (.int .u256))
    (srhs : Source.Idx Γ (.int .u256)) (root : Idx Δ (.mem (.array (.prim .uint))))
    (i j : Idx Δ (.val .uint)) (rhs : Idx Δ (.val .uint)) (k l : PrimTy.uint.Denote) (value : PrimTy.uint.Denote)
    (hsroot : y.1.get sroot=.memRef rfl address) (hsi : y.1.get si=sourceUint k)
    (hsj : y.1.get sj=sourceUint l) (hsrhs : y.1.get srhs=sourceUint value)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get i σ.env=k)
    (htj : TEnv.get j σ.env=l) (htrhs : TEnv.get rhs σ.env=value)
    (hk : k.1.toNat<σ.heap.len r .dyn) (hl : l.1.toNat<σ.heap.len r .dyn)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) :
    ∃ (mid out : Heap σ.H) (ym z : Source.EMState E Γ) (mm target : Evm.Machine),
      σ.heap.writeAddr (.index r .dyn k) value=some mid ∧ mid.writeAddr (.index r .dyn l) (PrimTy.dflt .uint)=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (horizon+3) (.mem address k.1.toNat) (sourceUint value)).run y=(.ok (),ym) ∧
      (Source.deleteLoc (E := E) (Γ := Γ) Fsrc (horizon+2) (τ := .int .u256) (.mem address l.1.toNat)).run ym=(.ok (),z) ∧
      (Source.execS G Fsrc (horizon+5) Γ.length none (.expr (sourceUintIndexedAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal y.1),(.nil,ym.2)) ∧
      (Source.execS G Fsrc (horizon+4) Γ.length none (.expr (sourceUintIndexedDelete sroot sj) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
        (.ok (.normal ym.1),(.nil,z.2)) ∧
      (Source.execItems G Fsrc (horizon+6) Γ.length none
        (.stmt (.expr (sourceUintIndexedAssign sroot si srhs)) (.stmt (.expr (sourceUintIndexedDelete sroot sj)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal y.1),(.nil,z.2)) ∧
      Prog.run σ (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local i))) (.val (.simple (.local rhs))))
        (.cons (.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local j)))) rfl) .nil))=
          .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs))) m=.ok mm 0 ∧
      Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) mm=.ok target 0 ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs)) ++
        Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) m=.ok target 0 ∧
      SourceUintMemoryAt ym address mid r .dyn ∧ SourceUintMemoryAt z address out r .dyn ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap mid) base mm ∧ Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      Source.MemOK E SH ym ∧ Source.MemOK E SH z ∧ ym.1=y.1 ∧ z.1=y.1 ∧ target.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target := by
  obtain ⟨mid,ym,mm,hw1,hsw1,_,hs1,hi1,hc1,hr1,hm1,hmem1,hy1,hstack1,ha1⟩ :=
    resolved_uint_assign_word G Fsrc (horizon+1) σ r hr sroot si srhs root i rhs k value
      hsroot hsi hsrhs htroot hti htrhs hk hm SH hmem
  have hlen : mid.len r .dyn=σ.heap.len r .dyn := by
    change (MObj.elems .dyn (mid.get r)).length=_
    rw [indexedWrite_elems σ.heap mid r .dyn k value hw1,List.length_set]
    rfl
  have hl' : l.1.toNat<(σ.withHeap mid).heap.len r .dyn := by
    change l.1.toNat<mid.len r .dyn
    rw [hlen];exact hl
  obtain ⟨out,z,target,hw2,hsw2,_,hs2,hi2,hc2,hr2,hm2,hmem2,hy2,hstack2,ha2⟩ :=
    resolved_uint_delete_word G Fsrc horizon (σ.withHeap mid) r hr1 sroot sj root j l
      (by rw [hy1];exact hsroot) (by rw [hy1];exact hsj) htroot htj hl' hm1 SH hmem1
  have hs1' : (Source.execS G Fsrc (horizon+5) Γ.length none (.expr (sourceUintIndexedAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.ok (.normal ym.1),(.nil,ym.2)) := by simpa only [hy1] using hs1
  have hs2' : (Source.execS G Fsrc (horizon+4) Γ.length none (.expr (sourceUintIndexedDelete sroot sj) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
      (.ok (.normal z.1),(.nil,z.2)) := by simpa only [hy2] using hs2
  have hseq := source_items_pair_run G Fsrc horizon Γ.length _ _ y ym z hs1' hs2'
  refine ⟨mid,out,ym,z,mm,target,hw1,hw2,hsw1,hsw2,hs1,hs2,?_,intrinsic_heap_pair_run σ _ _ mid out hi1 hi2,hc1,hc2,?_,hr1,hr2,hm1,hm2,hmem1,hmem2,hy1,hy2.trans hy1,hstack2.trans hstack1,?_⟩
  · simpa only [hy2,hy1] using hseq
  · rw [Evm.run_append_ok hc1];exact hc2
  · intro cursor hb ha
    exact ha2 cursor hb (ha1 cursor hb ha)

theorem resolved_uint_delete_assign_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (horizon : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .uint)))
    (hr : SourceUintMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) none)) (si sj : Source.Idx Γ (.int .u256))
    (srhs : Source.Idx Γ (.int .u256)) (root : Idx Δ (.mem (.array (.prim .uint))))
    (i j : Idx Δ (.val .uint)) (rhs : Idx Δ (.val .uint)) (k l : PrimTy.uint.Denote) (value : PrimTy.uint.Denote)
    (hsroot : y.1.get sroot=.memRef rfl address) (hsi : y.1.get si=sourceUint k)
    (hsj : y.1.get sj=sourceUint l) (hsrhs : y.1.get srhs=sourceUint value)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get i σ.env=k)
    (htj : TEnv.get j σ.env=l) (htrhs : TEnv.get rhs σ.env=value)
    (hk : k.1.toNat<σ.heap.len r .dyn) (hl : l.1.toNat<σ.heap.len r .dyn)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) :
    ∃ (mid out : Heap σ.H) (ym z : Source.EMState E Γ) (mm target : Evm.Machine),
      σ.heap.writeAddr (.index r .dyn l) (PrimTy.dflt .uint)=some mid ∧ mid.writeAddr (.index r .dyn k) value=some out ∧
      (Source.execS G Fsrc (horizon+5) Γ.length none (.expr (sourceUintIndexedDelete sroot sj) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal y.1),(.nil,ym.2)) ∧
      (Source.execS G Fsrc (horizon+4) Γ.length none (.expr (sourceUintIndexedAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
        (.ok (.normal ym.1),(.nil,z.2)) ∧
      (Source.execItems G Fsrc (horizon+6) Γ.length none
        (.stmt (.expr (sourceUintIndexedDelete sroot sj)) (.stmt (.expr (sourceUintIndexedAssign sroot si srhs)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal y.1),(.nil,z.2)) ∧
      Prog.run σ (.cons (.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local j)))) rfl)
        (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local i))) (.val (.simple (.local rhs)))) .nil))=
          .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) m=.ok mm 0 ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs))) mm=.ok target 0 ∧
      Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint)) ++
        Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs))) m=.ok target 0 ∧
      SourceUintMemoryAt ym address mid r .dyn ∧ SourceUintMemoryAt z address out r .dyn ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap mid) base mm ∧ Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      Source.MemOK E SH ym ∧ Source.MemOK E SH z ∧ ym.1=y.1 ∧ z.1=y.1 ∧ target.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target := by
  obtain ⟨mid,ym,mm,hw1,hsw1,_,hs1,hi1,hc1,hr1,hm1,hmem1,hy1,hstack1,ha1⟩ :=
    resolved_uint_delete_word G Fsrc (horizon+1) σ r hr sroot sj root j l hsroot hsj htroot htj hl hm SH hmem
  have hlen : mid.len r .dyn=σ.heap.len r .dyn := by
    change (MObj.elems .dyn (mid.get r)).length=_
    rw [indexedWrite_elems σ.heap mid r .dyn l (PrimTy.dflt .uint) hw1,List.length_set]
    rfl
  have hk' : k.1.toNat<(σ.withHeap mid).heap.len r .dyn := by
    change k.1.toNat<mid.len r .dyn
    rw [hlen];exact hk
  obtain ⟨out,z,target,hw2,hsw2,_,hs2,hi2,hc2,hr2,hm2,hmem2,hy2,hstack2,ha2⟩ :=
    resolved_uint_assign_word G Fsrc horizon (σ.withHeap mid) r hr1 sroot si srhs root i rhs k value
      (by rw [hy1];exact hsroot) (by rw [hy1];exact hsi) (by rw [hy1];exact hsrhs)
      htroot hti htrhs hk' hm1 SH hmem1
  have hs1' : (Source.execS G Fsrc (horizon+5) Γ.length none (.expr (sourceUintIndexedDelete sroot sj) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.ok (.normal ym.1),(.nil,ym.2)) := by simpa only [hy1] using hs1
  have hs2' : (Source.execS G Fsrc (horizon+4) Γ.length none (.expr (sourceUintIndexedAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
      (.ok (.normal z.1),(.nil,z.2)) := by simpa only [hy2] using hs2
  have hseq := source_items_pair_run G Fsrc horizon Γ.length _ _ y ym z hs1' hs2'
  refine ⟨mid,out,ym,z,mm,target,hw1,hw2,hs1,hs2,?_,intrinsic_heap_pair_run σ _ _ mid out hi1 hi2,hc1,hc2,?_,hr1,hr2,hm1,hm2,hmem1,hmem2,hy1,hy2.trans hy1,hstack2.trans hstack1,?_⟩
  · simpa only [hy2,hy1] using hseq
  · rw [Evm.run_append_ok hc1];exact hc2
  · intro cursor hb ha
    exact ha2 cursor hb (ha1 cursor hb ha)

theorem resolved_uint_assign_delete_reject {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (horizon : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .uint)))
    (hr : SourceUintMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) none)) (si sj : Source.Idx Γ (.int .u256))
    (srhs : Source.Idx Γ (.int .u256)) (root : Idx Δ (.mem (.array (.prim .uint))))
    (i j : Idx Δ (.val .uint)) (rhs : Idx Δ (.val .uint)) (k l : PrimTy.uint.Denote) (value : PrimTy.uint.Denote)
    (hsroot : y.1.get sroot=.memRef rfl address) (hsi : y.1.get si=sourceUint k)
    (hsj : y.1.get sj=sourceUint l) (hsrhs : y.1.get srhs=sourceUint value)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get i σ.env=k)
    (htj : TEnv.get j σ.env=l) (htrhs : TEnv.get rhs σ.env=value)
    (hk : k.1.toNat<σ.heap.len r .dyn) (hl : σ.heap.len r .dyn≤l.1.toNat)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) :
    ∃ (mid : Heap σ.H) (ym : Source.EMState E Γ) (mm : Evm.Machine),
      σ.heap.writeAddr (.index r .dyn k) value=some mid ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (horizon+3) (.mem address k.1.toNat) (sourceUint value)).run y=(.ok (),ym) ∧
      (Source.execS G Fsrc (horizon+5) Γ.length none (.expr (sourceUintIndexedAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal y.1),(.nil,ym.2)) ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs))) m=.ok mm 0 ∧
      (Source.execItems G Fsrc (horizon+6) Γ.length none
        (.stmt (.expr (sourceUintIndexedAssign sroot si srhs)) (.stmt (.expr (sourceUintIndexedDelete sroot sj)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      Prog.run σ (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local i))) (.val (.simple (.local rhs))))
        (.cons (.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local j)))) rfl) .nil))=.error .revert ∧
      Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) mm=.revert ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local i)) (.simple (.local rhs)) ++
        Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local j) : Val C Δ .uint))) m=.revert ∧
      SourceUintMemoryAt ym address mid r .dyn ∧ Source.MemOK E SH ym ∧ ym.1=y.1 := by
  obtain ⟨mid,ym,mm,hw1,hsw1,_,hs1,hi1,hc1,hr1,hm1,hmem1,hy1,hstack1,ha1⟩ :=
    resolved_uint_assign_word G Fsrc (horizon+1) σ r hr sroot si srhs root i rhs k value
      hsroot hsi hsrhs htroot hti htrhs hk hm SH hmem
  have hlen : mid.len r .dyn=σ.heap.len r .dyn := by
    change (MObj.elems .dyn (mid.get r)).length=_
    rw [indexedWrite_elems σ.heap mid r .dyn k value hw1,List.length_set]
    rfl
  have hl' : (σ.withHeap mid).heap.len r .dyn≤l.1.toNat := by
    change mid.len r .dyn≤l.1.toNat
    rw [hlen];exact hl
  have hb := resolved_uint_delete_word_bounds G Fsrc horizon (σ.withHeap mid) r hr1 sroot sj root j l
    (by rw [hy1];exact hsroot) (by rw [hy1];exact hsj) htroot htj hl' hm1
  have hs2 := source_expr_statement_error G Fsrc (horizon+3) Γ.length (sourceUintIndexedDelete sroot sj) ym ym _ hb.1
  have hs1' : (Source.execS G Fsrc (horizon+5) Γ.length none (.expr (sourceUintIndexedAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.ok (.normal ym.1),(.nil,ym.2)) := by simpa only [hy1] using hs1
  have hseq := source_items_pair_error G Fsrc horizon Γ.length _ _ y ym ym _ hs1' hs2
  have hn := (hr1.delete_bounds Fsrc horizon l hl').2
  have hi2 : Stmt.run (σ.withHeap mid) (.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local j)))) rfl)=.error .revert := by
    change TRun.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local j)))) (σ.withHeap mid)=_
    simp only [TRun.deleteMem,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,State.withHeap,htroot,htj,
      bind,Except.bind,pure,Except.pure,TRun.clearT,hn,TRes.ofOpt]
  refine ⟨mid,ym,mm,hw1,hsw1,hs1,hc1,hseq,intrinsic_heap_pair_error σ _ _ mid .revert hi1 hi2,hb.2,?_,hr1,hmem1,hy1⟩
  rw [Evm.run_append_ok hc1];exact hb.2

/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_assign_delete_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_assign_delete_word
/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_delete_assign_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_delete_assign_word
/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_assign_delete_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_assign_delete_reject
end Solidity.Backend.MemoryOps
