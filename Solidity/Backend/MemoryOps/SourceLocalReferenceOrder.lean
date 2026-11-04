import Solidity.Backend.MemoryOps.SourceLocalReferenceDelete

/-! An actual indexed write followed by local-reference deletion. The second
operation consumes the reached write state, and retained aliases keep the
changed old object rather than the fresh empty object. -/
namespace Solidity.Backend.MemoryOps

/-- Both successful statements, actual typed program and whole word append.
The changed old heap, source state and word machine are derived, not premises.
This is an allocating-rebind adapter, not general compiler selection for delete. -/
theorem source_bool_write_local_delete_program {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat) (y : Source.EMState E Γ)
    (sroot : Source.Idx Γ SourceBoolArrayTy) (si : Source.Idx Γ (.int .u256)) (srhs : Source.Idx Γ .bool)
    (σ : State C Δ) (root : Idx Δ (.mem (.array (.prim .bool))))
    (index : Idx Δ (.val .uint)) (rhs : Idx Δ (.val .bool))
    (old : HRef σ.H (.array (.prim .bool))) (address : Nat) (k : PrimTy.uint.Denote) (value : Bool)
    (hr : SourceBoolMemoryAt y address σ.heap old .dyn)
    (hsroot : y.1.get sroot=.memRef rfl address) (htroot : TEnv.get root σ.env=some old)
    (hsi : y.1.get si=sourceUint k) (hsrhs : y.1.get srhs=.bool value)
    (hti : TEnv.get index σ.env=k) (htrhs : TEnv.get rhs σ.env=value)
    (bound : k.1.toNat<σ.heap.len old .dyn)
    (SH : Source.HeapTy) (sourceOK : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (repr : Evm.Memory.StateRepr L b frame F σ base m)
    (allocator : Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m)
    (positive : 0<b) (space : cursor.val+1<Evm.W) :
    ∃ (mid : Heap σ.H) (ym : Source.EMState E Γ) (mm : Evm.Machine),
    let pair := (σ.withHeap mid).alloc (Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩)
    let ext := List.prefix_append σ.H [RefTy.array (.prim .bool)]
    let state := pair.1.setLocal root (some pair.2)
    let target := Evm.Memory.writeMachine (Evm.Memory.allocateMachine mm cursor ⟨0,Evm.W_pos⟩)
      (Evm.cellOf b root) (.val cursor)
    let z : Source.EMState E Γ := (ym.1.set sroot (.memRef rfl ym.2.heap.next),
      {ym.2 with heap := (ym.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory []⟩).1})
    σ.heap.writeAddr (.index old .dyn k) value=some mid ∧
    SourceBoolMemoryAt ym address mid old .dyn ∧
    (∀ a v,a≠address → y.2.heap.get a=some v → ym.2.heap.get a=some v) ∧
    (Source.execS G Fsrc (horizon+5) Γ.length none
      (.expr (sourceIndexedAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal ym.1),(.nil,ym.2)) ∧
    (Source.execS G Fsrc (horizon+4) Γ.length none
      (.expr (.delete (.local sroot)) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
    (Source.execItems G Fsrc (horizon+6) Γ.length none
      (.stmt (.expr (sourceIndexedAssign sroot si srhs)) (.stmt (.expr (.delete (.local sroot))) .nil) :
        Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
    Stmt.run σ (.assignMem (.index .dyn (.var root rfl) (.simple (.local index))) (.val (.simple (.local rhs))))=
      .ok ⟨σ.withHeap mid,List.prefix_refl _⟩ ∧
    Stmt.run (σ.withHeap mid) (.rebindMem root (.newArr (.lit 0 rfl) rfl))=.ok ⟨state,ext⟩ ∧
    Prog.run σ (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local index))) (.val (.simple (.local rhs))))
      (.cons (.rebindMem root (.newArr (.lit 0 rfl) rfl)) .nil))=.ok ⟨state,ext⟩ ∧
    Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local index)) (.simple (.local rhs))) m=.ok mm 0 ∧
    Evm.run (Evm.Memory.rebindNewCode b root (.lit 0 rfl : Simple C Δ .uint)) mm=.ok target 0 ∧
    Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local index)) (.simple (.local rhs)) ++
      Evm.Memory.rebindNewCode b root (.lit 0 rfl : Simple C Δ .uint)) m=.ok target 0 ∧
    SourceBoolMemoryAt z address state.heap (old.wk ext) .dyn ∧
    SourceBoolMemoryAt z ym.2.heap.next state.heap pair.2 .dyn ∧ Source.MemOK E SH z ∧
    Evm.Memory.StateRepr L b frame F state (Evm.upd base σ.H.length cursor) target ∧
    Evm.Memory.StructAllocatorRepr state.heap (Evm.upd base σ.H.length cursor) frame ⟨cursor.val+1,space⟩ target ∧
    Heap.Keeps ext mid state.heap ∧
    MObj.elems .dyn (state.heap.get (old.wk ext))=(MObj.elems .dyn (σ.heap.get old)).set k.1.toNat value ∧
    (∀ Q (q : HRef σ.H Q),old.id≠q.id → state.heap.get (q.wk ext)=MObj.wk ext Q (σ.heap.get q)) ∧
    (∀ a v,a≠address → y.2.heap.get a=some v → z.2.heap.get a=some v) ∧
    ym.1=y.1 ∧ ym.2.heap.next=y.2.heap.next ∧ z.2.heap.next=y.2.heap.next+1 ∧
    z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals ∧
    pair.2.id=σ.H.length ∧ pair.2.id≠old.id ∧ target.stack=m.stack := by
  first
  | solve | rfl | simp only [] | omega
  | obtain ⟨mid,ym,mm,write,expr,stmt₁,native₁,word₁,old₁,repr₁,mok₁,locals₁,stack₁,alloc₁⟩ :=
      resolved_assign_word G Fsrc (horizon+1) σ old hr sroot si srhs root index rhs k value
        hsroot hsi hsrhs htroot hti htrhs bound repr SH sourceOK
    have firstStmt : (Source.execS G Fsrc (horizon+5) Γ.length none
        (.expr (sourceIndexedAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal ym.1),(.nil,ym.2)) := by simpa only [locals₁] using stmt₁
    have second := source_bool_local_delete_rebind_word G Fsrc horizon ym sroot (σ.withHeap mid) root old address
      old₁ (by rw [locals₁];exact hsroot) htroot SH mok₁ repr₁ (alloc₁ cursor positive allocator) positive space
    rcases second with ⟨_,stmt₂,native₂,word₂,repr₂,alloc₂,stack₂,mok₂,fresh,keep,old₂,id,ne,_,cells,next₂,effects,_,_⟩
    change Heap.Keeps (List.prefix_append σ.H [RefTy.array (.prim .bool)]) mid
      ((σ.withHeap mid).alloc (Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩)).1.heap at keep
    obtain ⟨ht,w⟩ := source_bool_write y address _ hr k.1.toNat bound value
    have known := hr.eval_assign_of_run G Fsrc (horizon+1) sroot si srhs k value hsroot hsi hsrhs bound w
    have same : ym=(y.1,{y.2 with heap := (y.2.heap.write address
        (sourceBoolMemory ((MObj.elems .dyn (σ.heap.get old)).set k.1.toNat value)) ht)}) :=
      congrArg (fun q => q.2) (expr.symm.trans known)
    have next₁ : ym.2.heap.next=y.2.heap.next := congrArg (fun q => q.2.heap.next) same
    have otherMidSource : ∀ a v,a≠address → y.2.heap.get a=some v → ym.2.heap.get a=some v := by
      intro a v ne found
      rw [same,Source.Heap.write_other _ ne]
      exact found
    have otherSource : ∀ a v,a≠address → y.2.heap.get a=some v →
        (ym.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory []⟩).1.get a=some v := by
      intro a v ne found
      apply cells
      exact otherMidSource a v ne found
    have elems : MObj.elems .dyn (((σ.withHeap mid).alloc
        (Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩)).1.heap.get
        (old.wk (List.prefix_append σ.H [RefTy.array (.prim .bool)])))=
        (MObj.elems .dyn (σ.heap.get old)).set k.1.toNat value := by
      rw [keep old,MObj.elems_wk,List.map_id'' (f := MVal.wk (List.prefix_append σ.H [RefTy.array (.prim .bool)]) (.prim .bool)) (fun _ => rfl)]
      exact indexedWrite_elems σ.heap mid old .dyn k value write
    refine ⟨mid,ym,mm,write,old₁,otherMidSource,firstStmt,stmt₂,source_items_pair_run G Fsrc horizon Γ.length _ _ y ym _ firstStmt stmt₂,
      native₁,native₂,?_,word₁,word₂,?_,old₂,fresh,mok₂,repr₂,alloc₂,keep,elems,?_,otherSource,locals₁,next₁,?_,?_,?_,?_,?_,id,ne,stack₂.trans stack₁⟩
    · rw [Prog.run_cons_ok native₁,Prog.run_cons_ok native₂,Prog.run_nil];rfl
    · rw [Evm.run_append_ok word₁];exact word₂
    · intro Q q ne
      change ((σ.withHeap mid).alloc (Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩)).1.heap.get
        (q.wk (List.prefix_append σ.H [RefTy.array (.prim .bool)]))=_
      rw [keep q,indexedWrite_frame σ.heap mid old .dyn k value write q ne]
    · exact next₂.trans (congrArg (·+1) next₁)
    · exact effects.1.trans (congrArg (fun q => q.2.ex) same)
    · exact effects.2.1.trans (congrArg (fun q => q.2.events) same)
    · exact effects.2.2.1.trans (congrArg (fun q => q.2.logs) same)
    · exact effects.2.2.2.trans (congrArg (fun q => q.2.fnLocals) same)

/-- info: 'Solidity.Backend.MemoryOps.source_bool_write_local_delete_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_bool_write_local_delete_program
end Solidity.Backend.MemoryOps
