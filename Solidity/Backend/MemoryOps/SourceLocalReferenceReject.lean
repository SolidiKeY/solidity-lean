import Solidity.Backend.MemoryOps.SourceLocalReferenceDelete
import Solidity.Backend.MemoryOps.SourceReferenceAliasDelete

/-! A local-reference deletion really allocates and changes the binding before
an indexed assignment rejects on the fresh empty array. Source retains the
reached prefix; native/word errors do not return a suffix state. -/
namespace Solidity.Backend.MemoryOps

private theorem local_bool_after_reference_set {D : Source.Layout} : {Γ : Source.RCtx} →
    (l : Source.Locals D Γ) → (root : Source.Idx Γ SourceBoolArrayTy) →
    (rhs : Source.Idx Γ .bool) → (v : Source.Val D SourceBoolArrayTy) →
    (l.set root v).get rhs=l.get rhs
  | _,.cons _ _,.here,.there _,_ => rfl
  | _,.cons _ _,.there _,.here,_ => rfl
  | _,.cons _ tail,.there root,.there rhs,v => local_bool_after_reference_set tail root rhs v

private theorem memory_scalar_position_ne {Δ : Ctx} {p : PrimTy}
    (root : Idx Δ (.mem (.array (.prim .bool)))) (scalar : Idx Δ (.val p)) : root.toNat≠scalar.toNat := by
  first
  | solve | rfl | simp only [] | omega
  | intro eq
    have h := root.getElem?_toNat
    rw [eq,scalar.getElem?_toNat] at h
    cases h

/-- INITIAL operands and the actual deletion certificate derive a reached
bounds failure. There is no assumed intermediate relation, suffix run or
rollback. The first successful allocation/rebinding prefix is explicit. -/
theorem source_bool_local_delete_reject_program {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat) (y : Source.EMState E Γ)
    (sdst : Source.Idx Γ SourceBoolArrayTy) (si : Source.Idx Γ (.int .u256)) (srhs : Source.Idx Γ .bool)
    (σ : State C Δ) (dst : Idx Δ (.mem (.array (.prim .bool))))
    (index : Idx Δ (.val .uint)) (rhs : Idx Δ (.val .bool))
    (old : HRef σ.H (.array (.prim .bool))) (addr : Nat) (k : PrimTy.uint.Denote) (value : Bool)
    (hr : SourceBoolMemoryAt y addr σ.heap old .dyn)
    (hs : y.1.get sdst=.memRef rfl addr) (ht : TEnv.get dst σ.env=some old)
    (hsi : y.1.get si=sourceUint k) (hsrhs : y.1.get srhs=.bool value)
    (hti : TEnv.get index σ.env=k) (htrhs : TEnv.get rhs σ.env=value)
    (SH : Source.HeapTy) (sourceOK : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (repr : Evm.Memory.StateRepr L b frame F σ base m)
    (allocator : Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m)
    (positive : 0<b) (space : cursor.val+1<Evm.W) :
    let pair := σ.alloc (Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩)
    let ext := List.prefix_append σ.H [RefTy.array (.prim .bool)]
    let state := pair.1.setLocal dst (some pair.2)
    let target := Evm.Memory.writeMachine (Evm.Memory.allocateMachine m cursor ⟨0,Evm.W_pos⟩)
      (Evm.cellOf b dst) (.val cursor)
    let z : Source.EMState E Γ := (y.1.set sdst (.memRef rfl y.2.heap.next),
      {y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory []⟩).1})
    (Source.execS G Fsrc (horizon+5) Γ.length none
      (.expr (.delete (.local sdst)) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
    Stmt.run σ (.rebindMem dst (.newArr (.lit 0 rfl) rfl))=.ok ⟨state,ext⟩ ∧
    Evm.run (Evm.Memory.rebindNewCode b dst (.lit 0 rfl : Simple C Δ .uint)) m=.ok target 0 ∧
    (Source.evalE G Fsrc (horizon+3) (sourceIndexedAssign sdst si srhs)).run z=
      (.error (.revert (Source.panicData .index)),z) ∧
    (Source.execItems G Fsrc (horizon+6) Γ.length none
      (.stmt (.expr (.delete (.local sdst))) (.stmt (.expr (sourceIndexedAssign sdst si srhs)) .nil) :
        Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.error (.revert (Source.panicData .index)),(.nil,z.2)) ∧
    Stmt.run state (.assignMem (.index .dyn (.var dst rfl) (.simple (.local index))) (.val (.simple (.local rhs))))=
      .error .revert ∧
    Prog.run σ (.cons (.rebindMem dst (.newArr (.lit 0 rfl) rfl))
      (.cons (.assignMem (.index .dyn (.var dst rfl) (.simple (.local index))) (.val (.simple (.local rhs)))) .nil))=
      .error .revert ∧
    Evm.run (Evm.Memory.writeLocalCode (C := C) b dst (.simple (.local index)) (.simple (.local rhs))) target=.revert ∧
    Evm.run (Evm.Memory.rebindNewCode b dst (.lit 0 rfl : Simple C Δ .uint) ++
      Evm.Memory.writeLocalCode (C := C) b dst (.simple (.local index)) (.simple (.local rhs))) m=.revert ∧
    Heap.Keeps ext σ.heap state.heap ∧ Source.MemOK E SH z ∧ SourceBoolMemoryAt z y.2.heap.next state.heap pair.2 .dyn ∧
    SourceBoolMemoryAt z addr state.heap (old.wk ext) .dyn ∧
    Evm.Memory.StateRepr L b frame F state (Evm.upd base σ.H.length cursor) target ∧
    Evm.Memory.StructAllocatorRepr state.heap (Evm.upd base σ.H.length cursor) frame ⟨cursor.val+1,space⟩ target ∧
    state.heap.len pair.2 .dyn=0 ∧ pair.2.id=σ.H.length ∧ pair.2.id≠old.id ∧
    (∀ a v,y.2.heap.get a=some v → z.2.heap.get a=some v) ∧
    z.2.heap.next=y.2.heap.next+1 ∧ z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧
    z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals ∧ target.stack=m.stack := by
  first
  | solve | rfl | simp only [] | omega
  | dsimp only
    have first := source_bool_local_delete_rebind_word G Fsrc (horizon+1) y sdst σ dst old addr hr hs ht
      SH sourceOK repr allocator positive space
    rcases first with ⟨_,stmt,native,word,represented,allocated,stack,mok,fresh,keep,oldAt,id,ne,_,cells,next,effects,_,_⟩
    let pair := σ.alloc (Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩)
    let state := pair.1.setLocal dst (some pair.2)
    have localRoot : TEnv.get dst state.env=some pair.2 := TEnv.get_set _ _ _
    have scalarIndex : TEnv.get index state.env=k := by
      change TEnv.get index (TEnv.set dst (some pair.2) (TEnv.wk _ Δ σ.env))=k
      rw [TEnv.get_set_ne dst index _ _ (memory_scalar_position_ne dst index),TEnv.get_wk,hti]
      rfl
    have scalarRhs : TEnv.get rhs state.env=value := by
      change TEnv.get rhs (TEnv.set dst (some pair.2) (TEnv.wk _ Δ σ.env))=value
      rw [TEnv.get_set_ne dst rhs _ _ (memory_scalar_position_ne dst rhs),TEnv.get_wk,htrhs]
      rfl
    have length : state.heap.len pair.2 .dyn=0 := by
      change (MObj.elems .dyn ((σ.heap.alloc (Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩)).1.get
        (σ.heap.alloc (Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩)).2)).length=0
      rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
      rfl
    have outside : state.heap.len pair.2 .dyn≤k.1.toNat := by rw [length];exact Nat.zero_le _
    have bad := resolved_assign_word_bounds G Fsrc horizon state pair.2 fresh sdst si srhs dst index rhs k value
      (source_locals_get_set _ _ _) ((source_bool_alias_uint_frame _ _ _ _).trans hsi)
      ((local_bool_after_reference_set _ _ _ _).trans hsrhs) localRoot scalarIndex scalarRhs outside represented
    have suffix := source_expr_statement_error G Fsrc (horizon+3) Γ.length (sourceIndexedAssign sdst si srhs) _ _ _ bad.1
    have items := source_items_pair_error G Fsrc horizon Γ.length _ _ y _ _ _ stmt suffix
    have noWrite : state.heap.writeAddr (.index pair.2 .dyn k) value=none := by
      simp only [Heap.len] at outside
      simp only [Heap.writeAddr,Heap.setIndex,show ¬k.1.toNat<(MObj.elems .dyn (state.heap.get pair.2)).length from Nat.not_lt.mpr outside,↓reduceIte]
    have nativeBad : Stmt.run state (.assignMem (.index .dyn (.var dst rfl) (.simple (.local index))) (.val (.simple (.local rhs))))=.error .revert := by
      change TRun.assignMem _ _ state=_
      simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,
        localRoot,scalarIndex,scalarRhs,bind,Except.bind,pure,Except.pure,noWrite,TRes.ofOpt]
    have tail : Prog.run state (.cons (.assignMem (.index .dyn (.var dst rfl) (.simple (.local index))) (.val (.simple (.local rhs)))) .nil)=.error .revert := by
      change TRun.seq _ _ state=_
      simp only [TRun.seq]
      rw [show TRun.assignMem _ _ state=.error .revert from nativeBad]
    refine ⟨stmt,native,word,bad.1,items,nativeBad,?_,bad.2,?_,keep,mok,fresh,oldAt,represented,allocated,length,id,ne,cells,next,effects.1,effects.2.1,effects.2.2.1,effects.2.2.2,stack⟩
    · rw [Prog.run_cons_ok native,tail];rfl
    · rw [Evm.run_append_ok word];exact bad.2

/-- info: 'Solidity.Backend.MemoryOps.source_bool_local_delete_reject_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_bool_local_delete_reject_program
end Solidity.Backend.MemoryOps
