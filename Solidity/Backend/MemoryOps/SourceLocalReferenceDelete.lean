import Solidity.Backend.MemoryOps.SourceStructGrowth
import Solidity.Backend.MemoryOps.SourceSequence

/-! Actual Source local-reference deletion uses its existing zeroVal then
writeLoc. The corresponding concrete adapter allocates/rebinds an empty array;
it is NOT the existing intrinsic object-content deleteMem operation. General
compiler selection of this adapter and physical byte execution stay open. -/
namespace Solidity.Backend.MemoryOps

/-- Actual independent Source expression, including the new heap and binding.
The old binding is not read to choose the new default object. -/
theorem source_bool_local_delete_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (dst : Source.Idx Γ (.array .memory .bool none)) :
    (Source.evalE G F (fuel+3) (.delete (.local dst))).run y=
      (.ok Source.RVal.unit,
        (y.1.set dst (.memRef rfl y.2.heap.next),
          {y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory []⟩).1})) := by
  first
  | solve | rfl | simp only [] | omega
  | rw [Source.evalE,Source.Hoare.run_bind,
      show (Source.evalLoc G F (fuel+2) (.local dst)).run y=(.ok (.local dst),y) from rfl]
    change ((Source.deleteLoc F (fuel+2) (.local dst)) >>= fun _ => pure Source.RVal.unit).run y=_
    rw [Source.deleteLoc,Source.Hoare.run_bind,Source.Hoare.run_bind,source_bool_default_run y fuel]
    all_goals first | rfl | (intro p h; cases h)

/-- Actual Source delete, native allocating rebind and the WHOLE existing word
allocation/rebind code, with exact fresh observer and old alias preservation.
The word certificate is the published primitive rebind producer; it is not a
claim that a general Source compiler already selects that code for delete. -/
theorem source_bool_local_delete_rebind_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (sdst : Source.Idx Γ (.array .memory .bool none)) (σ : State C Δ)
    (dst : Idx Δ (.mem (.array (.prim .bool))))
    (old : HRef σ.H (.array (.prim .bool))) (addr : Nat)
    (hr : SourceBoolMemoryAt y addr σ.heap old .dyn)
    (hs : y.1.get sdst=.memRef rfl addr) (ht : TEnv.get dst σ.env=some old)
    (SH : Source.HeapTy) (sourceOK : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (repr : Evm.Memory.StateRepr L b frame F σ base m)
    (allocator : Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m)
    (positive : 0<b) (space : cursor.val+1<Evm.W) :
    let obj := Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩
    let pair := σ.alloc obj
    let ext := List.prefix_append σ.H [RefTy.array (.prim .bool)]
    let state := pair.1.setLocal dst (some pair.2)
    let target := Evm.Memory.writeMachine (Evm.Memory.allocateMachine m cursor ⟨0,Evm.W_pos⟩)
      (Evm.cellOf b dst) (.val cursor)
    let z : Source.EMState E Γ :=
      (y.1.set sdst (.memRef rfl y.2.heap.next),
        {y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory []⟩).1})
    (Source.evalE G Fsrc (fuel+3) (.delete (.local sdst))).run y=(.ok Source.RVal.unit,z) ∧
    (Source.execS G Fsrc (fuel+4) Γ.length none
      (.expr (.delete (.local sdst)) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
    Stmt.run σ (.rebindMem dst (.newArr (.lit 0 rfl) rfl))=.ok ⟨state,ext⟩ ∧
    Evm.run (Evm.Memory.rebindNewCode b dst (.lit 0 rfl : Simple C Δ .uint)) m=.ok target 0 ∧
    Evm.Memory.StateRepr L b frame F state (Evm.upd base σ.H.length cursor) target ∧
    Evm.Memory.StructAllocatorRepr state.heap (Evm.upd base σ.H.length cursor) frame ⟨cursor.val+1,space⟩ target ∧
    target.stack=m.stack ∧ Source.MemOK E SH z ∧
    SourceBoolMemoryAt z y.2.heap.next state.heap pair.2 .dyn ∧
    Heap.Keeps ext σ.heap state.heap ∧ SourceBoolMemoryAt z addr state.heap (old.wk ext) .dyn ∧
    pair.2.id=σ.H.length ∧ pair.2.id≠(old.wk ext).id ∧ addr≠y.2.heap.next ∧
    (∀ a value,y.2.heap.get a=some value → z.2.heap.get a=some value) ∧
    z.2.heap.next=y.2.heap.next+1 ∧
    (z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals) ∧
    y.1.get sdst=.memRef rfl addr ∧ TEnv.get dst σ.env=some old := by
  first
  | solve | rfl | simp only [] | omega
  | dsimp only
    obtain ⟨native,word,repr',allocator',stack⟩ := Evm.Memory.rebindNew_correct repr allocator positive .bool dst
      (.lit 0 rfl) rfl ⟨0,Evm.W_pos⟩ rfl space
    have run := source_bool_local_delete_run G Fsrc fuel y sdst
    have defaults := source_bool_default_memOK (E := E) (Γ := Γ) SH fuel y sourceOK
    rw [source_bool_default_run] at defaults
    have mok := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) Fsrc (fuel+2) (.local sdst)
      (.memRef rfl y.2.heap.next) _ defaults
    have keeps : Heap.Keeps (List.prefix_append σ.H [RefTy.array (.prim .bool)]) σ.heap
        (σ.heap.alloc (Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩)).1 := Heap.keeps_alloc σ.heap (Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩)
    have occupied : addr≠y.2.heap.next := by
      intro he
      have empty := y.2.heap.alloc_fresh ⟨SourceBoolArrayTy,sourceBoolMemory []⟩
      change y.2.heap.get y.2.heap.next=none at empty
      rw [←he,hr] at empty
      cases empty
    have oldCells : ∀ a value,y.2.heap.get a=some value →
        (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory []⟩).1.get a=some value := by
      intro a value found
      have ne : a≠y.2.heap.next := by
        intro he
        have hf := y.2.heap.alloc_fresh ⟨SourceBoolArrayTy,sourceBoolMemory []⟩
        change y.2.heap.get y.2.heap.next=none at hf
        rw [←he,found] at hf
        cases hf
      rw [Source.Heap.alloc_other _ _ ne]
      exact found
    refine ⟨run,source_expr_statement_run G Fsrc (fuel+3) Γ.length _ y _ _ run,native,word,repr',allocator',stack,
      mok,?_,keeps,hr.transport keeps oldCells,rfl,?_,occupied,oldCells,rfl,⟨rfl,rfl,rfl,rfl⟩,hs,ht⟩
    · unfold SourceBoolMemoryAt
      have values : MObj.elems .dyn ((σ.alloc (Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩)).1.heap.get
          (σ.alloc (Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩)).2)=[] := by
        change MObj.elems .dyn ((σ.heap.alloc (Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩)).1.get
          (σ.heap.alloc (Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩)).2)=_
        rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
        rfl
      change (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory []⟩).1.get y.2.heap.next =
        some ⟨SourceBoolArrayTy,sourceBoolMemory (MObj.elems .dyn
          ((σ.alloc (Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩)).1.heap.get
          (σ.alloc (Evm.Memory.defaultArray (H := σ.H) .bool ⟨0,Evm.W_pos⟩)).2))⟩
      rw [values]
      exact Source.Heap.alloc_get _ _
    · have h := old.id_lt
      change σ.H.length≠old.id
      omega

/-- info: 'Solidity.Backend.MemoryOps.source_bool_local_delete_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_bool_local_delete_run
/-- info: 'Solidity.Backend.MemoryOps.source_bool_local_delete_rebind_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_bool_local_delete_rebind_word
end Solidity.Backend.MemoryOps
