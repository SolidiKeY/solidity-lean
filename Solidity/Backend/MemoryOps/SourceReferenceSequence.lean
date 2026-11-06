import Solidity.Backend.MemoryOps.SourceReferenceAssignment
import Solidity.Backend.MemoryOps.SourceSequence

/-! Parent redirection followed by deletion through the ACTUAL reached pointer.
Only published Source RItems, intrinsic Prog and word List composition are used.
The second selected identity and bounds follow the first executed slot write. -/
namespace Solidity.Backend.MemoryOps

def referenceStmt {C : Contract} {Γ : Ctx} (root : Idx Γ (.mem BoolRefsRef))
    (i : Idx Γ (.val .uint)) (rhs : Idx Γ (.mem (.array (.prim .bool)))) : Stmt C Γ Γ :=
  .assignMem (.index .dyn (.var root rfl) (.simple (.local i))) (.ref (.var rhs rfl))

def nestedDeleteStmt {C : Contract} {Γ : Ctx} (root : Idx Γ (.mem BoolRefsRef))
    (i j : Idx Γ (.val .uint)) : Stmt C Γ Γ :=
  .deleteMem (.loc (.index .dyn (.loc (.index .dyn (.var root rfl) (.simple (.local i)))) (.simple (.local j)))) rfl

/-- INITIAL local/table alignment and bounds suffice. The nested delete selects
what the first write installed, not what the original parent selected. -/
theorem resolved_reference_delete_sequence {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (G : Source.Glob E) (Fsrc : Source.Fr) (n : Nat)
    (sroot : Source.Idx Γ SourceBoolRefsTy) (si sj : Source.Idx Γ (.int .u256))
    (srhs : Source.Idx Γ (.array .memory .bool none))
    (σ : State C Δ) (root : Idx Δ (.mem BoolRefsRef)) (i j : Idx Δ (.val .uint))
    (rhs : Idx Δ (.mem (.array (.prim .bool))))
    (r : HRef σ.H BoolRefsRef) (v : HRef σ.H (.array (.prim .bool))) (k l : Fin Evm.W)
    (address : Nat → Nat) (hr : SourceBoolRefsAt y a σ.heap r address)
    (hv : SourceBoolMemoryAt y (address v.id) σ.heap v .dyn)
    (hsroot : y.1.get sroot=.memRef rfl a) (hsi : y.1.get si=sourceUint (Evm.Memory.indexValue k))
    (hsj : y.1.get sj=sourceUint (Evm.Memory.indexValue l)) (hsrhs : y.1.get srhs=.memRef rfl (address v.id))
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get i σ.env=Evm.Memory.indexValue k)
    (htj : TEnv.get j σ.env=Evm.Memory.indexValue l) (htrhs : TEnv.get rhs σ.env=some v)
    (hk : k.val<σ.heap.len r .dyn) (hl : l.val<σ.heap.len v .dyn)
    (hsep : ∀ t∈MObj.elems .dyn (σ.heap.get r),t.id≠v.id → address t.id≠address v.id)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    ∃ (mid out : Heap σ.H) (ym z : Source.EMState E Γ) (mm target : Evm.Machine),
      σ.heap.writeAddr (.index r .dyn (Evm.Memory.indexValue k)) v=some mid ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (n+4) (.mem (τ := .array .memory .bool none) a k.val)
        (.memRef rfl (address v.id))).run y=(.ok (),ym) ∧
      mid.index r .dyn (Evm.Memory.indexValue k)=some v ∧
      mid.writeAddr (.index v .dyn (Evm.Memory.indexValue l)) false=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (n+3) (.mem (τ := .bool) (address v.id) l.val) (.bool false)).run ym=(.ok (),z) ∧
      (Source.execS G Fsrc (n+6) Γ.length none
        (.expr (sourceReferenceAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS G Fsrc (n+5) Γ.length none
        (.expr (sourceNestedDelete sroot si sj) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems G Fsrc (n+7) Γ.length none
        (.stmt (.expr (sourceReferenceAssign sroot si srhs)) (.stmt (.expr (sourceNestedDelete sroot si sj)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run σ (.cons (referenceStmt root i rhs) (.cons (nestedDeleteStmt root i j) .nil))=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (referenceWriteCode (C := C) b root i rhs) m=.ok mm 0 ∧
      Evm.run (nestedDeleteCode (C := C) b root i j) mm=.ok target 0 ∧
      Evm.run (referenceWriteCode (C := C) b root i rhs++nestedDeleteCode (C := C) b root i j) m=.ok target 0 ∧
      SourceBoolRefsAt ym a mid r address ∧ SourceBoolRefsAt z a out r address ∧
      Source.MemOK E SH ym ∧ Source.MemOK E SH z ∧
      Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap mid) base mm ∧
      Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap out) base target ∧
      ym.1=y.1 ∧ z.1=y.1 ∧
      MObj.elems .dyn (out.get r)=(MObj.elems .dyn (σ.heap.get r)).set k.val v ∧ target.stack=m.stack ∧
      (∀ cursor, 0<b → Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m →
        (base r.id).val+1+σ.heap.len r .dyn≤cursor.val →
        Evm.Memory.StructAllocatorRepr out base frame cursor target) ∧
      mm=Evm.Memory.writeMachine m ((base r.id).val+1+k.val) (.val (base v.id)) ∧
      target=Evm.Memory.writeMachine mm ((base v.id).val+1+l.val) (.val (Evm.bword false)) := by
  obtain ⟨mid,ym,ho₁,hw₁,he₁,hs₁,hi₁,hc₁,hr₁,hmem₁,hm₁,hy₁,hparent₁,hchildren,hsource,heffects⟩ :=
    hr.resolved_reference_assign_word G Fsrc (n+2) σ r v address hv sroot si srhs root i rhs k
      hsroot hsi hsrhs htroot hti htrhs hk SH hmem hm
  let mm := Evm.Memory.writeMachine m ((base r.id).val+1+k.val) (.val (base v.id))
  have hq₂ : mid.index r .dyn (Evm.Memory.indexValue k)=some v := by
    change (MObj.elems .dyn (mid.get r))[(Evm.Memory.indexValue k).1.toNat]?=some v
    rw [hparent₁]
    simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using List.getElem?_set_self hk (a := v)
  have hl₂ : l.val<mid.len v .dyn := by
    change l.val<(MObj.elems .dyn (mid.get v)).length
    rw [hchildren v];exact hl
  have hsep₂ : ∀ t∈MObj.elems .dyn (mid.get r),t.id≠v.id → address t.id≠address v.id := by
    rw [hparent₁]
    intro t ht hn
    rcases List.mem_or_eq_of_mem_set ht with ht | ht
    · exact hsep t ht hn
    · subst t;exact (hn rfl).elim
  obtain ⟨out,z,ho₂,hw₂,he₂,hs₂,hi₂,hc₂,hr₂,hmem₂,hm₂,hy₂,hparent₂,ha₂⟩ :=
    SourceBoolRefsAt.resolved_nested_delete_word G Fsrc n sroot si sj (σ.withHeap mid) root i j r v k l address hr₁
      (by rw [hy₁];exact hsroot) (by rw [hy₁];exact hsi) (by rw [hy₁];exact hsj)
      htroot hti htj hq₂ hl₂ hsep₂ SH hmem₁ hm₁
  let target := Evm.Memory.writeMachine mm ((base v.id).val+1+l.val) (.val (Evm.bword false))
  have hs₁' : (Source.execS G Fsrc (n+6) Γ.length none
      (.expr (sourceReferenceAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal ym.1),(.nil,ym.2)) := by rw [hy₁];exact hs₁
  refine ⟨mid,out,ym,z,mm,target,ho₁,hw₁,hq₂,ho₂,hw₂,hs₁',hs₂,?_,?_,hc₁,hc₂,?_,hr₁,hr₂,hmem₁,hmem₂,hm₁,hm₂,hy₁,hy₂.trans hy₁,?_,rfl,?_,rfl,rfl⟩
  · exact source_items_pair_run G Fsrc (n+1) Γ.length _ _ y ym z hs₁' hs₂
  · exact intrinsic_heap_pair_run σ _ _ mid out hi₁ hi₂
  · rw [Evm.run_append_ok hc₁];exact hc₂
  · rw [hparent₂];exact hparent₁
  · intro cursor hb ha hbound
    have hmid : mid=σ.heap.set r (MObj.setElem .dyn (σ.heap.get r) k.val v) := by
      have hw : σ.heap.writeAddr (.index r .dyn (Evm.Memory.indexValue k)) v=
          some (σ.heap.set r (MObj.setElem .dyn (σ.heap.get r) k.val v)) := by
        simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast]
        exact if_pos hk
      exact Option.some.inj (ho₁.symm.trans hw)
    apply ha₂ cursor hb
    change Evm.Memory.StructAllocatorRepr mid base frame cursor mm
    rw [hmid]
    exact reference_slot_allocator hm r k.val hk v cursor ha hbound

theorem resolved_reference_delete_late_error {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (G : Source.Glob E) (Fsrc : Source.Fr) (n : Nat)
    (sroot : Source.Idx Γ SourceBoolRefsTy) (si sj : Source.Idx Γ (.int .u256))
    (srhs : Source.Idx Γ (.array .memory .bool none))
    (σ : State C Δ) (root : Idx Δ (.mem BoolRefsRef)) (i j : Idx Δ (.val .uint))
    (rhs : Idx Δ (.mem (.array (.prim .bool))))
    (r : HRef σ.H BoolRefsRef) (v : HRef σ.H (.array (.prim .bool))) (k l : Fin Evm.W)
    (address : Nat → Nat) (hr : SourceBoolRefsAt y a σ.heap r address)
    (hv : SourceBoolMemoryAt y (address v.id) σ.heap v .dyn)
    (hsroot : y.1.get sroot=.memRef rfl a) (hsi : y.1.get si=sourceUint (Evm.Memory.indexValue k))
    (hsj : y.1.get sj=sourceUint (Evm.Memory.indexValue l)) (hsrhs : y.1.get srhs=.memRef rfl (address v.id))
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get i σ.env=Evm.Memory.indexValue k)
    (htj : TEnv.get j σ.env=Evm.Memory.indexValue l) (htrhs : TEnv.get rhs σ.env=some v)
    (hk : k.val<σ.heap.len r .dyn) (hl : σ.heap.len v .dyn≤l.val)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    ∃ (mid : Heap σ.H) (ym : Source.EMState E Γ) (mm : Evm.Machine),
      σ.heap.writeAddr (.index r .dyn (Evm.Memory.indexValue k)) v=some mid ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (n+4) (.mem (τ := .array .memory .bool none) a k.val)
        (.memRef rfl (address v.id))).run y=(.ok (),ym) ∧
      mid.index r .dyn (Evm.Memory.indexValue k)=some v ∧
      (Source.execS G Fsrc (n+6) Γ.length none
        (.expr (sourceReferenceAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.evalE G Fsrc (n+4) (sourceNestedDelete sroot si sj)).run ym=
        (.error (.revert (Source.panicData .index)),ym) ∧
      (Source.execItems G Fsrc (n+7) Γ.length none
        (.stmt (.expr (sourceReferenceAssign sroot si srhs)) (.stmt (.expr (sourceNestedDelete sroot si sj)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      Prog.run σ (.cons (referenceStmt root i rhs) (.cons (nestedDeleteStmt root i j) .nil))=.error .revert ∧
      Evm.run (referenceWriteCode (C := C) b root i rhs) m=.ok mm 0 ∧
      Evm.run (nestedDeleteCode (C := C) b root i j) mm=.revert ∧
      Evm.run (referenceWriteCode (C := C) b root i rhs++nestedDeleteCode (C := C) b root i j) m=.revert ∧
      SourceBoolRefsAt ym a mid r address ∧ Source.MemOK E SH ym ∧
      Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap mid) base mm ∧ ym.1=y.1 ∧
      mm=Evm.Memory.writeMachine m ((base r.id).val+1+k.val) (.val (base v.id)) := by
  obtain ⟨mid,ym,ho₁,hw₁,he₁,hs₁,hi₁,hc₁,hr₁,hmem₁,hm₁,hy₁,hparent₁,hchildren,hsource,heffects⟩ :=
    hr.resolved_reference_assign_word G Fsrc (n+2) σ r v address hv sroot si srhs root i rhs k
      hsroot hsi hsrhs htroot hti htrhs hk SH hmem hm
  let mm := Evm.Memory.writeMachine m ((base r.id).val+1+k.val) (.val (base v.id))
  have hq₂ : mid.index r .dyn (Evm.Memory.indexValue k)=some v := by
    change (MObj.elems .dyn (mid.get r))[(Evm.Memory.indexValue k).1.toNat]?=some v
    rw [hparent₁]
    simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using List.getElem?_set_self hk (a := v)
  have hl₂ : mid.len v .dyn≤l.val := by
    change (MObj.elems .dyn (mid.get v)).length≤l.val
    rw [hchildren v];exact hl
  obtain ⟨he₂,hi₂,hc₂⟩ := SourceBoolRefsAt.nested_delete_child_bounds G Fsrc n sroot si sj
    (σ.withHeap mid) root i j r v k l address hr₁
    (by rw [hy₁];exact hsroot) (by rw [hy₁];exact hsi) (by rw [hy₁];exact hsj)
    htroot hti htj hq₂ hl₂ hm₁
  have hs₁' : (Source.execS G Fsrc (n+6) Γ.length none
      (.expr (sourceReferenceAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal ym.1),(.nil,ym.2)) := by rw [hy₁];exact hs₁
  have hs₂ := source_expr_statement_error G Fsrc (n+4) Γ.length (sourceNestedDelete sroot si sj) ym ym _ he₂
  refine ⟨mid,ym,mm,ho₁,hw₁,hq₂,hs₁',he₂,?_,?_,hc₁,hc₂,?_,hr₁,hmem₁,hm₁,hy₁,rfl⟩
  · exact source_items_pair_error G Fsrc (n+1) Γ.length _ _ y ym ym _ hs₁' hs₂
  · exact intrinsic_heap_pair_error σ _ _ mid .revert hi₁ hi₂
  · rw [Evm.run_append_ok hc₁];exact hc₂

/-- info: 'Solidity.Backend.MemoryOps.resolved_reference_delete_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms resolved_reference_delete_sequence
/-- info: 'Solidity.Backend.MemoryOps.resolved_reference_delete_late_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms resolved_reference_delete_late_error
end Solidity.Backend.MemoryOps
