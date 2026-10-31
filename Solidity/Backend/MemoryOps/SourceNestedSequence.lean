import Solidity.Backend.MemoryOps.SourceNestedAssignment
import Solidity.Backend.MemoryOps.SourceSequence

/-! Reached-state sequencing of existing resolved nested assignments.
The second operation uses the first actual Source/intrinsic/word output;
lengths/parent identity and initial local alignment discharge its premises. -/
namespace Solidity.Backend.MemoryOps

def nestedStmt {C : Contract} {Γ : Ctx} (root : Idx Γ (.mem BoolRefsRef))
    (i j : Idx Γ (.val .uint)) (rhs : Idx Γ (.val .bool)) : Stmt C Γ Γ :=
  .assignMem (.index .dyn (.loc (.index .dyn (.var root rfl) (.simple (.local i)))) (.simple (.local j)))
    (.val (.simple (.local rhs)))

theorem resolved_nested_pair_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {parentAddress : Nat} (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
    (sroot : Source.Idx Γ SourceBoolRefsTy) (si sj₁ sj₂ : Source.Idx Γ (.int .u256)) (sv₁ sv₂ : Source.Idx Γ .bool)
    (σ : State C Δ) (root : Idx Δ (.mem BoolRefsRef)) (i j₁ j₂ : Idx Δ (.val .uint)) (rhs₁ rhs₂ : Idx Δ (.val .bool))
    (r : HRef σ.H BoolRefsRef) (q : HRef σ.H (.array (.prim .bool))) (k l₁ l₂ : Fin Evm.W) (v₁ v₂ : Bool)
    (address : Nat → Nat) (hr : SourceBoolRefsAt y parentAddress σ.heap r address)
    (hsroot : y.1.get sroot=.memRef rfl parentAddress)
    (hsi : y.1.get si=sourceUint (Evm.Memory.indexValue k))
    (hsj₁ : y.1.get sj₁=sourceUint (Evm.Memory.indexValue l₁)) (hsj₂ : y.1.get sj₂=sourceUint (Evm.Memory.indexValue l₂))
    (hsv₁ : y.1.get sv₁=.bool v₁) (hsv₂ : y.1.get sv₂=.bool v₂)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get i σ.env=Evm.Memory.indexValue k)
    (htj₁ : TEnv.get j₁ σ.env=Evm.Memory.indexValue l₁) (htj₂ : TEnv.get j₂ σ.env=Evm.Memory.indexValue l₂)
    (htv₁ : TEnv.get rhs₁ σ.env=v₁) (htv₂ : TEnv.get rhs₂ σ.env=v₂)
    (hq : σ.heap.index r .dyn (Evm.Memory.indexValue k)=some q)
    (hl₁ : l₁.val<σ.heap.len q .dyn) (hl₂ : l₂.val<σ.heap.len q .dyn)
    (hsep : ∀ t∈MObj.elems .dyn (σ.heap.get r),t.id≠q.id → address t.id≠address q.id)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    ∃ (mid out : Heap σ.H) (ym z : Source.EMState E Γ) (mm target : Evm.Machine),
      σ.heap.writeAddr (.index q .dyn (Evm.Memory.indexValue l₁)) v₁=some mid ∧
      mid.writeAddr (.index q .dyn (Evm.Memory.indexValue l₂)) v₂=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (horizon+4) (.mem (address q.id) l₁.val) (.bool v₁)).run y=(.ok (),ym) ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (horizon+3) (.mem (address q.id) l₂.val) (.bool v₂)).run ym=(.ok (),z) ∧
      (Source.execS G Fsrc (horizon+6) Γ.length none
        (.expr (sourceNestedAssign sroot si sj₁ sv₁) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS G Fsrc (horizon+5) Γ.length none
        (.expr (sourceNestedAssign sroot si sj₂ sv₂) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems G Fsrc (horizon+7) Γ.length none
        (.stmt (.expr (sourceNestedAssign sroot si sj₁ sv₁)) (.stmt (.expr (sourceNestedAssign sroot si sj₂ sv₂)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run σ (.cons (nestedStmt root i j₁ rhs₁) (.cons (nestedStmt root i j₂ rhs₂) .nil))=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (nestedWriteCode (C := C) b root i j₁ rhs₁) m=.ok mm 0 ∧
      Evm.run (nestedWriteCode (C := C) b root i j₂ rhs₂) mm=.ok target 0 ∧
      Evm.run (nestedWriteCode (C := C) b root i j₁ rhs₁ ++ nestedWriteCode (C := C) b root i j₂ rhs₂) m=.ok target 0 ∧
      SourceBoolRefsAt ym parentAddress mid r address ∧ SourceBoolRefsAt z parentAddress out r address ∧
      Source.MemOK E SH ym ∧ Source.MemOK E SH z ∧
      Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap mid) base mm ∧
      Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap out) base target ∧
      ym.1=y.1 ∧ z.1=y.1 ∧ out.get r=σ.heap.get r ∧ target.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target ∧
      mm=Evm.Memory.writeMachine m ((base q.id).val+1+l₁.val) (.val (Evm.bword v₁)) ∧
      target=Evm.Memory.writeMachine mm ((base q.id).val+1+l₂.val) (.val (Evm.bword v₂)) := by
  obtain ⟨mid,ym,ho₁,hw₁,_,_,hs₁,hi₁,hc₁,hr₁,hmem₁,hm₁,hy₁,hparent₁,ha₁⟩ :=
    hr.resolved_nested_assign_word G Fsrc (horizon+1) sroot si sj₁ sv₁ σ root i j₁ rhs₁ r q k l₁ v₁ address
      hsroot hsi hsj₁ hsv₁ htroot hti htj₁ htv₁ hq hl₁ hsep SH hmem hm
  let mm := Evm.Memory.writeMachine m ((base q.id).val+1+l₁.val) (.val (Evm.bword v₁))
  have hq₂ : mid.index r .dyn (Evm.Memory.indexValue k)=some q := by
    change (MObj.elems .dyn (mid.get r))[(Evm.Memory.indexValue k).1.toNat]?=some q
    rw [hparent₁];exact hq
  have hl₂' : l₂.val<mid.len q .dyn := by rw [Heap.len_writeAddr ho₁];exact hl₂
  have hsep₂ : ∀ t∈MObj.elems .dyn (mid.get r),t.id≠q.id → address t.id≠address q.id := by
    rw [hparent₁];exact hsep
  obtain ⟨out,z,ho₂,hw₂,_,_,hs₂,hi₂,hc₂,hr₂,hmem₂,hm₂,hy₂,hparent₂,ha₂⟩ :=
    hr₁.resolved_nested_assign_word G Fsrc horizon sroot si sj₂ sv₂ (σ.withHeap mid) root i j₂ rhs₂ r q k l₂ v₂ address
      (by rw [hy₁];exact hsroot) (by rw [hy₁];exact hsi) (by rw [hy₁];exact hsj₂) (by rw [hy₁];exact hsv₂)
      htroot hti htj₂ htv₂ hq₂ hl₂' hsep₂ SH hmem₁ hm₁
  let target := Evm.Memory.writeMachine mm ((base q.id).val+1+l₂.val) (.val (Evm.bword v₂))
  refine ⟨mid,out,ym,z,mm,target,ho₁,ho₂,hw₁,hw₂,hs₁,hs₂,?_,?_,hc₁,hc₂,?_,hr₁,hr₂,hmem₁,hmem₂,hm₁,hm₂,hy₁,hy₂.trans hy₁,
    hparent₂.trans hparent₁,rfl,?_,rfl,rfl⟩
  · exact source_items_pair_run G Fsrc (horizon+1) Γ.length _ _ y ym z hs₁ hs₂
  · exact intrinsic_heap_pair_run σ _ _ mid out hi₁ hi₂
  · rw [Evm.run_append_ok hc₁];exact hc₂
  · intro cursor hb ha
    exact ha₂ cursor hb (ha₁ cursor hb ha)

theorem resolved_nested_pair_child_error {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {parentAddress : Nat} (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
    (sroot : Source.Idx Γ SourceBoolRefsTy) (si sj₁ sj₂ : Source.Idx Γ (.int .u256)) (sv₁ sv₂ : Source.Idx Γ .bool)
    (σ : State C Δ) (root : Idx Δ (.mem BoolRefsRef)) (i j₁ j₂ : Idx Δ (.val .uint)) (rhs₁ rhs₂ : Idx Δ (.val .bool))
    (r : HRef σ.H BoolRefsRef) (q : HRef σ.H (.array (.prim .bool))) (k l₁ l₂ : Fin Evm.W) (v₁ v₂ : Bool)
    (address : Nat → Nat) (hr : SourceBoolRefsAt y parentAddress σ.heap r address)
    (hsroot : y.1.get sroot=.memRef rfl parentAddress)
    (hsi : y.1.get si=sourceUint (Evm.Memory.indexValue k))
    (hsj₁ : y.1.get sj₁=sourceUint (Evm.Memory.indexValue l₁)) (hsj₂ : y.1.get sj₂=sourceUint (Evm.Memory.indexValue l₂))
    (hsv₁ : y.1.get sv₁=.bool v₁) (hsv₂ : y.1.get sv₂=.bool v₂)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get i σ.env=Evm.Memory.indexValue k)
    (htj₁ : TEnv.get j₁ σ.env=Evm.Memory.indexValue l₁) (htj₂ : TEnv.get j₂ σ.env=Evm.Memory.indexValue l₂)
    (htv₁ : TEnv.get rhs₁ σ.env=v₁) (htv₂ : TEnv.get rhs₂ σ.env=v₂)
    (hq : σ.heap.index r .dyn (Evm.Memory.indexValue k)=some q)
    (hl₁ : l₁.val<σ.heap.len q .dyn) (hl₂ : σ.heap.len q .dyn≤l₂.val)
    (hsep : ∀ t∈MObj.elems .dyn (σ.heap.get r),t.id≠q.id → address t.id≠address q.id)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    ∃ (mid : Heap σ.H) (ym : Source.EMState E Γ) (mm : Evm.Machine),
      σ.heap.writeAddr (.index q .dyn (Evm.Memory.indexValue l₁)) v₁=some mid ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (horizon+4) (.mem (address q.id) l₁.val) (.bool v₁)).run y=(.ok (),ym) ∧
      (Source.execS G Fsrc (horizon+6) Γ.length none
        (.expr (sourceNestedAssign sroot si sj₁ sv₁) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.evalE G Fsrc (horizon+4) (sourceNestedAssign sroot si sj₂ sv₂)).run ym=
        (.error (.revert (Source.panicData .index)),ym) ∧
      (Source.execItems G Fsrc (horizon+7) Γ.length none
        (.stmt (.expr (sourceNestedAssign sroot si sj₁ sv₁)) (.stmt (.expr (sourceNestedAssign sroot si sj₂ sv₂)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      Prog.run σ (.cons (nestedStmt root i j₁ rhs₁) (.cons (nestedStmt root i j₂ rhs₂) .nil))=.error .revert ∧
      Evm.run (nestedWriteCode (C := C) b root i j₁ rhs₁) m=.ok mm 0 ∧
      Evm.run (nestedWriteCode (C := C) b root i j₂ rhs₂) mm=.revert ∧
      Evm.run (nestedWriteCode (C := C) b root i j₁ rhs₁ ++ nestedWriteCode (C := C) b root i j₂ rhs₂) m=.revert ∧
      SourceBoolRefsAt ym parentAddress mid r address ∧ Source.MemOK E SH ym ∧
      Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap mid) base mm ∧ ym.1=y.1 ∧
      mm=Evm.Memory.writeMachine m ((base q.id).val+1+l₁.val) (.val (Evm.bword v₁)) := by
  obtain ⟨mid,ym,ho₁,hw₁,_,_,hs₁,hi₁,hc₁,hr₁,hmem₁,hm₁,hy₁,hparent₁,_⟩ :=
    hr.resolved_nested_assign_word G Fsrc (horizon+1) sroot si sj₁ sv₁ σ root i j₁ rhs₁ r q k l₁ v₁ address
      hsroot hsi hsj₁ hsv₁ htroot hti htj₁ htv₁ hq hl₁ hsep SH hmem hm
  let mm := Evm.Memory.writeMachine m ((base q.id).val+1+l₁.val) (.val (Evm.bword v₁))
  have hq₂ : mid.index r .dyn (Evm.Memory.indexValue k)=some q := by
    change (MObj.elems .dyn (mid.get r))[(Evm.Memory.indexValue k).1.toNat]?=some q
    rw [hparent₁];exact hq
  have hl₂' : mid.len q .dyn≤l₂.val := by rw [Heap.len_writeAddr ho₁];exact hl₂
  obtain ⟨he₂,hi₂,hc₂⟩ := SourceBoolRefsAt.nested_assign_child_bounds G Fsrc horizon sroot si sj₂ sv₂ (σ.withHeap mid)
    root i j₂ rhs₂ r q k l₂ v₂ address hr₁ (by rw [hy₁];exact hsroot) (by rw [hy₁];exact hsi)
    (by rw [hy₁];exact hsj₂) (by rw [hy₁];exact hsv₂) htroot hti htj₂ htv₂ hq₂ hl₂' hm₁
  have hs₂ := source_expr_statement_error G Fsrc (horizon+4) Γ.length (sourceNestedAssign sroot si sj₂ sv₂) ym ym _ he₂
  refine ⟨mid,ym,mm,ho₁,hw₁,hs₁,he₂,source_items_pair_error G Fsrc (horizon+1) Γ.length _ _ y ym ym _ hs₁ hs₂,
    intrinsic_heap_pair_error σ _ _ mid .revert hi₁ hi₂,hc₁,hc₂,?_,hr₁,hmem₁,hm₁,hy₁,rfl⟩
  rw [Evm.run_append_ok hc₁];exact hc₂

/-- info: 'Solidity.Backend.MemoryOps.resolved_nested_pair_child_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resolved_nested_pair_child_error

/-- info: 'Solidity.Backend.MemoryOps.resolved_nested_pair_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resolved_nested_pair_word
end Solidity.Backend.MemoryOps
