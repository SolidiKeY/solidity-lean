import Solidity.Backend.MemoryOps.SourceStructSequence

/-! Actual named reference-field replacement THEN deletion through the newly
selected child. Existing independent Source RItems, intrinsic Prog and published
whole word programs only; no assumed reached correspondence or new evaluator. -/
namespace Solidity.Backend.MemoryOps
open Semantics

def sourceStructReferenceDelete {E : Source.Env} {Γ : Source.RCtx}
    (layout : SourceBoolStructLayout E dn s tag child)
    (root : Source.Idx Γ (.struct .memory dn)) (rhs : Source.Idx Γ SourceBoolArrayTy)
    (i : Source.Idx Γ (.int .u256)) : Source.RItems E [] false .body Γ Γ :=
  .stmt (.expr (sourceStructAssign layout root rhs))
    (.stmt (.expr (sourceStructChildDelete layout root i)) .nil)

theorem SourceBoolStructAt.reference_delete_program
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (Fsrc : Source.Fr) (n : Nat)
    (σ : State C Δ) (r : HRef σ.H (.struct s)) (v : HRef σ.H (.array (.prim .bool)))
    (address : Nat → Nat) (hr : SourceBoolStructAt y a σ.heap r address layout)
    (hv : SourceBoolMemoryAt y (address v.id) σ.heap v .dyn)
    (sroot : Source.Idx Γ (.struct .memory dn)) (srhs : Source.Idx Γ SourceBoolArrayTy) (si : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.struct s))) (rhs : Idx Δ (.mem (.array (.prim .bool))))
    (i : Simple C Δ .uint) (k : PrimTy.uint.Denote)
    (hsroot : y.1.get sroot=.memRef rfl a) (hsrhs : y.1.get srhs=.memRef rfl (address v.id))
    (hsi : y.1.get si=sourceUint k) (htroot : TEnv.get root σ.env=some r)
    (htrhs : TEnv.get rhs σ.env=some v) (hti : i.evalT σ=k)
    (hmf : (Ty.ref (.struct s)).mapFree=true) (hk : k.1.toNat<σ.heap.len v .dyn)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (hif : Evm.valIn F (.simple i)=true) :
    let mid := σ.heap.setField r layout.child_type v
    let path := MPath.loc (.field (.var root hmf) child layout.child_type)
    ∃ (ym z : Source.EMState E Γ) (out : Heap σ.H) (mm target : Evm.Machine),
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (n+4) (.mem (τ := SourceBoolArrayTy) a 1) (.memRef rfl (address v.id))).run y=(.ok (),ym) ∧
      (Source.execS G Fsrc (n+6) Γ.length none (.expr (sourceStructAssign layout sroot srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS G Fsrc (n+5) Γ.length none (.expr (sourceStructChildDelete layout sroot si) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems G Fsrc (n+7) Γ.length none (sourceStructReferenceDelete layout sroot srhs si) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run σ (.cons (.assignMem (.field (.var root hmf) child layout.child_type) (.ref (.var rhs rfl)))
        (.cons (.deleteMem (.loc (.index .dyn path (.simple i))) rfl) .nil))=.ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (structReferenceWriteCode b root rhs child) m=.ok mm 0 ∧
      Evm.run (structChildDeleteCode b root child (.simple i)) mm=.ok target 0 ∧
      Evm.run (structReferenceWriteCode b root rhs child++structChildDeleteCode b root child (.simple i)) m=.ok target 0 ∧
      mid.field r layout.child_type=v ∧ mid.len v .dyn=σ.heap.len v .dyn ∧
      mid.writeAddr (.index v .dyn k) (PrimTy.dflt .bool)=some out ∧
      SourceBoolStructAt ym a mid r address layout ∧ SourceBoolMemoryAt ym (address v.id) mid v .dyn ∧
      SourceBoolStructAt z a out r address layout ∧ Source.MemOK E SH ym ∧ Source.MemOK E SH z ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap mid) base mm ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧ ym.1=y.1 ∧ z.1=y.1 ∧
      out.field r layout.tag_type=σ.heap.field r layout.tag_type ∧ out.field r layout.child_type=v ∧
      out.index v .dyn k=some false ∧
      (∀ t : HRef σ.H (.array (.prim .bool)),v.id≠t.id → out.get t=σ.heap.get t) ∧
      (∀ t : HRef σ.H (.array (.prim .bool)),SourceBoolMemoryAt y (address t.id) σ.heap t .dyn →
        v.id≠t.id → address t.id≠address v.id → SourceBoolMemoryAt z (address t.id) out t .dyn) ∧
      target.stack=m.stack ∧ Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target := by
  dsimp only
  let mid := σ.heap.setField r layout.child_type v
  obtain ⟨ym,mm,hwrite₁,he₁,hs₁,hi₁,hc₁,hr₁,hmem₁,hm₁,hy₁,hstack₁,hmm,ha₁,htag₁,hsel,hchildren,hsource₁,heffects₁⟩ :=
    SourceBoolStructAt.resolved_assign_word layout G Fsrc (n+2) σ r v address hr hv sroot srhs root rhs
      hsroot hsrhs htroot htrhs hmf SH hmem hm
  have hlen : mid.len v .dyn=σ.heap.len v .dyn := by
    unfold Heap.len
    rw [hchildren v]
  have hk₂ : k.1.toNat<mid.len (mid.field r layout.child_type) .dyn := by rw [hsel,hlen];exact hk
  have hti₂ : (Val.simple i).evalT (σ.withHeap mid)=.ok k := by
    change Except.ok (i.evalT (σ.withHeap mid))=.ok k
    cases i <;> exact congrArg Except.ok hti
  obtain ⟨out,z,target,hw₂,hdelete₂,he₂,hs₂,hi₂,hc₂,hr₂,hmem₂,hm₂,hy₂,hstack₂,ha₂,hparent₂,hother₂,hsource₂,heffects₂⟩ :=
    hr₁.delete_child_word layout G Fsrc n (σ.withHeap mid) r address sroot si root (.simple i) k
      (by rw [hy₁];exact hsroot) (by rw [hy₁];exact hsi) htroot hti₂ hmf hk₂ SH hmem₁ hm₁ hif
  have hselected : (σ.withHeap mid).heap.field r layout.child_type=v := hsel
  rw [hselected] at hw₂ hother₂ hsource₂
  have hs₁' : (Source.execS G Fsrc (n+6) Γ.length none (.expr (sourceStructAssign layout sroot srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.ok (.normal ym.1),(.nil,ym.2)) := by rw [hy₁];exact hs₁
  have hs₂' : (Source.execS G Fsrc (n+5) Γ.length none (.expr (sourceStructChildDelete layout sroot si) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
      (.ok (.normal z.1),(.nil,z.2)) := by rw [hy₂];exact hs₂
  have htag₂ : out.field r layout.tag_type=mid.field r layout.tag_type := by unfold Heap.field;rw [hparent₂];rfl
  have hsel₂ : out.field r layout.child_type=v := by unfold Heap.field;rw [hparent₂];exact hsel
  have hread : out.index v .dyn k=some false := by
    change (MObj.elems .dyn (out.get v))[k.1.toNat]?=some false
    rw [indexedWrite_elems mid out v .dyn k false hw₂]
    exact List.getElem?_set_self (by change k.1.toNat<mid.len v .dyn;rw [hlen];exact hk)
  refine ⟨ym,z,out,mm,target,hwrite₁,hs₁',hs₂',?_,?_,hc₁,hc₂,?_,hsel,hlen,hw₂,hr₁,hsource₁ v hv,hr₂,hmem₁,hmem₂,hm₁,hm₂,hy₁,hy₂.trans hy₁,
    htag₂.trans htag₁,hsel₂,hread,?_,?_,hstack₂.trans hstack₁,?_⟩
  · exact source_items_pair_run G Fsrc (n+1) Γ.length _ _ y ym z hs₁' hs₂'
  · exact intrinsic_heap_pair_run σ _ _ mid out hi₁ hi₂
  · exact (Evm.run_append_ok hc₁).trans hc₂
  · intro t hne
    exact (hother₂ t hne).trans (hchildren t)
  · intro t ht hne haddr
    unfold SourceBoolMemoryAt
    rw [hsource₂ _ haddr,hother₂ t hne]
    exact hsource₁ t ht
  · intro cursor hb ha
    exact ha₂ cursor hb (ha₁ cursor hb ha)


/-- Bounds rejection is tested against the NEW child after successful reference
replacement. Actual Source keeps that reached prefix; word revert has no state
or asserted panic bytes, and no successful suffix heap is manufactured. -/
theorem SourceBoolStructAt.reference_delete_reject
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (Fsrc : Source.Fr) (n : Nat)
    (σ : State C Δ) (r : HRef σ.H (.struct s)) (v : HRef σ.H (.array (.prim .bool)))
    (address : Nat → Nat) (hr : SourceBoolStructAt y a σ.heap r address layout)
    (hv : SourceBoolMemoryAt y (address v.id) σ.heap v .dyn)
    (sroot : Source.Idx Γ (.struct .memory dn)) (srhs : Source.Idx Γ SourceBoolArrayTy) (si : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.struct s))) (rhs : Idx Δ (.mem (.array (.prim .bool))))
    (i : Simple C Δ .uint) (k : PrimTy.uint.Denote)
    (hsroot : y.1.get sroot=.memRef rfl a) (hsrhs : y.1.get srhs=.memRef rfl (address v.id))
    (hsi : y.1.get si=sourceUint k) (htroot : TEnv.get root σ.env=some r)
    (htrhs : TEnv.get rhs σ.env=some v) (hti : i.evalT σ=k)
    (hmf : (Ty.ref (.struct s)).mapFree=true) (hk : σ.heap.len v .dyn≤k.1.toNat)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (hif : Evm.valIn F (.simple i)=true) :
    let mid := σ.heap.setField r layout.child_type v
    let path := MPath.loc (.field (.var root hmf) child layout.child_type)
    ∃ (ym : Source.EMState E Γ) (mm : Evm.Machine),
      (Source.execS G Fsrc (n+6) Γ.length none (.expr (sourceStructAssign layout sroot srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execItems G Fsrc (n+7) Γ.length none (sourceStructReferenceDelete layout sroot srhs si) y.1).run (.nil,y.2)=
        (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      Prog.run σ (.cons (.assignMem (.field (.var root hmf) child layout.child_type) (.ref (.var rhs rfl)))
        (.cons (.deleteMem (.loc (.index .dyn path (.simple i))) rfl) .nil))=.error .revert ∧
      Evm.run (structReferenceWriteCode b root rhs child) m=.ok mm 0 ∧
      Evm.run (structReferenceWriteCode b root rhs child++structChildDeleteCode b root child (.simple i)) m=.revert ∧
      SourceBoolStructAt ym a mid r address layout ∧ Source.MemOK E SH ym ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap mid) base mm ∧ ym.1=y.1 ∧
      mid.field r layout.child_type=v ∧ mid.len v .dyn=σ.heap.len v .dyn ∧
      mid.writeAddr (.index v .dyn k) (PrimTy.dflt .bool)=none ∧ mm.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap mid) mm := by
  dsimp only
  let mid := σ.heap.setField r layout.child_type v
  obtain ⟨ym,mm,hwrite₁,he₁,hs₁,hi₁,hc₁,hr₁,hmem₁,hm₁,hy₁,hstack₁,hmm,ha₁,htag₁,hsel,hchildren,hsource₁,heffects₁⟩ :=
    SourceBoolStructAt.resolved_assign_word layout G Fsrc (n+2) σ r v address hr hv sroot srhs root rhs
      hsroot hsrhs htroot htrhs hmf SH hmem hm
  have hlen : mid.len v .dyn=σ.heap.len v .dyn := by unfold Heap.len;rw [hchildren v]
  have hk₂ : mid.len (mid.field r layout.child_type) .dyn≤k.1.toNat := by rw [hsel,hlen];exact hk
  have hti₂ : (Val.simple i).evalT (σ.withHeap mid)=.ok k := by
    change Except.ok (i.evalT (σ.withHeap mid))=.ok k
    cases i <;> exact congrArg Except.ok hti
  obtain ⟨he₂,hn₂,hi₂,hc₂⟩ := hr₁.delete_child_word_bounds layout G Fsrc n (σ.withHeap mid) r address sroot si root (.simple i) k
    (by rw [hy₁];exact hsroot) (by rw [hy₁];exact hsi) htroot hti₂ hmf hk₂ hm₁ hif
  have hselected : (σ.withHeap mid).heap.field r layout.child_type=v := hsel
  rw [hselected] at hn₂
  have hs₁' : (Source.execS G Fsrc (n+6) Γ.length none (.expr (sourceStructAssign layout sroot srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.ok (.normal ym.1),(.nil,ym.2)) := by rw [hy₁];exact hs₁
  have hs₂ := source_expr_statement_error G Fsrc (n+4) Γ.length (sourceStructChildDelete layout sroot si) ym ym _ he₂
  refine ⟨ym,mm,hs₁',?_,?_,hc₁,?_,hr₁,hmem₁,hm₁,hy₁,hsel,hlen,hn₂,hstack₁,ha₁⟩
  · exact source_items_pair_error G Fsrc (n+1) Γ.length _ _ y ym ym _ hs₁' hs₂
  · exact intrinsic_heap_pair_error σ _ _ mid _ hi₁ hi₂
  · rw [Evm.run_append_ok hc₁];exact hc₂


/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.reference_delete_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.reference_delete_program

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.reference_delete_reject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.reference_delete_reject

end Solidity.Backend.MemoryOps
