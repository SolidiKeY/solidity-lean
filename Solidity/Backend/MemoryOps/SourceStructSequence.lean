import Solidity.Backend.MemoryOps.SourceStructDelete

/-! An ACTUAL Source RItems member-write/then-delete program and corresponding
intrinsic Prog/whole word append. Second operands, length and representation
are derived from the first reached state. Pure core Simple target operands only. -/
namespace Solidity.Backend.MemoryOps
open Semantics

def sourceStructWriteDelete {E : Source.Env} {Γ : Source.RCtx}
    (layout : SourceBoolStructLayout E dn s tag child)
    (root : Source.Idx Γ (.struct .memory dn)) (i : Source.Idx Γ (.int .u256)) (v : Source.Idx Γ .bool) :
    Source.RItems E [] false .body Γ Γ :=
  .stmt (.expr (sourceStructChildAssign layout root i v))
    (.stmt (.expr (sourceStructChildDelete layout root i)) .nil)

theorem SourceBoolStructAt.write_delete_program
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (Fsrc : Source.Fr) (n : Nat)
    (σ : State C Δ) (r : HRef σ.H (.struct s)) (address : Nat → Nat)
    (hr : SourceBoolStructAt y a σ.heap r address layout)
    (sroot : Source.Idx Γ (.struct .memory dn)) (si : Source.Idx Γ (.int .u256)) (sv : Source.Idx Γ .bool)
    (root : Idx Δ (.mem (.struct s))) (i : Simple C Δ .uint) (v : Simple C Δ .bool)
    (k : PrimTy.uint.Denote) (value : Bool)
    (hsroot : y.1.get sroot=.memRef rfl a) (hsi : y.1.get si=sourceUint k) (hsv : y.1.get sv=.bool value)
    (htroot : TEnv.get root σ.env=some r) (hti : i.evalT σ=k) (htv : v.evalT σ=value)
    (hmf : (Ty.ref (.struct s)).mapFree=true)
    (hk : k.1.toNat<σ.heap.len (σ.heap.field r layout.child_type) .dyn)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m)
    (hif : Evm.valIn F (.simple i)=true) (hvf : Evm.valIn F (.simple v)=true) :
    let q := σ.heap.field r layout.child_type
    let path := MPath.loc (.field (.var root hmf) child layout.child_type)
    ∃ (mid out : Heap σ.H) (ym z : Source.EMState E Γ) (mm target : Evm.Machine),
      σ.heap.writeAddr (.index q .dyn k) value=some mid ∧
      mid.writeAddr (.index q .dyn k) (PrimTy.dflt .bool)=some out ∧
      (Source.execS G Fsrc (n+6) Γ.length none (.expr (sourceStructChildAssign layout sroot si sv) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS G Fsrc (n+5) Γ.length none (.expr (sourceStructChildDelete layout sroot si) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems G Fsrc (n+7) Γ.length none (sourceStructWriteDelete layout sroot si sv) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run σ (.cons (.assignMem (.index .dyn path (.simple i)) (.val (.simple v)))
        (.cons (.deleteMem (.loc (.index .dyn path (.simple i))) rfl) .nil))=.ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (structChildWriteCode b root child (.simple i) (.simple v)) m=.ok mm 0 ∧
      Evm.run (structChildDeleteCode b root child (.simple i)) mm=.ok target 0 ∧
      Evm.run (structChildWriteCode b root child (.simple i) (.simple v)++structChildDeleteCode b root child (.simple i)) m=.ok target 0 ∧
      SourceBoolStructAt ym a mid r address layout ∧ SourceBoolStructAt z a out r address layout ∧
      Source.MemOK E SH ym ∧ Source.MemOK E SH z ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap mid) base mm ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      ym.1=y.1 ∧ z.1=y.1 ∧ mid.len q .dyn=σ.heap.len q .dyn ∧
      out.get r=σ.heap.get r ∧ out.index q .dyn k=some false ∧ target.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target := by
  dsimp only
  let q := σ.heap.field r layout.child_type
  obtain ⟨mid,ym,mm,hw₁,hwrite₁,he₁,hs₁,hi₁,hc₁,hr₁,hmem₁,hm₁,hy₁,hstack₁,ha₁,hparent₁,hother₁,hsource₁,heffects₁⟩ :=
    hr.assign_child_word layout G Fsrc (n+1) σ r address sroot si sv root (.simple i) (.simple v) k value
      hsroot hsi hsv htroot (congrArg Except.ok hti) (congrArg Except.ok htv) hmf hk SH hmem hm hif hvf
  have hmid : mid=σ.heap.set q (MObj.setElem .dyn (σ.heap.get q) k.1.toNat value) := by
    have hw : σ.heap.writeAddr (.index q .dyn k) value=some (σ.heap.set q (MObj.setElem .dyn (σ.heap.get q) k.1.toNat value)) := by
      simp only [Heap.writeAddr,Heap.setIndex]
      exact if_pos hk
    exact Option.some.inj (hw₁.symm.trans hw)
  have hq : mid.field r layout.child_type=q := by unfold Heap.field;rw [hparent₁];rfl
  have hlen : mid.len q .dyn=σ.heap.len q .dyn := by
    rw [hmid]
    simp only [Heap.len,Heap.get_set_same,MObj.elems_setElem,List.length_set]
  have hk₂ : k.1.toNat<mid.len (mid.field r layout.child_type) .dyn := by rw [hq,hlen];exact hk
  have hti₂ : (Val.simple i).evalT (σ.withHeap mid)=.ok k := by
    change Except.ok (i.evalT (σ.withHeap mid))=.ok k
    cases i <;> exact congrArg Except.ok hti
  obtain ⟨out,z,target,hw₂,hdelete₂,he₂,hs₂,hi₂,hc₂,hr₂,hmem₂,hm₂,hy₂,hstack₂,ha₂,hparent₂,hother₂,hsource₂,heffects₂⟩ :=
    hr₁.delete_child_word layout G Fsrc n (σ.withHeap mid) r address sroot si root (.simple i) k
      (by rw [hy₁];exact hsroot) (by rw [hy₁];exact hsi) htroot hti₂ hmf hk₂ SH hmem₁ hm₁ hif
  have hq₂ : (σ.withHeap mid).heap.field r layout.child_type=q := hq
  rw [hq₂] at hw₂
  have hSource₁ : (Source.execS G Fsrc (n+6) Γ.length none (.expr (sourceStructChildAssign layout sroot si sv) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.ok (.normal ym.1),(.nil,ym.2)) := by rw [hy₁];exact hs₁
  have hSource₂ : (Source.execS G Fsrc (n+5) Γ.length none (.expr (sourceStructChildDelete layout sroot si) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
      (.ok (.normal z.1),(.nil,z.2)) := by rw [hy₂];exact hs₂
  have hout : out=mid.set q (MObj.setElem .dyn (mid.get q) k.1.toNat false) := by
    have hw : mid.writeAddr (.index q .dyn k) false=some (mid.set q (MObj.setElem .dyn (mid.get q) k.1.toNat false)) := by
      simp only [Heap.writeAddr,Heap.setIndex]
      exact if_pos (by change k.1.toNat<mid.len q .dyn;rw [hlen];exact hk)
    exact Option.some.inj (hw₂.symm.trans hw)
  have hread : out.index q .dyn k=some false := by
    rw [hout]
    simp only [Heap.index,Heap.get_set_same,MObj.elems_setElem]
    exact List.getElem?_set_self (by change k.1.toNat<mid.len q .dyn;rw [hlen];exact hk)
  refine ⟨mid,out,ym,z,mm,target,hw₁,hw₂,hSource₁,hSource₂,?_,?_,hc₁,hc₂,?_,hr₁,hr₂,hmem₁,hmem₂,hm₁,hm₂,hy₁,hy₂.trans hy₁,hlen,hparent₂.trans hparent₁,hread,hstack₂.trans hstack₁,?_⟩
  · exact source_items_pair_run G Fsrc (n+1) Γ.length _ _ y ym z hSource₁ hSource₂
  · exact intrinsic_heap_pair_run σ _ _ mid out hi₁ hi₂
  · exact (Evm.run_append_ok hc₁).trans hc₂
  · intro cursor hb ha
    exact ha₂ cursor hb (ha₁ cursor hb ha)


/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.write_delete_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.write_delete_program

end Solidity.Backend.MemoryOps
