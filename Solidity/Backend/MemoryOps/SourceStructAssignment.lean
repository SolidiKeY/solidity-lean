import Solidity.Backend.MemoryOps.SourceStructMemory

/-! Actual resolved named struct-member pointer assignment. Published pointer,
writeReference_correct, StateRepr and allocator certificates remain read-only. -/
namespace Solidity.Backend.MemoryOps
open Semantics

def sourceStructAssign {E : Source.Env} {Γ : Source.RCtx}
    (layout : SourceBoolStructLayout E dn s tag child)
    (root : Source.Idx Γ (.struct .memory dn)) (rhs : Source.Idx Γ SourceBoolArrayTy) :
    Source.RExpr E Γ SourceBoolArrayTy :=
  .assign (.member (.local root) (by decide) 1 layout.source_child_type) (.local rhs)

def structReferenceWriteCode {Γ : Ctx} (b : Nat)
    (root : Idx Γ (.mem (.struct s))) (rhs : Idx Γ (.mem (.array (.prim .bool)))) (child : Name) :
    List Evm.Instr := [.mload (Evm.cellOf b rhs)] ++ [.mload (Evm.cellOf b root)] ++
      Evm.Memory.writeFieldCode (Evm.Memory.fieldOffset (structDef s) child)

theorem source_struct_member_loc {E : Source.Env} {Γ : Source.RCtx}
    (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (y : Source.EMState E Γ)
    (root : Source.Idx Γ (.struct .memory dn)) (a : Nat) (hroot : y.1.get root=.memRef rfl a) :
    (Source.evalLoc G F (n+2) (.member (.local root) (by decide) 1 layout.source_child_type)).run y=
      (.ok (.mem a 1),y) := by
  rw [Source.evalLoc,Source.Hoare.run_bind,source_local_value_run G F n y root _ hroot]
  rfl

/-- INITIAL declaration/name layout and independent heap observations derive
actual Source expression/statement, intrinsic assignment and the WHOLE published
word reference-field sequence. No desired postcorrespondence is an input. -/
theorem SourceBoolStructAt.resolved_assign_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (Fsrc : Source.Fr) (n : Nat)
    (σ : State C Δ) (r : HRef σ.H (.struct s)) (v : HRef σ.H (.array (.prim .bool)))
    (address : Nat → Nat) (hr : SourceBoolStructAt y a σ.heap r address layout)
    (hv : SourceBoolMemoryAt y (address v.id) σ.heap v .dyn)
    (sroot : Source.Idx Γ (.struct .memory dn)) (srhs : Source.Idx Γ SourceBoolArrayTy)
    (root : Idx Δ (.mem (.struct s))) (rhs : Idx Δ (.mem (.array (.prim .bool))))
    (hsroot : y.1.get sroot=.memRef rfl a) (hsrhs : y.1.get srhs=.memRef rfl (address v.id))
    (htroot : TEnv.get root σ.env=some r) (htrhs : TEnv.get rhs σ.env=some v)
    (hmf : (Ty.ref (.struct s)).mapFree=true)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) :
    ∃ (z : Source.EMState E Γ) (target : Evm.Machine),
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (n+2) (.mem (τ := SourceBoolArrayTy) a 1)
        (.memRef rfl (address v.id))).run y=(.ok (),z) ∧
      (Source.evalE G Fsrc (n+3) (sourceStructAssign layout sroot srhs)).run y=
        (.ok (.val (.memRef rfl (address v.id))),z) ∧
      (Source.execS G Fsrc (n+4) Γ.length none
        (.expr (sourceStructAssign layout sroot srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal y.1),(.nil,z.2)) ∧
      Stmt.run σ (.assignMem (.field (.var root hmf) child layout.child_type) (.ref (.var rhs rfl)))=
        .ok ⟨σ.withHeap (σ.heap.setField r layout.child_type v),List.prefix_refl _⟩ ∧
      Evm.run (structReferenceWriteCode b root rhs child) m=.ok target 0 ∧
      SourceBoolStructAt z a (σ.heap.setField r layout.child_type v) r address layout ∧ Source.MemOK E SH z ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap (σ.heap.setField r layout.child_type v)) base target ∧
      z.1=y.1 ∧ target.stack=m.stack ∧
      target=Evm.Memory.writeMachine m ((base r.id).val+Evm.Memory.fieldOffset (structDef s) child) (.val (base v.id)) ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap (σ.heap.setField r layout.child_type v)) target ∧
      (σ.heap.setField r layout.child_type v).field r layout.tag_type=σ.heap.field r layout.tag_type ∧
      (σ.heap.setField r layout.child_type v).field r layout.child_type=v ∧
      (∀ q : HRef σ.H (.array (.prim .bool)),(σ.heap.setField r layout.child_type v).get q=σ.heap.get q) ∧
      (∀ q,SourceBoolMemoryAt y (address q.id) σ.heap q .dyn →
        SourceBoolMemoryAt z (address q.id) (σ.heap.setField r layout.child_type v) q .dyn) ∧
      (z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals) := by
  obtain ⟨z,hs,hr',hmk,hl,htag,hchild,hchildren,hsource,heffects⟩ := hr.write_reference v hv Fsrc (n+2) SH hmem
  have he : (Source.evalE G Fsrc (n+3) (sourceStructAssign layout sroot srhs)).run y=
      (.ok (.val (.memRef rfl (address v.id))),z) := by
    rw [sourceStructAssign,Source.evalE,Source.Hoare.run_bind,
      source_local_value_run G Fsrc (n+1) y srhs _ hsrhs]
    change ((Source.evalLoc G Fsrc (n+2) (.member (.local sroot) (by decide) 1 layout.source_child_type)) >>=
      fun loc => Source.writeLoc Fsrc (n+2) loc (.memRef rfl (address v.id)) >>=
        fun _ => pure (Source.RVal.val (.memRef rfl (address v.id)))).run y=_
    rw [Source.Hoare.run_bind,source_struct_member_loc layout G Fsrc n y sroot a hsroot]
    change (Source.writeLoc Fsrc (n+2) (.mem (τ := SourceBoolArrayTy) a 1) (.memRef rfl (address v.id)) >>=
      fun _ => pure (Source.RVal.val (.memRef rfl (address v.id)))).run y=_
    rw [Source.Hoare.run_bind,hs]
    rfl
  have hsstmt := source_expr_statement_run G Fsrc (n+3) Γ.length _ y z (.val (.memRef rfl (address v.id))) he
  rw [hl] at hsstmt
  have hi : TRun.assignMem (.field (.var root hmf) child layout.child_type) (.ref (.var rhs rfl)) σ=
      .ok ⟨σ.withHeap (σ.heap.setField r layout.child_type v),List.prefix_refl _⟩ := by
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,htroot,htrhs,Heap.writeAddr,
      TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have cert := Evm.Memory.writeReference_correct hm (Evm.Memory.PtrFrag.local root hmf)
    (Evm.Memory.PtrFrag.local rhs rfl) layout.child_type
  rw [hi] at cert
  rcases cert with ⟨o,target,ho,hcode,hstate,hstack,halloc⟩ | ⟨hbad,_⟩
  · cases Except.ok.inj ho
    have hcv := (Evm.Memory.PtrFrag.local (b := b) rhs rfl).run_of_eval (r := v) hm
      (by simp only [MPath.mvalT,htrhs])
    have hcp := (Evm.Memory.PtrFrag.local (b := b) root hmf).run_of_eval (r := r) (hm.push (.val (base v.id)))
      (by simp only [MPath.mvalT,htroot])
    have hb : (base r.id).val+Evm.Memory.fieldOffset (structDef s) child<Evm.W := by
      have ho := Evm.Memory.fieldOffset_bound layout.child_type
      have hs := (hm.structs.objects r).space
      omega
    have hc : Evm.run (structReferenceWriteCode b root rhs child) m=
        .ok (Evm.Memory.writeMachine m ((base r.id).val+Evm.Memory.fieldOffset (structDef s) child) (.val (base v.id))) 0 := by
      rw [structReferenceWriteCode,List.append_assoc,Evm.run_append_ok hcv,Evm.run_append_ok hcp]
      exact Evm.Memory.writeFieldWord_run m (base r.id) _ _ hb
    have ht := (Evm.Out.ok.inj (hcode.symm.trans hc)).1
    exact ⟨z,target,hs,he,hsstmt,hi,hcode,hr',hmk,hstate,hl,hstack,ht,halloc,htag,hchild,hchildren,hsource,heffects⟩
  · cases hbad

theorem source_struct_assign_low_horizon {E : Source.Env} {Γ : Source.RCtx}
    (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (root : Source.Idx Γ (.struct .memory dn)) (rhs : Source.Idx Γ SourceBoolArrayTy) :
    ∀ n,n≤2 → (Source.evalE G F n (sourceStructAssign layout root rhs)).run y=(.error .timeout,y) := by
  intro n hn
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n+3 => omega
/-- info: 'Solidity.Backend.MemoryOps.source_struct_member_loc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_struct_member_loc

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.resolved_assign_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolStructAt.resolved_assign_word

/-- info: 'Solidity.Backend.MemoryOps.source_struct_assign_low_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_struct_assign_low_horizon

end Solidity.Backend.MemoryOps
