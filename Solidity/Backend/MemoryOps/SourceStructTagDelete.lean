import Solidity.Backend.MemoryOps.SourceStructTag
import Solidity.Evm.MemoryDelete

/-! Named uint256 deletion uses the actual Source default and the published
primitive deletion/write certificate. Reference children are framed, not copied. -/
namespace Solidity.Backend.MemoryOps
open Semantics

def sourceStructTagDelete {E : Source.Env} {Γ : Source.RCtx}
    (layout : SourceBoolStructLayout E dn s tag child)
    (root : Source.Idx Γ (.struct .memory dn)) : Source.RExpr E Γ (.tuple []) :=
  .delete (.member (.local root) (by decide) 0 layout.source_tag_type)

def structTagDeleteCode {C : Contract} {Δ : Ctx} (b : Nat)
    (root : Idx Δ (.mem (.struct s))) (tag : Name) : List Evm.Instr :=
  structTagWriteCode (C := C) b root tag (Evm.Memory.deleteDefaultValue .uint)

/-- Actual named-member deletion from INITIAL correspondence. The zero default,
Source unit result, intrinsic delete and whole pointer/write program are derived.
The selected child and all represented old Boolean aliases retain their contents. -/
theorem SourceBoolStructAt.delete_tag_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (Fsrc : Source.Fr) (n : Nat)
    (σ : State C Δ) (r : HRef σ.H (.struct s)) (address : Nat → Nat)
    (hr : SourceBoolStructAt y a σ.heap r address layout)
    (sroot : Source.Idx Γ (.struct .memory dn))
    (root : Idx Δ (.mem (.struct s)))
    (hsroot : y.1.get sroot=.memRef rfl a)
    (htroot : TEnv.get root σ.env=some r)
    (hmf : (Ty.ref (.struct s)).mapFree=true) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) :
    let out := σ.heap.setField r layout.tag_type (PrimTy.dflt .uint)
    ∃ (z : Source.EMState E Γ) (target : Evm.Machine),
      (Source.deleteLoc (E := E) (Γ := Γ) Fsrc (n+2) (τ := .int .u256) (.mem a 0)).run y=(.ok (),z) ∧
      (Source.evalE G Fsrc (n+3) (sourceStructTagDelete layout sroot)).run y=(.ok Source.RVal.unit,z) ∧
      (Source.execS G Fsrc (n+4) Γ.length none (.expr (sourceStructTagDelete layout sroot) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
      Stmt.run σ (.deleteMem (.loc (.field (.var root hmf) tag layout.tag_type)) rfl)=.ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (structTagDeleteCode (C := C) b root tag) m=.ok target 0 ∧
      SourceBoolStructAt z a out r address layout ∧ Source.MemOK E SH z ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      z.1=y.1 ∧ target.stack=m.stack ∧ Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target ∧
      out.field r layout.tag_type=PrimTy.dflt .uint ∧ out.field r layout.child_type=σ.heap.field r layout.child_type ∧
      (∀ q,SourceBoolMemoryAt y (address q.id) σ.heap q .dyn → SourceBoolMemoryAt z (address q.id) out q .dyn) ∧
      (∀ b,b≠a → z.2.heap.get b=y.2.heap.get b) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  dsimp only
  obtain ⟨z,hw,hr',hmk,hl,htag,hchild,hchildren,hsource,hframe,hex,hev,hlog,hfn⟩ := hr.write_tag (PrimTy.dflt .uint) Fsrc (n+2) SH hmem
  have hd : (Source.deleteLoc (E := E) (Γ := Γ) Fsrc (n+2) (τ := .int .u256) (.mem a 0)).run y=(.ok (),z) := hw
  have he : (Source.evalE G Fsrc (n+3) (sourceStructTagDelete layout sroot)).run y=(.ok Source.RVal.unit,z) := by
    have hloc : (Source.evalLoc G Fsrc (n+2) (.member (.local sroot) (by decide) 0 layout.source_tag_type)).run y=(.ok (.mem a 0),y) := by
      rw [Source.evalLoc,Source.Hoare.run_bind,source_local_value_run G Fsrc n y sroot (.memRef rfl a) hsroot]
      rfl
    rw [sourceStructTagDelete,Source.evalE,Source.Hoare.run_bind,hloc]
    change (Source.deleteLoc Fsrc (n+2) (τ := .int .u256) (.mem a 0) >>= fun _ => pure Source.RVal.unit).run y=_
    rw [Source.Hoare.run_bind,hd]
    rfl
  have hi : TRun.assignMem (.field (.var root hmf) tag layout.tag_type) (.val (Evm.Memory.deleteDefaultValue .uint)) σ=.ok ⟨σ.withHeap (σ.heap.setField r layout.tag_type (PrimTy.dflt .uint)),List.prefix_refl _⟩ := by
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,htroot,Evm.Memory.deleteDefaultValue_eval,Heap.writeAddr,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have hdelete : TRun.deleteMem (.loc (.field (.var root hmf) tag layout.tag_type)) σ=.ok ⟨σ.withHeap (σ.heap.setField r layout.tag_type (PrimTy.dflt .uint)),List.prefix_refl _⟩ := by
    rw [Evm.Memory.deleteMem_primitive_eq_assign]
    exact hi
  have cert := Evm.Memory.PtrFrag.writePrimitive hm (Evm.Memory.PtrFrag.local root hmf) layout.tag_type (Evm.Memory.deleteDefaultValue .uint) (Evm.compileVal b (Evm.Memory.deleteDefaultValue .uint)) (Evm.val_sim _ hm.core rfl)
  rw [hi] at cert
  rcases cert with ⟨o,target,ho,hcode,hstate,hstack,halloc⟩ | ⟨hbad,_⟩
  · cases Except.ok.inj ho
    exact ⟨z,target,hd,he,source_expr_statement_run G Fsrc (n+3) Γ.length _ y z _ he,hdelete,hcode,hr',hmk,hstate,hl,hstack,halloc,htag,hchild,hsource,hframe,hex,hev,hlog,hfn⟩
  · cases hbad

theorem source_struct_tag_delete_low_horizon {E : Source.Env} {Γ : Source.RCtx}
    (layout : SourceBoolStructLayout E dn s tag child)
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (root : Source.Idx Γ (.struct .memory dn)) :
    ∀ n,n≤2 → (Source.evalE G F n (sourceStructTagDelete layout root)).run y=(.error .timeout,y) := by
  intro n hn
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n+3 => omega

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.delete_tag_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolStructAt.delete_tag_word
/-- info: 'Solidity.Backend.MemoryOps.source_struct_tag_delete_low_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_struct_tag_delete_low_horizon
end Solidity.Backend.MemoryOps
