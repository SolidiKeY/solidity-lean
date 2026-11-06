import Solidity.Backend.MemoryOps.SourceIndexedDelete
import Solidity.Evm.MemorySource

/-! Supported resolved Source indexed assignment consumes the existing RHS-first
Source evaluator and published word write certificate. No assignment semantics,
IR, allocator or conversion layer is introduced. -/
namespace Solidity.Backend.MemoryOps

def sourceIndexedAssign {E : Source.Env} {Γ : Source.RCtx}
    (root : Source.Idx Γ (.array .memory .bool none))
    (index : Source.Idx Γ (.int .u256)) (rhs : Source.Idx Γ .bool) : Source.RExpr E Γ .bool :=
  .assign (.indexArray (.local root) (by decide) (.local index) rfl) (.local rhs)

theorem SourceBoolMemoryAt.eval_assign_of_run {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y z : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ (.array .memory .bool none)) (index : Source.Idx Γ (.int .u256))
    (rhs : Source.Idx Γ .bool) (k : PrimTy.uint.Denote) (value : Bool)
    (hroot : y.1.get root=.memRef rfl address) (hindex : y.1.get index=sourceUint k)
    (hrhs : y.1.get rhs=.bool value) (hk : k.1.toNat<hp.len r a)
    (hwrite : (Source.writeLoc (E := E) (Γ := Γ) F (horizon+2) (.mem address k.1.toNat) (.bool value)).run y=(.ok (),z)) :
    (Source.evalE G F (horizon+3) (sourceIndexedAssign root index rhs)).run y=(.ok (.val (.bool value)),z) := by
  unfold sourceIndexedAssign
  rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F (horizon+1) y rhs (.bool value) hrhs]
  change ((Source.evalLoc G F (horizon+2)
    (.indexArray (.local root) (by decide) (.local index) rfl)) >>= fun loc =>
    Source.writeLoc F (horizon+2) loc (.bool value) >>= fun _ => pure (Source.RVal.val (.bool value))).run y=_
  rw [Source.Hoare.run_bind,hr.eval_index_loc G F horizon root index k hroot hindex hk]
  change ((Source.writeLoc (E := E) (Γ := Γ) F (horizon+2) (.mem address k.1.toNat) (.bool value)) >>=
    fun _ => pure (Source.RVal.val (.bool value))).run y=_
  rw [Source.Hoare.run_bind,hwrite]
  rfl

theorem SourceBoolMemoryAt.eval_assign_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ (.array .memory .bool none)) (index : Source.Idx Γ (.int .u256))
    (rhs : Source.Idx Γ .bool) (k : PrimTy.uint.Denote) (value : Bool)
    (hroot : y.1.get root=.memRef rfl address) (hindex : y.1.get index=sourceUint k)
    (hrhs : y.1.get rhs=.bool value) (hk : hp.len r a≤k.1.toNat) :
    (Source.evalE G F (horizon+3) (sourceIndexedAssign root index rhs)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  unfold sourceIndexedAssign
  rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F (horizon+1) y rhs (.bool value) hrhs]
  change ((Source.evalLoc G F (horizon+2)
    (.indexArray (.local root) (by decide) (.local index) rfl)) >>= fun loc =>
    Source.writeLoc F (horizon+2) loc (.bool value) >>= fun _ => pure (Source.RVal.val (.bool value))).run y=_
  rw [Source.Hoare.run_bind,hr.eval_index_bounds G F horizon root index k hroot hindex hk]

theorem resolved_assign_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (horizon : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .bool)))
    (hr : SourceBoolMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory .bool none)) (sindex : Source.Idx Γ (.int .u256))
    (srhs : Source.Idx Γ .bool) (root : Idx Δ (.mem (.array (.prim .bool))))
    (index : Idx Δ (.val .uint)) (rhs : Idx Δ (.val .bool)) (k : PrimTy.uint.Denote) (value : Bool)
    (hsroot : y.1.get sroot=.memRef rfl address) (hsindex : y.1.get sindex=sourceUint k)
    (hsrhs : y.1.get srhs=.bool value) (htroot : TEnv.get root σ.env=some r)
    (htindex : TEnv.get index σ.env=k) (htrhs : TEnv.get rhs σ.env=value)
    (hk : k.1.toNat<σ.heap.len r .dyn)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) :
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      σ.heap.writeAddr (.index r .dyn k) value=some out ∧
      (Source.evalE G Fsrc (horizon+3) (sourceIndexedAssign sroot sindex srhs)).run y=(.ok (.val (.bool value)),z) ∧
      (Source.execS G Fsrc (horizon+4) Γ.length none
        (.expr (sourceIndexedAssign sroot sindex srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal y.1),(.nil,z.2)) ∧
      Stmt.run σ (.assignMem (.index .dyn (.var root rfl) (.simple (.local index))) (.val (.simple (.local rhs))))=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local index)) (.simple (.local rhs))) m=.ok target 0 ∧
      SourceBoolMemoryAt z address out r .dyn ∧ Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      Source.MemOK E SH z ∧ z.1=y.1 ∧ target.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target := by
  obtain ⟨out,z,hw,hs,hr'⟩ := hr.write_addr Fsrc (horizon+2) k value hk
  have hi : TRun.assignMem (.index .dyn (.var root rfl) (.simple (.local index))) (.val (.simple (.local rhs))) σ=
      .ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,
      htroot,htindex,htrhs,bind,Except.bind,pure,Except.pure,hw,TRes.ofOpt]
  have hc := Evm.Memory.writeLocal_correct hm root (.simple (.local index)) (.simple (.local rhs)) rfl rfl
  rw [hi] at hc
  rcases hc with ⟨o,target,heq,hcode,hm',hstack,halloc⟩ | ⟨hbad,_⟩
  · cases Except.ok.inj heq
    have he := hr.eval_assign_of_run G Fsrc horizon sroot sindex srhs k value hsroot hsindex hsrhs hk hs
    have hstmt := source_expr_statement_run G Fsrc (horizon+3) Γ.length _ y z (.val (.bool value)) he
    obtain ⟨ht,hwrite⟩ := source_bool_write y address _ hr k.1.toNat hk value
    have hl : z.1=y.1 := congrArg (fun q : Except Source.Halt Unit × Source.EMState E Γ => q.2.1) (hs.symm.trans hwrite)
    have hmk := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) Fsrc (horizon+2)
      (.mem (τ := .bool) address k.1.toNat) (.bool value) y ⟨hmem,trivial⟩
    rw [hs] at hmk
    refine ⟨out,z,target,hw,he,?_,hi,hcode,hr',hm',hmk,hl,hstack,halloc⟩
    simpa only [hl] using hstmt
  · cases hbad

/-- Bounds rejection derives both actual Source syntax and target observations
from the runtime local values; panic bytes and target revert stay distinct. -/
theorem resolved_assign_word_bounds {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (horizon : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .bool)))
    (hr : SourceBoolMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory .bool none)) (sindex : Source.Idx Γ (.int .u256))
    (srhs : Source.Idx Γ .bool) (root : Idx Δ (.mem (.array (.prim .bool))))
    (index : Idx Δ (.val .uint)) (rhs : Idx Δ (.val .bool)) (k : PrimTy.uint.Denote) (value : Bool)
    (hsroot : y.1.get sroot=.memRef rfl address) (hsindex : y.1.get sindex=sourceUint k)
    (hsrhs : y.1.get srhs=.bool value) (htroot : TEnv.get root σ.env=some r)
    (htindex : TEnv.get index σ.env=k) (htrhs : TEnv.get rhs σ.env=value)
    (hk : σ.heap.len r .dyn≤k.1.toNat)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) :
    (Source.evalE G Fsrc (horizon+3) (sourceIndexedAssign sroot sindex srhs)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
    Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local index)) (.simple (.local rhs))) m=.revert := by
  have hn : σ.heap.writeAddr (.index r .dyn k) value=none := by
    simp only [Heap.len] at hk
    simp only [Heap.writeAddr,Heap.setIndex,show ¬k.1.toNat<(MObj.elems .dyn (σ.heap.get r)).length from Nat.not_lt.mpr hk,↓reduceIte]
  have hi : TRun.assignMem (.index .dyn (.var root rfl) (.simple (.local index))) (.val (.simple (.local rhs))) σ=
      .error .revert := by
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,
      htroot,htindex,htrhs,bind,Except.bind,pure,Except.pure,hn,TRes.ofOpt]
  have hc := Evm.Memory.writeLocal_correct hm root (.simple (.local index)) (.simple (.local rhs)) rfl rfl
  rw [hi] at hc
  refine ⟨hr.eval_assign_bounds G Fsrc horizon sroot sindex srhs k value hsroot hsindex hsrhs hk,?_⟩
  rcases hc with ⟨o,target,heq,_⟩ | ⟨_,hcode⟩
  · cases heq
  · exact hcode

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.eval_assign_of_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.eval_assign_of_run
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.eval_assign_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.eval_assign_bounds
/-- info: 'Solidity.Backend.MemoryOps.resolved_assign_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resolved_assign_word
/-- info: 'Solidity.Backend.MemoryOps.resolved_assign_word_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resolved_assign_word_bounds
end Solidity.Backend.MemoryOps
