import Solidity.Backend.MemoryOps.SourceReferenceWrite

/-! RHS-first resolved parent-element redirection to an existing Boolean
array. Uses the published reference path/slot code, with reached correspondence
from the actual Source/intrinsic pointer write. -/
namespace Solidity.Backend.MemoryOps

def sourceReferenceAssign {E : Source.Env} {Γ : Source.RCtx}
    (root : Source.Idx Γ SourceBoolRefsTy) (index : Source.Idx Γ (.int .u256))
    (rhs : Source.Idx Γ (.array .memory .bool none)) : Source.RExpr E Γ (.array .memory .bool none) :=
  .assign (.indexArray (.local root) (by decide) (.local index) rfl) (.local rhs)

def referenceWriteCode {C : Contract} {Γ : Ctx} (b : Nat)
    (root : Idx Γ (.mem BoolRefsRef)) (index : Idx Γ (.val .uint))
    (rhs : Idx Γ (.mem (.array (.prim .bool)))) : List Evm.Instr :=
  [.mload (Evm.cellOf b rhs)] ++ [.mload (Evm.cellOf b root)] ++
    Evm.compileVal b (.simple (.local index) : Val C Γ .uint) ++ Evm.Memory.writeArrayStackCode

theorem SourceBoolRefsAt.eval_reference_loc {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y a hp r address)
    (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (root : Source.Idx Γ SourceBoolRefsTy) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl a)
    (hindex : y.1.get index=sourceUint k) (hk : k.1.toNat<hp.len r .dyn) :
    (Source.evalLoc G F (n+2) (.indexArray (.local root) (by decide) (.local index) rfl)).run y=
      (.ok (.mem a k.1.toNat),y) := by
  rw [Source.evalLoc,Source.Hoare.run_bind,source_local_value_run G F n y root _ hroot]
  change ((Source.evalE G F (n+1) (.local index)) >>= fun v => Source.indexNat v >>= fun i =>
    Source.indexLoc F (.memRef rfl a : Source.Val E.layout SourceBoolRefsTy) i).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F n y index _ hindex]
  exact hr.indexLoc_run F _ hk

/-- All three executions derive from INITIAL aligned parent/child/local facts.
The value is an already existing child identity, not a copied payload. -/
theorem SourceBoolRefsAt.resolved_reference_assign_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (G : Source.Glob E) (Fsrc : Source.Fr) (n : Nat)
    (σ : State C Δ) (r : HRef σ.H BoolRefsRef) (v : HRef σ.H (.array (.prim .bool)))
    (address : Nat → Nat) (hr : SourceBoolRefsAt y a σ.heap r address)
    (hv : SourceBoolMemoryAt y (address v.id) σ.heap v .dyn)
    (sroot : Source.Idx Γ SourceBoolRefsTy) (si : Source.Idx Γ (.int .u256))
    (srhs : Source.Idx Γ (.array .memory .bool none))
    (root : Idx Δ (.mem BoolRefsRef)) (index : Idx Δ (.val .uint))
    (rhs : Idx Δ (.mem (.array (.prim .bool)))) (i : Fin Evm.W)
    (hroot : y.1.get sroot=.memRef rfl a) (hindex : y.1.get si=sourceUint (Evm.Memory.indexValue i))
    (hval : y.1.get srhs=.memRef rfl (address v.id))
    (htroot : TEnv.get root σ.env=some r) (htindex : TEnv.get index σ.env=Evm.Memory.indexValue i)
    (htval : TEnv.get rhs σ.env=some v) (hi : i.val<σ.heap.len r .dyn)
    (SH : Source.HeapTy) (hmk : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ),
      σ.heap.writeAddr (.index r .dyn (Evm.Memory.indexValue i)) v=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (n+2) (.mem (τ := .array .memory .bool none) a i.val)
        (.memRef rfl (address v.id))).run y=(.ok (),z) ∧
      (Source.evalE G Fsrc (n+3) (sourceReferenceAssign sroot si srhs)).run y=
        (.ok (.val (.memRef rfl (address v.id))),z) ∧
      (Source.execS G Fsrc (n+4) Γ.length none
        (.expr (sourceReferenceAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal y.1),(.nil,z.2)) ∧
      Stmt.run σ (.assignMem (.index .dyn (.var root rfl) (.simple (.local index))) (.ref (.var rhs rfl)))=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (referenceWriteCode (C := C) b root index rhs) m=
        .ok (Evm.Memory.writeMachine m ((base r.id).val+1+i.val) (.val (base v.id))) 0 ∧
      SourceBoolRefsAt z a out r address ∧ Source.MemOK E SH z ∧
      Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap out) base
        (Evm.Memory.writeMachine m ((base r.id).val+1+i.val) (.val (base v.id))) ∧
      z.1=y.1 ∧ MObj.elems .dyn (out.get r)=(MObj.elems .dyn (σ.heap.get r)).set i.val v ∧
      (∀ q : HRef σ.H (.array (.prim .bool)),out.get q=σ.heap.get q) ∧
      (∀ q, SourceBoolMemoryAt y (address q.id) σ.heap q .dyn → SourceBoolMemoryAt z (address q.id) out q .dyn) ∧
      (z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals) := by
  obtain ⟨out,z,ho,hs,hword,hr',hm',ht',hl,he,hchildren,hsource,heffects⟩ :=
    hr.write_reference_word σ r address v hv Fsrc (n+2) i hi SH hmk hm
  have hloc := hr.eval_reference_loc G Fsrc n sroot si (Evm.Memory.indexValue i) hroot hindex
    (by simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hi)
  have hexpr : (Source.evalE G Fsrc (n+3) (sourceReferenceAssign sroot si srhs)).run y=
      (.ok (.val (.memRef rfl (address v.id))),z) := by
    rw [sourceReferenceAssign,Source.evalE,Source.Hoare.run_bind,
      source_local_value_run G Fsrc (n+1) y srhs _ hval]
    change ((Source.evalLoc G Fsrc (n+2) (.indexArray (.local sroot) (by decide) (.local si) rfl)) >>=
      fun loc => Source.writeLoc Fsrc (n+2) loc (.memRef rfl (address v.id)) >>=
        fun _ => pure (Source.RVal.val (.memRef rfl (address v.id)))).run y=_
    rw [Source.Hoare.run_bind,hloc]
    change (Source.writeLoc Fsrc (n+2) (.mem (τ := .array .memory .bool none) a i.val)
      (.memRef rfl (address v.id)) >>= fun _ => pure (Source.RVal.val (.memRef rfl (address v.id)))).run y=_
    rw [Source.Hoare.run_bind,hs]
    rfl
  have hstmt := source_expr_statement_run G Fsrc (n+3) Γ.length _ y z
    (.val (.memRef rfl (address v.id))) hexpr
  rw [hl] at hstmt
  have hint : Stmt.run σ (.assignMem (.index .dyn (.var root rfl) (.simple (.local index))) (.ref (.var rhs rfl)))=
      .ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
    change TRun.assignMem _ _ σ=_
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,
      htroot,htindex,htval,ho,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have hcv := (Evm.Memory.RefPtrFrag.local (b := b) (F := F) rhs rfl).run_of_eval (r := v) hm
    (by simp only [MPath.mvalT,htval])
  have hcp := (Evm.Memory.RefPtrFrag.local (b := b) (F := F) root rfl).run_of_eval (r := r)
    (hm.push (.val (base v.id))) (by simp only [MPath.mvalT,htroot])
  have hci : Evm.run (Evm.compileVal b (.simple (.local index) : Val C Δ .uint))
      ((m.push (.val (base v.id))).push (.val (base r.id)))=
      .ok (((m.push (.val (base v.id))).push (.val (base r.id))).push (.val i)) 0 := by
    obtain ⟨w,hw,hc⟩ := Evm.simple_sim ((hm.push (.val (base v.id))).push (.val (base r.id))).state.core (.local index) rfl
    change Evm.ReprV .uint (TEnv.get index σ.env) w at hw
    rw [htindex] at hw
    obtain ⟨a,ha,heq,rfl⟩ := hw.uint_inv
    have hie : a=i.val := by
      have hh := congrArg Int.toNat heq
      simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hh.symm
    subst a
    exact hc
  have hcode : Evm.run (referenceWriteCode (C := C) b root index rhs) m=
      .ok (Evm.Memory.writeMachine m ((base r.id).val+1+i.val) (.val (base v.id))) 0 := by
    change Evm.run ([.mload (Evm.cellOf b rhs)] ++ ([.mload (Evm.cellOf b root)] ++
      (Evm.compileVal b (.simple (.local index) : Val C Δ .uint) ++ Evm.Memory.writeArrayStackCode))) m=_
    rw [Evm.run_append_ok hcv,Evm.run_append_ok hcp,Evm.run_append_ok hci]
    rw [Evm.Memory.writeArrayStackCode,Evm.Memory.arrayStack_append_eq (m.push (.val (base v.id)))
      (base r.id) i _ (σ.heap.len_dyn_lt r) (hm.arrays.arrays r).length,←Evm.Memory.writeArrayCode]
    exact hword
  exact ⟨out,z,ho,hs,hexpr,hstmt,hint,hcode,hr',hm',ht',hl,he,hchildren,hsource,heffects⟩

/-- Bounds rejection is the Source panic, before any pointer write. -/
theorem SourceBoolRefsAt.reference_assign_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y a hp r address)
    (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (root : Source.Idx Γ SourceBoolRefsTy) (index : Source.Idx Γ (.int .u256))
    (rhs : Source.Idx Γ (.array .memory .bool none)) (k : PrimTy.uint.Denote) (v : Nat)
    (hroot : y.1.get root=.memRef rfl a) (hindex : y.1.get index=sourceUint k)
    (hrhs : y.1.get rhs=.memRef rfl v) (hk : hp.len r .dyn≤k.1.toNat) :
    (Source.evalE G F (n+3) (sourceReferenceAssign root index rhs)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  rw [sourceReferenceAssign,Source.evalE,Source.Hoare.run_bind,
    source_local_value_run G F (n+1) y rhs _ hrhs]
  change ((Source.evalLoc G F (n+2) (.indexArray (.local root) (by decide) (.local index) rfl)) >>=
    fun loc => Source.writeLoc F (n+2) loc (.memRef rfl v) >>= fun _ => pure (Source.RVal.val (.memRef rfl v))).run y=_
  have hloc : (Source.evalLoc G F (n+2) (.indexArray (.local root) (by decide) (.local index) rfl)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
    rw [Source.evalLoc,Source.Hoare.run_bind,source_local_value_run G F n y root _ hroot]
    change ((Source.evalE G F (n+1) (.local index)) >>= fun v => Source.indexNat v >>= fun i =>
      Source.indexLoc F (.memRef rfl a : Source.Val E.layout SourceBoolRefsTy) i).run y=_
    rw [Source.Hoare.run_bind,source_local_value_run G F n y index _ hindex]
    exact hr.indexLoc_bounds F _ hk
  rw [Source.Hoare.run_bind,hloc]

theorem reference_assign_low_horizon {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (root : Source.Idx Γ SourceBoolRefsTy) (index : Source.Idx Γ (.int .u256))
    (rhs : Source.Idx Γ (.array .memory .bool none)) (n : Nat) (hn : n≤2) :
    (Source.evalE G F n (sourceReferenceAssign root index rhs)).run y=(.error .timeout,y) := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 =>
    simp only [sourceReferenceAssign,Source.evalE,Source.Hoare.run_bind]
    rfl

/-- The old primitive/struct allocator does not own reference-array intervals.
A local live-parent bound protects its zero tail; full reference ownership
supplies the remaining frames. This is not a source admission condition. -/
theorem reference_slot_allocator {C : Contract} {Δ : Ctx} {L b frame : Nat}
    {F : Evm.Frag Δ} {σ : State C Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m)
    (r : HRef σ.H BoolRefsRef) (i : Nat) (hi : i<σ.heap.len r .dyn)
    (v : HRef σ.H (.array (.prim .bool))) (cursor : Fin Evm.W)
    (ha : Evm.Memory.StructAllocatorRepr σ.heap base frame cursor m)
    (hlive : (base r.id).val+1+σ.heap.len r .dyn≤cursor.val) :
    Evm.Memory.StructAllocatorRepr (σ.heap.set r (MObj.setElem .dyn (σ.heap.get r) i v)) base frame cursor
      (Evm.Memory.writeMachine m ((base r.id).val+1+i) (.val (base v.id))) := by
  have hn := hm.setReference r i hi v
  have hb := hm.arrays.above r
  have hz := ha.arrays.free.reserved
  refine ⟨⟨hn.state.heap,⟨ha.arrays.free.reserved,ha.arrays.free.above,?_,?_⟩,?_⟩,
    hn.state.structs,hn.state.separated,ha.live⟩
  · change Evm.upd m.mem _ _ 0= _
    rw [Evm.upd_other _ _ (by omega)]
    exact ha.arrays.free.cell
  · intro addr haddr
    change Evm.upd m.mem _ _ addr= _
    rw [Evm.upd_other _ _ (by omega)]
    exact ha.arrays.free.zero addr haddr
  · intro p q
    simpa only [Evm.Memory.dynamicLen_setElem] using ha.arrays.live q

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.eval_reference_loc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.eval_reference_loc

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.resolved_reference_assign_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.resolved_reference_assign_word

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.reference_assign_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.reference_assign_bounds

/-- info: 'Solidity.Backend.MemoryOps.reference_assign_low_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reference_assign_low_horizon

/-- info: 'Solidity.Backend.MemoryOps.reference_slot_allocator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reference_slot_allocator

end Solidity.Backend.MemoryOps
