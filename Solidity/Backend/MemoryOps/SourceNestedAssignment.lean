import Solidity.Backend.MemoryOps.SourceNestedMutation

/-! Actual resolved nested assignment over existing Source syntax, intrinsic
paths and published symbolic-word pointer/write code. No new evaluator or path
compiler: only composition of existing certified operations. -/
namespace Solidity.Backend.MemoryOps

def sourceNestedLoc {E : Source.Env} {Γ : Source.RCtx}
    (root : Source.Idx Γ SourceBoolRefsTy) (i j : Source.Idx Γ (.int .u256)) : Source.RLVal E Γ .bool :=
  .indexArray (.indexArray (.local root) (.local i) rfl) (by decide) (.local j) rfl

def sourceNestedAssign {E : Source.Env} {Γ : Source.RCtx}
    (root : Source.Idx Γ SourceBoolRefsTy) (i j : Source.Idx Γ (.int .u256))
    (rhs : Source.Idx Γ .bool) : Source.RExpr E Γ .bool := .assign (sourceNestedLoc root i j) (.local rhs)

def nestedWriteCode {C : Contract} {Γ : Ctx} (b : Nat)
    (root : Idx Γ (.mem BoolRefsRef)) (i j : Idx Γ (.val .uint)) (rhs : Idx Γ (.val .bool)) : List Evm.Instr :=
  Evm.compileVal b (.simple (.local rhs) : Val C Γ .bool) ++
    ([.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local i) : Val C Γ .uint) ++ Evm.Memory.readArrayStackCode) ++
    Evm.compileVal b (.simple (.local j) : Val C Γ .uint) ++ Evm.Memory.writeArrayStackCode

theorem SourceBoolRefsAt.eval_nested_loc {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ SourceBoolRefsTy) (i j : Source.Idx Γ (.int .u256))
    (k l : PrimTy.uint.Denote) (q : HRef H (.array (.prim .bool)))
    (hroot : y.1.get root=.memRef rfl parentAddress) (hi : y.1.get i=sourceUint k) (hj : y.1.get j=sourceUint l)
    (hq : hp.index r .dyn k=some q) (hl : l.1.toNat<hp.len q .dyn) :
    (Source.evalLoc G F (horizon+3) (sourceNestedLoc root i j)).run y=(.ok (.mem (address q.id) l.1.toNat),y) := by
  have hc := hr.child_at k.1.toNat q hq
  rw [sourceNestedLoc,Source.evalLoc.eq_def,Source.Hoare.run_bind,hr.eval_parent_read G F horizon root i k q hroot hi hq]
  change ((Source.evalE G F (horizon+2) (.local j)) >>= fun v => Source.indexNat v >>= fun n =>
    Source.indexLoc F (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory .bool none)) n).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F (horizon+1) y j _ hj]
  change (Source.indexLoc F (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory .bool none)) l.1.toNat).run y=_
  exact hc.indexLoc_run F _ hl

theorem SourceBoolRefsAt.eval_nested_assign_of_write {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y z : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ SourceBoolRefsTy) (i j : Source.Idx Γ (.int .u256)) (rhs : Source.Idx Γ .bool)
    (k l : PrimTy.uint.Denote) (q : HRef H (.array (.prim .bool))) (v : Bool)
    (hroot : y.1.get root=.memRef rfl parentAddress) (hi : y.1.get i=sourceUint k) (hj : y.1.get j=sourceUint l)
    (hv : y.1.get rhs=.bool v) (hq : hp.index r .dyn k=some q) (hl : l.1.toNat<hp.len q .dyn)
    (hw : (Source.writeLoc (E := E) (Γ := Γ) F (horizon+3) (.mem (address q.id) l.1.toNat) (.bool v)).run y=(.ok (),z)) :
    (Source.evalE G F (horizon+4) (sourceNestedAssign root i j rhs)).run y=(.ok (.val (.bool v)),z) := by
  rw [sourceNestedAssign,Source.evalE,Source.Hoare.run_bind,source_local_value_run G F (horizon+2) y rhs (.bool v) hv]
  change ((Source.evalLoc G F (horizon+3) (sourceNestedLoc root i j)) >>= fun loc =>
    Source.writeLoc F (horizon+3) loc (.bool v) >>= fun _ => pure (Source.RVal.val (.bool v))).run y=_
  rw [Source.Hoare.run_bind,hr.eval_nested_loc G F horizon root i j k l q hroot hi hj hq hl]
  change (Source.writeLoc F (horizon+3) (.mem (address q.id) l.1.toNat) (.bool v) >>= fun _ => pure (Source.RVal.val (.bool v))).run y=_
  rw [Source.Hoare.run_bind,hw]
  rfl

private theorem local_uint_code {C : Contract} {Γ : Ctx} {L b : Nat} {F : Evm.Frag Γ}
    {σ : State C Γ} {m : Evm.Machine} (hm : Evm.Sim C L b F σ m)
    (index : Idx Γ (.val .uint)) (i : Fin Evm.W) (ht : TEnv.get index σ.env=Evm.Memory.indexValue i) :
    Evm.run (Evm.compileVal b (.simple (.local index) : Val C Γ .uint)) m=.ok (m.push (.val i)) 0 := by
  obtain ⟨w,hw,hc⟩ := Evm.simple_sim hm (.local index) rfl
  change Evm.ReprV .uint (TEnv.get index σ.env) w at hw
  rw [ht] at hw
  obtain ⟨a,ha,he,rfl⟩ := hw.uint_inv
  have heq : a=i.val := by
    have h := congrArg Int.toNat he
    simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using h.symm
  subst a
  exact hc

private theorem local_bool_code {C : Contract} {Γ : Ctx} {L b : Nat} {F : Evm.Frag Γ}
    {σ : State C Γ} {m : Evm.Machine} (hm : Evm.Sim C L b F σ m)
    (rhs : Idx Γ (.val .bool)) (v : Bool) (ht : TEnv.get rhs σ.env=v) :
    Evm.run (Evm.compileVal b (.simple (.local rhs) : Val C Γ .bool)) m=.ok (m.push (.val (Evm.bword v))) 0 := by
  obtain ⟨w,hw,hc⟩ := Evm.simple_sim hm (.local rhs) rfl
  change Evm.ReprV .bool (TEnv.get rhs σ.env) w at hw
  rw [ht] at hw
  rw [hw.bool_inv] at hc
  exact hc


private theorem nested_code_of_write {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Evm.Frag Γ}
    {σ : State C Γ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m)
    (root : Idx Γ (.mem BoolRefsRef)) (i j : Idx Γ (.val .uint)) (rhs : Idx Γ (.val .bool))
    (r : HRef σ.H BoolRefsRef) (q : HRef σ.H (.array (.prim .bool))) (k l : Fin Evm.W) (v : Bool)
    (ht : TEnv.get root σ.env=some r) (hi : TEnv.get i σ.env=Evm.Memory.indexValue k)
    (hj : TEnv.get j σ.env=Evm.Memory.indexValue l) (hv : TEnv.get rhs σ.env=v)
    (hq : σ.heap.index r .dyn (Evm.Memory.indexValue k)=some q)
    {out : Evm.Out}
    (hw : Evm.run (Evm.Memory.writeArrayCode (base q.id)) ((m.push (.val (Evm.bword v))).push (.val l))=out) :
    Evm.run (nestedWriteCode (C := C) b root i j rhs) m=out := by
  let ptr := [.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local i) : Val C Γ .uint) ++ Evm.Memory.readArrayStackCode
  have hp : Evm.Memory.RefPtrFrag b F (.loc (.index .dyn (.var root rfl) (.simple (.local i)))) ptr :=
    .index _ _ (.local root rfl) _ rfl
  have he : (MPath.loc (.index .dyn (.var root rfl) (.simple (.local i)))).mvalT σ=.ok q := by
    simp only [MPath.mvalT,MLoc.addrT,Val.evalT,Simple.evalT,ht,hi,Heap.readAddr,hq,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have hval := local_bool_code hm.state.core rhs v hv
  have hptr := hp.run_of_eval (hm.push (.val (Evm.bword v))) he
  have hindex := local_uint_code ((hm.push (.val (Evm.bword v))).push (.val (base q.id))).state.core j l hj
  change Evm.run (Evm.compileVal b (.simple (.local rhs) : Val C Γ .bool) ++
    (ptr ++ (Evm.compileVal b (.simple (.local j) : Val C Γ .uint) ++ Evm.Memory.writeArrayStackCode))) m=_
  rw [Evm.run_append_ok hval,Evm.run_append_ok hptr,Evm.run_append_ok hindex]
  rw [Evm.Memory.writeArrayStackCode,Evm.Memory.arrayStack_append_eq (m.push (.val (Evm.bword v)))
    (base q.id) l _ (σ.heap.len_dyn_lt q) (hm.state.heap.arrays q).length,←Evm.Memory.writeArrayCode]
  exact hw

/-- Actual Source RHS-first nested assignment, actual intrinsic nested address,
and the WHOLE published symbolic-word pointer-path-to-write sequence. All reached
observers are derived from INITIAL alignment and the actual write. -/
theorem SourceBoolRefsAt.resolved_nested_assign_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {parentAddress : Nat}
    (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
    (sroot : Source.Idx Γ SourceBoolRefsTy) (si sj : Source.Idx Γ (.int .u256)) (srhs : Source.Idx Γ .bool)
    (σ : State C Δ) (root : Idx Δ (.mem BoolRefsRef)) (i j : Idx Δ (.val .uint)) (rhs : Idx Δ (.val .bool))
    (r : HRef σ.H BoolRefsRef) (q : HRef σ.H (.array (.prim .bool))) (k l : Fin Evm.W) (v : Bool)
    (address : Nat → Nat) (hr : SourceBoolRefsAt y parentAddress σ.heap r address)
    (hsroot : y.1.get sroot=.memRef rfl parentAddress)
    (hsi : y.1.get si=sourceUint (Evm.Memory.indexValue k)) (hsj : y.1.get sj=sourceUint (Evm.Memory.indexValue l))
    (hsrhs : y.1.get srhs=.bool v) (htroot : TEnv.get root σ.env=some r)
    (hti : TEnv.get i σ.env=Evm.Memory.indexValue k) (htj : TEnv.get j σ.env=Evm.Memory.indexValue l)
    (htrhs : TEnv.get rhs σ.env=v) (hq : σ.heap.index r .dyn (Evm.Memory.indexValue k)=some q)
    (hj : l.val<σ.heap.len q .dyn)
    (hsep : ∀ t∈MObj.elems .dyn (σ.heap.get r), t.id≠q.id → address t.id≠address q.id)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ),
      σ.heap.writeAddr (.index q .dyn (Evm.Memory.indexValue l)) v=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (horizon+3) (.mem (address q.id) l.val) (.bool v)).run y=(.ok (),z) ∧
      (Source.evalLoc G Fsrc (horizon+3) (sourceNestedLoc sroot si sj)).run y=(.ok (.mem (address q.id) l.val),y) ∧
      (Source.evalE G Fsrc (horizon+4) (sourceNestedAssign sroot si sj srhs)).run y=(.ok (.val (.bool v)),z) ∧
      (Source.execS G Fsrc (horizon+5) Γ.length none
        (.expr (sourceNestedAssign sroot si sj srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
      Stmt.run σ (.assignMem (.index .dyn (.loc (.index .dyn (.var root rfl) (.simple (.local i)))) (.simple (.local j)))
        (.val (.simple (.local rhs))))=.ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (nestedWriteCode (C := C) b root i j rhs) m=
        .ok (Evm.Memory.writeMachine m ((base q.id).val+1+l.val) (.val (Evm.bword v))) 0 ∧
      SourceBoolRefsAt z parentAddress out r address ∧ Source.MemOK E SH z ∧
      Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap out) base
        (Evm.Memory.writeMachine m ((base q.id).val+1+l.val) (.val (Evm.bword v))) ∧
      z.1=y.1 ∧ out.get r=σ.heap.get r ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out)
        (Evm.Memory.writeMachine m ((base q.id).val+1+l.val) (.val (Evm.bword v))) := by
  have hmember : q∈MObj.elems .dyn (σ.heap.get r) := by
    obtain ⟨hb,he⟩ := List.getElem?_eq_some_iff.mp hq
    rw [←he];exact List.getElem_mem hb
  obtain ⟨out,z,ho,hs,hword,hr',hmk,hm',hl,hparent⟩ := hr.write_child_word σ r address q hmember hsep Fsrc (horizon+3) l v hj SH hmem hm
  have hsi' := hr.eval_nested_loc G Fsrc horizon sroot si sj (Evm.Memory.indexValue k) (Evm.Memory.indexValue l) q hsroot hsi hsj hq
    (by simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hj)
  have he := hr.eval_nested_assign_of_write G Fsrc horizon sroot si sj srhs (Evm.Memory.indexValue k)
    (Evm.Memory.indexValue l) q v hsroot hsi hsj hsrhs hq
    (by simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hj) (by simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hs)
  have hstmt := source_expr_statement_run G Fsrc (horizon+4) Γ.length _ y z (.val (.bool v)) he
  have hi' : Stmt.run σ (.assignMem (.index .dyn (.loc (.index .dyn (.var root rfl) (.simple (.local i)))) (.simple (.local j)))
      (.val (.simple (.local rhs))))=.ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
    change TRun.assignMem _ _ σ=_
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,htroot,hti,htj,htrhs,
      Heap.readAddr,hq,ho,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  refine ⟨out,z,ho,hs,?_,he,hstmt,hi',nested_code_of_write hm root i j rhs r q k l v htroot hti htj htrhs hq hword,
    hr',hmk,hm',hl,hparent,?_⟩
  · simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hsi'
  · intro cursor hb ha
    have hout : out=σ.heap.set q (MObj.setElem .dyn (σ.heap.get q) l.val v) := by
      have hw : σ.heap.writeAddr (.index q .dyn (Evm.Memory.indexValue l)) v=
          some (σ.heap.set q (MObj.setElem .dyn (σ.heap.get q) l.val v)) := by
        simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast];exact ite_eq_left hj
      exact Option.some.inj (ho.symm.trans hw)
    rw [hout]
    exact ha.setArray q l.val hj v (.val (Evm.bword v)) rfl


theorem SourceBoolRefsAt.eval_nested_loc_parent_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ SourceBoolRefsTy) (i j : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl parentAddress)
    (hi : y.1.get i=sourceUint k) (hk : hp.len r .dyn≤k.1.toNat) :
    (Source.evalLoc G F (horizon+3) (sourceNestedLoc root i j)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  rw [sourceNestedLoc,Source.evalLoc.eq_def,Source.Hoare.run_bind,hr.eval_parent_bounds G F horizon root i k hroot hi hk]

theorem SourceBoolRefsAt.eval_nested_loc_child_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ SourceBoolRefsTy) (i j : Source.Idx Γ (.int .u256))
    (k l : PrimTy.uint.Denote) (q : HRef H (.array (.prim .bool)))
    (hroot : y.1.get root=.memRef rfl parentAddress) (hi : y.1.get i=sourceUint k) (hj : y.1.get j=sourceUint l)
    (hq : hp.index r .dyn k=some q) (hl : hp.len q .dyn≤l.1.toNat) :
    (Source.evalLoc G F (horizon+3) (sourceNestedLoc root i j)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  have hc := hr.child_at k.1.toNat q hq
  rw [sourceNestedLoc,Source.evalLoc.eq_def,Source.Hoare.run_bind,hr.eval_parent_read G F horizon root i k q hroot hi hq]
  change ((Source.evalE G F (horizon+2) (.local j)) >>= fun v => Source.indexNat v >>= fun n =>
    Source.indexLoc F (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory .bool none)) n).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F (horizon+1) y j _ hj]
  change (Source.indexLoc F (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory .bool none)) l.1.toNat).run y=_
  exact hc.indexLoc_bounds F _ hl

private theorem nested_assign_error {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat) (y : Source.EMState E Γ)
    (root : Source.Idx Γ SourceBoolRefsTy) (i j : Source.Idx Γ (.int .u256)) (rhs : Source.Idx Γ .bool) (v : Bool)
    (hv : y.1.get rhs=.bool v)
    (hl : (Source.evalLoc G F (horizon+3) (sourceNestedLoc root i j)).run y=(.error (.revert (Source.panicData .index)),y)) :
    (Source.evalE G F (horizon+4) (sourceNestedAssign root i j rhs)).run y=(.error (.revert (Source.panicData .index)),y) := by
  rw [sourceNestedAssign,Source.evalE,Source.Hoare.run_bind,source_local_value_run G F (horizon+2) y rhs (.bool v) hv]
  change ((Source.evalLoc G F (horizon+3) (sourceNestedLoc root i j)) >>= fun loc =>
    Source.writeLoc F (horizon+3) loc (.bool v) >>= fun _ => pure (Source.RVal.val (.bool v))).run y=_
  rw [Source.Hoare.run_bind,hl]

theorem SourceBoolRefsAt.nested_assign_parent_bounds {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {parentAddress : Nat}
    (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
    (sroot : Source.Idx Γ SourceBoolRefsTy) (si sj : Source.Idx Γ (.int .u256)) (srhs : Source.Idx Γ .bool)
    (σ : State C Δ) (root : Idx Δ (.mem BoolRefsRef)) (i j : Idx Δ (.val .uint)) (rhs : Idx Δ (.val .bool))
    (r : HRef σ.H BoolRefsRef) (k : Fin Evm.W) (v : Bool) (address : Nat → Nat)
    (hr : SourceBoolRefsAt y parentAddress σ.heap r address)
    (hsroot : y.1.get sroot=.memRef rfl parentAddress) (hsi : y.1.get si=sourceUint (Evm.Memory.indexValue k))
    (hsrhs : y.1.get srhs=.bool v) (htroot : TEnv.get root σ.env=some r)
    (hti : TEnv.get i σ.env=Evm.Memory.indexValue k) (htrhs : TEnv.get rhs σ.env=v)
    (hk : σ.heap.len r .dyn≤k.val)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    (Source.evalE G Fsrc (horizon+4) (sourceNestedAssign sroot si sj srhs)).run y=(.error (.revert (Source.panicData .index)),y) ∧
    Stmt.run σ (.assignMem (.index .dyn (.loc (.index .dyn (.var root rfl) (.simple (.local i)))) (.simple (.local j)))
      (.val (.simple (.local rhs))))=.error .revert ∧ Evm.run (nestedWriteCode (C := C) b root i j rhs) m=.revert := by
  have hn : σ.heap.index r .dyn (Evm.Memory.indexValue k)=none := by
    simp only [Heap.index,Evm.Memory.indexValue,Int.toNat_natCast];exact List.getElem?_eq_none_iff.mpr hk
  let ptr := [.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local i) : Val C Δ .uint) ++ Evm.Memory.readArrayStackCode
  have hp : Evm.Memory.RefPtrFrag b F (.loc (.index .dyn (.var root rfl) (.simple (.local i)))) ptr := .index _ _ (.local root rfl) _ rfl
  have he : (MPath.loc (.index .dyn (.var root rfl) (.simple (.local i)))).mvalT σ=.error .revert := by
    simp only [MPath.mvalT,MLoc.addrT,Val.evalT,Simple.evalT,htroot,hti,Heap.readAddr,hn,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have hptr : Evm.run ptr (m.push (.val (Evm.bword v)))=.revert := by
    rcases hp.correct (hm.push (.val (Evm.bword v))) with ⟨q,hq,_⟩|⟨_,hc⟩
    · rw [he] at hq;cases hq
    · exact hc
  refine ⟨nested_assign_error G Fsrc horizon y sroot si sj srhs v hsrhs
    (hr.eval_nested_loc_parent_bounds G Fsrc horizon sroot si sj (Evm.Memory.indexValue k) hsroot hsi
      (by simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hk)),?_,?_⟩
  · change TRun.assignMem _ _ σ=_
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,htroot,hti,htrhs,Heap.readAddr,hn,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  · change Evm.run (Evm.compileVal b (.simple (.local rhs) : Val C Δ .bool) ++ (ptr ++ _)) m=_
    rw [Evm.run_append_ok (local_bool_code hm.state.core rhs v htrhs)]
    exact Evm.run_append_revert hptr

theorem SourceBoolRefsAt.nested_assign_child_bounds {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {parentAddress : Nat}
    (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
    (sroot : Source.Idx Γ SourceBoolRefsTy) (si sj : Source.Idx Γ (.int .u256)) (srhs : Source.Idx Γ .bool)
    (σ : State C Δ) (root : Idx Δ (.mem BoolRefsRef)) (i j : Idx Δ (.val .uint)) (rhs : Idx Δ (.val .bool))
    (r : HRef σ.H BoolRefsRef) (q : HRef σ.H (.array (.prim .bool))) (k l : Fin Evm.W) (v : Bool)
    (address : Nat → Nat) (hr : SourceBoolRefsAt y parentAddress σ.heap r address)
    (hsroot : y.1.get sroot=.memRef rfl parentAddress)
    (hsi : y.1.get si=sourceUint (Evm.Memory.indexValue k)) (hsj : y.1.get sj=sourceUint (Evm.Memory.indexValue l))
    (hsrhs : y.1.get srhs=.bool v) (htroot : TEnv.get root σ.env=some r)
    (hti : TEnv.get i σ.env=Evm.Memory.indexValue k) (htj : TEnv.get j σ.env=Evm.Memory.indexValue l) (htrhs : TEnv.get rhs σ.env=v)
    (hq : σ.heap.index r .dyn (Evm.Memory.indexValue k)=some q) (hl : σ.heap.len q .dyn≤l.val)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    (Source.evalE G Fsrc (horizon+4) (sourceNestedAssign sroot si sj srhs)).run y=(.error (.revert (Source.panicData .index)),y) ∧
    Stmt.run σ (.assignMem (.index .dyn (.loc (.index .dyn (.var root rfl) (.simple (.local i)))) (.simple (.local j)))
      (.val (.simple (.local rhs))))=.error .revert ∧ Evm.run (nestedWriteCode (C := C) b root i j rhs) m=.revert := by
  have hn : σ.heap.writeAddr (.index q .dyn (Evm.Memory.indexValue l)) v=none := by
    simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast]
    exact ite_eq_right (Nat.not_lt.mpr hl)
  have hword : Evm.run (Evm.Memory.writeArrayCode (base q.id)) ((m.push (.val (Evm.bword v))).push (.val l))=.revert := by
    rcases Evm.Memory.writeArray_correct (hm.state.heap.arrays q) l v (.val (Evm.bword v)) rfl with ⟨_,hh,_,_⟩|⟨_,hc⟩
    · rw [hn] at hh;cases hh
    · exact hc
  refine ⟨nested_assign_error G Fsrc horizon y sroot si sj srhs v hsrhs
    (hr.eval_nested_loc_child_bounds G Fsrc horizon sroot si sj (Evm.Memory.indexValue k) (Evm.Memory.indexValue l) q hsroot hsi hsj hq
      (by simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hl)),?_,
    nested_code_of_write hm root i j rhs r q k l v htroot hti htj htrhs hq hword⟩
  change TRun.assignMem _ _ σ=_
  simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,htroot,hti,htj,htrhs,
    Heap.readAddr,hq,hn,TRes.ofOpt,bind,Except.bind,pure,Except.pure]

theorem source_nested_assign_low_horizon {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (root : Source.Idx Γ SourceBoolRefsTy) (i j : Source.Idx Γ (.int .u256)) (rhs : Source.Idx Γ .bool) :
    ∀ n, n≤3 → (Source.evalE G F n (sourceNestedAssign root i j rhs)).run y=(.error .timeout,y) := by
  intro n hn
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | n+4 => omega

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.eval_nested_loc_parent_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.eval_nested_loc_parent_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.eval_nested_loc_child_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.eval_nested_loc_child_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.nested_assign_parent_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.nested_assign_parent_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.nested_assign_child_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.nested_assign_child_bounds
/-- info: 'Solidity.Backend.MemoryOps.source_nested_assign_low_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_nested_assign_low_horizon

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.resolved_nested_assign_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.resolved_nested_assign_word

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.eval_nested_loc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.eval_nested_loc
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.eval_nested_assign_of_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.eval_nested_assign_of_write
end Solidity.Backend.MemoryOps
