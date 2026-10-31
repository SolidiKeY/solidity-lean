import Solidity.Backend.MemoryOps.SourceNestedAssignment

/-! Existing resolved nested Source delete and published symbolic-word clear.
The independent Source zeroVal supplies false; no RHS-local ghost input, decoder,
constructor, alternate evaluator or recursive deletion algorithm is added. -/
namespace Solidity.Backend.MemoryOps

def sourceNestedDelete {E : Source.Env} {Γ : Source.RCtx}
    (root : Source.Idx Γ SourceBoolRefsTy) (i j : Source.Idx Γ (.int .u256)) : Source.RExpr E Γ (.tuple []) :=
  .delete (sourceNestedLoc root i j)

def nestedDeleteCode {C : Contract} {Γ : Ctx} (b : Nat)
    (root : Idx Γ (.mem BoolRefsRef)) (i j : Idx Γ (.val .uint)) : List Evm.Instr :=
  [.push (.val (Evm.bword false))] ++ ([.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local i) : Val C Γ .uint) ++ Evm.Memory.readArrayStackCode) ++
    Evm.compileVal b (.simple (.local j) : Val C Γ .uint) ++ Evm.Memory.writeArrayStackCode

theorem SourceBoolRefsAt.eval_nested_delete_of_write {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y z : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ SourceBoolRefsTy) (i j : Source.Idx Γ (.int .u256))
    (k l : PrimTy.uint.Denote) (q : HRef H (.array (.prim .bool)))
    (hroot : y.1.get root=.memRef rfl parentAddress) (hi : y.1.get i=sourceUint k) (hj : y.1.get j=sourceUint l)
    (hq : hp.index r .dyn k=some q) (hl : l.1.toNat<hp.len q .dyn)
    (hw : (Source.writeLoc (E := E) (Γ := Γ) F (horizon+3) (τ := .bool) (.mem (address q.id) l.1.toNat) (.bool false)).run y=(.ok (),z)) :
    (Source.evalE G F (horizon+4) (sourceNestedDelete root i j)).run y=(.ok Source.RVal.unit,z) := by
  rw [sourceNestedDelete,Source.evalE,Source.Hoare.run_bind,hr.eval_nested_loc G F horizon root i j k l q hroot hi hj hq hl]
  change ((Source.deleteLoc (E := E) (Γ := Γ) F (horizon+3) (τ := .bool) (.mem (address q.id) l.1.toNat)) >>= fun _ => pure Source.RVal.unit).run y=_
  have hd : (Source.deleteLoc (E := E) (Γ := Γ) F (horizon+3) (τ := .bool) (.mem (address q.id) l.1.toNat)).run y=(.ok (),z) := hw
  rw [Source.Hoare.run_bind,hd];rfl

private theorem delete_index_code {C : Contract} {Γ : Ctx} {L b : Nat} {F : Evm.Frag Γ}
    {σ : State C Γ} {m : Evm.Machine} (hm : Evm.Sim C L b F σ m)
    (j : Idx Γ (.val .uint)) (l : Fin Evm.W) (ht : TEnv.get j σ.env=Evm.Memory.indexValue l) :
    Evm.run (Evm.compileVal b (.simple (.local j) : Val C Γ .uint)) m=.ok (m.push (.val l)) 0 := by
  obtain ⟨w,hw,hc⟩ := Evm.simple_sim hm (.local j) rfl
  change Evm.ReprV .uint (TEnv.get j σ.env) w at hw
  rw [ht] at hw
  obtain ⟨a,ha,he,rfl⟩ := hw.uint_inv
  have heq : a=l.val := by
    have h := congrArg Int.toNat he
    simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using h.symm
  subst a;exact hc

private theorem nested_delete_code_of_clear {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Evm.Frag Γ}
    {σ : State C Γ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m)
    (root : Idx Γ (.mem BoolRefsRef)) (i j : Idx Γ (.val .uint))
    (r : HRef σ.H BoolRefsRef) (q : HRef σ.H (.array (.prim .bool))) (k l : Fin Evm.W)
    (ht : TEnv.get root σ.env=some r) (hi : TEnv.get i σ.env=Evm.Memory.indexValue k) (hj : TEnv.get j σ.env=Evm.Memory.indexValue l)
    (hq : σ.heap.index r .dyn (Evm.Memory.indexValue k)=some q) {out : Evm.Out}
    (hw : Evm.run (Evm.Memory.writeArrayCode (base q.id)) ((m.push (.val (Evm.bword false))).push (.val l))=out) :
    Evm.run (nestedDeleteCode (C := C) b root i j) m=out := by
  let ptr := [.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local i) : Val C Γ .uint) ++ Evm.Memory.readArrayStackCode
  have hc : Evm.Memory.RefPtrFrag b F (.loc (.index .dyn (.var root rfl) (.simple (.local i)))) ptr := .index _ _ (.local root rfl) _ rfl
  have he : (MPath.loc (.index .dyn (.var root rfl) (.simple (.local i)))).mvalT σ=.ok q := by
    simp only [MPath.mvalT,MLoc.addrT,Val.evalT,Simple.evalT,ht,hi,Heap.readAddr,hq,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have hptr := hc.run_of_eval (hm.push (.val (Evm.bword false))) he
  have hidx := delete_index_code ((hm.push (.val (Evm.bword false))).push (.val (base q.id))).state.core j l hj
  change Evm.run ([.push (.val (Evm.bword false))] ++ (ptr ++ (Evm.compileVal b (.simple (.local j) : Val C Γ .uint) ++ Evm.Memory.writeArrayStackCode))) m=_
  rw [Evm.run_append_ok (show Evm.run [.push (.val (Evm.bword false))] m=.ok (m.push (.val (Evm.bword false))) 0 from rfl),Evm.run_append_ok hptr,Evm.run_append_ok hidx]
  rw [Evm.Memory.writeArrayStackCode,Evm.Memory.arrayStack_append_eq (m.push (.val (Evm.bword false))) (base q.id) l _
    (σ.heap.len_dyn_lt q) (hm.state.heap.arrays q).length,←Evm.Memory.writeArrayCode]
  exact hw

theorem SourceBoolRefsAt.resolved_nested_delete_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {parentAddress : Nat} (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
    (sroot : Source.Idx Γ SourceBoolRefsTy) (si sj : Source.Idx Γ (.int .u256))
    (σ : State C Δ) (root : Idx Δ (.mem BoolRefsRef)) (i j : Idx Δ (.val .uint))
    (r : HRef σ.H BoolRefsRef) (q : HRef σ.H (.array (.prim .bool))) (k l : Fin Evm.W)
    (address : Nat → Nat) (hr : SourceBoolRefsAt y parentAddress σ.heap r address)
    (hsroot : y.1.get sroot=.memRef rfl parentAddress)
    (hsi : y.1.get si=sourceUint (Evm.Memory.indexValue k)) (hsj : y.1.get sj=sourceUint (Evm.Memory.indexValue l))
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get i σ.env=Evm.Memory.indexValue k) (htj : TEnv.get j σ.env=Evm.Memory.indexValue l)
    (hq : σ.heap.index r .dyn (Evm.Memory.indexValue k)=some q) (hj : l.val<σ.heap.len q .dyn)
    (hsep : ∀ t∈MObj.elems .dyn (σ.heap.get r),t.id≠q.id → address t.id≠address q.id)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ),
      σ.heap.writeAddr (.index q .dyn (Evm.Memory.indexValue l)) false=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (horizon+3) (.mem (address q.id) l.val) (.bool false)).run y=(.ok (),z) ∧
      (Source.evalE G Fsrc (horizon+4) (sourceNestedDelete sroot si sj)).run y=(.ok Source.RVal.unit,z) ∧
      (Source.execS G Fsrc (horizon+5) Γ.length none
        (.expr (sourceNestedDelete sroot si sj) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      Stmt.run σ (.deleteMem (.loc (.index .dyn (.loc (.index .dyn (.var root rfl) (.simple (.local i)))) (.simple (.local j)))) rfl)=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (nestedDeleteCode (C := C) b root i j) m=.ok (Evm.Memory.writeMachine m ((base q.id).val+1+l.val) (.val (Evm.bword false))) 0 ∧
      SourceBoolRefsAt z parentAddress out r address ∧ Source.MemOK E SH z ∧
      Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap out) base (Evm.Memory.writeMachine m ((base q.id).val+1+l.val) (.val (Evm.bword false))) ∧
      z.1=y.1 ∧ out.get r=σ.heap.get r ∧ Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out)
        (Evm.Memory.writeMachine m ((base q.id).val+1+l.val) (.val (Evm.bword false))) := by
  have hmember : q∈MObj.elems .dyn (σ.heap.get r) := by
    obtain ⟨hb,he⟩ := List.getElem?_eq_some_iff.mp hq
    rw [←he];exact List.getElem_mem hb
  obtain ⟨out,z,ho,hs,hword,hr',hmk,hm',hl,hparent⟩ := hr.write_child_word σ r address q hmember hsep Fsrc (horizon+3) l false hj SH hmem hm
  have he := hr.eval_nested_delete_of_write G Fsrc horizon sroot si sj (Evm.Memory.indexValue k) (Evm.Memory.indexValue l) q
    hsroot hsi hsj hq (by simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hj)
    (by simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hs)
  have hi' : Stmt.run σ (.deleteMem (.loc (.index .dyn (.loc (.index .dyn (.var root rfl) (.simple (.local i)))) (.simple (.local j)))) rfl)=
      .ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
    change TRun.deleteMem (.loc (.index .dyn (.loc (.index .dyn (.var root rfl) (.simple (.local i)))) (.simple (.local j)))) σ=_
    simp only [TRun.deleteMem,TRun.clearT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,htroot,hti,htj,Heap.readAddr,hq,ho,
      TRes.ofOpt,bind,Except.bind,pure,Except.pure,PrimTy.dflt]
  refine ⟨out,z,ho,hs,he,source_expr_statement_run G Fsrc (horizon+4) Γ.length _ y z Source.RVal.unit he,hi',
    nested_delete_code_of_clear hm root i j r q k l htroot hti htj hq hword,hr',hmk,hm',hl,hparent,?_⟩
  intro cursor hb ha
  have hout : out=σ.heap.set q (MObj.setElem .dyn (σ.heap.get q) l.val false) := by
    have hw : σ.heap.writeAddr (.index q .dyn (Evm.Memory.indexValue l)) false=some (σ.heap.set q (MObj.setElem .dyn (σ.heap.get q) l.val false)) := by
      simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast];exact if_pos hj
    exact Option.some.inj (ho.symm.trans hw)
  rw [hout];exact ha.setArray q l.val hj false (.val (Evm.bword false)) rfl


private def nestedDeletePath {C : Contract} {Γ : Ctx} (root : Idx Γ (.mem BoolRefsRef))
    (i j : Idx Γ (.val .uint)) : MPath C Γ (.prim .bool) :=
  .loc (.index .dyn (.loc (.index .dyn (.var root rfl) (.simple (.local i)))) (.simple (.local j)))

private theorem nested_delete_error {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat) (y : Source.EMState E Γ)
    (root : Source.Idx Γ SourceBoolRefsTy) (i j : Source.Idx Γ (.int .u256))
    (hl : (Source.evalLoc G F (horizon+3) (sourceNestedLoc root i j)).run y=(.error (.revert (Source.panicData .index)),y)) :
    (Source.evalE G F (horizon+4) (sourceNestedDelete root i j)).run y=(.error (.revert (Source.panicData .index)),y) := by
  rw [sourceNestedDelete,Source.evalE,Source.Hoare.run_bind,hl]

theorem SourceBoolRefsAt.nested_delete_parent_bounds {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {parentAddress : Nat} (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
    (sroot : Source.Idx Γ SourceBoolRefsTy) (si sj : Source.Idx Γ (.int .u256))
    (σ : State C Δ) (root : Idx Δ (.mem BoolRefsRef)) (i j : Idx Δ (.val .uint))
    (r : HRef σ.H BoolRefsRef) (k : Fin Evm.W) (address : Nat → Nat)
    (hr : SourceBoolRefsAt y parentAddress σ.heap r address)
    (hsroot : y.1.get sroot=.memRef rfl parentAddress) (hsi : y.1.get si=sourceUint (Evm.Memory.indexValue k))
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get i σ.env=Evm.Memory.indexValue k)
    (hk : σ.heap.len r .dyn≤k.val)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    (Source.evalE G Fsrc (horizon+4) (sourceNestedDelete sroot si sj)).run y=(.error (.revert (Source.panicData .index)),y) ∧
    Stmt.run σ (.deleteMem (nestedDeletePath root i j) rfl)=.error .revert ∧
    Evm.run (nestedDeleteCode (C := C) b root i j) m=.revert := by
  have hn : σ.heap.index r .dyn (Evm.Memory.indexValue k)=none := by
    simp only [Heap.index,Evm.Memory.indexValue,Int.toNat_natCast];exact List.getElem?_eq_none_iff.mpr hk
  let ptr := [.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local i) : Val C Δ .uint) ++ Evm.Memory.readArrayStackCode
  have hc : Evm.Memory.RefPtrFrag b F (.loc (.index .dyn (.var root rfl) (.simple (.local i)))) ptr := .index _ _ (.local root rfl) _ rfl
  have he : (MPath.loc (.index .dyn (.var root rfl) (.simple (.local i)))).mvalT σ=.error .revert := by
    simp only [MPath.mvalT,MLoc.addrT,Val.evalT,Simple.evalT,htroot,hti,Heap.readAddr,hn,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have hptr : Evm.run ptr (m.push (.val (Evm.bword false)))=.revert := by
    rcases hc.correct (hm.push (.val (Evm.bword false))) with ⟨q,hq,_⟩|⟨_,hcode⟩
    · rw [he] at hq;cases hq
    · exact hcode
  refine ⟨nested_delete_error G Fsrc horizon y sroot si sj
    (hr.eval_nested_loc_parent_bounds G Fsrc horizon sroot si sj (Evm.Memory.indexValue k) hsroot hsi
      (by simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hk)),?_,?_⟩
  · change TRun.deleteMem (nestedDeletePath root i j) σ=_
    simp only [TRun.deleteMem,nestedDeletePath,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,htroot,hti,
      Heap.readAddr,hn,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  · change Evm.run ([.push (.val (Evm.bword false))] ++ (ptr ++ _)) m=_
    rw [Evm.run_append_ok (show Evm.run [.push (.val (Evm.bword false))] m=.ok (m.push (.val (Evm.bword false))) 0 from rfl)]
    exact Evm.run_append_revert hptr

theorem SourceBoolRefsAt.nested_delete_child_bounds {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {parentAddress : Nat} (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
    (sroot : Source.Idx Γ SourceBoolRefsTy) (si sj : Source.Idx Γ (.int .u256))
    (σ : State C Δ) (root : Idx Δ (.mem BoolRefsRef)) (i j : Idx Δ (.val .uint))
    (r : HRef σ.H BoolRefsRef) (q : HRef σ.H (.array (.prim .bool))) (k l : Fin Evm.W) (address : Nat → Nat)
    (hr : SourceBoolRefsAt y parentAddress σ.heap r address)
    (hsroot : y.1.get sroot=.memRef rfl parentAddress)
    (hsi : y.1.get si=sourceUint (Evm.Memory.indexValue k)) (hsj : y.1.get sj=sourceUint (Evm.Memory.indexValue l))
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get i σ.env=Evm.Memory.indexValue k) (htj : TEnv.get j σ.env=Evm.Memory.indexValue l)
    (hq : σ.heap.index r .dyn (Evm.Memory.indexValue k)=some q) (hl : σ.heap.len q .dyn≤l.val)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    (Source.evalE G Fsrc (horizon+4) (sourceNestedDelete sroot si sj)).run y=(.error (.revert (Source.panicData .index)),y) ∧
    Stmt.run σ (.deleteMem (nestedDeletePath root i j) rfl)=.error .revert ∧
    Evm.run (nestedDeleteCode (C := C) b root i j) m=.revert := by
  have hn : σ.heap.writeAddr (.index q .dyn (Evm.Memory.indexValue l)) false=none := by
    simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast];exact if_neg (Nat.not_lt.mpr hl)
  have hword : Evm.run (Evm.Memory.writeArrayCode (base q.id)) ((m.push (.val (Evm.bword false))).push (.val l))=.revert := by
    rcases Evm.Memory.writeArray_correct (hm.state.heap.arrays q) l false (.val (Evm.bword false)) rfl with ⟨_,hh,_,_⟩|⟨_,hc⟩
    · rw [hn] at hh;cases hh
    · exact hc
  refine ⟨nested_delete_error G Fsrc horizon y sroot si sj
    (hr.eval_nested_loc_child_bounds G Fsrc horizon sroot si sj (Evm.Memory.indexValue k) (Evm.Memory.indexValue l) q hsroot hsi hsj hq
      (by simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hl)),?_,
    nested_delete_code_of_clear hm root i j r q k l htroot hti htj hq hword⟩
  change TRun.deleteMem (nestedDeletePath root i j) σ=_
  simp only [TRun.deleteMem,nestedDeletePath,TRun.clearT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,htroot,hti,htj,
    Heap.readAddr,hq,hn,TRes.ofOpt,bind,Except.bind,pure,Except.pure,PrimTy.dflt]

theorem source_nested_delete_low_horizon {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (root : Source.Idx Γ SourceBoolRefsTy) (i j : Source.Idx Γ (.int .u256)) :
    ∀ n,n≤3 → (Source.evalE G F n (sourceNestedDelete root i j)).run y=(.error .timeout,y) := by
  intro n hn
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | n+4 => omega

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.nested_delete_parent_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.nested_delete_parent_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.nested_delete_child_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.nested_delete_child_bounds
/-- info: 'Solidity.Backend.MemoryOps.source_nested_delete_low_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_nested_delete_low_horizon

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.eval_nested_delete_of_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.eval_nested_delete_of_write
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.resolved_nested_delete_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.resolved_nested_delete_word
end Solidity.Backend.MemoryOps
