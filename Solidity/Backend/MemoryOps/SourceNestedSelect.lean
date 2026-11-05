import Solidity.Backend.MemoryOps.SourceNestedMemory
import Solidity.Evm.MemoryRefArrayStatements

/-! Actual Source parent indexing followed by local child-reference assignment,
consuming the INITIAL nested relation and existing published RefPtrFrag compiler
certificate. No new path compiler, decoder, heap or graph semantics. -/
namespace Solidity.Backend.MemoryOps

def sourceSelectedAlias {E : Source.Env} {Γ : Source.RCtx}
    (dst : Source.Idx Γ (.array .memory .bool none))
    (root : Source.Idx Γ SourceBoolRefsTy) (index : Source.Idx Γ (.int .u256)) :
    Source.RExpr E Γ (.array .memory .bool none) :=
  .assign (.local dst) (.indexArray (.local root) (.local index) rfl)

def selectedAliasCode {C : Contract} {Γ : Ctx} (b : Nat)
    (dst : Idx Γ (.mem (.array (.prim .bool)))) (root : Idx Γ (.mem BoolRefsRef))
    (index : Idx Γ (.val .uint)) : List Evm.Instr :=
  [.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local index) : Val C Γ .uint) ++
    Evm.Memory.readArrayStackCode ++ [.mstore (Evm.cellOf b dst)]

theorem SourceBoolRefsAt.selected_alias_run {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (dst : Source.Idx Γ (.array .memory .bool none))
    (root : Source.Idx Γ SourceBoolRefsTy) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (q : HRef H (.array (.prim .bool)))
    (hroot : y.1.get root=.memRef rfl parentAddress) (hindex : y.1.get index=sourceUint k)
    (hq : hp.index r .dyn k=some q) :
    (Source.evalE G F (horizon+3) (sourceSelectedAlias dst root index)).run y=
      (.ok (.val (.memRef rfl (address q.id))),(y.1.set dst (.memRef rfl (address q.id)),y.2)) := by
  unfold sourceSelectedAlias
  rw [Source.evalE,Source.Hoare.run_bind,hr.eval_parent_read G F horizon root index k q hroot hindex hq]
  change ((Source.evalLoc G F (horizon+2) (.local dst)) >>= fun loc =>
    Source.writeLoc F (horizon+2) loc (.memRef rfl (address q.id)) >>= fun _ =>
    pure (Source.RVal.val (.memRef rfl (address q.id)))).run y=_
  rw [Source.Hoare.run_bind,show (Source.evalLoc G F (horizon+2) (.local dst)).run y=(.ok (.local dst),y) from rfl]
  rfl

theorem SourceBoolRefsAt.selected_alias_memOK {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (dst : Source.Idx Γ (.array .memory .bool none)) (k : PrimTy.uint.Denote)
    (q : HRef H (.array (.prim .bool))) (hq : hp.index r .dyn k=some q)
    (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    Source.MemOK E SH (y.1.set dst (.memRef rfl (address q.id)),y.2) := by
  have hc := hr.child_at k.1.toNat q hq
  have hv : Source.Val.RefOK E y.2.heap.ty
      (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory .bool none)) := by
    refine ⟨.array .memory .bool none,?_,rfl⟩
    change (y.2.heap.get (address q.id)).map Sigma.fst=some (.array .memory .bool none)
    rw [hc];rfl
  exact ⟨⟨hm.1.1,Source.LocalsOK.set y.1 dst hm.1.2 hv⟩,hm.2⟩

/-- Existing parent index rejection is an actual RHS failure before any local
assignment. No reached success heap or Source rollback is fabricated. -/
theorem SourceBoolRefsAt.selected_alias_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (dst : Source.Idx Γ (.array .memory .bool none))
    (root : Source.Idx Γ SourceBoolRefsTy) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl parentAddress)
    (hindex : y.1.get index=sourceUint k) (hk : hp.len r .dyn≤k.1.toNat) :
    (Source.evalE G F (horizon+3) (sourceSelectedAlias dst root index)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  unfold sourceSelectedAlias
  rw [Source.evalE,Source.Hoare.run_bind,hr.eval_parent_bounds G F horizon root index k hroot hindex hk]

/-- The actual selected Source child and typed intrinsic path feed the SAME
published reference-array pointer compiler/rebind operation. -/
theorem SourceBoolRefsAt.selected_alias_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
    (y : Source.EMState E Γ) (sdst : Source.Idx Γ (.array .memory .bool none))
    (sroot : Source.Idx Γ SourceBoolRefsTy) (sindex : Source.Idx Γ (.int .u256))
    (parentAddress : Nat) (k : PrimTy.uint.Denote)
    (hsroot : y.1.get sroot=.memRef rfl parentAddress) (hsindex : y.1.get sindex=sourceUint k)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    (σ : State C Δ) (dst : Idx Δ (.mem (.array (.prim .bool))))
    (root : Idx Δ (.mem BoolRefsRef)) (index : Idx Δ (.val .uint))
    (r : HRef σ.H BoolRefsRef) (q : HRef σ.H (.array (.prim .bool)))
    (htroot : TEnv.get root σ.env=some r) (htindex : TEnv.get index σ.env=k)
    (address : Nat → Nat) (hr : SourceBoolRefsAt y parentAddress σ.heap r address)
    (hq : σ.heap.index r .dyn k=some q)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m)
    (hi : Evm.valIn (C := C) F (.simple (.local index))=true) :
    let z : Source.EMState E Γ := (y.1.set sdst (.memRef rfl (address q.id)),y.2)
    let σ' := σ.setLocal dst (some q)
    let m' := Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base q.id))
    (Source.evalE G Fsrc (horizon+3) (sourceSelectedAlias sdst sroot sindex)).run y=
      (.ok (.val (.memRef rfl (address q.id))),z) ∧
    (Source.execS G Fsrc (horizon+4) Γ.length none
      (.expr (sourceSelectedAlias sdst sroot sindex) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.ok (.normal z.1),(.nil,z.2)) ∧
    Stmt.run σ (.rebindMem dst (.alias (.loc (.index .dyn (.var root rfl) (.simple (.local index))))))=
      .ok ⟨σ',List.prefix_refl _⟩ ∧
    Evm.run (selectedAliasCode (C := C) b dst root index) m=.ok m' 0 ∧
    Source.MemOK E SH z ∧ SourceBoolMemoryAt z (address q.id) σ'.heap q .dyn ∧
    SourceBoolRefsAt z parentAddress σ'.heap r address ∧
    z.1.get sdst=.memRef rfl (address q.id) ∧ TEnv.get dst σ'.env=some q ∧
    Evm.Memory.RefArrayStateRepr L b frame F σ' base m' ∧ m'.stack=m.stack ∧
    Evm.Memory.KeepsAllocator b frame σ base m σ' m' := by
  dsimp only
  have he := hr.selected_alias_run G Fsrc horizon sdst sroot sindex k q hsroot hsindex hq
  have hs := source_expr_statement_run G Fsrc (horizon+3) Γ.length _ y
    (y.1.set sdst (.memRef rfl (address q.id)),y.2) (.val (.memRef rfl (address q.id))) he
  have hmk := hr.selected_alias_memOK sdst k q hq SH hmem
  let p : MPath C Δ (.ref (.array (.prim .bool))) := .loc (.index .dyn (.var root rfl) (.simple (.local index)))
  let ptr : List Evm.Instr := [.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local index) : Val C Δ .uint) ++ Evm.Memory.readArrayStackCode
  have hc : Evm.Memory.RefPtrFrag b F p ptr := .index _ _ (.local root rfl) _ hi
  have hp : p.mvalT σ=.ok q := by
    simp only [p,MPath.mvalT,MLoc.addrT,Val.evalT,Simple.evalT,htroot,htindex,Heap.readAddr,hq,TRes.ofOpt,
      bind,Except.bind,pure,Except.pure]
  have hptr := hc.run_of_eval hm hp
  have hcode : Evm.run (selectedAliasCode (C := C) b dst root index) m=
      .ok (Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base q.id))) 0 := by
    change Evm.run (ptr ++ [.mstore (Evm.cellOf b dst)]) m=_
    rw [Evm.run_append_ok hptr]
    rfl
  have hi' : Stmt.run σ (.rebindMem dst (.alias p))=
      .ok ⟨σ.setLocal dst (some q),List.prefix_refl _⟩ := by
    change TRun.rebindMem dst (.alias p) σ=_
    simp only [TRun.rebindMem,MRhs.evalT,hp,bind,Except.bind,pure,Except.pure]
  have hchild : SourceBoolMemoryAt (y.1.set sdst (.memRef rfl (address q.id)),y.2)
      (address q.id) (σ.setLocal dst (some q)).heap q .dyn := hr.child_at k.1.toNat q hq
  refine ⟨he,hs,hi',hcode,hmk,hchild,hr.same_heaps rfl rfl,source_locals_get_set _ _ _,
    TEnv.get_set _ _ _,hm.setMem dst q,rfl,?_⟩
  intro cursor hb ha
  exact ha.localWrite _ (Nat.lt_of_lt_of_le hb (Evm.le_lvl b dst))
    (Nat.lt_of_lt_of_le (Evm.lvl_lt b dst) hm.state.locals) _


theorem SourceBoolRefsAt.selected_alias_word_bounds {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
    (y : Source.EMState E Γ) (sdst : Source.Idx Γ (.array .memory .bool none))
    (sroot : Source.Idx Γ SourceBoolRefsTy) (sindex : Source.Idx Γ (.int .u256))
    (parentAddress : Nat) (k : PrimTy.uint.Denote)
    (hsroot : y.1.get sroot=.memRef rfl parentAddress) (hsindex : y.1.get sindex=sourceUint k)
    (σ : State C Δ) (dst : Idx Δ (.mem (.array (.prim .bool))))
    (root : Idx Δ (.mem BoolRefsRef)) (index : Idx Δ (.val .uint)) (r : HRef σ.H BoolRefsRef)
    (htroot : TEnv.get root σ.env=some r) (htindex : TEnv.get index σ.env=k)
    (address : Nat → Nat) (hr : SourceBoolRefsAt y parentAddress σ.heap r address)
    (hk : σ.heap.len r .dyn≤k.1.toNat)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m)
    (hi : Evm.valIn (C := C) F (.simple (.local index))=true) :
    (Source.evalE G Fsrc (horizon+3) (sourceSelectedAlias sdst sroot sindex)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
    Stmt.run σ (.rebindMem dst (.alias (.loc (.index .dyn (.var root rfl) (.simple (.local index))))))=
      .error .revert ∧ Evm.run (selectedAliasCode (C := C) b dst root index) m=.revert := by
  let p : MPath C Δ (.ref (.array (.prim .bool))) := .loc (.index .dyn (.var root rfl) (.simple (.local index)))
  let ptr : List Evm.Instr := [.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local index) : Val C Δ .uint) ++ Evm.Memory.readArrayStackCode
  have hc : Evm.Memory.RefPtrFrag b F p ptr := .index _ _ (.local root rfl) _ hi
  have hn : σ.heap.index r .dyn k=none := List.getElem?_eq_none_iff.mpr hk
  have hp : p.mvalT σ=.error .revert := by
    simp only [p,MPath.mvalT,MLoc.addrT,Val.evalT,Simple.evalT,htroot,htindex,Heap.readAddr,hn,TRes.ofOpt,
      bind,Except.bind,pure,Except.pure]
  have hcode : Evm.run ptr m=.revert := by
    rcases hc.correct hm with ⟨q,hq,_⟩ | ⟨_,hcode⟩
    · rw [hp] at hq;cases hq
    · exact hcode
  refine ⟨hr.selected_alias_bounds G Fsrc horizon sdst sroot sindex k hsroot hsindex hk,?_,?_⟩
  · change TRun.rebindMem dst (.alias p) σ=_
    simp only [TRun.rebindMem,MRhs.evalT,hp,bind,Except.bind]
  · exact Evm.run_append_revert hcode


/-- Exact insufficient-horizon observations for these pure local operands;
this is not a new fuel bound or a side-effectful evaluation-order claim. -/
theorem source_selected_alias_low_horizon {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (dst : Source.Idx Γ (.array .memory .bool none))
    (root : Source.Idx Γ SourceBoolRefsTy) (index : Source.Idx Γ (.int .u256)) :
    ∀ n, n≤2 → (Source.evalE G F n (sourceSelectedAlias dst root index)).run y=(.error .timeout,y) := by
  intro n hn
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n+3 => omega

/-- info: 'Solidity.Backend.MemoryOps.source_selected_alias_low_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_selected_alias_low_horizon

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.selected_alias_word_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.selected_alias_word_bounds

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.selected_alias_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.selected_alias_run
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.selected_alias_memOK' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.selected_alias_memOK
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.selected_alias_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.selected_alias_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.selected_alias_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.selected_alias_word
end Solidity.Backend.MemoryOps
