import Solidity.Backend.MemoryOps.SourceUintFixedAssignment
import Solidity.Evm.MemoryDelete

/-! Real uint256 primitive deletion, not copying. Actual Source default/unit,
intrinsic delete and the published complete word code have separate outcomes. -/
namespace Solidity.Backend.MemoryOps

def sourceUintFixedIndexedDelete {E : Source.Env} {Γ : Source.RCtx} {N : Nat}
    (root : Source.Idx Γ (.array .memory (.int .u256) (some N)))
    (index : Source.Idx Γ (.int .u256)) : Source.RExpr E Γ (.tuple []) :=
  .delete (.indexArray (.local root) (by decide) (.local index) rfl)

theorem SourceUintFixedAt.delete_addr {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {N : Nat}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H (.fixed (.prim .uint) N)}
    (hr : SourceUintFixedAt y address hp r)
    (F : Source.Fr) (fuel : Nat) (i : PrimTy.uint.Denote) (hi : i.1.toNat<N) :
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index r .fixed i) (PrimTy.dflt .uint)=some out ∧
      (Source.deleteLoc (E := E) (Γ := Γ) F (fuel+1) (τ := .int .u256) (.mem address i.1.toNat)).run y=(.ok (),z) ∧
      SourceUintFixedAt z address out r := by
  obtain ⟨out,z,hw,hs,hr'⟩ := hr.write_addr F (fuel+1) i (PrimTy.dflt .uint) hi
  exact ⟨out,z,hw,hs,hr'⟩

theorem SourceUintFixedAt.delete_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {N : Nat}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H (.fixed (.prim .uint) N)}
    (hr : SourceUintFixedAt y address hp r)
    (F : Source.Fr) (fuel : Nat) (i : PrimTy.uint.Denote) (hi : N≤i.1.toNat) :
    (Source.deleteLoc (E := E) (Γ := Γ) F (fuel+1) (τ := .int .u256) (.mem address i.1.toNat)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
    hp.writeAddr (.index r .fixed i) (PrimTy.dflt .uint)=none := by
  exact hr.write_bounds F (fuel+1) i (PrimTy.dflt .uint) hi

theorem SourceUintFixedAt.eval_delete_of_run {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {N : Nat}
    {y z : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H (.fixed (.prim .uint) N)}
    (hr : SourceUintFixedAt y address hp r)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ (.array .memory (.int .u256) (some N))) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl address)
    (hindex : y.1.get index=sourceUint k) (hk : k.1.toNat<N)
    (hdelete : (Source.deleteLoc (E := E) (Γ := Γ) F (fuel+2) (τ := .int .u256) (.mem address k.1.toNat)).run y=(.ok (),z)) :
    (Source.evalE G F (fuel+3) (sourceUintFixedIndexedDelete root index)).run y=(.ok Source.RVal.unit,z) := by
  rw [sourceUintFixedIndexedDelete,Source.evalE,Source.Hoare.run_bind,hr.eval_index_loc G F fuel root index k hroot hindex hk]
  change (Source.deleteLoc F (fuel+2) (τ := .int .u256) (.mem address k.1.toNat) >>= fun _ => pure Source.RVal.unit).run y=_
  rw [Source.Hoare.run_bind,hdelete]
  rfl

theorem resolved_uint_fixed_delete_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {N : Nat}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (n : Nat) (σ : State C Δ) (r : HRef σ.H (.fixed (.prim .uint) N))
    (hr : SourceUintFixedAt y address σ.heap r)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) (some N))) (sindex : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.fixed (.prim .uint) N))) (index : Idx Δ (.val .uint))
    (k : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address)
    (hsindex : y.1.get sindex=sourceUint k) (htroot : TEnv.get root σ.env=some r)
    (htindex : TEnv.get index σ.env=k) (hk : k.1.toNat<N)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) :
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      σ.heap.writeAddr (.index r .fixed k) (PrimTy.dflt .uint)=some out ∧
      (Source.deleteLoc (E := E) (Γ := Γ) Fsrc (n+2) (τ := .int .u256) (.mem address k.1.toNat)).run y=(.ok (),z) ∧
      (Source.evalE G Fsrc (n+3) (sourceUintFixedIndexedDelete sroot sindex)).run y=(.ok Source.RVal.unit,z) ∧
      (Source.execS G Fsrc (n+4) Γ.length none (.expr (sourceUintFixedIndexedDelete sroot sindex) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal y.1),(.nil,z.2)) ∧
      Stmt.run σ (.deleteMem (.loc (.index .fixed (.var root rfl) (.simple (.local index)))) rfl)=.ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (Evm.compileVal b (Evm.Memory.deleteDefaultValue .uint : Val C Δ .uint) ++ [.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local index) : Val C Δ .uint) ++ Evm.Memory.Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) N) (.prim .uint))) m=.ok target 0 ∧
      SourceUintFixedAt z address out r ∧ Evm.Memory.Objects.StateRepr L b frame F (σ.withHeap out) base target ∧
      Source.MemOK E SH z ∧ z.1=y.1 ∧ target.stack=m.stack ∧
      Evm.Memory.Objects.KeepsAllocator b frame σ base m (σ.withHeap out) target := by
  obtain ⟨out,z,hw,hdel,hr'⟩ := hr.delete_addr Fsrc (n+1) k hk
  have hi : TRun.deleteMem (.loc (.index .fixed (.var root rfl) (.simple (.local index)))) σ=.ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
    simp only [TRun.deleteMem,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,htroot,htindex,bind,Except.bind,pure,Except.pure,TRun.clearT,hw,TRes.ofOpt]
  have cert := Evm.Memory.Objects.PtrFrag.write hm (.fixed : ArrTy (.fixed (.prim .uint) N) (.prim .uint))
    (.local root rfl) (.val _ _ (.core (Evm.Memory.deleteDefaultValue .uint) rfl)) (.simple (.local index)) rfl
  unfold Evm.Memory.Objects.ResultRepr at cert
  rw [←Evm.Memory.deleteMem_primitive_eq_assign σ] at cert
  rw [hi] at cert
  rcases cert with ⟨o,target,ho,hcode,hstate,hstack,halloc⟩ | ⟨hbad,_⟩
  · cases Except.ok.inj ho
    have he := hr.eval_delete_of_run G Fsrc n sroot sindex k hsroot hsindex hk hdel
    have hwrite : (Source.writeLoc (E := E) (Γ := Γ) Fsrc (n+2) (.mem address k.1.toNat) (sourceUint (PrimTy.dflt .uint))).run y=(.ok (),z) := hdel
    have hf := hr.write_frames Fsrc (n+2) k (PrimTy.dflt .uint) hk hw hwrite
    have hmk := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) Fsrc (n+2)
      (.mem (τ := .int .u256) address k.1.toNat) (sourceUint (PrimTy.dflt .uint)) y ⟨hmem,trivial⟩
    rw [hwrite] at hmk
    refine ⟨out,z,target,hw,hdel,he,?_,hi,hcode,hr',hstate,hmk,hf.1,hstack,halloc⟩
    simpa only [hf.1] using source_expr_statement_run G Fsrc (n+3) Γ.length _ y z Source.RVal.unit he
  · cases hbad

theorem resolved_uint_fixed_delete_word_bounds {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {N : Nat}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (n : Nat) (σ : State C Δ) (r : HRef σ.H (.fixed (.prim .uint) N))
    (hr : SourceUintFixedAt y address σ.heap r)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) (some N))) (sindex : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.fixed (.prim .uint) N))) (index : Idx Δ (.val .uint))
    (k : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address)
    (hsindex : y.1.get sindex=sourceUint k) (htroot : TEnv.get root σ.env=some r)
    (htindex : TEnv.get index σ.env=k) (hk : N≤k.1.toNat)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m) :
    (Source.evalE G Fsrc (n+3) (sourceUintFixedIndexedDelete sroot sindex)).run y=(.error (.revert (Source.panicData .index)),y) ∧
    Evm.run (Evm.compileVal b (Evm.Memory.deleteDefaultValue .uint : Val C Δ .uint) ++ [.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local index) : Val C Δ .uint) ++ Evm.Memory.Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) N) (.prim .uint))) m=.revert := by
  have he : (Source.evalE G Fsrc (n+3) (sourceUintFixedIndexedDelete sroot sindex)).run y=(.error (.revert (Source.panicData .index)),y) := by
    rw [sourceUintFixedIndexedDelete,Source.evalE,Source.Hoare.run_bind,hr.eval_index_bounds G Fsrc n sroot sindex k hsroot hsindex hk]
  have hn : σ.heap.writeAddr (.index r .fixed k) (PrimTy.dflt .uint)=none := by
    simp only [Heap.writeAddr,Heap.setIndex,show ¬k.1.toNat<(MObj.elems .fixed (σ.heap.get r)).length from by simpa only [MObj.elems_fixed,(σ.heap.get r).2] using Nat.not_lt.mpr hk,↓reduceIte]
  have hi : TRun.deleteMem (.loc (.index .fixed (.var root rfl) (.simple (.local index)))) σ=.error .revert := by
    simp only [TRun.deleteMem,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,htroot,htindex,bind,Except.bind,pure,Except.pure,TRun.clearT,hn,TRes.ofOpt]
  have cert := Evm.Memory.Objects.PtrFrag.write hm (.fixed : ArrTy (.fixed (.prim .uint) N) (.prim .uint))
    (.local root rfl) (.val _ _ (.core (Evm.Memory.deleteDefaultValue .uint) rfl)) (.simple (.local index)) rfl
  unfold Evm.Memory.Objects.ResultRepr at cert
  rw [←Evm.Memory.deleteMem_primitive_eq_assign σ] at cert
  rw [hi] at cert
  refine ⟨he,?_⟩
  rcases cert with ⟨o,target,ho,_⟩ | ⟨_,hcode⟩
  · cases ho
  · exact hcode

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAt.delete_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedAt.delete_addr
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAt.delete_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedAt.delete_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAt.eval_delete_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedAt.eval_delete_of_run
/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_fixed_delete_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_fixed_delete_word
/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_fixed_delete_word_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_fixed_delete_word_bounds
end Solidity.Backend.MemoryOps
