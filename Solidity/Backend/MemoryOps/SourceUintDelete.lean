import Solidity.Backend.MemoryOps.SourceUintAssignment
import Solidity.Evm.MemoryDelete

/-! Real uint256 primitive deletion, not copying. Actual Source default/unit,
intrinsic delete and the published complete word code have separate outcomes. -/
namespace Solidity.Backend.MemoryOps

def sourceUintIndexedDelete {E : Source.Env} {Γ : Source.RCtx}
    (root : Source.Idx Γ (.array .memory (.int .u256) none))
    (index : Source.Idx Γ (.int .u256)) : Source.RExpr E Γ (.tuple []) :=
  .delete (.indexArray (.local root) (by decide) (.local index) rfl)

theorem SourceUintMemoryAt.delete_addr {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (F : Source.Fr) (fuel : Nat) (i : PrimTy.uint.Denote) (hi : i.1.toNat<hp.len r a) :
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index r a i) (PrimTy.dflt .uint)=some out ∧
      (Source.deleteLoc (E := E) (Γ := Γ) F (fuel+1) (τ := .int .u256) (.mem address i.1.toNat)).run y=(.ok (),z) ∧
      SourceUintMemoryAt z address out r a := by
  obtain ⟨out,z,hw,hs,hr'⟩ := hr.write_addr F (fuel+1) i (PrimTy.dflt .uint) hi
  exact ⟨out,z,hw,hs,hr'⟩

theorem SourceUintMemoryAt.delete_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (F : Source.Fr) (fuel : Nat) (i : PrimTy.uint.Denote) (hi : hp.len r a≤i.1.toNat) :
    (Source.deleteLoc (E := E) (Γ := Γ) F (fuel+1) (τ := .int .u256) (.mem address i.1.toNat)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
    hp.writeAddr (.index r a i) (PrimTy.dflt .uint)=none := by
  refine ⟨source_uint_write_bounds y address _ hr i.1.toNat hi (PrimTy.dflt .uint),?_⟩
  simp only [Heap.writeAddr,Heap.setIndex,show ¬i.1.toNat<(MObj.elems a (hp.get r)).length from Nat.not_lt.mpr hi,↓reduceIte]

theorem SourceUintMemoryAt.eval_delete_of_run {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y z : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .uint)} (hr : SourceUintMemoryAt y address hp r a)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ (.array .memory (.int .u256) none)) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl address)
    (hindex : y.1.get index=sourceUint k) (hk : k.1.toNat<hp.len r a)
    (hdelete : (Source.deleteLoc (E := E) (Γ := Γ) F (fuel+2) (τ := .int .u256) (.mem address k.1.toNat)).run y=(.ok (),z)) :
    (Source.evalE G F (fuel+3) (sourceUintIndexedDelete root index)).run y=(.ok Source.RVal.unit,z) := by
  rw [sourceUintIndexedDelete,Source.evalE,Source.Hoare.run_bind,hr.eval_index_loc G F fuel root index k hroot hindex hk]
  change (Source.deleteLoc F (fuel+2) (τ := .int .u256) (.mem address k.1.toNat) >>= fun _ => pure Source.RVal.unit).run y=_
  rw [Source.Hoare.run_bind,hdelete]
  rfl

theorem resolved_uint_delete_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (n : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .uint)))
    (hr : SourceUintMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) none)) (sindex : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.array (.prim .uint)))) (index : Idx Δ (.val .uint))
    (k : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address)
    (hsindex : y.1.get sindex=sourceUint k) (htroot : TEnv.get root σ.env=some r)
    (htindex : TEnv.get index σ.env=k) (hk : k.1.toNat<σ.heap.len r .dyn)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) :
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      σ.heap.writeAddr (.index r .dyn k) (PrimTy.dflt .uint)=some out ∧
      (Source.deleteLoc (E := E) (Γ := Γ) Fsrc (n+2) (τ := .int .u256) (.mem address k.1.toNat)).run y=(.ok (),z) ∧
      (Source.evalE G Fsrc (n+3) (sourceUintIndexedDelete sroot sindex)).run y=(.ok Source.RVal.unit,z) ∧
      (Source.execS G Fsrc (n+4) Γ.length none (.expr (sourceUintIndexedDelete sroot sindex) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal y.1),(.nil,z.2)) ∧
      Stmt.run σ (.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local index)))) rfl)=.ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local index) : Val C Δ .uint))) m=.ok target 0 ∧
      SourceUintMemoryAt z address out r .dyn ∧ Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      Source.MemOK E SH z ∧ z.1=y.1 ∧ target.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target := by
  obtain ⟨out,z,hw,hdel,hr'⟩ := hr.delete_addr Fsrc (n+1) k hk
  have hi : TRun.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local index)))) σ=.ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
    simp only [TRun.deleteMem,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,htroot,htindex,bind,Except.bind,pure,Except.pure,TRun.clearT,hw,TRes.ofOpt]
  have cert := Evm.Memory.deleteLocalValue_correct hm root (.simple (.local index))
    (Evm.compileVal b (.simple (.local index) : Val C Δ .uint)) (fun h' => Evm.val_sim _ h'.core rfl)
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

theorem resolved_uint_delete_word_bounds {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (n : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .uint)))
    (hr : SourceUintMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) none)) (sindex : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.array (.prim .uint)))) (index : Idx Δ (.val .uint))
    (k : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address)
    (hsindex : y.1.get sindex=sourceUint k) (htroot : TEnv.get root σ.env=some r)
    (htindex : TEnv.get index σ.env=k) (hk : σ.heap.len r .dyn≤k.1.toNat)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) :
    (Source.evalE G Fsrc (n+3) (sourceUintIndexedDelete sroot sindex)).run y=(.error (.revert (Source.panicData .index)),y) ∧
    Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local index) : Val C Δ .uint))) m=.revert := by
  have he : (Source.evalE G Fsrc (n+3) (sourceUintIndexedDelete sroot sindex)).run y=(.error (.revert (Source.panicData .index)),y) := by
    rw [sourceUintIndexedDelete,Source.evalE,Source.Hoare.run_bind,hr.eval_index_bounds G Fsrc n sroot sindex k hsroot hsindex hk]
  have hn : σ.heap.writeAddr (.index r .dyn k) (PrimTy.dflt .uint)=none := by
    simp only [Heap.writeAddr,Heap.setIndex,show ¬k.1.toNat<(MObj.elems .dyn (σ.heap.get r)).length from Nat.not_lt.mpr hk,↓reduceIte]
  have hi : TRun.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local index)))) σ=.error .revert := by
    simp only [TRun.deleteMem,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,htroot,htindex,bind,Except.bind,pure,Except.pure,TRun.clearT,hn,TRes.ofOpt]
  have cert := Evm.Memory.deleteLocalValue_correct hm root (.simple (.local index))
    (Evm.compileVal b (.simple (.local index) : Val C Δ .uint)) (fun h' => Evm.val_sim _ h'.core rfl)
  rw [hi] at cert
  refine ⟨he,?_⟩
  rcases cert with ⟨o,target,ho,_⟩ | ⟨_,hcode⟩
  · cases ho
  · exact hcode

/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.delete_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.delete_addr
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.eval_delete_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.eval_delete_of_run
/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_delete_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_delete_word
/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_delete_word_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_delete_word_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryAt.delete_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintMemoryAt.delete_bounds
end Solidity.Backend.MemoryOps
