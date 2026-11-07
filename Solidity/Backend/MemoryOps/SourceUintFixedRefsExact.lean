import Solidity.Backend.MemoryOps.SourceUintFixedRefsDeleteTarget

/-! Exact machine effect for the published nested fixed-child store. This
strengthens observations without changing compilation or its representation. -/
namespace Solidity.Backend.MemoryOps

private theorem uint_value_run {C : Contract} {Δ : Ctx} {L b : Nat} {F : Evm.Frag Δ}
    {σ : State C Δ} {m : Evm.Machine} (hm : Evm.Sim C L b F σ m)
    (value : Val C Δ .uint) (inside : Evm.valIn F value=true) (v : Fin Evm.W)
    (eval : value.evalT σ=.ok (Evm.Memory.indexValue v)) :
    Evm.run (Evm.compileVal b value) m=.ok (m.push (.val v)) 0 := by
  rcases Evm.val_sim value hm inside with ⟨x,w,hx,hw,run⟩ | ⟨bad,_⟩
  · cases Except.ok.inj (hx.symm.trans eval)
    obtain ⟨a,ha,eq,rfl⟩ := hw.uint_inv
    have same : a=v.val := by
      have e := congrArg Int.toNat eq
      simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using e.symm
    subst a
    exact run
  · rw [eval] at bad
    cases bad

theorem nested_fixed_store_exact {C : Contract} {Δ : Ctx} {n L b frame : Nat}
    {F : Evm.Frag Δ} {σ : State C Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (root : Idx Δ (.mem (UintFixedRefsRef n))) (i j : Idx Δ (.val .uint))
    (value : Val C Δ .uint) (inside : Evm.valIn F value=true)
    (r : HRef σ.H (UintFixedRefsRef n)) (q : HRef σ.H (.fixed (.prim .uint) n)) (k l v : Fin Evm.W)
    (hroot : TEnv.get root σ.env=some r)
    (hi : TEnv.get i σ.env=Evm.Memory.indexValue k) (hj : TEnv.get j σ.env=Evm.Memory.indexValue l)
    (hv : value.evalT σ=.ok (Evm.Memory.indexValue v))
    (selected : σ.heap.index r .dyn (Evm.Memory.indexValue k)=some q) (valid : l.val<n) :
    Evm.run (Evm.compileVal b value ++
      ([.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local i) : Val C Δ .uint) ++
        Evm.Memory.Objects.readCode (.dyn : ArrTy (UintFixedRefsRef n) (.ref (.fixed (.prim .uint) n)))) ++
      Evm.compileVal b (.simple (.local j) : Val C Δ .uint) ++
      Evm.Memory.Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))) m=
      .ok (Evm.Memory.writeMachine m ((base q.id).val+l.val) (.val v)) 0 := by
  first
  | solve | simp only [] | omega
  | have rhs := uint_value_run hm.core value inside v hv
    have pointer : Evm.Memory.Objects.PtrFrag b F (uintFixedChildPath (C := C) root i)
        ([.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local i) : Val C Δ .uint) ++ Evm.Memory.Objects.readCode (.dyn : ArrTy (UintFixedRefsRef n) (.ref (.fixed (.prim .uint) n)))) :=
      .index .dyn _ _ (.local root rfl) (.simple (.local i)) rfl
    have path : (uintFixedChildPath (C := C) root i).mvalT σ=.ok q := by
      simp only [uintFixedChildPath,MPath.mvalT,MLoc.addrT,Val.evalT,Simple.evalT,hroot,hi,
        Heap.readAddr,selected,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have ptr := pointer.run_of_eval (hm.push (.val v)) path
    have index := uint_value_run ((hm.push (.val v)).push (.val (base q.id))).core
      (.simple (.local j)) rfl l (by change Except.ok (TEnv.get j σ.env)=_;rw [hj])
    have write := (hm.heap.arrays .fixed q).write l (Evm.Memory.indexValue v) (.val v) (Evm.ReprV.uint_of rfl)
    rcases write with ⟨out,typed,run,_⟩ | ⟨bad,_⟩
    · rw [List.append_assoc,List.append_assoc,Evm.run_append_ok rhs,Evm.run_append_ok ptr,Evm.run_append_ok index]
      simpa only [Evm.Memory.Objects.header,Nat.add_zero] using run
    · have length : (MObj.elems .fixed (σ.heap.get q)).length=n := by rw [MObj.elems_fixed];exact (σ.heap.get q).2
      simp only [Heap.writeAddr,Heap.setIndex,length,Evm.Memory.indexValue,Int.toNat_natCast,valid,↓reduceIte] at bad
      cases bad

/-- info: 'Solidity.Backend.MemoryOps.nested_fixed_store_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_fixed_store_exact
end Solidity.Backend.MemoryOps
