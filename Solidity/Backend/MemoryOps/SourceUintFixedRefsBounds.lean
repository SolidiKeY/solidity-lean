import Solidity.Backend.MemoryOps.SourceUintFixedRefsTarget

/-! Actual fixed-child bounds failure: Source panic/state retention and symbolic
word revert are distinct outcomes, with no invented post-revert machine. -/
namespace Solidity.Backend.MemoryOps

theorem SourceUintFixedRefsAt.eval_nested_loc_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ (SourceUintFixedRefsTy n)) (i j : Source.Idx Γ (.int .u256))
    (k l : PrimTy.uint.Denote) (q : HRef H (.fixed (.prim .uint) n))
    (hroot : y.1.get root=.memRef rfl a) (hi : y.1.get i=sourceUint k) (hj : y.1.get j=sourceUint l)
    (hq : hp.index r .dyn k=some q) (hl : n≤l.1.toNat) :
    (Source.evalLoc G F (horizon+3) (sourceUintFixedNestedLoc root i j)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  rw [sourceUintFixedNestedLoc,Source.evalLoc,Source.Hoare.run_bind,hr.eval_parent_read G F horizon root i k q hroot hi hq]
  change ((Source.evalE G F (horizon+2) (.local j)) >>= fun v => Source.indexNat v >>= fun index =>
    Source.indexLoc F (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory (.int .u256) (some n))) index).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F (horizon+1) y j _ hj]
  change (Source.indexLoc F (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory (.int .u256) (some n))) l.1.toNat).run y=_
  rw [Source.indexLoc,Source.lengthOf]
  simp only [Source.Hoare.run_bind]
  change (if l.1.toNat<n then pure (Source.Loc.mem (address q.id) l.1.toNat : Source.Loc E.layout Γ (.int .u256)) else Source.EM.lift (Source.panic .index)).run y=_
  rw [if_neg (Nat.not_lt.mpr hl)]
  rfl


theorem SourceUintFixedRefsAt.resolved_write_bounds_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} (G : Source.Glob E) (Fs : Source.Fr) (horizon : Nat)
    (σ : State C Δ) (r : HRef σ.H (UintFixedRefsRef n)) (address : Nat → Nat)
    (hr : SourceUintFixedRefsAt y a σ.heap r address)
    (sr : Source.Idx Γ (SourceUintFixedRefsTy n)) (si sj sv : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (UintFixedRefsRef n))) (i j rhs : Idx Δ (.val .uint))
    (k l v : PrimTy.uint.Denote) (q : HRef σ.H (.fixed (.prim .uint) n))
    (hsr : y.1.get sr=.memRef rfl a) (hsi : y.1.get si=sourceUint k) (hsj : y.1.get sj=sourceUint l) (hsv : y.1.get sv=sourceUint v)
    (htr : TEnv.get root σ.env=some r) (hti : TEnv.get i σ.env=k) (htj : TEnv.get j σ.env=l) (htv : TEnv.get rhs σ.env=v)
    (hq : σ.heap.index r .dyn k=some q)
    (hl : n≤l.1.toNat)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m) :
    (Source.evalE G Fs (horizon+4) (sourceUintFixedNestedAssign sr si sj sv)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
    Stmt.run σ (.assignMem (.index .fixed (uintFixedChildPath root i) (.simple (.local j))) (.val (.simple (.local rhs))))=.error .revert ∧
    Evm.run (uintFixedChildWriteCode (C := C) b root i j rhs) m=.revert := by
  first
  | solve | simp only [] | omega
  | have source : (Source.evalE G Fs (horizon+4) (sourceUintFixedNestedAssign sr si sj sv)).run y=
        (.error (.revert (Source.panicData .index)),y) := by
      rw [sourceUintFixedNestedAssign,Source.evalE,Source.Hoare.run_bind,source_local_value_run G Fs (horizon+2) y sv _ hsv]
      change ((Source.evalLoc G Fs (horizon+3) (sourceUintFixedNestedLoc sr si sj)) >>= fun loc =>
        Source.writeLoc Fs (horizon+3) loc (sourceUint v) >>= fun _ => pure (Source.RVal.val (sourceUint v))).run y=_
      rw [Source.Hoare.run_bind,hr.eval_nested_loc_bounds G Fs horizon sr si sj k l q hsr hsi hsj hq hl]
    have selected : (uintFixedChildPath (C := C) root i).mvalT σ=.ok q := by
      simp only [uintFixedChildPath,MPath.mvalT,MLoc.addrT,Val.evalT,Simple.evalT,htr,hti,
        Heap.readAddr,hq,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have length : (MObj.elems .fixed (σ.heap.get q)).length=n := by rw [MObj.elems_fixed];exact (σ.heap.get q).2
    have rejected : σ.heap.writeAddr (.index q .fixed l) v=none := by
      simp only [Heap.writeAddr,Heap.setIndex,length,if_neg (Nat.not_lt.mpr hl)]
    have intrinsic : TRun.assignMem (.index .fixed (uintFixedChildPath root i) (.simple (.local j))) (.val (.simple (.local rhs))) σ=.error .revert := by
      simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,selected,Val.evalT,Simple.evalT,htj,htv,
        rejected,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have pointer : Evm.Memory.Objects.PtrFrag b F (uintFixedChildPath (C := C) root i)
        ([.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local i) : Val C Δ .uint) ++ Evm.Memory.Objects.readCode (.dyn : ArrTy (UintFixedRefsRef n) (.ref (.fixed (.prim .uint) n)))) :=
      .index .dyn _ _ (.local root rfl) (.simple (.local i)) rfl
    have code := Evm.Memory.Objects.PtrFrag.write hm (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))
      pointer (.val _ _ (.core (.simple (.local rhs)) rfl)) (.simple (.local j)) rfl
    unfold Evm.Memory.Objects.ResultRepr at code
    rw [intrinsic] at code
    rcases code with ⟨o,target,bad,_⟩ | ⟨_,revert⟩
    · cases bad
    · exact ⟨source,intrinsic,revert⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.eval_nested_loc_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.eval_nested_loc_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.resolved_write_bounds_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.resolved_write_bounds_word
end Solidity.Backend.MemoryOps
