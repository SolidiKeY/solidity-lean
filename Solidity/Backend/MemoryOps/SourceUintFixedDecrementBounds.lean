import Solidity.Backend.MemoryOps.SourceUintFixedDecrement

/-! Fixed-array bounds: the actual indexed location
rejects before reading/arithmetic/writing. No post-revert machine is returned. -/
namespace Solidity.Backend.MemoryOps

theorem resolved_uint_fixed_decrement_bounds_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {N : Nat}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (fuel : Nat) (pre : Bool) (σ : State C Δ) (r : HRef σ.H (.fixed (.prim .uint) N))
    (hr : SourceUintFixedAt y address σ.heap r)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) (some N))) (si : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.fixed (.prim .uint) N))) (index : Idx Δ (.val .uint))
    (k : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address) (hsi : y.1.get si=sourceUint k)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get index σ.env=k)
    (hk : N≤k.1.toNat)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m) :
    (Source.evalE G Fsrc (fuel+3) (sourceUintFixedDecrement pre sroot si)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
    (Source.execS G Fsrc (fuel+4) Γ.length none
      (.expr (sourceUintFixedDecrement pre sroot si) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.error (.revert (Source.panicData .index)),(.nil,y.2)) ∧
    TRun.incDec (fixedUintDecrementOp pre) (.mindex .fixed (.var root rfl) (.local index)) σ=.error .revert ∧
    Evm.run (fixedUintDecrementCode (C := C) b root index) m=.revert := by
  have he : (Source.evalE G Fsrc (fuel+3) (sourceUintFixedDecrement pre sroot si)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
    rw [sourceUintFixedDecrement,Source.evalE,Source.Hoare.run_bind,
      hr.eval_index_bounds G Fsrc fuel sroot si k hsroot hsi hk]
  have hread : σ.heap.readAddr (.index r .fixed k)=none := by
    change (MObj.elems .fixed (σ.heap.get r))[k.1.toNat]?=none
    exact List.getElem?_eq_none_iff.mpr (by simpa only [MObj.elems_fixed,(σ.heap.get r).2] using hk)
  have hi : TRun.incDec (fixedUintDecrementOp pre) (.mindex .fixed (.var root rfl) (.local index)) σ=.error .revert := by
    rw [Evm.Memory.incrementMemory_eq_compound σ (fixedUintDecrementOp pre) rfl .fixed (.var root rfl) (.local index)]
    have hop : (fixedUintDecrementOp pre).binOp=.sub := by cases pre <;> rfl
    rw [hop]
    simp only [TRun.opAssign,OpLoc.storeT,MLoc.addrT,MPath.mvalT,Simple.evalT,Val.evalT,hti,htroot,
      Evm.Memory.incrementOne,PrimTy.ofLit,opMemT,hread,PrimTy.key,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have cert : Evm.Memory.Objects.ResultRepr L b frame F σ base m
      (TRun.incDec (fixedUintDecrementOp pre) (.mindex .fixed (.var root rfl) (.local index)) σ)
      (Evm.run (fixedUintDecrementCode b root index) m) := fixed_uint_decrement_certificate hm pre root index
  unfold Evm.Memory.Objects.ResultRepr at cert
  rw [hi] at cert
  rcases cert with ⟨out,target,hno,_⟩ | ⟨_,hc⟩
  · cases hno
  · exact ⟨he,source_expr_statement_error G Fsrc (fuel+3) Γ.length _ y y _ he,hi,hc⟩

/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_fixed_decrement_bounds_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_fixed_decrement_bounds_word
end Solidity.Backend.MemoryOps
