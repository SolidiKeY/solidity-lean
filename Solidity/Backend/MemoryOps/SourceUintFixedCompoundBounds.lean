import Solidity.Backend.MemoryOps.SourceUintFixedCompound

/-! Exact genuine fixed bounds rejection, preserving Source panic versus symbolic word revert scope. -/
namespace Solidity.Backend.MemoryOps

theorem resolved_uint_fixed_add_bounds_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {N : Nat}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (n : Nat) (σ : State C Δ) (r : HRef σ.H (.fixed (.prim .uint) N))
    (hr : SourceUintFixedAt y address σ.heap r)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) (some N))) (si srhs : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.fixed (.prim .uint) N))) (index rhs : Idx Δ (.val .uint))
    (k value : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address)
    (hsi : y.1.get si=sourceUint k) (hsrhs : y.1.get srhs=sourceUint value)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get index σ.env=k) (htrhs : TEnv.get rhs σ.env=value)
    (hk : N≤k.1.toNat)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m) :
    (Source.evalE G Fsrc (n+3) (sourceUintFixedIndexedAdd sroot si srhs)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
    Stmt.run σ (.opAssign .add rfl rfl (.mindex .fixed (.var root rfl) (.local index)) (.simple (.local rhs)))=.error .revert ∧
    Evm.run (fixedUintAddCode (C := C) b root index rhs) m=.revert := by
  have hlen : (MObj.elems .fixed (σ.heap.get r)).length≤k.1.toNat := by
    simpa only [MObj.elems_fixed,(σ.heap.get r).2] using hk
  have hread : σ.heap.readAddr (.index r .fixed k)=none := List.getElem?_eq_none hlen
  have hi : TRun.opAssign .add (.mindex .fixed (.var root rfl) (.local index)) (.simple (.local rhs)) σ=.error .revert := by
    simp only [TRun.opAssign,OpLoc.storeT,MLoc.addrT,MPath.mvalT,Simple.evalT,Val.evalT,hti,htrhs,htroot,
      opMemT,hread,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have cert := fixed_uint_add_certificate hm root index rhs
  unfold Evm.Memory.Objects.ResultRepr at cert
  rw [hi] at cert
  rcases cert with ⟨o,target,hno,_⟩ | ⟨_,hc⟩
  · cases hno
  · exact ⟨hr.compound_add_bounds G Fsrc n sroot si srhs k value hsroot hsi hsrhs hk,hi,hc⟩

/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_fixed_add_bounds_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_fixed_add_bounds_word
end Solidity.Backend.MemoryOps
