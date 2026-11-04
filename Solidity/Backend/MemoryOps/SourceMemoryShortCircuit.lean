import Solidity.Backend.MemoryOps.SourceSequence

/-! A real initial indexed-write bounds error absorbs arbitrary typed
continuations. No successful allocation, suffix execution or target error
machine is supplied or inferred. -/
namespace Solidity.Backend.MemoryOps

/-- Arbitrary continuations may change contexts and allocate, but are not run.
Only INITIAL operands, represented contents and actual bounds are premises.
The tails are independent parameters; this is not a compiler theorem for tails. -/
theorem source_bool_write_bounds_short_circuit {E : Source.Env} {Γ Γ' : Source.RCtx}
    {C : Contract} {Δ Ξ : Ctx} (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
    (y : Source.EMState E Γ) (σ : State C Δ) (r : HRef σ.H (.array (.prim .bool))) (address : Nat)
    (hr : SourceBoolMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory .bool none)) (si : Source.Idx Γ (.int .u256)) (srhs : Source.Idx Γ .bool)
    (root : Idx Δ (.mem (.array (.prim .bool)))) (index : Idx Δ (.val .uint)) (rhs : Idx Δ (.val .bool))
    (k : PrimTy.uint.Denote) (value : Bool)
    (hsroot : y.1.get sroot=.memRef rfl address) (hsi : y.1.get si=sourceUint k) (hsrhs : y.1.get srhs=.bool value)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get index σ.env=k) (htrhs : TEnv.get rhs σ.env=value)
    (outside : σ.heap.len r .dyn≤k.1.toNat)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (repr : Evm.Memory.StateRepr L b frame F σ base m)
    (sourceTail : Source.RItems E [] false .body Γ Γ') (nativeTail : Prog C Δ Ξ) (wordTail : List Evm.Instr) :
    (Source.evalE G Fsrc (horizon+3) (sourceIndexedAssign sroot si srhs)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
    (Source.execS G Fsrc (horizon+4) Γ.length none
      (.expr (sourceIndexedAssign sroot si srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.error (.revert (Source.panicData .index)),(.nil,y.2)) ∧
    (Source.execItems G Fsrc (horizon+5) Γ.length none
      (.stmt (.expr (sourceIndexedAssign sroot si srhs)) sourceTail) y.1).run (.nil,y.2)=
      (.error (.revert (Source.panicData .index)),(.nil,y.2)) ∧
    σ.heap.writeAddr (.index r .dyn k) value=none ∧
    Stmt.run σ (.assignMem (.index .dyn (.var root rfl) (.simple (.local index))) (.val (.simple (.local rhs))))=
      .error .revert ∧
    Prog.run σ (.cons (.assignMem (.index .dyn (.var root rfl) (.simple (.local index)))
      (.val (.simple (.local rhs)))) nativeTail)=.error .revert ∧
    Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local index)) (.simple (.local rhs))) m=.revert ∧
    Evm.run (Evm.Memory.writeLocalCode (C := C) b root (.simple (.local index)) (.simple (.local rhs)) ++ wordTail) m=.revert := by
  first
  | solve | rfl | simp only [] | omega
  | have rejected := resolved_assign_word_bounds G Fsrc horizon σ r hr sroot si srhs root index rhs k value
      hsroot hsi hsrhs htroot hti htrhs outside repr
    have stmt := source_expr_statement_error G Fsrc (horizon+3) Γ.length _ y y _ rejected.1
    have items : (Source.execItems G Fsrc (horizon+5) Γ.length none
        (.stmt (.expr (sourceIndexedAssign sroot si srhs)) sourceTail) y.1).run (.nil,y.2)=
        (.error (.revert (Source.panicData .index)),(.nil,y.2)) := by
      rw [Source.execItems,Source.Hoare.run_bind,stmt]
    have noWrite : σ.heap.writeAddr (.index r .dyn k) value=none := by
      simp only [Heap.len] at outside
      simp only [Heap.writeAddr,Heap.setIndex,show ¬k.1.toNat<(MObj.elems .dyn (σ.heap.get r)).length from Nat.not_lt.mpr outside,↓reduceIte]
    have native : Stmt.run σ (.assignMem (.index .dyn (.var root rfl) (.simple (.local index))) (.val (.simple (.local rhs))))=.error .revert := by
      change TRun.assignMem _ _ σ=_
      simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,
        htroot,hti,htrhs,bind,Except.bind,pure,Except.pure,noWrite,TRes.ofOpt]
    refine ⟨rejected.1,stmt,items,noWrite,native,?_,rejected.2,Evm.run_append_revert rejected.2⟩
    change TRun.seq _ _ σ=_
    simp only [TRun.seq]
    rw [show TRun.assignMem _ _ σ=.error .revert from native]

/-- info: 'Solidity.Backend.MemoryOps.source_bool_write_bounds_short_circuit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_bool_write_bounds_short_circuit
end Solidity.Backend.MemoryOps
