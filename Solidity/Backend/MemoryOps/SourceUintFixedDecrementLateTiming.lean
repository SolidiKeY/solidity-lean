import Solidity.Backend.MemoryOps.SourceUintFixedDecrementLate

/-! Reached-state timeout companion: the actual first prefix succeeds but the second
expression has horizon two and times out at the reached state. No target
horizon or transaction rollback theorem is asserted. -/
namespace Solidity.Backend.MemoryOps

theorem source_uint_fixed_decrement_prefix_timeout
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {N : Nat}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (nps : Nat) (first second : Bool) (σ : State C Δ)
    (r : HRef σ.H (.fixed (.prim .uint) N)) (hr : SourceUintFixedAt y address σ.heap r)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) (some N))) (si : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.fixed (.prim .uint) N))) (index : Idx Δ (.val .uint))
    (k : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address) (hsi : y.1.get si=sourceUint k)
    (htroot : TEnv.get root σ.env=some r) (hti : TEnv.get index σ.env=k)
    (hk : k.1.toNat<σ.heap.len r .fixed)
    (hsub : PrimTy.uint.inRange ((MObj.elems .fixed (σ.heap.get r))[k.1.toNat].1-1)=true)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m) :
    let old := (MObj.elems .fixed (σ.heap.get r))[k.1.toNat]
    let new : PrimTy.uint.Denote := ⟨old.1-1,hsub⟩
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      (Source.evalE G Fsrc 3 (sourceUintFixedDecrement first sroot si)).run y=
        (.ok (.val (sourceUint (if first then new else old))),z) ∧
      (Source.evalE G Fsrc 2 (sourceUintFixedDecrement second sroot si)).run z=(.error .timeout,z) ∧
      (Source.execItems G Fsrc 5 nps none (sourceUintFixedDecrementTwice first second sroot si) y.1).run (.nil,y.2)=
        (.error .timeout,(.nil,z.2)) ∧
      σ.heap.writeAddr (.index r .fixed k) new=some out ∧
      Evm.run (fixedUintDecrementCode (C := C) b root index) m=.ok target 0 ∧
      SourceUintFixedAt z address out r ∧ Source.MemOK E SH z ∧ z.1=y.1 ∧
      Evm.Memory.Objects.StateRepr L b frame F (σ.withHeap out) base target ∧
      target.stack=m.stack ∧
      Evm.Memory.Objects.KeepsAllocator b frame σ base m (σ.withHeap out) target ∧
      (∀ {Q : RefTy} (q : HRef σ.H Q),r.id≠q.id → out.get q=σ.heap.get q) ∧
      (∀ a,a≠address → z.2.heap.get a=y.2.heap.get a) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  dsimp only
  obtain ⟨out,z,target,hw,hsw,he,hstmt,hi,hc,hr1,hm1,hmok1,hl,hstack,keep,hobj,haddr,hex,hev,hlog,hfn⟩ :=
    resolved_uint_fixed_decrement_word G Fsrc 0 first σ r hr sroot si root index k
      hsroot hsi htroot hti hk hsub SH hmem hm
  have htimeout : (Source.evalE G Fsrc 2 (sourceUintFixedDecrement second sroot si)).run z=
      (.error .timeout,z) := source_uint_fixed_decrement_horizon_two G Fsrc z second sroot si
  have hs1 : (Source.execS G Fsrc (3+1) nps none
      (.expr (sourceUintFixedDecrement first sroot si) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) := source_expr_statement_run G Fsrc 3 nps _ y z _ he
  have hs2 : (Source.execS G Fsrc (2+1) nps none
      (.expr (sourceUintFixedDecrement second sroot si) : Source.RStmt E [] false .body Γ Γ) z.1).run (.nil,z.2)=
        (.error .timeout,(.nil,z.2)) := source_expr_statement_error G Fsrc 2 nps _ z z _ htimeout
  have hs1' : (Source.execS G Fsrc 4 nps none
      (.expr (sourceUintFixedDecrement first sroot si) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.ok (.normal z.1),(.nil,z.2)) := by simpa only [hl] using hs1
  have htail : (Source.execItems G Fsrc 4 nps none
      (.stmt (.expr (sourceUintFixedDecrement second sroot si)) .nil : Source.RItems E [] false .body Γ Γ) z.1).run (.nil,z.2)=
      (.error .timeout,(.nil,z.2)) := by
    rw [Source.execItems,Source.Hoare.run_bind,hs2]
  have hitems : (Source.execItems G Fsrc 5 nps none (sourceUintFixedDecrementTwice first second sroot si) y.1).run (.nil,y.2)=
      (.error .timeout,(.nil,z.2)) := by
    rw [sourceUintFixedDecrementTwice,Source.execItems,Source.Hoare.run_bind,hs1']
    change (Source.execItems G Fsrc 4 nps none
      (.stmt (.expr (sourceUintFixedDecrement second sroot si)) .nil : Source.RItems E [] false .body Γ Γ) z.1 >>=
      fun o => Source.EM.lift (o.up Γ)).run (.nil,z.2)=_
    rw [Source.Hoare.run_bind,htail]
  exact ⟨out,z,target,he,htimeout,hitems,hw,hc,hr1,hmok1,hl,hm1,hstack,keep,hobj,haddr,hex,hev,hlog,hfn⟩

/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_decrement_prefix_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_decrement_prefix_timeout
end Solidity.Backend.MemoryOps
