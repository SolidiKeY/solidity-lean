import Solidity.Backend.MemoryOps.SourceUintFixedAliasProgram

/-! Reached bounds rejection after real reference-local rebinding. The Source
error exposes unchanged globals, not the rebound local or any target suffix. -/
namespace Solidity.Backend.MemoryOps

def sourceUintFixedAliasReject {E : Source.Env} {Γ : Source.RCtx} {n : Nat}
    (dst src : Source.Idx Γ (.array .memory (.int .u256) (some n)))
    (si sv : Source.Idx Γ (.int .u256)) : Source.RItems E [] false .body Γ Γ :=
  .stmt (.expr (sourceLocalAlias dst src)) (.stmt (.expr (sourceUintFixedIndexedAssign dst si sv)) .nil)
def intrinsicUintFixedAliasReject {C : Contract} {Δ : Ctx} {n : Nat}
    (dst src : Idx Δ (.mem (.fixed (.prim .uint) n))) (i v : Idx Δ (.val .uint)) : Prog C Δ Δ :=
  .cons (.rebindMem dst (.alias (.var src rfl)))
    (.cons (.assignMem (.index .fixed (.var dst rfl) (.simple (.local i))) (.val (.simple (.local v)))) .nil)

theorem source_uint_fixed_alias_reject
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {n : Nat}
    (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat) (y : Source.EMState E Γ)
    (sdst ssrc : Source.Idx Γ (.array .memory (.int .u256) (some n)))
    (si sv : Source.Idx Γ (.int .u256)) (address : Nat) (σ : State C Δ)
    (dst src : Idx Δ (.mem (.fixed (.prim .uint) n))) (i v : Idx Δ (.val .uint))
    (r : HRef σ.H (.fixed (.prim .uint) n)) (k value : PrimTy.uint.Denote)
    (hsrc : y.1.get ssrc=.memRef rfl address) (hsi : y.1.get si=sourceUint k) (hsv : y.1.get sv=sourceUint value)
    (htsrc : TEnv.get src σ.env=some r) (hti : TEnv.get i σ.env=k) (htv : TEnv.get v σ.env=value)
    (hr : SourceUintFixedAt y address σ.heap r) (hk : n≤k.1.toNat) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m) (hb : 0<b) :
    let ym : Source.EMState E Γ := (y.1.set sdst (.memRef rfl address),y.2)
    let σm := σ.setLocal dst (some r)
    let mm := Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base r.id))
    let wc := Evm.compileVal b (.simple (.local v) : Val C Δ .uint) ++ [.mload (Evm.cellOf b dst)] ++
      Evm.compileVal b (.simple (.local i) : Val C Δ .uint) ++ Evm.Memory.Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))
    (Source.execS G Fsrc (horizon+5) Γ.length none (.expr (sourceLocalAlias sdst ssrc) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
      (.ok (.normal ym.1),(.nil,ym.2)) ∧
    (Source.evalE G Fsrc (horizon+3) (sourceUintFixedIndexedAssign sdst si sv)).run ym=
      (.error (.revert (Source.panicData .index)),ym) ∧
    (Source.execItems G Fsrc (horizon+6) Γ.length none (sourceUintFixedAliasReject sdst ssrc si sv) y.1).run (.nil,y.2)=
      (.error (.revert (Source.panicData .index)),(.nil,y.2)) ∧
    Prog.run σ (intrinsicUintFixedAliasReject dst src i v)=.error .revert ∧
    Evm.run (Evm.Memory.aliasLocalCode b dst src) m=.ok mm 0 ∧ Evm.run wc mm=.revert ∧
    Evm.run (Evm.Memory.aliasLocalCode b dst src ++ wc) m=.revert ∧
    σm.heap.writeAddr (.index r .fixed k) value=none ∧
    SourceUintFixedAt ym address σm.heap r ∧ Source.MemOK E SH ym ∧
    Evm.Memory.Objects.StateRepr L b frame F σm base mm ∧ Evm.Memory.Objects.AllocatorRepr σm.heap base frame cursor mm ∧
    ym.1.get sdst=.memRef rfl address ∧ TEnv.get dst σm.env=some r ∧ ym.2=y.2 ∧ σm.heap=σ.heap ∧
    mm.stack=m.stack ∧ mm.mem 0=m.mem 0 := by
  dsimp only
  let ym : Source.EMState E Γ := (y.1.set sdst (.memRef rfl address),y.2)
  let σm := σ.setLocal dst (some r)
  obtain ⟨heA,hsA,hiA,hcA,hrA,hmokA,hmA,haA,keepA,hrootS,hrootT,hglob,hheap,hstackA,hfree,hsloc,htloc,hhp,hhS⟩ :=
    source_uint_fixed_alias_word G Fsrc (horizon+2) y sdst ssrc address hsrc SH hmem σ dst src r htsrc hr hm ha hb
  have hsi' : ym.1.get si=sourceUint k := (fixed_alias_scalar_frames y sdst si address σ dst i r).1.trans hsi
  have hsv' : ym.1.get sv=sourceUint value := (fixed_alias_scalar_frames y sdst sv address σ dst v r).1.trans hsv
  have hti' : TEnv.get i σm.env=k := (fixed_alias_scalar_frames y sdst si address σ dst i r).2.trans hti
  have htv' : TEnv.get v σm.env=value := (fixed_alias_scalar_frames y sdst sv address σ dst v r).2.trans htv
  have hbad := resolved_uint_fixed_assign_word_bounds G Fsrc horizon σm r hrA sdst si sv dst i v k value
    hrootS hsi' hsv' hrootT hti' htv' hk hmA
  have hsB := source_expr_statement_error G Fsrc (horizon+3) Γ.length _ ym ym _ hbad.1
  have hitems := source_items_pair_error G Fsrc horizon Γ.length _ _ y ym ym _ hsA hsB
  have hn := (hrA.write_bounds Fsrc (horizon+2) k value hk).2
  have hrootT' : TEnv.get dst σm.env=some r := hrootT
  have hn' : σm.heap.writeAddr (.index r .fixed k) value=none := hn
  have hiB : Stmt.run σm (.assignMem (.index .fixed (.var dst rfl) (.simple (.local i))) (.val (.simple (.local v))))=.error .revert := by
    change TRun.assignMem (.index .fixed (.var dst rfl) (.simple (.local i))) (.val (.simple (.local v))) σm=_
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,
      hrootT',hti',htv',hn',bind,Except.bind,pure,Except.pure,TRes.ofOpt]
  have htail : Prog.run σm (.cons (.assignMem (.index .fixed (.var dst rfl) (.simple (.local i))) (.val (.simple (.local v)))) .nil)=.error .revert := by
    let t : Stmt C Δ Δ := .assignMem (.index .fixed (.var dst rfl) (.simple (.local i))) (.val (.simple (.local v)))
    change TRun.seq t.runR (Prog.nil : Prog C Δ Δ).runR σm=_
    simp only [TRun.seq]
    rw [show t.runR σm=.error .revert from hiB]
  have hp : Prog.run σ (intrinsicUintFixedAliasReject dst src i v)=.error .revert := by
    rw [intrinsicUintFixedAliasReject,Prog.run_cons_ok hiA,htail]
    rfl
  refine ⟨hsA,hbad.1,hitems,hp,hcA,hbad.2,?_,hn,hrA,hmokA,hmA,haA,hrootS,hrootT,rfl,rfl,hstackA,hfree⟩
  rw [Evm.run_append_ok hcA,hbad.2]

/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_alias_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_alias_reject
end Solidity.Backend.MemoryOps
