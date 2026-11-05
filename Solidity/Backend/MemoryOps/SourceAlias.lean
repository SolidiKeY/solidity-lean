import Solidity.Backend.MemoryOps.SourceIndexedDelete
import Solidity.Evm.MemoryRefArrayState

/-! Actual existing Source local assignment and published intrinsic/word memory
reference rebinding. Initial pointer alignment only; no new type/graph relation,
constructor, value/state layer, copy algorithm or physical-address assumption. -/
namespace Solidity.Backend.MemoryOps

def sourceLocalAlias {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (dst src : Source.Idx Γ τ) : Source.RExpr E Γ τ := .assign (.local dst) (.local src)

theorem source_locals_get_set {D : Source.Layout} : {Γ : Source.RCtx} → {τ : Source.STy} →
    (l : Source.Locals D Γ) → (i : Source.Idx Γ τ) → (v : Source.Val D τ) → (l.set i v).get i=v
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons _ l, .there i, v => source_locals_get_set l i v

theorem source_local_alias_run {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat) (y : Source.EMState E Γ)
    (dst src : Source.Idx Γ τ) (v : Source.Val E.layout τ) (hs : y.1.get src=v) :
    (Source.evalE G F (horizon+2) (sourceLocalAlias dst src)).run y=
      (.ok (.val v),(y.1.set dst v,y.2)) := by
  unfold sourceLocalAlias
  rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F horizon y src v hs]
  change ((Source.evalLoc G F (horizon+1) (.local dst)) >>= fun loc =>
    Source.writeLoc F (horizon+1) loc v >>= fun _ => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,show (Source.evalLoc G F (horizon+1) (.local dst)).run y=(.ok (.local dst),y) from rfl]
  rfl

theorem source_local_alias_memOK {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (F : Source.Fr) (horizon : Nat) (y : Source.EMState E Γ) (dst src : Source.Idx Γ τ)
    (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    Source.MemOK E SH (y.1.set dst (y.1.get src),y.2) := by
  have hv := Source.LocalsOK.get y.1 src hm.1.2
  have hpres := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) F horizon (.local dst) (y.1.get src) y ⟨hm,hv⟩
  have hw : (Source.writeLoc (E := E) (Γ := Γ) F horizon (.local dst) (y.1.get src)).run y=
      (.ok (),(y.1.set dst (y.1.get src),y.2)) := rfl
  rw [hw] at hpres
  exact hpres

/-- Generic typed reference identity transport, including reference-containing
arrays. Source and target copy their actual INITIAL pointer, leaving both heaps
unchanged. This is not a source type-graph or deep-content representation theorem. -/
theorem source_alias_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {τ : Source.STy} (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
    (y : Source.EMState E Γ) (sdst ssrc : Source.Idx Γ τ)
    (hloc : τ.loc?=some .memory) (address : Nat) (hs : y.1.get ssrc=.memRef hloc address)
    (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    (σ : State C Δ) {R : RefTy} (dst src : Idx Δ (.mem R))
    (r : HRef σ.H R) (ht : TEnv.get src σ.env=some r) (hmf : (Ty.ref R).mapFree=true)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    let z : Source.EMState E Γ := (y.1.set sdst (.memRef hloc address),y.2)
    let σ' := σ.setLocal dst (some r)
    let m' := Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base r.id))
    (Source.evalE G Fsrc (horizon+2) (sourceLocalAlias sdst ssrc)).run y=(.ok (.val (.memRef hloc address)),z) ∧
    (Source.execS G Fsrc (horizon+3) Γ.length none
      (.expr (sourceLocalAlias sdst ssrc) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
    Stmt.run σ (.rebindMem dst (.alias (.var src hmf)))=.ok ⟨σ',List.prefix_refl _⟩ ∧
    Evm.run (Evm.Memory.aliasLocalCode b dst src) m=.ok m' 0 ∧
    Source.MemOK E SH z ∧ z.2.heap=y.2.heap ∧ σ'.heap=σ.heap ∧
    z.1.get sdst=.memRef hloc address ∧ TEnv.get dst σ'.env=some r ∧
    Evm.Memory.RefArrayStateRepr L b frame F σ' base m' ∧ m'.stack=m.stack ∧
    Evm.Memory.KeepsAllocator b frame σ base m σ' m' := by
  dsimp only
  have he := source_local_alias_run G Fsrc horizon y sdst ssrc (.memRef hloc address) hs
  have hsstmt := source_expr_statement_run G Fsrc (horizon+2) Γ.length _ y
    (y.1.set sdst (.memRef hloc address),y.2) (.val (.memRef hloc address)) he
  have hmk := source_local_alias_memOK Fsrc (horizon+1) y sdst ssrc SH hmem
  rw [hs] at hmk
  have hi : Stmt.run σ (.rebindMem dst (.alias (.var src hmf)))=.ok ⟨σ.setLocal dst (some r),List.prefix_refl _⟩ := by
    change TRun.rebindMem dst (.alias (.var src hmf)) σ=_
    simp only [TRun.rebindMem,MRhs.evalT,MPath.mvalT,ht,bind,Except.bind,pure,Except.pure]
  have hc := Evm.Memory.aliasLocal_correct hm.state dst src hmf
  rw [show TRun.rebindMem dst (.alias (.var src hmf)) σ=.ok ⟨σ.setLocal dst (some r),List.prefix_refl _⟩ from hi] at hc
  obtain ⟨q,hq,hptr⟩ := hm.state.pointers src
  have hqr : q=r := Option.some.inj (hq.symm.trans ht)
  subst q
  have hcode : Evm.run (Evm.Memory.aliasLocalCode b dst src) m=
      .ok (Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base r.id))) 0 := by
    simp only [Evm.run,Evm.Memory.aliasLocalCode,Evm.exec_cons_zero,Evm.Instr.step,Evm.Machine.next,
      Evm.Out.ok_bind,hptr,Evm.exec_nil,Evm.Memory.writeMachine]
  rcases hc with ⟨o,target,ho,hrun,hstate,hstack,halloc⟩ | ⟨hbad,_⟩
  · cases Except.ok.inj ho
    have heq := hcode.symm.trans hrun
    cases heq
    exact ⟨he,hsstmt,hi,hcode,hmk,rfl,rfl,source_locals_get_set _ _ _,TEnv.get_set _ _ _,hm.setMem dst r,rfl,halloc⟩
  · cases hbad

theorem source_local_alias_low_horizon {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ) (dst src : Source.Idx Γ τ) :
    ∀ n, n≤1 → (Source.evalE G F n (sourceLocalAlias dst src)).run y=(.error .timeout,y) := by
  intro n hn
  match n with
  | 0 => rfl
  | 1 => rfl
  | n+2 => omega

/-- info: 'Solidity.Backend.MemoryOps.source_locals_get_set' does not depend on any axioms -/
#guard_msgs in #print axioms source_locals_get_set
/-- info: 'Solidity.Backend.MemoryOps.source_local_alias_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_local_alias_run
/-- info: 'Solidity.Backend.MemoryOps.source_local_alias_memOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_local_alias_memOK
/-- info: 'Solidity.Backend.MemoryOps.source_alias_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_alias_word
/-- info: 'Solidity.Backend.MemoryOps.source_local_alias_low_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_local_alias_low_horizon
end Solidity.Backend.MemoryOps
