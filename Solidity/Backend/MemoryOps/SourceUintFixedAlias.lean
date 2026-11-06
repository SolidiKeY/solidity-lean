import Solidity.Backend.MemoryOps.SourceAlias
import Solidity.Backend.MemoryOps.SourceUintFixedDelete
import Solidity.Evm.MemoryObjectStatements

/-! Existing fixed-reference local rebinding, now carrying the INITIAL fixed
Source observer and compatible Objects.StateRepr. No copy or new evaluator. -/
namespace Solidity.Backend.MemoryOps

/-- Other Source locals are framed by their actual intrinsic positions. -/
theorem source_locals_get_set_other {D : Source.Layout} :
    {Γ : Source.RCtx} → {τ υ : Source.STy} → (l : Source.Locals D Γ) →
    (i : Source.Idx Γ τ) → (j : Source.Idx Γ υ) → (v : Source.Val D τ) →
    i.toNat≠j.toNat → (l.set i v).get j=l.get j
  | _, _, _, .cons _ _, .here, .here, _, h => (h rfl).elim
  | _, _, _, .cons _ _, .here, .there _, _, _ => rfl
  | _, _, _, .cons _ _, .there _, .here, _, _ => rfl
  | _, _, _, .cons _ rest, .there i, .there j, v, h =>
      source_locals_get_set_other rest i j v (fun he => h (congrArg (·+1) he))

private theorem source_idx_type {Γ : Source.RCtx} {τ : Source.STy} (i : Source.Idx Γ τ) : Γ[i.toNat]?=some τ := by
  induction i with
  | here => rfl
  | there i ih => exact ih

private theorem source_ref_uint_ne {Γ : Source.RCtx} {n : Nat}
    (dst : Source.Idx Γ (.array .memory (.int .u256) (some n))) (i : Source.Idx Γ (.int .u256)) : dst.toNat≠i.toNat := by
  intro h
  have hd := source_idx_type dst
  rw [h,source_idx_type i] at hd
  cases hd

private theorem target_ref_uint_ne {Δ : Ctx} {n : Nat}
    (dst : Idx Δ (.mem (.fixed (.prim .uint) n))) (i : Idx Δ (.val .uint)) : dst.toNat≠i.toNat := by
  intro h
  have hd := dst.getElem?_toNat
  rw [h,i.getElem?_toNat] at hd
  cases hd

/-- Scalar operands cannot be the rebound reference local by their actual types;
there is no independent caller-supplied noninterference premise. -/
theorem fixed_alias_scalar_frames {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {n : Nat}
    (y : Source.EMState E Γ) (sdst : Source.Idx Γ (.array .memory (.int .u256) (some n)))
    (si : Source.Idx Γ (.int .u256)) (address : Nat) (σ : State C Δ)
    (dst : Idx Δ (.mem (.fixed (.prim .uint) n))) (i : Idx Δ (.val .uint))
    (r : HRef σ.H (.fixed (.prim .uint) n)) :
    (y.1.set sdst (.memRef rfl address)).get si=y.1.get si ∧
    TEnv.get i (σ.setLocal dst (some r)).env=TEnv.get i σ.env :=
  ⟨source_locals_get_set_other _ _ _ _ (source_ref_uint_ne sdst si),
    TEnv.get_set_ne _ _ _ _ (target_ref_uint_ne dst i)⟩

/-- Actual pointer replacement, from initial alignment and represented contents.
No final agreement or heap preservation is assumed; all are derived. -/
theorem source_uint_fixed_alias_word
    {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {n : Nat}
    (G : Source.Glob E) (Fsrc : Source.Fr) (horizon : Nat)
    (y : Source.EMState E Γ) (sdst ssrc : Source.Idx Γ (.array .memory (.int .u256) (some n)))
    (address : Nat) (hs : y.1.get ssrc=.memRef rfl address) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y)
    (σ : State C Δ) (dst src : Idx Δ (.mem (.fixed (.prim .uint) n)))
    (r : HRef σ.H (.fixed (.prim .uint) n)) (ht : TEnv.get src σ.env=some r)
    (hr : SourceUintFixedAt y address σ.heap r)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {cursor : Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m)
    (ha : Evm.Memory.Objects.AllocatorRepr σ.heap base frame cursor m) (hb : 0<b) :
    let z : Source.EMState E Γ := (y.1.set sdst (.memRef rfl address),y.2)
    let σ' := σ.setLocal dst (some r)
    let m' := Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base r.id))
    (Source.evalE G Fsrc (horizon+2) (sourceLocalAlias sdst ssrc)).run y=(.ok (.val (.memRef rfl address)),z) ∧
    (Source.execS G Fsrc (horizon+3) Γ.length none
      (.expr (sourceLocalAlias sdst ssrc) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
    Stmt.run σ (.rebindMem dst (.alias (.var src rfl)))=.ok ⟨σ',List.prefix_refl _⟩ ∧
    Evm.run (Evm.Memory.aliasLocalCode b dst src) m=.ok m' 0 ∧
    SourceUintFixedAt z address σ'.heap r ∧ Source.MemOK E SH z ∧
    Evm.Memory.Objects.StateRepr L b frame F σ' base m' ∧
    Evm.Memory.Objects.AllocatorRepr σ'.heap base frame cursor m' ∧
    Evm.Memory.Objects.KeepsAllocator b frame σ base m σ' m' ∧
    z.1.get sdst=.memRef rfl address ∧ TEnv.get dst σ'.env=some r ∧
    z.2=y.2 ∧ σ'.heap=σ.heap ∧ m'.stack=m.stack ∧ m'.mem 0=m.mem 0 ∧
    (∀ {τ : Source.STy} (q : Source.Idx Γ τ),sdst.toNat≠q.toNat → z.1.get q=y.1.get q) ∧
    (∀ {t : LTy} (q : Idx Δ t),dst.toNat≠q.toNat → TEnv.get q σ'.env=TEnv.get q σ.env) ∧
    (∀ {Q : RefTy} (q : HRef σ.H Q),σ'.heap.get q=σ.heap.get q) ∧
    (∀ a,z.2.heap.get a=y.2.heap.get a) := by
  dsimp only
  have he := source_local_alias_run G Fsrc horizon y sdst ssrc (.memRef rfl address) hs
  have hsstmt := source_expr_statement_run G Fsrc (horizon+2) Γ.length _ y
    (y.1.set sdst (.memRef rfl address),y.2) (.val (.memRef rfl address)) he
  have hmk := source_local_alias_memOK Fsrc (horizon+1) y sdst ssrc SH hmem
  rw [hs] at hmk
  have hi : TRun.rebindMem dst (.alias (.var src rfl)) σ=.ok ⟨σ.setLocal dst (some r),List.prefix_refl _⟩ := by
    simp only [TRun.rebindMem,MRhs.evalT,MPath.mvalT,ht,bind,Except.bind,pure,Except.pure]
  have cert := Evm.Memory.Objects.PtrFrag.rebind hm (.local src rfl) dst
  unfold Evm.Memory.Objects.ResultRepr at cert
  rw [hi] at cert
  obtain ⟨q,hq,hptr⟩ := hm.pointers src
  have hqr : q=r := Option.some.inj (hq.symm.trans ht)
  subst q
  have hcode : Evm.run (Evm.Memory.aliasLocalCode b dst src) m=
      .ok (Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base r.id))) 0 := by
    simp only [Evm.run,Evm.Memory.aliasLocalCode,Evm.exec_cons_zero,Evm.Instr.step,Evm.Machine.next,
      Evm.Out.ok_bind,hptr,Evm.exec_nil,Evm.Memory.writeMachine]
  rcases cert with ⟨o,target,ho,hc,hm',hstack,halloc⟩ | ⟨hbad,_⟩
  · cases Except.ok.inj ho
    have htgt : target=Evm.Memory.writeMachine m (Evm.cellOf b dst) (.val (base r.id)) := (Evm.Out.ok.inj (hc.symm.trans hcode)).1
    subst target
    have ha' := halloc cursor hb ha
    refine ⟨he,hsstmt,hi,hcode,hr,hmk,hm',ha',halloc,source_locals_get_set _ _ _,TEnv.get_set _ _ _,rfl,rfl,rfl,
      ha'.free.cell.trans ha.free.cell.symm,?_,?_,fun _ => rfl,fun _ => rfl⟩
    · intro τ q hn
      exact source_locals_get_set_other y.1 sdst q _ hn
    · intro t q hn
      exact TEnv.get_set_ne dst q _ σ.env hn
  · cases hbad

/-- info: 'Solidity.Backend.MemoryOps.source_locals_get_set_other' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms source_locals_get_set_other
/-- info: 'Solidity.Backend.MemoryOps.fixed_alias_scalar_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_alias_scalar_frames
/-- info: 'Solidity.Backend.MemoryOps.source_uint_fixed_alias_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_uint_fixed_alias_word
end Solidity.Backend.MemoryOps
