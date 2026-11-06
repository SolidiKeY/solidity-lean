import Solidity.Backend.MemoryOps.SourceUintFixedWrite
import Solidity.Evm.MemoryObjectStatements
import Solidity.Evm.MemorySource

/-! Actual uint256 indexed Source assignment and whole published word program.
Pure aligned local operands, RHS-first Source evaluation; no new compiler,
semantics, payload cap or desired reached relation premise. -/
namespace Solidity.Backend.MemoryOps

theorem SourceUintFixedAt.eval_index_loc {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H (.fixed (.prim .uint) n)}
    (_hr : SourceUintFixedAt y address hp r)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ (.array .memory (.int .u256) (some n))) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl address)
    (hindex : y.1.get index=sourceUint k) (hk : k.1.toNat<n) :
    (Source.evalLoc G F (fuel+2) (.indexArray (.local root) (by decide) (.local index) rfl)).run y=
      (.ok (.mem address k.1.toNat),y) := by
  rw [Source.evalLoc,Source.Hoare.run_bind,source_local_value_run G F fuel y root _ hroot]
  change ((Source.evalE G F (fuel+1) (.local index)) >>= fun value =>
    Source.indexNat value >>= fun j => Source.indexLoc F
      (.memRef rfl address : Source.Val E.layout (.array .memory (.int .u256) (some n))) j).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F fuel y index _ hindex]
  change (Source.indexLoc F
    (.memRef rfl address : Source.Val E.layout (.array .memory (.int .u256) (some n))) k.1.toNat).run y=_
  rw [Source.indexLoc,Source.Hoare.run_bind]
  change (if k.1.toNat<n then pure (Source.Loc.mem address k.1.toNat : Source.Loc E.layout Γ (.int .u256)) else Source.EM.lift (Source.panic .index)).run y=_
  rw [if_pos hk];rfl

theorem SourceUintFixedAt.eval_index_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H (.fixed (.prim .uint) n)}
    (_hr : SourceUintFixedAt y address hp r)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ (.array .memory (.int .u256) (some n))) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl address)
    (hindex : y.1.get index=sourceUint k) (hk : n≤k.1.toNat) :
    (Source.evalLoc G F (fuel+2) (.indexArray (.local root) (by decide) (.local index) rfl)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  rw [Source.evalLoc,Source.Hoare.run_bind,source_local_value_run G F fuel y root _ hroot]
  change ((Source.evalE G F (fuel+1) (.local index)) >>= fun value =>
    Source.indexNat value >>= fun j => Source.indexLoc F
      (.memRef rfl address : Source.Val E.layout (.array .memory (.int .u256) (some n))) j).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F fuel y index _ hindex]
  change (Source.indexLoc F
    (.memRef rfl address : Source.Val E.layout (.array .memory (.int .u256) (some n))) k.1.toNat).run y=_
  rw [Source.indexLoc,Source.Hoare.run_bind]
  change (if k.1.toNat<n then pure (Source.Loc.mem address k.1.toNat : Source.Loc E.layout Γ (.int .u256)) else Source.EM.lift (Source.panic .index)).run y=_
  rw [if_neg (Nat.not_lt.mpr hk)];rfl

def sourceUintFixedIndexedAssign {E : Source.Env} {Γ : Source.RCtx} {n : Nat}
    (root : Source.Idx Γ (.array .memory (.int .u256) (some n)))
    (index : Source.Idx Γ (.int .u256)) (rhs : Source.Idx Γ (.int .u256)) : Source.RExpr E Γ (.int .u256) :=
  .assign (.indexArray (.local root) (by decide) (.local index) rfl) (.local rhs)

theorem SourceUintFixedAt.eval_assign_of_run {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y z : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H (.fixed (.prim .uint) n)}
    (hr : SourceUintFixedAt y address hp r)
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ (.array .memory (.int .u256) (some n))) (index : Source.Idx Γ (.int .u256))
    (rhs : Source.Idx Γ (.int .u256)) (k : PrimTy.uint.Denote) (value : PrimTy.uint.Denote)
    (hroot : y.1.get root=.memRef rfl address) (hindex : y.1.get index=sourceUint k)
    (hrhs : y.1.get rhs=sourceUint value) (hk : k.1.toNat<n)
    (hwrite : (Source.writeLoc (E := E) (Γ := Γ) F (horizon+2) (.mem address k.1.toNat) (sourceUint value)).run y=(.ok (),z)) :
    (Source.evalE G F (horizon+3) (sourceUintFixedIndexedAssign root index rhs)).run y=(.ok (.val (sourceUint value)),z) := by
  unfold sourceUintFixedIndexedAssign
  rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F (horizon+1) y rhs (sourceUint value) hrhs]
  change ((Source.evalLoc G F (horizon+2)
    (.indexArray (.local root) (by decide) (.local index) rfl)) >>= fun loc =>
    Source.writeLoc F (horizon+2) loc (sourceUint value) >>= fun _ => pure (Source.RVal.val (sourceUint value))).run y=_
  rw [Source.Hoare.run_bind,hr.eval_index_loc G F horizon root index k hroot hindex hk]
  change ((Source.writeLoc (E := E) (Γ := Γ) F (horizon+2) (.mem address k.1.toNat) (sourceUint value)) >>=
    fun _ => pure (Source.RVal.val (sourceUint value))).run y=_
  rw [Source.Hoare.run_bind,hwrite]
  rfl

theorem SourceUintFixedAt.eval_assign_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H (.fixed (.prim .uint) n)}
    (hr : SourceUintFixedAt y address hp r)
    (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ (.array .memory (.int .u256) (some n))) (index : Source.Idx Γ (.int .u256))
    (rhs : Source.Idx Γ (.int .u256)) (k : PrimTy.uint.Denote) (value : PrimTy.uint.Denote)
    (hroot : y.1.get root=.memRef rfl address) (hindex : y.1.get index=sourceUint k)
    (hrhs : y.1.get rhs=sourceUint value) (hk : n≤k.1.toNat) :
    (Source.evalE G F (horizon+3) (sourceUintFixedIndexedAssign root index rhs)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  unfold sourceUintFixedIndexedAssign
  rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F (horizon+1) y rhs (sourceUint value) hrhs]
  change ((Source.evalLoc G F (horizon+2)
    (.indexArray (.local root) (by decide) (.local index) rfl)) >>= fun loc =>
    Source.writeLoc F (horizon+2) loc (sourceUint value) >>= fun _ => pure (Source.RVal.val (sourceUint value))).run y=_
  rw [Source.Hoare.run_bind,hr.eval_index_bounds G F horizon root index k hroot hindex hk]

theorem resolved_uint_fixed_assign_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {n : Nat}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (horizon : Nat) (σ : State C Δ) (r : HRef σ.H (.fixed (.prim .uint) n))
    (hr : SourceUintFixedAt y address σ.heap r)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) (some n))) (sindex : Source.Idx Γ (.int .u256))
    (srhs : Source.Idx Γ (.int .u256)) (root : Idx Δ (.mem (.fixed (.prim .uint) n)))
    (index : Idx Δ (.val .uint)) (rhs : Idx Δ (.val .uint)) (k : PrimTy.uint.Denote) (value : PrimTy.uint.Denote)
    (hsroot : y.1.get sroot=.memRef rfl address) (hsindex : y.1.get sindex=sourceUint k)
    (hsrhs : y.1.get srhs=sourceUint value) (htroot : TEnv.get root σ.env=some r)
    (htindex : TEnv.get index σ.env=k) (htrhs : TEnv.get rhs σ.env=value)
    (hk : k.1.toNat<n)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) :
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      σ.heap.writeAddr (.index r .fixed k) value=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc (horizon+2) (.mem address k.1.toNat) (sourceUint value)).run y=(.ok (),z) ∧
      (Source.evalE G Fsrc (horizon+3) (sourceUintFixedIndexedAssign sroot sindex srhs)).run y=(.ok (.val (sourceUint value)),z) ∧
      (Source.execS G Fsrc (horizon+4) Γ.length none
        (.expr (sourceUintFixedIndexedAssign sroot sindex srhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal y.1),(.nil,z.2)) ∧
      Stmt.run σ (.assignMem (.index .fixed (.var root rfl) (.simple (.local index))) (.val (.simple (.local rhs))))=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (Evm.compileVal b (.simple (.local rhs) : Val C Δ .uint) ++ [.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local index) : Val C Δ .uint) ++ Evm.Memory.Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))) m=.ok target 0 ∧
      SourceUintFixedAt z address out r ∧ Evm.Memory.Objects.StateRepr L b frame F (σ.withHeap out) base target ∧
      Source.MemOK E SH z ∧ z.1=y.1 ∧ target.stack=m.stack ∧
      Evm.Memory.Objects.KeepsAllocator b frame σ base m (σ.withHeap out) target := by
  obtain ⟨out,z,hw,hs,hr'⟩ := hr.write_addr Fsrc (horizon+2) k value hk
  have hi : TRun.assignMem (.index .fixed (.var root rfl) (.simple (.local index))) (.val (.simple (.local rhs))) σ=
      .ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,
      htroot,htindex,htrhs,bind,Except.bind,pure,Except.pure,hw,TRes.ofOpt]
  have hc := Evm.Memory.Objects.PtrFrag.write hm (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))
    (.local root rfl) (.val _ _ (.core (.simple (.local rhs)) rfl)) (.simple (.local index)) rfl
  unfold Evm.Memory.Objects.ResultRepr at hc
  rw [hi] at hc
  rcases hc with ⟨o,target,heq,hcode,hm',hstack,halloc⟩ | ⟨hbad,_⟩
  · cases Except.ok.inj heq
    have he := hr.eval_assign_of_run G Fsrc horizon sroot sindex srhs k value hsroot hsindex hsrhs hk hs
    have hstmt := source_expr_statement_run G Fsrc (horizon+3) Γ.length _ y z (.val (sourceUint value)) he
    obtain ⟨ht,hwrite⟩ := source_uint_fixed_write y address (σ.heap.get r) hr k.1.toNat hk value
    have hl : z.1=y.1 := congrArg (fun q : Except Source.Halt Unit × Source.EMState E Γ => q.2.1) (hs.symm.trans hwrite)
    have hmk := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) Fsrc (horizon+2)
      (.mem (τ := .int .u256) address k.1.toNat) (sourceUint value) y ⟨hmem,trivial⟩
    rw [hs] at hmk
    refine ⟨out,z,target,hw,hs,he,?_,hi,hcode,hr',hm',hmk,hl,hstack,halloc⟩
    simpa only [hl] using hstmt
  · cases hbad

/-- Bounds rejection derives both actual Source syntax and target observations
from the runtime local values; panic bytes and target revert stay distinct. -/
theorem resolved_uint_fixed_assign_word_bounds {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx} {n : Nat}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (horizon : Nat) (σ : State C Δ) (r : HRef σ.H (.fixed (.prim .uint) n))
    (hr : SourceUintFixedAt y address σ.heap r)
    (sroot : Source.Idx Γ (.array .memory (.int .u256) (some n))) (sindex : Source.Idx Γ (.int .u256))
    (srhs : Source.Idx Γ (.int .u256)) (root : Idx Δ (.mem (.fixed (.prim .uint) n)))
    (index : Idx Δ (.val .uint)) (rhs : Idx Δ (.val .uint)) (k : PrimTy.uint.Denote) (value : PrimTy.uint.Denote)
    (hsroot : y.1.get sroot=.memRef rfl address) (hsindex : y.1.get sindex=sourceUint k)
    (hsrhs : y.1.get srhs=sourceUint value) (htroot : TEnv.get root σ.env=some r)
    (htindex : TEnv.get index σ.env=k) (htrhs : TEnv.get rhs σ.env=value)
    (hk : n≤k.1.toNat)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.Objects.StateRepr L b frame F σ base m) :
    (Source.evalE G Fsrc (horizon+3) (sourceUintFixedIndexedAssign sroot sindex srhs)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
    Evm.run (Evm.compileVal b (.simple (.local rhs) : Val C Δ .uint) ++ [.mload (Evm.cellOf b root)] ++ Evm.compileVal b (.simple (.local index) : Val C Δ .uint) ++ Evm.Memory.Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))) m=.revert := by
  have hn : σ.heap.writeAddr (.index r .fixed k) value=none := by
    simp only [Heap.writeAddr,Heap.setIndex,show ¬k.1.toNat<(MObj.elems .fixed (σ.heap.get r)).length from by simpa only [MObj.elems_fixed,(σ.heap.get r).2] using Nat.not_lt.mpr hk,↓reduceIte]
  have hi : TRun.assignMem (.index .fixed (.var root rfl) (.simple (.local index))) (.val (.simple (.local rhs))) σ=
      .error .revert := by
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,
      htroot,htindex,htrhs,bind,Except.bind,pure,Except.pure,hn,TRes.ofOpt]
  have hc := Evm.Memory.Objects.PtrFrag.write hm (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))
    (.local root rfl) (.val _ _ (.core (.simple (.local rhs)) rfl)) (.simple (.local index)) rfl
  unfold Evm.Memory.Objects.ResultRepr at hc
  rw [hi] at hc
  refine ⟨hr.eval_assign_bounds G Fsrc horizon sroot sindex srhs k value hsroot hsindex hsrhs hk,?_⟩
  rcases hc with ⟨o,target,heq,_⟩ | ⟨_,hcode⟩
  · cases heq
  · exact hcode

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAt.eval_index_loc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedAt.eval_index_loc
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAt.eval_index_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedAt.eval_index_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAt.eval_assign_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedAt.eval_assign_of_run
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedAt.eval_assign_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedAt.eval_assign_bounds
/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_fixed_assign_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_fixed_assign_word
/-- info: 'Solidity.Backend.MemoryOps.resolved_uint_fixed_assign_word_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_uint_fixed_assign_word_bounds
end Solidity.Backend.MemoryOps
