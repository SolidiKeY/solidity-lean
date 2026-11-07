import Solidity.Backend.MemoryOps.SourceDeleteTarget
import Solidity.Backend.MemoryOps.CalldataUintTransfer
import Solidity.Source.ExprProgress

/-! Existing resolved Source delete syntax, actual location evaluation and the
published intrinsic/word operation. No new AST, evaluator or source profile. -/
namespace Solidity.Backend.MemoryOps

/-- A family of EXISTING resolved Source terms: memory base local then uint
index local, with the read/write restrictions carried by its intrinsic type. -/
def sourceIndexedDelete {E : Source.Env} {Γ : Source.RCtx}
    (root : Source.Idx Γ (.array .memory .bool none))
    (index : Source.Idx Γ (.int .u256)) : Source.RExpr E Γ (.tuple []) :=
  .delete (.indexArray (.local root) (by decide) (.local index) rfl)

theorem source_local_value_run {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (j : Source.Idx Γ τ) (value : Source.Val E.layout τ) (hj : y.1.get j=value) :
    (Source.evalE G F (fuel+1) (.local j)).run y=(.ok (.val value),y) := by
  rw [Source.evalE,Source.Hoare.run_bind]
  rw [show (Source.EM.locals (E := E) (Γ := Γ)).run y=(.ok y.1,y) from rfl]
  change (Except.ok (Source.RVal.val (y.1.get j)),y)=(.ok (.val value),y)
  rw [hj]

theorem SourceBoolMemoryAt.length_run {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a) (F : Source.Fr) :
    (Source.lengthOf (E := E) (Γ := Γ) F
      (.memRef rfl address : Source.Val E.layout (.array .memory .bool none))).run y=(.ok (hp.len r a),y) := by
  simp only [Source.lengthOf,Source.Hoare.run_bind,Heap.len]
  rw [source_heapObj_run y address _ hr]
  rfl

theorem SourceBoolMemoryAt.indexLoc_run {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (F : Source.Fr) (k : Nat) (hk : k<hp.len r a) :
    (Source.indexLoc (E := E) (Γ := Γ) F
      (.memRef rfl address : Source.Val E.layout (.array .memory .bool none)) k).run y=(.ok (.mem address k),y) := by
  rw [Source.indexLoc,Source.Hoare.run_bind,hr.length_run F]
  simp only [hk,↓reduceIte]
  rfl

theorem SourceBoolMemoryAt.indexLoc_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (F : Source.Fr) (k : Nat) (hk : hp.len r a≤k) :
    (Source.indexLoc (E := E) (Γ := Γ) F
      (.memRef rfl address : Source.Val E.layout (.array .memory .bool none)) k).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  rw [Source.indexLoc,Source.Hoare.run_bind,hr.length_run F]
  simp only [show ¬k<hp.len r a from Nat.not_lt.mpr hk,↓reduceIte]
  rfl

theorem source_index_ops {E : Source.Env} {Γ : Source.RCtx}
    (root : Source.Idx Γ (.array .memory .bool none)) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) :
    (sourceIndexedDelete (E := E) root index).OpsOK ∧
      Source.NotStuckR ((Source.RVal.val (sourceUint (D := E.layout) k)).amount) := by
  constructor
  · trivial
  · exact Source.amount_ok rfl _

/-- Actual resolved location execution derives the location from the two
independent Source locals; no computed-location oracle is a premise. -/
theorem SourceBoolMemoryAt.eval_index_loc {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ (.array .memory .bool none)) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl address)
    (hindex : y.1.get index=sourceUint k) (hk : k.1.toNat<hp.len r a) :
    (Source.evalLoc G F (fuel+2) (.indexArray (.local root) (by decide) (.local index) rfl)).run y=
      (.ok (.mem address k.1.toNat),y) := by
  rw [Source.evalLoc,Source.Hoare.run_bind,source_local_value_run G F fuel y root _ hroot]
  change ((Source.evalE G F (fuel+1) (.local index)) >>= fun value =>
    Source.indexNat value >>= fun n => Source.indexLoc F
      (.memRef rfl address : Source.Val E.layout (.array .memory .bool none)) n).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F fuel y index _ hindex]
  change (Source.indexLoc F
    (.memRef rfl address : Source.Val E.layout (.array .memory .bool none)) k.1.toNat).run y=_
  exact hr.indexLoc_run F _ hk

theorem SourceBoolMemoryAt.eval_index_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ (.array .memory .bool none)) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl address)
    (hindex : y.1.get index=sourceUint k) (hk : hp.len r a≤k.1.toNat) :
    (Source.evalLoc G F (fuel+2) (.indexArray (.local root) (by decide) (.local index) rfl)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  rw [Source.evalLoc,Source.Hoare.run_bind,source_local_value_run G F fuel y root _ hroot]
  change ((Source.evalE G F (fuel+1) (.local index)) >>= fun value =>
    Source.indexNat value >>= fun n => Source.indexLoc F
      (.memRef rfl address : Source.Val E.layout (.array .memory .bool none)) n).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F fuel y index _ hindex]
  change (Source.indexLoc F
    (.memRef rfl address : Source.Val E.layout (.array .memory .bool none)) k.1.toNat).run y=_
  exact hr.indexLoc_bounds F _ hk

/-- The effectful resolved delete actually evaluates its base and index before
calling the existing write operation, at the actual Source state. -/
theorem SourceBoolMemoryAt.eval_delete_of_run {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y z : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ (.array .memory .bool none)) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl address)
    (hindex : y.1.get index=sourceUint k) (hk : k.1.toNat<hp.len r a)
    (hdelete : (Source.deleteLoc (E := E) (Γ := Γ) F (fuel+2) (τ := .bool) (.mem address k.1.toNat)).run y=(.ok (),z)) :
    (Source.evalE G F (fuel+3) (sourceIndexedDelete root index)).run y=(.ok Source.RVal.unit,z) := by
  unfold sourceIndexedDelete
  rw [Source.evalE,Source.Hoare.run_bind,hr.eval_index_loc G F fuel root index k hroot hindex hk]
  change ((Source.deleteLoc (E := E) (Γ := Γ) F (fuel+2) (τ := .bool) (.mem address k.1.toNat)) >>=
    fun _ => pure Source.RVal.unit).run y=_
  rw [Source.Hoare.run_bind,hdelete]
  rfl

theorem SourceBoolMemoryAt.eval_delete_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ (.array .memory .bool none)) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl address)
    (hindex : y.1.get index=sourceUint k) (hk : hp.len r a≤k.1.toNat) :
    (Source.evalE G F (fuel+3) (sourceIndexedDelete root index)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  unfold sourceIndexedDelete
  rw [Source.evalE,Source.Hoare.run_bind,hr.eval_index_bounds G F fuel root index k hroot hindex hk]

/-- Lift an ACTUAL expression run to its existing resolved expression statement.
The outer interpreter locals are empty; the returned typed frame is explicit. -/
theorem source_expr_statement_run {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat)
    (e : Source.RExpr E Γ τ) (y z : Source.EMState E Γ) (value : Source.RVal E.layout τ)
    (he : (Source.evalE G F fuel e).run y=(.ok value,z)) :
    (Source.execS G F (fuel+1) nps none
      (.expr e : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
        (.ok (.normal z.1),(.nil,z.2)) := by
  have hsub : (Source.EM.sub (Γ := []) y.1 (Source.evalE G F fuel e)).run (.nil,y.2)=
      (.ok (value,z.1),(.nil,z.2)) := by
    unfold Source.EM.sub
    have he' : (Source.evalE (plan := none) G F fuel e) (y.1,y.2)=(.ok value,z) := he
    cases z
    simp only [ExceptT.run,ExceptT.mk,he']
  rw [Source.execS,Source.Hoare.run_bind,hsub]
  rfl

/-- Supported resolved Source syntax is related to the ACTUAL intrinsic
statement and its published word code. No location/evaluation/postrelation
oracle appears: local scalar/reference alignment is INITIAL input data. -/
theorem resolved_delete_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (fuel : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .bool)))
    (hr : SourceBoolMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory .bool none)) (sindex : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.array (.prim .bool)))) (index : Idx Δ (.val .uint))
    (k : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address)
    (hsindex : y.1.get sindex=sourceUint k) (htroot : TEnv.get root σ.env=some r)
    (htindex : TEnv.get index σ.env=k) (hk : k.1.toNat<σ.heap.len r .dyn)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (SH : Source.HeapTy) (hmem : Source.MemOK E SH y) :
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      σ.heap.writeAddr (.index r .dyn k) (PrimTy.dflt .bool)=some out ∧
      (Source.evalE G Fsrc (fuel+3) (sourceIndexedDelete sroot sindex)).run y=(.ok Source.RVal.unit,z) ∧
      (Source.execS G Fsrc (fuel+4) Γ.length none
        (.expr (sourceIndexedDelete sroot sindex) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal y.1),(.nil,z.2)) ∧
      Stmt.run σ (.deleteMem (.loc (.index .dyn (.var root rfl) (.simple (.local index)))) rfl)=
        .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local index) : Val C Δ .uint))) m=
        .ok target 0 ∧ SourceBoolMemoryAt z address out r .dyn ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      Source.MemOK E SH z ∧ z.1=y.1 ∧ target.stack=m.stack ∧
      Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target := by
  have he : (Val.simple (Simple.local index)).evalT σ=.ok k := by
    simp only [Val.evalT,Simple.evalT,htindex]
  obtain ⟨out,z,target,hw,hintr,hdelete,hcode,hr',hm',hstack,halloc⟩ :=
    source_delete_word_target σ r hr Fsrc (fuel+1) root htroot (.simple (.local index)) k he hk hm rfl
  have hexpr := hr.eval_delete_of_run G Fsrc fuel sroot sindex k hsroot hsindex hk hdelete
  have hstmt := source_expr_statement_run G Fsrc (fuel+3) Γ.length
    (sourceIndexedDelete sroot sindex) y z Source.RVal.unit hexpr
  obtain ⟨ht,hwrite⟩ := source_bool_write y address _ hr k.1.toNat hk false
  have hlocals : z.1=y.1 := by
    exact congrArg (fun q : Except Source.Halt Unit × Source.EMState E Γ => q.2.1) (hdelete.symm.trans hwrite)
  have hmem' := source_bool_delete_memOK y z SH hmem Fsrc (fuel+2) address k.1.toNat hdelete
  refine ⟨out,z,target,hw,hexpr,?_,hintr,hcode,hr',hm',hmem',hlocals,hstack,halloc⟩
  simpa only [hlocals] using hstmt

/-- Exact statement-free bounds rejection: failure arises during actual
Source location evaluation before its deletion operation is reached. -/
theorem resolved_delete_word_bounds {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (G : Source.Glob E) (Fsrc : Source.Fr)
    (fuel : Nat) (σ : State C Δ) (r : HRef σ.H (.array (.prim .bool)))
    (hr : SourceBoolMemoryAt y address σ.heap r .dyn)
    (sroot : Source.Idx Γ (.array .memory .bool none)) (sindex : Source.Idx Γ (.int .u256))
    (root : Idx Δ (.mem (.array (.prim .bool)))) (index : Idx Δ (.val .uint))
    (k : PrimTy.uint.Denote) (hsroot : y.1.get sroot=.memRef rfl address)
    (hsindex : y.1.get sindex=sourceUint k) (htroot : TEnv.get root σ.env=some r)
    (htindex : TEnv.get index σ.env=k) (hk : σ.heap.len r .dyn≤k.1.toNat)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) :
    (Source.evalE G Fsrc (fuel+3) (sourceIndexedDelete sroot sindex)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
    Evm.run (Evm.Memory.deleteLocalCode b root (Evm.compileVal b (.simple (.local index) : Val C Δ .uint))) m=.revert := by
  have he : (Val.simple (Simple.local index)).evalT σ=.ok k := by
    simp only [Val.evalT,Simple.evalT,htindex]
  exact ⟨hr.eval_delete_bounds G Fsrc fuel sroot sindex k hsroot hsindex hk,
    (source_delete_word_bounds σ r hr Fsrc (fuel+1) root htroot (.simple (.local index)) k he hk hm rfl).2⟩

/-- info: 'Solidity.Backend.MemoryOps.source_local_value_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_local_value_run
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.length_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.length_run
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.indexLoc_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.indexLoc_run
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.indexLoc_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.indexLoc_bounds
/-- info: 'Solidity.Backend.MemoryOps.source_index_ops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_index_ops
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.eval_index_loc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.eval_index_loc
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.eval_index_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.eval_index_bounds
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.eval_delete_of_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.eval_delete_of_run
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.eval_delete_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolMemoryAt.eval_delete_bounds
/-- info: 'Solidity.Backend.MemoryOps.source_expr_statement_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_expr_statement_run
/-- info: 'Solidity.Backend.MemoryOps.resolved_delete_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resolved_delete_word
/-- info: 'Solidity.Backend.MemoryOps.resolved_delete_word_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resolved_delete_word_bounds
end Solidity.Backend.MemoryOps
