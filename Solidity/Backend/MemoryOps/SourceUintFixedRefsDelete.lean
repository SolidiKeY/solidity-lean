import Solidity.Backend.MemoryOps.SourceUintFixedRefsWrite
import Solidity.Backend.MemoryOps.SourceSequence

/-! Actual primitive deletion through a represented fixed child, preserving
both repeated aliases and separately addressed sibling objects. -/
namespace Solidity.Backend.MemoryOps

def sourceUintFixedNestedDelete {E : Source.Env} {Γ : Source.RCtx} {n : Nat}
    (root : Source.Idx Γ (SourceUintFixedRefsTy n)) (i j : Source.Idx Γ (.int .u256)) : Source.RExpr E Γ (.tuple []) :=
  .delete (sourceUintFixedNestedLoc root i j)

theorem SourceUintFixedRefsAt.resolved_delete {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (G : Source.Glob E) (F : Source.Fr) (horizon nps : Nat)
    (root : Source.Idx Γ (SourceUintFixedRefsTy n)) (i j : Source.Idx Γ (.int .u256))
    (k l : PrimTy.uint.Denote) (q : HRef H (.fixed (.prim .uint) n))
    (hroot : y.1.get root=.memRef rfl a) (hi : y.1.get i=sourceUint k) (hj : y.1.get j=sourceUint l)
    (hq : hp.index r .dyn k=some q)
    (separate : ∀ t∈MObj.elems .dyn (hp.get r),t.id≠q.id → address t.id≠address q.id)
    (hl : l.1.toNat<n) (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index q .fixed l) (PrimTy.dflt .uint)=some out ∧
      (Source.evalE G F (horizon+4) (sourceUintFixedNestedDelete root i j)).run y=(.ok Source.RVal.unit,z) ∧
      (Source.execS G F (horizon+5) nps none
        (.expr (sourceUintFixedNestedDelete root i j) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      SourceUintFixedRefsAt z a out r address ∧ Source.MemOK E SH z ∧ z.1=y.1 ∧ z.2.heap.next=y.2.heap.next ∧ out.get r=hp.get r ∧
      (∀ {Q : RefTy} (t : HRef H Q),q.id≠t.id → out.get t=hp.get t) ∧
      (∀ b,b≠address q.id → z.2.heap.get b=y.2.heap.get b) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve | simp only [] | omega
  | have member : q∈MObj.elems .dyn (hp.get r) := List.mem_of_getElem? hq
    obtain ⟨out,z,typed,write,reached,preserved,locals,next,parent,objects,addresses,world,events,logs,fnLocals⟩ :=
      hr.write_child q member separate F (horizon+3) l (PrimTy.dflt .uint) hl SH memOK
    have deletion : (Source.deleteLoc (E := E) (Γ := Γ) F (horizon+3)
        (τ := .int .u256) (.mem (address q.id) l.1.toNat)).run y=(.ok (),z) := write
    have expr : (Source.evalE G F (horizon+4) (sourceUintFixedNestedDelete root i j)).run y=(.ok Source.RVal.unit,z) := by
      rw [sourceUintFixedNestedDelete,Source.evalE,Source.Hoare.run_bind,
        hr.eval_nested_loc G F horizon root i j k l q hroot hi hj hq hl]
      change (Source.deleteLoc F (horizon+3) (τ := .int .u256) (.mem (address q.id) l.1.toNat) >>= fun _ => pure Source.RVal.unit).run y=_
      rw [Source.Hoare.run_bind,deletion]
      rfl
    exact ⟨out,z,typed,expr,source_expr_statement_run G F (horizon+4) nps _ y z Source.RVal.unit expr,
      reached,preserved,locals,next,parent,objects,addresses,world,events,logs,fnLocals⟩


theorem SourceUintFixedRefsAt.write_delete_items {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (G : Source.Glob E) (F : Source.Fr) (horizon nps : Nat)
    (root : Source.Idx Γ (SourceUintFixedRefsTy n)) (i j rhs : Source.Idx Γ (.int .u256))
    (k l v : PrimTy.uint.Denote) (q : HRef H (.fixed (.prim .uint) n))
    (hroot : y.1.get root=.memRef rfl a) (hi : y.1.get i=sourceUint k) (hj : y.1.get j=sourceUint l)
    (hv : y.1.get rhs=sourceUint v) (hq : hp.index r .dyn k=some q)
    (separate : ∀ t∈MObj.elems .dyn (hp.get r),t.id≠q.id → address t.id≠address q.id)
    (hl : l.1.toNat<n) (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    ∃ (mid out : Heap H) (ym z : Source.EMState E Γ),
      hp.writeAddr (.index q .fixed l) v=some mid ∧
      mid.writeAddr (.index q .fixed l) (PrimTy.dflt .uint)=some out ∧
      (Source.execS G F (horizon+6) nps none
        (.expr (sourceUintFixedNestedAssign root i j rhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS G F (horizon+5) nps none
        (.expr (sourceUintFixedNestedDelete root i j) : Source.RStmt E [] false .body Γ Γ) ym.1).run (.nil,ym.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems G F (horizon+7) nps none
        (.stmt (.expr (sourceUintFixedNestedAssign root i j rhs))
          (.stmt (.expr (sourceUintFixedNestedDelete root i j)) .nil) : Source.RItems E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      SourceUintFixedRefsAt ym a mid r address ∧ SourceUintFixedRefsAt z a out r address ∧
      Source.MemOK E SH ym ∧ Source.MemOK E SH z ∧ ym.1=y.1 ∧ z.1=y.1 ∧
      z.2.heap.next=y.2.heap.next ∧ out.get r=hp.get r ∧
      (∀ {Q : RefTy} (t : HRef H Q),q.id≠t.id → out.get t=hp.get t) ∧
      (∀ b,b≠address q.id → z.2.heap.get b=y.2.heap.get b) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve | simp only [] | omega
  | obtain ⟨mid,ym,tw,ew,sw,rm,mm,lm,nm,pm,om,am,wm,em,lgm,fm⟩ :=
      hr.resolved_write G F (horizon+1) nps root i j rhs k l v q hroot hi hj hv hq separate hl SH memOK
    have middleIndex : mid.index r .dyn k=some q := by
      change (MObj.elems .dyn (mid.get r))[k.1.toNat]?=some q
      rw [pm];exact hq
    have middleSeparate : ∀ t∈MObj.elems .dyn (mid.get r),t.id≠q.id → address t.id≠address q.id := by
      rw [pm];exact separate
    obtain ⟨out,z,td,ed,sd,rz,mz,lz,nz,pz,oz,az,wz,ez,lgz,fz⟩ :=
      rm.resolved_delete G F horizon nps root i j k l q
        (by rw [lm];exact hroot) (by rw [lm];exact hi) (by rw [lm];exact hj)
        middleIndex middleSeparate hl SH mm
    exact ⟨mid,out,ym,z,tw,td,sw,sd,source_items_pair_run G F (horizon+1) nps _ _ y ym z sw sd,
      rm,rz,mm,mz,lm,lz.trans lm,nz.trans nm,pz.trans pm,
      fun t ht => (oz t ht).trans (om t ht),fun b hb => (az b hb).trans (am b hb),
      wz.trans wm,ez.trans em,lgz.trans lgm,fz.trans fm⟩


/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.resolved_delete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.resolved_delete
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.write_delete_items' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.write_delete_items
end Solidity.Backend.MemoryOps
