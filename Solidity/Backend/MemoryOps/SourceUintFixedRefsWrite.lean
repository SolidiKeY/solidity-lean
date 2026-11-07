import Solidity.Backend.MemoryOps.SourceUintFixedRefsMemory

/-! Actual mutation of an already represented fixed child. Selected-footprint
address separation is sufficient for this observer, not a global injection or
Source-profile restriction; no necessity for no-op writes is asserted. -/
namespace Solidity.Backend.MemoryOps

theorem SourceUintFixedRefsAt.same_heap {E : Source.Env} {Γ Δ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {z : Source.EMState E Δ} {a : Nat} {hp : Heap H}
    {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (same : z.2.heap=y.2.heap) :
    SourceUintFixedRefsAt z a hp r address := by
  refine ⟨?_,?_⟩
  · rw [same];exact hr.parent
  · intro q member
    unfold SourceUintFixedAt
    rw [same]
    exact hr.children q member

theorem SourceUintFixedRefsAt.write_child {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (q : HRef H (.fixed (.prim .uint) n))
    (member : q∈MObj.elems .dyn (hp.get r))
    (separate : ∀ t∈MObj.elems .dyn (hp.get r),t.id≠q.id → address t.id≠address q.id)
    (F : Source.Fr) (fuel : Nat) (i v : PrimTy.uint.Denote) (hi : i.1.toNat<n)
    (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index q .fixed i) v=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem (address q.id) i.1.toNat) (sourceUint v)).run y=(.ok (),z) ∧
      SourceUintFixedRefsAt z a out r address ∧ Source.MemOK E SH z ∧
      z.1=y.1 ∧ z.2.heap.next=y.2.heap.next ∧ out.get r=hp.get r ∧
      (∀ {Q : RefTy} (t : HRef H Q),q.id≠t.id → out.get t=hp.get t) ∧
      (∀ b,b≠address q.id → z.2.heap.get b=y.2.heap.get b) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve | simp only [] | omega
  | have child := hr.children q member
    obtain ⟨ty,known⟩ := source_uint_fixed_write y (address q.id) (hp.get q) child i.1.toNat hi v
    let out := hp.set q (MObj.setElem .fixed (hp.get q) i.1.toNat v)
    let z : Source.EMState E Γ :=
      (y.1,{y.2 with heap := y.2.heap.write (address q.id) (sourceUintFixedObject (MObj.setElem .fixed (hp.get q) i.1.toNat v)) ty})
    have typed : hp.writeAddr (.index q .fixed i) v=some out := by
      have length : (MObj.elems .fixed (hp.get q)).length=n := by rw [MObj.elems_fixed];exact (hp.get q).2
      simp only [Heap.writeAddr,Heap.setIndex,length,hi,↓reduceIte]
      rfl
    have run : (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem (address q.id) i.1.toNat) (sourceUint v)).run y=(.ok (),z) := known
    have different : q.id≠r.id := by intro eq;cases (HRef.heq_of_id q r eq).1
    have parent : out.get r=hp.get r := Heap.get_set_ne hp q r different _
    have preserved := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) F fuel
      (.mem (τ := .int .u256) (address q.id) i.1.toNat) (sourceUint v) y ⟨memOK,trivial⟩
    rw [run] at preserved
    have reached : SourceUintFixedRefsAt z a out r address := by
      refine ⟨?_,?_⟩
      · rw [parent]
        exact (Source.Heap.write_other y.2.heap (hr.parent_ne_child q member) _ ty).trans hr.parent
      · intro t hit
        rw [parent] at hit
        by_cases same : t.id=q.id
        · have eq : t=q := eq_of_heq (HRef.heq_of_id t q same).2
          subst t
          unfold SourceUintFixedAt
          change (y.2.heap.write _ _ ty).get (address q.id)=some _
          rw [Source.Heap.write_get,Heap.get_set_same]
        · unfold SourceUintFixedAt
          change (y.2.heap.write _ _ ty).get (address t.id)=some _
          rw [Source.Heap.write_other y.2.heap (separate t hit same),Heap.get_set_ne hp q t (Ne.symm same)]
          exact hr.children t hit
    obtain ⟨locals,objects,addresses,world,events,logs,fnLocals⟩ := child.write_frames F fuel i v hi typed run
    exact ⟨out,z,typed,run,reached,preserved,locals,rfl,parent,objects,addresses,world,events,logs,fnLocals⟩

def sourceUintFixedNestedLoc {E : Source.Env} {Γ : Source.RCtx} {n : Nat}
    (root : Source.Idx Γ (SourceUintFixedRefsTy n)) (i j : Source.Idx Γ (.int .u256)) : Source.RLVal E Γ (.int .u256) :=
  .indexArray (.indexArray (.local root) (.local i) rfl) (by decide) (.local j) rfl

def sourceUintFixedNestedAssign {E : Source.Env} {Γ : Source.RCtx} {n : Nat}
    (root : Source.Idx Γ (SourceUintFixedRefsTy n)) (i j rhs : Source.Idx Γ (.int .u256)) : Source.RExpr E Γ (.int .u256) :=
  .assign (sourceUintFixedNestedLoc root i j) (.local rhs)

theorem SourceUintFixedRefsAt.eval_nested_loc {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (root : Source.Idx Γ (SourceUintFixedRefsTy n)) (i j : Source.Idx Γ (.int .u256))
    (k l : PrimTy.uint.Denote) (q : HRef H (.fixed (.prim .uint) n))
    (hroot : y.1.get root=.memRef rfl a) (hi : y.1.get i=sourceUint k) (hj : y.1.get j=sourceUint l)
    (hq : hp.index r .dyn k=some q) (hl : l.1.toNat<n) :
    (Source.evalLoc G F (horizon+3) (sourceUintFixedNestedLoc root i j)).run y=
      (.ok (.mem (address q.id) l.1.toNat),y) := by
  rw [sourceUintFixedNestedLoc,Source.evalLoc,Source.Hoare.run_bind,hr.eval_parent_read G F horizon root i k q hroot hi hq]
  change ((Source.evalE G F (horizon+2) (.local j)) >>= fun v => Source.indexNat v >>= fun index =>
    Source.indexLoc F (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory (.int .u256) (some n))) index).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F (horizon+1) y j _ hj]
  change (Source.indexLoc F (.memRef rfl (address q.id) : Source.Val E.layout (.array .memory (.int .u256) (some n))) l.1.toNat).run y=_
  rw [Source.indexLoc,Source.lengthOf]
  simp only [Source.Hoare.run_bind]
  change (if l.1.toNat<n then pure (Source.Loc.mem (address q.id) l.1.toNat : Source.Loc E.layout Γ (.int .u256)) else Source.EM.lift (Source.panic .index)).run y=_
  rw [if_pos hl]
  rfl

theorem SourceUintFixedRefsAt.resolved_write {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {n : Nat}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H (UintFixedRefsRef n)} {address : Nat → Nat}
    (hr : SourceUintFixedRefsAt y a hp r address) (G : Source.Glob E) (F : Source.Fr) (horizon nps : Nat)
    (root : Source.Idx Γ (SourceUintFixedRefsTy n)) (i j rhs : Source.Idx Γ (.int .u256))
    (k l v : PrimTy.uint.Denote) (q : HRef H (.fixed (.prim .uint) n))
    (hroot : y.1.get root=.memRef rfl a) (hi : y.1.get i=sourceUint k) (hj : y.1.get j=sourceUint l)
    (hv : y.1.get rhs=sourceUint v) (hq : hp.index r .dyn k=some q)
    (separate : ∀ t∈MObj.elems .dyn (hp.get r),t.id≠q.id → address t.id≠address q.id)
    (hl : l.1.toNat<n) (SH : Source.HeapTy) (memOK : Source.MemOK E SH y) :
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index q .fixed l) v=some out ∧
      (Source.evalE G F (horizon+4) (sourceUintFixedNestedAssign root i j rhs)).run y=(.ok (.val (sourceUint v)),z) ∧
      (Source.execS G F (horizon+5) nps none
        (.expr (sourceUintFixedNestedAssign root i j rhs) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      SourceUintFixedRefsAt z a out r address ∧ Source.MemOK E SH z ∧ z.1=y.1 ∧ z.2.heap.next=y.2.heap.next ∧ out.get r=hp.get r ∧
      (∀ {Q : RefTy} (t : HRef H Q),q.id≠t.id → out.get t=hp.get t) ∧
      (∀ b,b≠address q.id → z.2.heap.get b=y.2.heap.get b) ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  first
  | solve | simp only [] | omega
  | have member : q∈MObj.elems .dyn (hp.get r) := List.mem_of_getElem? hq
    obtain ⟨out,z,typed,write,reached,preserved,locals,next,parent,objects,addresses,world,events,logs,fnLocals⟩ :=
      hr.write_child q member separate F (horizon+3) l v hl SH memOK
    have expr : (Source.evalE G F (horizon+4) (sourceUintFixedNestedAssign root i j rhs)).run y=(.ok (.val (sourceUint v)),z) := by
      rw [sourceUintFixedNestedAssign,Source.evalE,Source.Hoare.run_bind,source_local_value_run G F (horizon+2) y rhs (sourceUint v) hv]
      change ((Source.evalLoc G F (horizon+3) (sourceUintFixedNestedLoc root i j)) >>= fun loc =>
        Source.writeLoc F (horizon+3) loc (sourceUint v) >>= fun _ => pure (Source.RVal.val (sourceUint v))).run y=_
      rw [Source.Hoare.run_bind,hr.eval_nested_loc G F horizon root i j k l q hroot hi hj hq hl]
      change (Source.writeLoc F (horizon+3) (.mem (address q.id) l.1.toNat) (sourceUint v) >>= fun _ => pure (Source.RVal.val (sourceUint v))).run y=_
      rw [Source.Hoare.run_bind,write]
      rfl
    exact ⟨out,z,typed,expr,source_expr_statement_run G F (horizon+4) nps _ y z (.val (sourceUint v)) expr,
      reached,preserved,locals,next,parent,objects,addresses,world,events,logs,fnLocals⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.same_heap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.same_heap
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.write_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.write_child
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.eval_nested_loc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.eval_nested_loc
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsAt.resolved_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceUintFixedRefsAt.resolved_write
end Solidity.Backend.MemoryOps
