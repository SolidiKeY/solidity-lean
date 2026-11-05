import Solidity.Backend.MemoryOps.SourceCalldataTransfer
import Solidity.Backend.MemoryOps.SourceAlias
import Solidity.Backend.MemoryOps.SourceSequence

/-! Actual RHS-first Source calldata conversion followed by local reference
binding and reached observations. Existing syntax/evaluator/alloc/checked copy
are consumed. No emitted raw-copy or allocator code certificate is assumed. -/
namespace Solidity.Backend.MemoryOps

/-- Existing resolved local assignment whose RHS really allocates the copy. -/
def sourceBoolCalldataBind {E : Source.Env} {Γ : Source.RCtx}
    (dst : Source.Idx Γ SourceBoolArrayTy)
    (src : Source.Idx Γ (.array .calldata .bool none)) : Source.RExpr E Γ SourceBoolArrayTy :=
  .assign (.local dst) (sourceBoolCalldataCopy src)

/-- Only the selected local changes; no address injectivity is involved. -/
theorem source_locals_get_set_other {D : Source.Layout} {Γ : Source.RCtx} {τ υ : Source.STy}
    (l : Source.Locals D Γ) (dst : Source.Idx Γ τ) (other : Source.Idx Γ υ)
    (v : Source.Val D τ) (ne : dst.toNat≠other.toNat) : (l.set dst v).get other=l.get other := by
  induction l generalizing τ υ with
  | nil => cases dst
  | cons head tail ih =>
    cases dst with
    | here =>
      cases other with
      | here => exact (ne rfl).elim
      | there other => rfl
    | there dst =>
      cases other with
      | here => rfl
      | there other => exact ih dst other v (fun eq => ne (congrArg (·+1) eq))

/-- The actual assignment retains the RHS allocation; decoder failure occurs
before local replacement, not after an invented successful suffix. -/
theorem source_cd_bool_bind_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (y : Source.EMState E Γ)
    (dst : Source.Idx Γ SourceBoolArrayTy) (src : Source.Idx Γ (.array .calldata .bool none))
    (off len : Nat) (hs : y.1.get src=.cdRef rfl off len) :
    (Source.evalE G F (fuel+3) (sourceBoolCalldataBind dst src)).run y=
      match sourceCalldataBoolValues E F off len with
      | .error e => (.error e,y)
      | .ok vs =>
        let z : Source.EMState E Γ :=
          (y.1.set dst (.memRef rfl y.2.heap.next),
            {y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory (sourceBoolValuePayload vs)⟩).1})
        (.ok (.val (.memRef rfl y.2.heap.next)),z) := by
  unfold sourceBoolCalldataBind
  rw [Source.evalE,Source.Hoare.run_bind,source_cd_bool_eval G F fuel y src off len hs,source_cd_bool_run]
  cases decoded : sourceCalldataBoolValues E F off len with
  | error e => rfl
  | ok vs =>
    dsimp only
    rw [Source.Hoare.run_bind]
    rfl

/-- Replacing a local with a represented array pointer preserves the published
MemOK invariant; its RefOK fact follows from the actual object observation. -/
theorem SourceBoolMemoryAt.bind_memOK {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (dst : Source.Idx Γ SourceBoolArrayTy) (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    Source.MemOK E SH (y.1.set dst (.memRef rfl address),y.2) := by
  have hv : Source.Val.RefOK E y.2.heap.ty
      (.memRef rfl address : Source.Val E.layout SourceBoolArrayTy) := by
    refine ⟨SourceBoolArrayTy,?_,rfl⟩
    change (y.2.heap.get address).map Sigma.fst=some SourceBoolArrayTy
    rw [hr]
    rfl
  exact ⟨⟨hm.1.1,Source.LocalsOK.set y.1 dst hm.1.2 hv⟩,hm.2⟩

/-- Primitive Boolean indexing is derived from the actual initial object and
locals. The read value is an intrinsic observation, not a conversion oracle. -/
theorem SourceBoolMemoryAt.eval_local_read {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ SourceBoolArrayTy) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (value : Bool) (hroot : y.1.get root=.memRef rfl address)
    (hindex : y.1.get index=sourceUint k) (read : hp.index r a k=some value) :
    (Source.evalE G F (fuel+2) (.indexArray (.local root) (.local index) rfl)).run y=
      (.ok (.val (.bool value)),y) := by
  have bound : k.1.toNat<hp.len r a := (List.getElem?_eq_some_iff.mp read).1
  rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F fuel y root _ hroot]
  change ((Source.evalE G F (fuel+1) (.local index)) >>= fun v => Source.indexNat v >>= fun n =>
    Source.indexLoc F (.memRef rfl address : Source.Val E.layout SourceBoolArrayTy) n >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F fuel y index _ hindex]
  change (Source.indexLoc F (.memRef rfl address : Source.Val E.layout SourceBoolArrayTy) k.1.toNat >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,hr.indexLoc_run F _ bound]
  change (Source.readLoc F (τ := .bool) (.mem address k.1.toNat) >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,(hr.read_iff F k value).mpr read]
  rfl

/-- The computed fresh pointer is bound only AFTER actual Source conversion.
All reached observers and MemOK follow from the initial named observer and
published allocation/copy laws. No emitted copy program is claimed. -/
theorem SourceBoolStructAt.bind_cd_bool_copy {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {addr : Nat} {hp : Heap H} {r : HRef H (.struct s)}
    {address : Nat → Nat} {layout : SourceBoolStructLayout E dn s tag child}
    (hr : SourceBoolStructAt y addr hp r address layout)
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat)
    (dst : Source.Idx Γ SourceBoolArrayTy) (src : Source.Idx Γ (.array .calldata .bool none))
    (off len : Nat) (hsrc : y.1.get src=.cdRef rfl off len) (cap : len<2^256)
    (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    match sourceCalldataBoolValues E F off len with
    | .error e =>
      (Source.evalE G F (fuel+3) (sourceBoolCalldataBind dst src)).run y=(.error e,y) ∧
      (Source.execS G F (fuel+4) nps none
        (.expr (sourceBoolCalldataBind dst src) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.error e,(.nil,y.2))
    | .ok vs => ∃ valid : (sourceBoolValuePayload vs).length<2^256,
      let o : MObj H (.array (.prim .bool)) := ⟨sourceBoolValuePayload vs,valid⟩
      let pair := hp.alloc o
      let ext := List.prefix_append H [RefTy.array (.prim .bool)]
      let address' := allocatedSourceAddress address H.length y.2.heap.next
      let z : Source.EMState E Γ :=
        (y.1.set dst (.memRef rfl y.2.heap.next),
          {y.2 with heap := (y.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory (sourceBoolValuePayload vs)⟩).1})
      (Source.evalE G F (fuel+3) (sourceBoolCalldataBind dst src)).run y=(.ok (.val (.memRef rfl y.2.heap.next)),z) ∧
      (Source.execS G F (fuel+4) nps none
        (.expr (sourceBoolCalldataBind dst src) : Source.RStmt E [] false .body Γ Γ) y.1).run (.nil,y.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      checkedSourceFreshBools (E := E) F off len hp cap=.ok (some pair.1) ∧
      Heap.Keeps ext hp pair.1 ∧ SourceBoolStructAt z addr pair.1 (r.wk ext) address' layout ∧
      SourceBoolMemoryAt z y.2.heap.next pair.1 pair.2 .dyn ∧ Source.MemOK E SH z ∧
      z.1.get dst=.memRef rfl y.2.heap.next ∧
      (∀ τ (i : Source.Idx Γ τ),dst.toNat≠i.toNat → z.1.get i=y.1.get i) ∧
      pair.2.id=H.length ∧ address' pair.2.id=y.2.heap.next ∧
      z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals := by
  have run := source_cd_bool_bind_run G F fuel y dst src off len hsrc
  have paired := hr.checked_cd_bool_copy F off len cap SH hm
  cases decoded : sourceCalldataBoolValues E F off len with
  | error err =>
    rw [decoded] at run
    exact ⟨run,source_expr_statement_error G F (fuel+3) nps _ y y err run⟩
  | ok vs =>
    rw [decoded] at run paired
    obtain ⟨valid,adapter,_,keep,old,new,mok,fresh,fp,_⟩ := paired
    rw [fp] at new
    have boundOK := new.bind_memOK dst SH mok
    refine ⟨valid,run,source_expr_statement_run G F (fuel+3) nps _ y _ _ run,
      adapter,keep,⟨old.parent,old.leaf⟩,new,boundOK,source_locals_get_set _ _ _,?_,fresh,fp,rfl,rfl,rfl,rfl⟩
    intro τ i ne
    exact source_locals_get_set_other y.1 dst i _ ne

/-- Real empty/end rejection through the reached local, with Source's own
panic bytes and unchanged reached state. This is not target rollback. -/
theorem SourceBoolMemoryAt.eval_local_bounds {E : Source.Env} {Γ : Source.RCtx} {H : HTy} {R : RefTy}
    {y : Source.EMState E Γ} {address : Nat} {hp : Heap H} {r : HRef H R}
    {a : ArrTy R (.prim .bool)} (hr : SourceBoolMemoryAt y address hp r a)
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (root : Source.Idx Γ SourceBoolArrayTy) (index : Source.Idx Γ (.int .u256))
    (k : PrimTy.uint.Denote) (hroot : y.1.get root=.memRef rfl address)
    (hindex : y.1.get index=sourceUint k) (bound : hp.len r a≤k.1.toNat) :
    (Source.evalE G F (fuel+2) (.indexArray (.local root) (.local index) rfl)).run y=
      (.error (.revert (Source.panicData .index)),y) := by
  rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run G F fuel y root _ hroot]
  change ((Source.evalE G F (fuel+1) (.local index)) >>= fun v => Source.indexNat v >>= fun n =>
    Source.indexLoc F (.memRef rfl address : Source.Val E.layout SourceBoolArrayTy) n >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,source_local_value_run G F fuel y index _ hindex]
  change (Source.indexLoc F (.memRef rfl address : Source.Val E.layout SourceBoolArrayTy) k.1.toNat >>= fun loc =>
    Source.readLoc F loc >>= fun v => pure (Source.RVal.val v)).run y=_
  rw [Source.Hoare.run_bind,hr.indexLoc_bounds F _ bound]

/-- Conversion cannot reach its allocation at these actual evaluator horizons. -/
theorem source_cd_bool_bind_low {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (y : Source.EMState E Γ)
    (dst : Source.Idx Γ SourceBoolArrayTy) (src : Source.Idx Γ (.array .calldata .bool none)) :
    ∀ fuel,fuel≤2 → (Source.evalE G F fuel (sourceBoolCalldataBind dst src)).run y=(.error .timeout,y) := by
  intro fuel low
  match fuel with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | fuel+3 => omega

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.eval_local_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolMemoryAt.eval_local_bounds
/-- info: 'Solidity.Backend.MemoryOps.source_cd_bool_bind_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_cd_bool_bind_low
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.eval_local_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolMemoryAt.eval_local_read
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolStructAt.bind_cd_bool_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolStructAt.bind_cd_bool_copy
/-- info: 'Solidity.Backend.MemoryOps.source_locals_get_set_other' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms source_locals_get_set_other
/-- info: 'Solidity.Backend.MemoryOps.source_cd_bool_bind_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_cd_bool_bind_run
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolMemoryAt.bind_memOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceBoolMemoryAt.bind_memOK
end Solidity.Backend.MemoryOps
