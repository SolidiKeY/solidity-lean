import Solidity.Calculus.SoundKit

/-!
# Taclets that produce an update

`Taclet.sound_update`: a rule whose premise is an update `{U}` has the
statement's effect — `U` applied in `σ` ends as running the statement from
`σ` does, or both halt.  An update is parallel and reads every right-hand
side in the state it is applied in, the statement runs left to right; the
lemmas below show the two reach the same writes through the same reads.
-/

namespace Solidity

open Semantics SemanticsProperties

variable {C : Contract}

/-! ### Term evaluation, one constructor at a time (keeps `envVal`/`envRef` atomic) -/
section
variable (σ : State)
theorem Term.eval_lit' (v : Value) : (Term.lit v : Term C).eval σ = pure v := rfl
theorem Term.eval_binop' (op : BinOp) (p : PrimTy) (a b : Term C) :
    (Term.binop op p a b).eval σ = (do evalBinop op p (← a.eval σ) (b.eval σ)) := rfl
theorem Term.eval_find' (s : STerm C) (p : PTerm C) :
    (Term.find s p).eval σ = (do
      let τ ← s.eval σ
      let (r, segs) ← p.eval σ
      (← τ.findStorage r segs).asValue) := rfl
theorem Term.eval_len' (s : STerm C) (p : PTerm C) :
    (Term.len s p).eval σ = (do
      let τ ← s.eval σ
      let (r, segs) ← p.eval σ
      arrayLen τ r segs) := rfl
theorem Term.eval_read' (m : MTerm C) (a : MAddr C) :
    (Term.read m a).eval σ = (do
      let τ ← m.eval σ
      (← readAddr τ (← a.eval σ)).asValue) := rfl
theorem ITerm.eval_read' (m : MTerm C) (a : MAddr C) :
    (ITerm.read m a).eval σ = (do
      let τ ← m.eval σ
      (← readAddr τ (← a.eval σ)).asRef) := rfl
theorem ITerm.eval_alloc' (m : MTerm C) (R : RefTy) :
    (ITerm.alloc m R).eval σ = (do
      let τ ← m.eval σ
      return (← allocDefault τ R).2) := rfl
theorem ITerm.eval_copy' (m : MTerm C) (v : SValT C) :
    (ITerm.copy m v).eval σ = (do
      let sv ← v.eval σ
      let τ ← m.eval σ
      (← copyStToM τ sv).2.asRef) := rfl
theorem MAddr.eval_field' (i : ITerm C) (f : Name) :
    (MAddr.field i f).eval σ = (do pure (.memoryField (← i.eval σ) f)) := rfl
theorem MAddr.eval_at' (i : ITerm C) (k : Term C) :
    (MAddr.at i k).eval σ = (do
      let id ← i.eval σ
      pure (.memoryIndex id (← (← k.eval σ).asInt))) := rfl
end

theorem memWriteField_eq' (σ : State) (id : Nat) (f : Name) (mv : MVal) :
    memWriteField σ id f mv = writeAddr σ mv (.memoryField id f) := rfl
theorem memWriteIndex_eq' (σ : State) (id : Nat) (i : Int) (mv : MVal) :
    memWriteIndex σ id i mv = writeAddr σ mv (.memoryIndex id i) := rfl

/-- `upd_unfold_with`, one term constructor at a time (so `envVal`/`envRef`
stay atomic), with each write as the storage or heap it leaves. -/
macro "upd_unfold'" : tactic => `(tactic| upd_unfold_with [Term.eval_lit', Term.eval_binop',
    Term.eval_find', Term.eval_len', Term.eval_read', ITerm.eval_read', ITerm.eval_alloc',
    ITerm.eval_copy', MAddr.eval_field', MAddr.eval_at', State.writeRes_toSVal,
    State.saveStorage_eq, State.writeStorage_eq, writeAddr_eq, MPath.mval_loc, memWriteField_eq',
    memWriteIndex_eq'])

theorem upd_localOpAssign {p : PrimTy} {op : BinOp} (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (v : Var) (se : Simple C p) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.val v (Term.binop op p (Term.pv v) se.lower)] σ)
      (Stmt.run σ (Stmt.opAssign op hop hp (OpLoc.local v) (Val.simple se))) := by
  upd_unfold'
  simp only [evalBinop_compound hop]
  res_split

theorem upd_localIncrement {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (v : Var)
    (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.val v (Term.binop op.binOp p (Term.pv v) (Term.lit (.int 1)))] σ)
      (Stmt.run σ (Stmt.incDec op hp (OpLoc.local v) : Stmt C)) := by
  upd_unfold'
  res_split

theorem upd_memoryFieldOpAssign {p : PrimTy} {op : BinOp} (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) (mv : Var) {fld x : Name} (hfld : C.fieldType x fld = some (Ty.prim p))
    (se : Simple C p) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.memory
          (MTerm.memory.write (MAddr.field (ITerm.pv mv) fld)
            (MValT.val (Term.binop op p (Term.read MTerm.memory (MAddr.field (ITerm.pv mv) fld)) se.lower)))] σ)
      (Stmt.run σ (Stmt.opAssign op hop hp (OpLoc.mfield (MPath.var mv) fld hfld) (Val.simple se))) := by
  upd_unfold'
  simp only [evalBinop_compound hop]
  res_split

theorem upd_memoryIndexArrayOpAssign {p : PrimTy} {op : BinOp} (hop : op.hasCompoundAssign = true)
    (hp : p.isNumeric = true) {R : RefTy} (a : ArrTy R (.prim p)) (mv : Var) (ie : Simple C PrimTy.uint) (se : Simple C p) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.memory
          (MTerm.memory.write (MAddr.at (ITerm.pv mv) ie.lower)
            (MValT.val (Term.binop op p (Term.read MTerm.memory (MAddr.at (ITerm.pv mv) ie.lower)) se.lower)))] σ)
      (Stmt.run σ (Stmt.opAssign op hop hp (OpLoc.mindex a (MPath.var mv) ie) (Val.simple se))) := by
  upd_unfold'
  simp only [evalBinop_compound hop]
  res_split

theorem upd_memoryFieldIncrement {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true) (mv : Var)
    {fld x : Name} (hfld : C.fieldType x fld = some (Ty.prim p)) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.memory
          (MTerm.memory.write (MAddr.field (ITerm.pv mv) fld)
            (MValT.val
              (Term.binop op.binOp p (Term.read MTerm.memory (MAddr.field (ITerm.pv mv) fld))
                (Term.lit (.int 1)))))] σ)
      (Stmt.run σ (Stmt.incDec op hp (OpLoc.mfield (MPath.var mv) fld hfld))) := by
  upd_unfold'
  res_split

theorem upd_memoryIndexArrayIncrement {p : PrimTy} (op : IncDec) (hp : p.isNumeric = true)
    {R : RefTy} (a : ArrTy R (.prim p)) (mv : Var)
    (ie : Simple C PrimTy.uint) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.memory
          (MTerm.memory.write (MAddr.at (ITerm.pv mv) ie.lower)
            (MValT.val
              (Term.binop op.binOp p (Term.read MTerm.memory (MAddr.at (ITerm.pv mv) ie.lower))
                (Term.lit (.int 1)))))] σ)
      (Stmt.run σ (Stmt.incDec op hp (OpLoc.mindex a (MPath.var mv) ie))) := by
  upd_unfold'
  res_split

theorem upd_localAssignIncrement {p : PrimTy} (vp : Var) (op : IncDec) (hp : p.isNumeric = true)
    (v : Var) (hs : (OpLoc.local v : OpLoc C p).recvSimple = true) (σ : State) :
    SameOk [] (Upd.apply (C := C)
      [UpdElem.val v (Term.binop op.binOp p (Term.pv v) (Term.lit (.int 1))),
        UpdElem.val vp (Term.bumped op p (Term.pv v))] σ)
      (Stmt.run σ (Stmt.assignIncDec vp op hp (OpLoc.local v) hs)) := by
  rw [Term.bumped]; split <;> (upd_unfold'; res_split)

theorem upd_storageRootIncrementAssignment {p : PrimTy} (v : Var) (op : IncDec)
    (hp : p.isNumeric = true) (gsp : Name) (hgsp : C.rootType gsp = some (Ty.prim p))
    (hs : (OpLoc.root gsp hgsp).recvSimple = true) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.storage
          (STerm.storage.save (PTerm.root gsp)
            (SValT.val
              (Term.binop op.binOp p (Term.find STerm.storage (PTerm.root gsp)) (Term.lit (.int 1))))),
        UpdElem.val v (Term.bumped op p (Term.find STerm.storage (PTerm.root gsp)))] σ)
      (Stmt.run σ (Stmt.assignIncDec v op hp (OpLoc.root gsp hgsp) hs)) := by
  rw [Term.bumped]; split <;> (upd_unfold'; res_split)

theorem upd_storageFieldIncrementAssignment {p : PrimTy} (v : Var) (op : IncDec)
    (hp : p.isNumeric = true) {x : Name} (sp : SPath C (Ty.struct x)) {fld : Name}
    (hfld : C.fieldType x fld = some (Ty.prim p)) (hs : (OpLoc.field sp fld hfld).recvSimple = true)
    (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.storage
          (STerm.storage.save (sp.lower.field fld)
            (SValT.val
              (Term.binop op.binOp p (Term.find STerm.storage (sp.lower.field fld))
                (Term.lit (.int 1))))),
        UpdElem.val v (Term.bumped op p (Term.find STerm.storage (sp.lower.field fld)))] σ)
      (Stmt.run σ (Stmt.assignIncDec v op hp (OpLoc.field sp fld hfld) hs)) := by
  rw [Term.bumped]; split <;> (upd_unfold'; res_split)

theorem upd_storageIndexIncrementAssignment {p : PrimTy} (v : Var) (op : IncDec)
    (hp : p.isNumeric = true) {x : RefTy} {x_1 : PrimTy} (it : IndexTy x x_1 (Ty.prim p))
    (sp : SPath C (Ty.ref x)) (ie : Simple C x_1) (hs : (OpLoc.index it sp ie).recvSimple = true)
    (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.storage
          (STerm.storage.save (sp.lower.at ie.lower)
            (SValT.val
              (Term.binop op.binOp p (Term.find STerm.storage (sp.lower.at ie.lower))
                (Term.lit (.int 1))))),
        UpdElem.val v (Term.bumped op p (Term.find STerm.storage (sp.lower.at ie.lower)))] σ)
      (Stmt.run σ (Stmt.assignIncDec v op hp (OpLoc.index it sp ie) hs)) := by
  rw [Term.bumped]; split <;> (upd_unfold'; res_split)

theorem upd_memoryFieldIncrementAssignment {p : PrimTy} (v : Var) (op : IncDec)
    (hp : p.isNumeric = true) (mv : Var) {fld x : Name} (hfld : C.fieldType x fld = some (Ty.prim p))
    (hs : (OpLoc.mfield (MPath.var mv) fld hfld).recvSimple = true) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.memory
          (MTerm.memory.write (MAddr.field (ITerm.pv mv) fld)
            (MValT.val
              (Term.binop op.binOp p (Term.read MTerm.memory (MAddr.field (ITerm.pv mv) fld))
                (Term.lit (.int 1))))),
        UpdElem.val v (Term.bumped op p (Term.read MTerm.memory (MAddr.field (ITerm.pv mv) fld)))] σ)
      (Stmt.run σ (Stmt.assignIncDec v op hp (OpLoc.mfield (MPath.var mv) fld hfld) hs)) := by
  rw [Term.bumped]; split <;> (upd_unfold'; res_split)

theorem upd_memoryIndexArrayIncrementAssignment {p : PrimTy} (v : Var) (op : IncDec)
    (hp : p.isNumeric = true) {R : RefTy} (a : ArrTy R (.prim p)) (mv : Var) (ie : Simple C PrimTy.uint)
    (hs : (OpLoc.mindex a (MPath.var mv) ie).recvSimple = true) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.memory
          (MTerm.memory.write (MAddr.at (ITerm.pv mv) ie.lower)
            (MValT.val
              (Term.binop op.binOp p (Term.read MTerm.memory (MAddr.at (ITerm.pv mv) ie.lower))
                (Term.lit (.int 1))))),
        UpdElem.val v (Term.bumped op p (Term.read MTerm.memory (MAddr.at (ITerm.pv mv) ie.lower)))] σ)
      (Stmt.run σ (Stmt.assignIncDec v op hp (OpLoc.mindex a (MPath.var mv) ie) hs)) := by
  rw [Term.bumped]; split <;> (upd_unfold'; res_split)

/-! ### Memory reads, aliases and writes -/


macro "mem_unfold" : tactic => `(tactic| (
  try simp only [MPath.lower, MLoc.lower]
  upd_unfold'))

theorem upd_memoryFieldRead (v mv : Var) {fld x : Name} {q : PrimTy}
    (hfld : C.fieldType x fld = some (Ty.prim q)) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.val v (Term.read MTerm.memory (MAddr.field (ITerm.pv mv) fld))] σ)
      (Stmt.run σ (Stmt.assignLocal v (Val.readMem (MLoc.field (MPath.var mv) fld hfld)))) := by
  mem_unfold; res_split

theorem upd_memoryIndexReadArrayValue {q : PrimTy} {R : RefTy} (a : ArrTy R (Ty.prim q)) (v mv : Var)
    (ie : Simple C PrimTy.uint) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.val v (Term.read MTerm.memory (MAddr.at (ITerm.pv mv) ie.lower))] σ)
      (Stmt.run σ (Stmt.assignLocal v (Val.readMem (MLoc.index a (MPath.var mv) (Val.simple ie))))) := by
  mem_unfold; res_split

theorem upd_memoryRootRebind {R : RefTy} (mv₁ mv₂ : Var) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.mref mv₁ (ITerm.pv mv₂)] σ)
      (Stmt.run σ (Stmt.rebindMem mv₁ (MRhs.alias (MPath.var (C := C) (R := R) mv₂)))) := by
  mem_unfold; res_split

theorem upd_memoryFieldReadAliasRoot (mv₁ mv₂ : Var) {fr x : Name} {R : RefTy}
    (hfr : C.fieldType x fr = some (Ty.ref R)) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.mref mv₁ (ITerm.read MTerm.memory (MAddr.field (ITerm.pv mv₂) fr))] σ)
      (Stmt.run σ (Stmt.rebindMem mv₁ (MRhs.alias (MPath.loc (MLoc.field (MPath.var mv₂) fr hfr))))) := by
  mem_unfold; res_split

theorem upd_memoryIndexReadArrayMemory {R R' : RefTy} (a : ArrTy R' (Ty.ref R)) (mv₁ mv₂ : Var)
    (ie : Simple C PrimTy.uint) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.mref mv₁ (ITerm.read MTerm.memory (MAddr.at (ITerm.pv mv₂) ie.lower))] σ)
      (Stmt.run σ (Stmt.rebindMem mv₁
        (MRhs.alias (MPath.loc (MLoc.index a (MPath.var mv₂) (Val.simple ie)))))) := by
  mem_unfold; res_split

theorem upd_memoryFieldWrite (mv : Var) {fld x : Name} {q : PrimTy}
    (hfld : C.fieldType x fld = some (Ty.prim q)) (se : Simple C q) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.memory (MTerm.memory.write (MAddr.field (ITerm.pv mv) fld) (MValT.val se.lower))] σ)
      (Stmt.run σ (Stmt.assignMem (MLoc.field (MPath.var mv) fld hfld) (MSrc.val (Val.simple se)))) := by
  mem_unfold; res_split

theorem upd_memoryIndexWriteArray {q : PrimTy} {R : RefTy} (a : ArrTy R (Ty.prim q)) (mv : Var)
    (ie : Simple C PrimTy.uint) (se : Simple C q) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.memory (MTerm.memory.write (MAddr.at (ITerm.pv mv) ie.lower) (MValT.val se.lower))] σ)
      (Stmt.run σ (Stmt.assignMem (MLoc.index a (MPath.var mv) (Val.simple ie)) (MSrc.val (Val.simple se)))) := by
  mem_unfold; res_split

/-- `memoryFieldWriteCopy` from a memory local; a source that is a location is split by cases in `Taclet.sound_update`. -/
theorem upd_memoryFieldWriteCopy_var (mv : Var) {fld x : Name} {R : RefTy}
    (hfld : C.fieldType x fld = some (Ty.ref R)) (y : Var) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.memory (MTerm.memory.write (MAddr.field (ITerm.pv mv) fld)
        (MValT.ref (MPath.var (C := C) (R := R) y).lower))] σ)
      (Stmt.run σ (Stmt.assignMem (MLoc.field (MPath.var mv) fld hfld) (MSrc.ref (MPath.var y)))) := by
  mem_unfold; res_split

theorem upd_memoryIndexWriteCopy_var {R R' : RefTy} (a : ArrTy R' (Ty.ref R)) (mv : Var)
    (ie : Simple C PrimTy.uint) (y : Var) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.memory (MTerm.memory.write (MAddr.at (ITerm.pv mv) ie.lower)
        (MValT.ref (MPath.var (C := C) (R := R) y).lower))] σ)
      (Stmt.run σ (Stmt.assignMem (MLoc.index a (MPath.var mv) (Val.simple ie)) (MSrc.ref (MPath.var y)))) := by
  mem_unfold; res_split

/-! ### Copies and allocations: a new heap and counter, the rest kept -/

theorem res_frame_eq {α : Type} {σ : State} {x : Res (State × α)} (hx : FramePreserving σ x) :
    x = ((x.map fun p => (p.1.heap, p.1.nextId, p.2)) >>= fun q =>
      pure ({ σ with heap := q.1, nextId := q.2.1 }, q.2.2)) := by
  cases h : x with
  | error _ => rfl
  | ok p =>
    obtain ⟨τ, a⟩ := p
    obtain ⟨h1, h2, h3, h4, h5⟩ := hx τ a h
    cases τ; cases σ
    simp_all [Except.map, bind, Except.bind, pure, Except.pure]

/-- What a copy into memory leaves: the heap, the counter, the value. -/
def copyHN (σ : State) (sv : SVal) : Res (List (Nat × MObj) × Nat × MVal) :=
  (copyStToM σ sv).map fun p => (p.1.heap, p.1.nextId, p.2)

theorem copyStToM_eq (σ : State) (sv : SVal) :
    copyStToM σ sv = (copyHN σ sv >>= fun q => pure ({ σ with heap := q.1, nextId := q.2.1 }, q.2.2)) :=
  res_frame_eq (SemanticsProperties.copyStToM_frame σ sv)

theorem allocDefault_frame (σ : State) (R : RefTy) : FramePreserving σ (allocDefault σ R) := by
  intro t a h
  unfold allocDefault at h
  have hf := copyStToM_frame σ (defaultForRef R)
  split at h
  · rename_i s id heq
    cases h
    exact hf _ _ heq
  · cases h
  · cases h

/-- What a default allocation leaves: the heap, the counter, the identity. -/
def allocHN (σ : State) (R : RefTy) : Res (List (Nat × MObj) × Nat × Nat) :=
  (allocDefault σ R).map fun p => (p.1.heap, p.1.nextId, p.2)

@[no_panic_simp] theorem allocHN_noPanic (σ : State) (R : RefTy) : NoPanic (allocHN σ R) := by
  simp only [allocHN]
  cases h : allocDefault σ R with
  | error e =>
    exact fun hp => NoPanic.ne_of_eq (allocDefault_noPanic σ R) h (Except.error.inj hp)
  | ok _ => simp only [Except.map, ne_eq, reduceCtorEq, not_false_eq_true]

theorem allocDefault_eq (σ : State) (R : RefTy) :
    allocDefault σ R = (allocHN σ R >>= fun q => pure ({ σ with heap := q.1, nextId := q.2.1 }, q.2.2)) :=
  res_frame_eq (allocDefault_frame σ R)

theorem upd_memoryReferenceDeclFreshAlloc (R : RefTy) (mv : Var)
    (hd : ((none : Option (MRhs C R)).isSome || (Ty.ref R).defaultOkS) = true) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.mref mv (ITerm.alloc MTerm.memory R),
        UpdElem.memory (MTerm.memory.addM R)] σ)
      (Stmt.run σ (Stmt.declMem R mv none hd)) := by
  upd_unfold'
  simp only [allocDefault_eq, bind_assoc, pure_bind]
  res_split
  all_goals simp [State.setEnv, EnvAgreeExcept.refl]

theorem upd_memoryStorageCopy (mv : Var) {R : RefTy} (sp : SPath C (Ty.ref R))
    (hm : (Ty.ref R).mapFree = true) (σ : State) :
    SameOk [] (Upd.apply (C := C)
      [UpdElem.mref mv (ITerm.copy MTerm.memory (SValT.find STerm.storage sp.lower)),
        UpdElem.memory (MTerm.memory.copySt (SValT.find STerm.storage sp.lower))] σ)
      (Stmt.run σ (Stmt.rebindMem mv (MRhs.copy sp hm))) := by
  upd_unfold'
  simp only [copyStToM_eq, bind_assoc, pure_bind]
  res_split
  all_goals simp [State.setEnv, EnvAgreeExcept.refl]

theorem upd_memoryArrayFreshAlloc (mv : Var) {R : RefTy} (se : Simple C PrimTy.uint)
    (hn : R.newArrOk = true) (σ : State) :
    SameOk [] (Upd.apply (C := C)
      [UpdElem.mref mv (ITerm.copy MTerm.memory (SValT.newArr R se.lower)),
        UpdElem.memory (MTerm.memory.copySt (SValT.newArr R se.lower))] σ)
      (Stmt.run σ (Stmt.rebindMem mv (MRhs.newArr se hn))) := by
  upd_unfold'
  simp only [copyStToM_eq, bind_assoc, pure_bind]
  res_split
  all_goals simp [State.setEnv, EnvAgreeExcept.refl]

theorem upd_memoryRootDeleteFreshRebind (R : RefTy) (mv : Var) (hd : (Ty.ref R).defaultOkS = true)
    (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.mref mv (ITerm.alloc MTerm.memory R),
        UpdElem.memory (MTerm.memory.addM R)] σ)
      (Stmt.run σ (Stmt.deleteMem (MPath.var (C := C) (R := R) mv) hd)) := by
  upd_unfold'
  simp only [allocDefault_eq, bind_assoc, pure_bind]
  res_split
  all_goals simp [State.setEnv, EnvAgreeExcept.refl]

theorem Term.eval_mlen' (σ : State) (m : MTerm C) (i : ITerm C) :
    (Term.mlen m i).eval σ = (do
      let τ ← m.eval σ
      memArrayLen τ (← i.eval σ)) := rfl

theorem upd_memoryLengthRead {p : PrimTy} {E : Ty} (v mv : Var) (hlen : p = .uint) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.val v (Term.mlen MTerm.memory (ITerm.pv mv))] σ)
      (Stmt.run σ (Stmt.assignLocal v (Val.mlen (C := C) (E := E) (MPath.var mv) hlen))) := by
  mem_unfold
  res_split

theorem upd_memoryDeletePrimitive {p : PrimTy} (l : MLoc C (Ty.prim p)) (a : MAddr C)
    (ha : ∀ σ, a.eval σ = l.addr σ) (hd : (Ty.prim p).defaultOkS = true) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.memory (MTerm.memory.write a
        (MValT.val (Term.lit (PrimTy.default p))))] σ)
      (Stmt.run σ (Stmt.deleteMem (MPath.loc l) hd)) := by
  upd_unfold'
  simp only [ha, memClear, writeAddr_eq]
  res_split

theorem upd_memoryDeleteReference {R : RefTy} (l : MLoc C (Ty.ref R)) (a : MAddr C)
    (ha : ∀ σ, a.eval σ = l.addr σ) (hd : (Ty.ref R).defaultOkS = true) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.memory ((MTerm.memory.addM R).write a
        (MValT.ref (ITerm.alloc MTerm.memory R)))] σ)
      (Stmt.run σ (Stmt.deleteMem (MPath.loc l) hd)) := by
  upd_unfold'
  simp only [ha, memClear, allocDefault_eq, writeAddr_eq, bind_assoc, pure_bind]
  res_split

theorem MLoc.addr_field_var (mv : Var) {s f : Name} {T : Ty} (hf : C.fieldType s f = some T)
    (σ : State) :
    (MAddr.field (ITerm.pv mv) f : MAddr C).eval σ = (MLoc.field (MPath.var mv) f hf).addr σ := by
  simp only [tm_eval, MLoc.addr, MPath.mval, bind_assoc]
  cases σ.getEnv mv with
  | error _ => rfl
  | ok b => cases b <;> rfl

theorem MLoc.addr_index_var (mv : Var) {R : RefTy} {E : Ty} {a : ArrTy R E}
    (ie : Simple C PrimTy.uint) (σ : State) :
    (MAddr.at (ITerm.pv mv) ie.lower : MAddr C).eval σ =
      (MLoc.index a (MPath.var mv) (Val.simple ie)).addr σ := by
  simp only [tm_eval, MLoc.addr, MPath.mval, Val.eval, Simple.lower_eval, bind_assoc]
  cases σ.getEnv mv with
  | error _ => rfl
  | ok b => cases b <;> rfl

/-! ### Memory back to storage -/

theorem upd_memoryToStorageStoreRoot (gsp : Name) {R : RefTy} (hgsp : C.rootType gsp = some (Ty.ref R))
    (mpath : MPath C (Ty.ref R)) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.storage (STerm.storage.save (PTerm.root gsp)
        (SValT.copyMem MTerm.memory mpath.lower))] σ)
      (Stmt.run σ (Stmt.assignFromMem (Loc.root gsp hgsp) mpath)) := by
  upd_unfold'
  simp only [MPath.lower_eval, bind_assoc]
  res_split

theorem upd_memoryToStorageFieldCopyRoot {x : Name} (sp : SPath C (Ty.struct x)) {fld : Name} {R : RefTy}
    (hfld : C.fieldType x fld = some (Ty.ref R)) (mpath : MPath C (Ty.ref R)) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.storage (STerm.storage.save (sp.lower.field fld)
        (SValT.copyMem MTerm.memory mpath.lower))] σ)
      (Stmt.run σ (Stmt.assignFromMem (Loc.field sp fld hfld) mpath)) := by
  upd_unfold'
  simp only [MPath.lower_eval, bind_assoc]
  res_split

theorem upd_memoryToStorageIndexCopyRoot {R R' : RefTy} {q : PrimTy} (it : IndexTy R q (Ty.ref R'))
    (b : SPath C (Ty.ref R)) (ie : Simple C q) (mpath : MPath C (Ty.ref R')) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.storage (STerm.storage.save (b.lower.at ie.lower)
        (SValT.copyMem MTerm.memory mpath.lower))] σ)
      (Stmt.run σ (Stmt.assignFromMem (Loc.index it b (Val.simple ie)) mpath)) := by
  upd_unfold'
  simp only [MPath.lower_eval, bind_assoc]
  res_split

/-! ### Push and pop -/

/-- A push whose value ignores the slot does not depend on the element type:
`pushSlot` hands back the same recycled slots whatever `E` is. -/
theorem pushAt_const (σ : State) (E E' : Ty) (r : Name) (segs : List Seg) (f : Res SVal) :
    pushAt σ E r segs (fun _ => f) = pushAt σ E' r segs (fun _ => f) := by
  unfold pushAt
  cases σ.findStorage r segs with
  | error _ => rfl
  | ok v =>
    cases v with
    | array elems shadow => cases shadow <;> rfl
    | _ => rfl

theorem pushAt_pushVal_some (σ σ' : State) (E : Ty) (r : Name) (segs : List Seg) {T : Ty} (s : Src C T) :
    pushAt σ E r segs (Src.pushVal σ' (some s)) =
      pushAt σ .uint r segs (fun _ => do pure (← s.value σ').strip) :=
  pushAt_const σ E .uint r segs _

theorem pushAt_with (σ : State) (E : Ty) (r : Name) (segs : List Seg) (f : SVal → Res SVal) :
    (pushAt σ E r segs f >>= fun τ => pure { σ with storage := τ.storage }) = pushAt σ E r segs f := by
  unfold pushAt
  simp only [bind, Except.bind]
  cases σ.findStorage r segs with
  | error _ => rfl
  | ok v =>
    cases v with
    | array elems shadow =>
      simp only
      cases f (pushSlot E shadow).1 with
      | error _ => rfl
      | ok w => exact State.saveStorage_with σ r segs _
    | _ => rfl

theorem popAt_with (σ : State) (keep : Bool) (r : Name) (segs : List Seg) :
    (popAt σ keep r segs >>= fun τ => pure { σ with storage := τ.storage }) =
      popAt σ keep r segs := by
  unfold popAt
  simp only [bind, Except.bind]
  cases σ.findStorage r segs with
  | error _ => rfl
  | ok v =>
    cases v with
    | array elems shadow =>
      simp only
      cases elems.reverse with
      | nil => rfl
      | cons last rest => exact State.saveStorage_with σ r segs _
    | _ => rfl

theorem upd_storagePushValueSave {q : PrimTy} (sp : SPath C (Ty.prim q).array) (se : Simple C q)
    (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.storage (STerm.storage.push sp.lower (SValT.val se.lower))] σ)
      (Stmt.run σ (Stmt.push sp (some (Src.val (Val.simple se))) rfl)) := by
  simp only [Stmt.run, pushAt_pushVal_some]
  upd_unfold'
  simp only [pushAt_with]
  res_split

theorem upd_storagePushValueCopySource {R : RefTy} (sp : SPath C (Ty.ref R).array) (sp2 : SPath C (Ty.ref R))
    (hm : (Ty.ref R).mapFree = true) (σ : State) :
    SameOk [] (Upd.apply (C := C)
        [UpdElem.storage (STerm.storage.push sp.lower (SValT.find STerm.storage sp2.lower))] σ)
      (Stmt.run σ (Stmt.push sp (some (Src.copy sp2 hm)) rfl)) := by
  simp only [Stmt.run, pushAt_pushVal_some]
  upd_unfold'
  simp only [pushAt_with]
  res_split

theorem upd_storagePushLengthSave {E : Ty} (sp : SPath C E.array)
    (hd : ((none : Option (Src C E)).isSome || E.defaultOkS) = true) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.storage (STerm.storage.pushSlot sp.lower E)] σ)
      (Stmt.run σ (Stmt.push sp none hd)) := by
  simp only [Stmt.run, Src.pushVal_none]
  upd_unfold'
  simp only [pushAt_with]
  cases SPath.resolve σ sp <;> exact SameOk.self _ _

theorem upd_storagePushLengthSaveReferenceElement {E : Ty} (sp : SPath C E.array)
    (hd : ((none : Option (Src C E)).isSome || E.defaultOkS) = true) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.storage (STerm.storage.extend sp.lower E)] σ)
      (Stmt.run σ (Stmt.push sp none hd)) := by
  simp only [Stmt.run, Src.pushVal_none]
  upd_unfold'
  simp only [pushAt, pushPlaceAt, State.saveStorage_eq, bind_assoc, pure_bind]
  simp only [bind, Except.bind, pure, Except.pure]
  cases SPath.resolve σ sp with
  | error _ => trivial
  | ok rs =>
    simp only
    cases σ.findStorage rs.1 rs.2 with
    | error _ => trivial
    | ok v =>
      cases v with
      | array elems shadow =>
        simp only
        cases σ.storeRes rs.1 rs.2 _ with
        | error _ => trivial
        | ok st => simp
      | _ => trivial

theorem upd_storagePopSave {E : Ty} (sp : SPath C E.array) (hE : E.isMapping = false)
    (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.storage (STerm.storage.pop sp.lower)] σ)
      (Stmt.run σ (Stmt.pop sp)) := by
  upd_unfold'
  simp only [hE, popAt_with]
  res_split

theorem upd_storagePopSaveMappingElement {E : Ty} (sp : SPath C E.array) (hE : E.isMapping = true)
    (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.storage (STerm.storage.shrink sp.lower)] σ)
      (Stmt.run σ (Stmt.pop sp)) := by
  upd_unfold'
  simp only [hE, popAt_with]
  res_split

theorem upd_storageLocalRootPushBind {R : RefTy} (lsv : Var) (sp : SPath C (Ty.ref R).array)
    (hd : (Ty.ref R).defaultOkS = true) (σ : State) :
    SameOk [] (Upd.apply (C := C) [UpdElem.storage (STerm.storage.extend sp.lower (Ty.ref R)),
        UpdElem.path lsv sp.lower.next] σ)
      (Stmt.run σ (Stmt.rebind lsv (ARhs.push sp hd))) := by
  upd_unfold'
  simp only [pushPlaceAt, State.saveStorage_eq, bind_assoc, pure_bind]
  simp only [bind, Except.bind, pure, Except.pure]
  cases SPath.resolve σ sp with
  | error _ => trivial
  | ok rs =>
    simp only
    cases σ.findStorage rs.1 rs.2 with
    | error _ => trivial
    | ok v =>
      cases v with
      | array elems shadow =>
        simp only
        cases σ.storeRes rs.1 rs.2 _ with
        | error _ => trivial
        | ok st => simp
      | _ => trivial

/-- `transferNoCallbackBox`: the booking is the transfer, exactly.  Both read
the receiver, then the amount as a word (halting where it is not), and book
nothing at `this`. -/
theorem upd_transferNoCallbackBox_eq (sadr se : Simple C .uint) (σ : State) :
    Upd.apply [UpdElem.pay sadr.lower se.lower] σ =
      (Stmt.transfer (.simple sadr) (.simple se)).run σ := by
  simp only [Upd.apply, List.foldlM_cons, List.foldlM_nil, UpdElem.write, Stmt.run, Val.eval,
    Simple.lower_eval, transferAt, State.pay, bind, Except.bind, pure, Except.pure, Value.asInt]
  cases sadr.eval σ with
  | error _ => rfl
  | ok v =>
    cases v with
    | bool _ => rfl
    | int _ =>
      cases se.eval σ with
      | error _ => rfl
      | ok w => cases w <;> (try rfl) <;> dsimp only <;> split <;> rename_i heq <;> exact heq.symm

theorem upd_transferNoCallbackBox (sadr se : Simple C .uint) (σ : State) :
    SameOk [] (Upd.apply [UpdElem.pay sadr.lower se.lower] σ)
      ((Stmt.transfer (.simple sadr) (.simple se)).run σ) := by
  rw [upd_transferNoCallbackBox_eq]
  exact SameOk.self _ _

theorem Taclet.sound_update {k : Nat} {m : Modality} {s : Stmt C} {U : Upd C}
    (d : Taclet C k m s (.update U)) : ∀ σ, SameOk [] (U.apply σ) (s.run σ) := by
  cases d
  all_goals intro σ
  -- the element type picks what `pop` does to the element: read off the side condition
  case storagePopSave =>
    exact upd_storagePopSave _ (by simp_all [SPath.elemMapping, Ty.elemIsMapping]) σ
  case storagePopSaveMappingElement =>
    exact upd_storagePopSaveMappingElement _ (by simp_all [SPath.elemMapping, Ty.elemIsMapping]) σ
  all_goals clear_side
  case memoryReferenceDeclFreshAlloc => exact upd_memoryReferenceDeclFreshAlloc ..
  case localOpAssign => exact upd_localOpAssign ..
  case memoryFieldOpAssign => exact upd_memoryFieldOpAssign ..
  case memoryIndexArrayOpAssign => exact upd_memoryIndexArrayOpAssign ..
  case localIncrement => exact upd_localIncrement ..
  case memoryFieldIncrement => exact upd_memoryFieldIncrement ..
  case memoryIndexArrayIncrement => exact upd_memoryIndexArrayIncrement ..
  case localAssignIncrement => exact upd_localAssignIncrement ..
  case storageRootIncrementAssignment => exact upd_storageRootIncrementAssignment ..
  case storageFieldIncrementAssignment => exact upd_storageFieldIncrementAssignment ..
  case storageIndexIncrementAssignment => exact upd_storageIndexIncrementAssignment ..
  case memoryFieldIncrementAssignment => exact upd_memoryFieldIncrementAssignment ..
  case memoryIndexArrayIncrementAssignment => exact upd_memoryIndexArrayIncrementAssignment ..
  case storagePushValueSave => exact upd_storagePushValueSave ..
  case storagePushValueCopySource => exact upd_storagePushValueCopySource ..
  case storagePushLengthSave => exact upd_storagePushLengthSave ..
  case storagePushLengthSaveReferenceElement => exact upd_storagePushLengthSaveReferenceElement ..
  case storageLocalRootPushBind => exact upd_storageLocalRootPushBind ..
  case storageLocalRootPushBindMappingElement => exact upd_storageLocalRootPushBind ..
  case transferNoCallbackBox => exact upd_transferNoCallbackBox ..
  case memoryFieldRead => exact upd_memoryFieldRead ..
  case memoryIndexReadArrayValue => exact upd_memoryIndexReadArrayValue ..
  case memoryRootRebind => exact upd_memoryRootRebind ..
  case memoryFieldReadAliasRoot => exact upd_memoryFieldReadAliasRoot ..
  case memoryIndexReadArrayMemory => exact upd_memoryIndexReadArrayMemory ..
  case memoryFieldWrite => exact upd_memoryFieldWrite ..
  case memoryIndexWriteArray => exact upd_memoryIndexWriteArray ..
  case memoryStorageCopy => exact upd_memoryStorageCopy ..
  case memoryArrayFreshAlloc => exact upd_memoryArrayFreshAlloc ..
  case memoryRootDeleteFreshRebind => exact upd_memoryRootDeleteFreshRebind ..
  case memoryLengthRead => exact upd_memoryLengthRead ..
  case memoryFieldDeletePrimitive =>
    exact upd_memoryDeletePrimitive _ _ (MLoc.addr_field_var _ _) _ σ
  case memoryFieldDeleteReference =>
    exact upd_memoryDeleteReference _ _ (MLoc.addr_field_var _ _) _ σ
  case memoryIndexDeletePrimitive =>
    exact upd_memoryDeletePrimitive _ _ (MLoc.addr_index_var _ _) _ σ
  case memoryIndexDeleteReference =>
    exact upd_memoryDeleteReference _ _ (MLoc.addr_index_var _ _) _ σ
  case memoryToStorageStoreRoot => exact upd_memoryToStorageStoreRoot ..
  case memoryToStorageFieldCopyRoot => exact upd_memoryToStorageFieldCopyRoot ..
  case memoryToStorageIndexMappingCopyRoot => exact upd_memoryToStorageIndexCopyRoot ..
  case memoryToStorageIndexArrayCopyRoot => exact upd_memoryToStorageIndexCopyRoot ..
  case memoryFieldWriteCopy =>
    rename_i mpath
    cases mpath with
    | var y => exact upd_memoryFieldWriteCopy_var ..
    | loc l => cases l <;> mem_unfold <;> simp only [MPath.lower_eval, bind_assoc] <;> res_split
  case memoryIndexWriteCopy =>
    rename_i mpath
    cases mpath with
    | var y => exact upd_memoryIndexWriteCopy_var ..
    | loc l => cases l <;> mem_unfold <;> simp only [MPath.lower_eval, bind_assoc] <;> res_split
  all_goals (try (upd_unfold; res_split; done))
  all_goals (try (upd_unfold; simp only [evalBinop_compound (by assumption)]; res_split; done))
  all_goals (try (rename_i op _; cases op <;> (upd_unfold; res_split); done))

end Solidity
