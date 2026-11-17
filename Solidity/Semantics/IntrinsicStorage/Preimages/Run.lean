import Solidity.Semantics.IntrinsicStorage.Preimages.Ops

/-! Observed runs of the straight-line statements: each audited step keeps the hash
inputs of its storage accesses, and its result is the actual typed run result. -/
namespace Solidity.Semantics.IntrinsicStorage.Observe.Run

open Solidity.Storage
open Audit (lift atRef)
variable {C : Contract} {Γ : Ctx}

noncomputable def assign {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) : Step C Γ Γ := fun σ => do
  let sv ← source σ r
  let ref ← loc σ l
  let st ← Audit.write σ.storage ref sv
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

noncomputable def rebind {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) : Step C Γ Γ :=
  fun σ => do
    let (st, ref) ← aliasRhs σ r
    pure ⟨(σ.withStorage st).setLocal i (some ref), List.prefix_refl _⟩

noncomputable def assignLocal {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p) : Step C Γ Γ :=
  fun σ => do pure ⟨σ.setLocal i (← value σ r), List.prefix_refl _⟩

noncomputable def declLocal (p : PrimTy) (init : Option (Val C Γ p)) : Step C Γ (.val p :: Γ) :=
  fun σ => do
    let v ← match init with | none => pure (PrimTy.dflt p) | some e => value σ e
    pure ⟨σ.push (t := .val p) v, List.prefix_refl _⟩

noncomputable def declStorage (R : RefTy) (init : Option (ARhs C Γ R)) : Step C Γ (.alias R :: Γ) :=
  fun σ => match init with
  | none => pure ⟨σ.push (t := .alias R) none, List.prefix_refl _⟩
  | some r => do
    let (st, ref) ← aliasRhs σ r
    pure ⟨(σ.withStorage st).push (t := .alias R) (some ref), List.prefix_refl _⟩

noncomputable def opAssign {p : PrimTy} (op : BinOp) (l : OpLoc C Γ p) (r : Val C Γ p) :
    Step C Γ Γ := fun σ => do storeOp σ op l (← value σ r)

noncomputable def incDec {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) : Step C Γ Γ :=
  fun σ => do pure (← bumpOp σ op l).1

noncomputable def assignIncDec {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (l : OpLoc C Γ p) : Step C Γ Γ := fun σ => do
  let (o, v) ← bumpOp σ op l
  pure ⟨o.st.setLocal i v, o.ext⟩

noncomputable def push {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E)) :
    Step C Γ Γ := fun σ => do
  let ref ← path σ b
  let x ← match v with
    | none => pure none
    | some r => do pure (some (← source σ r).strip)
  if σ.storage.full ref then atRef ref (.error .exhausted) else
  let st ← Audit.push σ.storage ref (fun slot => some (x.getD slot))
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

noncomputable def assignLocalPush {p : PrimTy} (i : Idx Γ (.val p))
    (b : SPath C Γ (.array (.prim p))) : Step C Γ Γ := fun σ => do
  let o ← push b none σ
  pure ⟨o.st.setLocal i (PrimTy.dflt p), o.ext⟩

noncomputable def pushOpAssign {p : PrimTy} (op : BinOp) (b : SPath C Γ (.array (.prim p)))
    (rhs : Val C Γ p) : Step C Γ Γ := fun σ => do
  let v ← value σ rhs
  let ref ← path σ b
  if σ.storage.full ref then atRef ref (.error .exhausted) else
  let (st, i) ← Audit.place σ.storage ref
  atRef (ref.index (.arr .dyn) i) (opStoreT (σ.withStorage st) op (ref.index (.arr .dyn) i) v)

noncomputable def pushIncDec {p : PrimTy} (op : IncDec) (b : SPath C Γ (.array (.prim p))) :
    Step C Γ Γ := fun σ => do
  let ref ← path σ b
  if σ.storage.full ref then atRef ref (.error .exhausted) else
  let (st, i) ← Audit.place σ.storage ref
  pure (← atRef (ref.index (.arr .dyn) i) (bumpStoreT (σ.withStorage st) op
    (ref.index (.arr .dyn) i))).1

noncomputable def pop {E : Ty} (b : SPath C Γ (.array E)) : Step C Γ Γ := fun σ => do
  let ref ← path σ b
  let st ← Audit.arrayOp σ.storage ref true (TRes.ofOpt (σ.storage.pop E.isMapping ref))
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

noncomputable def transfer (r a : Val C Γ .uint) : Step C Γ Γ := fun σ => do
  let addr ← value σ r
  let amt ← value σ a
  if σ.canPay addr amt then pure ⟨σ.pay addr amt.1, List.prefix_refl _⟩
  else lift (.error .revert)

noncomputable def send (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) : Step C Γ Γ := fun σ => do
  let addr ← value σ r
  let amt ← value σ a
  pure (sendT σ pv addr amt)

noncomputable def declMem (R : RefTy) (init : Option (MRhs C Γ R))
    (hm : (Ty.ref R).mapFree = true) : Step C Γ (.mem R :: Γ) := fun σ => match init with
  | none =>
    let g := σ.allocDefaultG R hm
    pure ⟨g.st.push (t := .mem R) (some g.val), g.ext⟩
  | some r => do
    let g ← memoryRhs σ r
    pure ⟨g.st.push (t := .mem R) (some g.val), g.ext⟩

noncomputable def rebindMem {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) : Step C Γ Γ :=
  fun σ => do
    let g ← memoryRhs σ r
    pure ⟨g.st.setLocal i (some g.val), g.ext⟩

noncomputable def assignFromMem {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) :
    Step C Γ Γ := fun σ => do
  let m ← memoryPath σ p
  let ref ← loc σ l
  let st ← Audit.write σ.storage ref (MVal.copyMToSt σ.heap m)
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

noncomputable def assignMem {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) : Step C Γ Γ := fun σ => do
  let mv ← memorySource σ r
  let a ← memoryLoc σ l
  let hp ← lift (TRes.ofOpt (σ.heap.writeAddr a mv))
  pure ⟨σ.withHeap hp, List.prefix_refl _⟩

noncomputable def delete {T : Ty} (l : Loc C Γ T) : Step C Γ Γ := fun σ => do
  let ref ← loc σ l
  let st ← Audit.touch σ.storage ref (TRes.ofOpt (σ.storage.delete ref))
  pure ⟨σ.withStorage st, List.prefix_refl _⟩

noncomputable def deleteMem {T : Ty} (p : MPath C Γ T) : Step C Γ Γ := fun σ => match p with
  | .var i hm => lift (TRun.deleteMem (.var i hm) σ)
  | .loc l => do lift (TRun.clearT σ (← memoryLoc σ l) l.mapFree)

noncomputable def assignNew {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint)
    (h : R.newArrOk = true) : Step C Γ Γ := fun σ =>
  let g := σ.copyStToMG (newArrT R (n.evalT σ) h) (RefTy.mapFree_of_newArrOk h)
  match l with
  | .store l => do
    let ref ← loc g.st l
    let st ← Audit.write g.st.storage ref (MVal.copyMToSt g.st.heap g.val)
    pure ⟨g.st.withStorage st, g.ext⟩
  | .mem l => do
    let a ← memoryLoc g.st l
    let hp ← lift (TRes.ofOpt (g.st.heap.writeAddr a g.val))
    pure ⟨g.st.withHeap hp, g.ext⟩

noncomputable def require (c : Val C Γ .bool) : Step C Γ Γ := fun σ => do
  let v ← value σ c
  if boolT v then pure ⟨σ, List.prefix_refl _⟩ else lift (.error .revert)

noncomputable def assert (c : Val C Γ .bool) : Step C Γ Γ := fun σ => do
  let v ← value σ c
  if boolT v then pure ⟨σ, List.prefix_refl _⟩ else lift (.error .panic)

theorem assign_result {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) (σ : State C Γ) :
    (assign l r σ).result = TRun.assign l r σ := by
  simp only [assign, TRun.assign, Audit.result_bind, Audit.result_pure,
    Audit.result_write,
    source_result, loc_result]

theorem rebind_result {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) (σ : State C Γ) :
    (rebind i r σ).result = TRun.rebind i r σ := by
  simp only [rebind, TRun.rebind, Audit.result_bind, Audit.result_pure,
    aliasRhs_result]

theorem assignLocal_result {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p) (σ : State C Γ) :
    (assignLocal i r σ).result = TRun.assignLocal i r σ := by
  simp only [assignLocal, TRun.assignLocal, Audit.result_bind, Audit.result_pure,
    value_result]

theorem declLocal_result (p : PrimTy) (init : Option (Val C Γ p)) (σ : State C Γ) :
    (declLocal p init σ).result = TRun.declLocal p init σ := by
  cases init <;>
  simp only [declLocal, TRun.declLocal, Audit.result_bind, Audit.result_pure,
    value_result]

theorem declStorage_result (R : RefTy) (init : Option (ARhs C Γ R)) (σ : State C Γ) :
    (declStorage R init σ).result = TRun.declStorage R init σ := by
  cases init <;>
  simp only [declStorage, TRun.declStorage, Audit.result_bind, Audit.result_pure,
    aliasRhs_result]

theorem opAssign_result {p : PrimTy} (op : BinOp) (l : OpLoc C Γ p) (r : Val C Γ p) (σ : State C Γ) :
    (opAssign op l r σ).result = TRun.opAssign op l r σ := by
  simp only [opAssign, TRun.opAssign, Audit.result_bind,
    value_result,
    storeOp_result]

theorem incDec_result {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) (σ : State C Γ) :
    (incDec op l σ).result = TRun.incDec op l σ := by
  simp only [incDec, TRun.incDec, Audit.result_bind, Audit.result_pure,
    bumpOp_result]

theorem assignIncDec_result {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec)
    (l : OpLoc C Γ p) (σ : State C Γ) :
    (assignIncDec i op l σ).result = TRun.assignIncDec i op l σ := by
  simp only [assignIncDec, TRun.assignIncDec, Audit.result_bind, Audit.result_pure,
    bumpOp_result]

theorem push_result {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E)) (σ : State C Γ) :
    (push b v σ).result = TRun.push b v σ := by
  cases v <;>
  simp only [push, TRun.push, Audit.result_bind, Audit.result_pure,
    Audit.result_atRef,
    Audit.result_push, source_result, path_result,
    apply_ite Audit.result]

theorem assignLocalPush_result {p : PrimTy} (i : Idx Γ (.val p))
    (b : SPath C Γ (.array (.prim p))) (σ : State C Γ) :
    (assignLocalPush i b σ).result = TRun.assignLocalPush i b σ := by
  simp only [assignLocalPush, TRun.assignLocalPush, push_result, Audit.result_bind, Audit.result_pure]

theorem pushOpAssign_result {p : PrimTy} (op : BinOp) (b : SPath C Γ (.array (.prim p)))
    (rhs : Val C Γ p) (σ : State C Γ) :
    (pushOpAssign op b rhs σ).result = TRun.pushOpAssign op b rhs σ := by
  simp only [pushOpAssign, TRun.pushOpAssign, Audit.result_bind,
    Audit.result_atRef,
    Audit.result_place, value_result, path_result,
    apply_ite Audit.result]

theorem pushIncDec_result {p : PrimTy} (op : IncDec) (b : SPath C Γ (.array (.prim p))) (σ : State C Γ) :
    (pushIncDec op b σ).result = TRun.pushIncDec op b σ := by
  simp only [pushIncDec, TRun.pushIncDec, Audit.result_bind, Audit.result_pure,
    Audit.result_atRef,
    Audit.result_place, path_result,
    apply_ite Audit.result]

theorem pop_result {E : Ty} (b : SPath C Γ (.array E)) (σ : State C Γ) :
    (pop b σ).result = TRun.pop b σ := by
  simp only [pop, TRun.pop, Audit.result_bind, Audit.result_pure,
    Audit.result_arrayOp, path_result]

theorem transfer_result (r a : Val C Γ .uint) (σ : State C Γ) :
    (transfer r a σ).result = TRun.transfer r a σ := by
  simp only [transfer, TRun.transfer, Audit.result_bind, Audit.result_pure,
    Audit.result_lift,
    value_result,
    apply_ite Audit.result]
  rfl

theorem send_result (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) (σ : State C Γ) :
    (send pv r a σ).result = TRun.send pv r a σ := by
  simp only [send, TRun.send, Audit.result_bind, Audit.result_pure,
    value_result]

theorem declMem_result (R : RefTy) (init : Option (MRhs C Γ R))
    (hm : (Ty.ref R).mapFree = true) (σ : State C Γ) :
    (declMem R init hm σ).result = TRun.declMem R init hm σ := by
  cases init <;>
  simp only [declMem, TRun.declMem, Audit.result_bind, Audit.result_pure,
    memoryRhs_result]

theorem rebindMem_result {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) (σ : State C Γ) :
    (rebindMem i r σ).result = TRun.rebindMem i r σ := by
  simp only [rebindMem, TRun.rebindMem, Audit.result_bind, Audit.result_pure,
    memoryRhs_result]

theorem assignFromMem_result {R : RefTy} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R)) (σ : State C Γ) :
    (assignFromMem l p σ).result = TRun.assignFromMem l p σ := by
  simp only [assignFromMem, TRun.assignFromMem, Audit.result_bind, Audit.result_pure,
    Audit.result_write,
    loc_result,
    memoryPath_result]

theorem assignMem_result {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) (σ : State C Γ) :
    (assignMem l r σ).result = TRun.assignMem l r σ := by
  simp only [assignMem, TRun.assignMem, Audit.result_bind, Audit.result_pure,
    Audit.result_lift,
    memorySource_result, memoryLoc_result]

theorem delete_result {T : Ty} (l : Loc C Γ T) (σ : State C Γ) :
    (delete l σ).result = TRun.delete l σ := by
  simp only [delete, TRun.delete, Audit.result_bind, Audit.result_pure,
    Audit.result_touch, loc_result]

theorem deleteMem_result {T : Ty} (p : MPath C Γ T) (σ : State C Γ) :
    (deleteMem p σ).result = TRun.deleteMem p σ := by
  cases p <;>
  simp only [deleteMem, TRun.deleteMem, Audit.result_bind,
    Audit.result_lift,
    memoryLoc_result]

theorem assignNew_result {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint)
    (h : R.newArrOk = true) (σ : State C Γ) :
    (assignNew l n h σ).result = TRun.assignNew l n h σ := by
  cases l <;>
  simp only [assignNew, TRun.assignNew, Audit.result_bind, Audit.result_pure,
    Audit.result_lift, Audit.result_write,
    loc_result,
    memoryLoc_result]

theorem require_result (c : Val C Γ .bool) (σ : State C Γ) :
    (require c σ).result = TRun.require c σ := by
  simp only [require, TRun.require, Audit.result_bind, Audit.result_pure,
    Audit.result_lift,
    value_result,
    apply_ite Audit.result]

theorem assert_result (c : Val C Γ .bool) (σ : State C Γ) :
    (assert c σ).result = TRun.assert c σ := by
  simp only [assert, TRun.assert, Audit.result_bind, Audit.result_pure,
    Audit.result_lift,
    value_result,
    apply_ite Audit.result]

end Solidity.Semantics.IntrinsicStorage.Observe.Run
