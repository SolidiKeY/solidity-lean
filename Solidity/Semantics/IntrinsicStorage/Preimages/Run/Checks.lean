import Solidity.Semantics.IntrinsicStorage.Preimages.Run

/-! Regressions for the observed straight-line steps under sequencing: a
continuation sees exactly the actual typed result, and a failing actual run
skips the continuation and keeps the inputs observed up to the failure. -/
namespace Solidity.Semantics.IntrinsicStorage.Observe.Run.Checks

open Solidity.Storage
variable {C : Contract} {Γ : Ctx}

-- Storage assignment then delete: the delete runs in the state the actual assignment returns.
example {T U : Ty} (l : Loc C Γ T) (r : Src C Γ T) (l' : Loc C Γ U) (σ : State C Γ) :
    (assign l r σ >>= fun o => (delete l' o.st).map (·.st.storage)).result =
    (TRun.assign l r σ >>= fun o => (TRun.delete l' o.st).map (·.st.storage)) := by
  simp only [Audit.result_bind, Audit.result_map_direct, assign_result, delete_result]

-- A declaration extends the context the next observed step runs in.
example (p : PrimTy) (init : Option (Val C Γ p)) (R : RefTy)
    (a : Option (ARhs C (.val p :: Γ) R)) (σ : State C Γ) :
    (declLocal p init σ >>= fun o => (declStorage R a o.st).map (·.st.storage)).result =
    (TRun.declLocal p init σ >>= fun o => (TRun.declStorage R a o.st).map (·.st.storage)) := by
  simp only [Audit.result_bind, Audit.result_map_direct, declLocal_result, declStorage_result]

-- A memory declaration may grow the heap; the rebind reads the returned state.
example (R : RefTy) (init : Option (MRhs C Γ R)) (hm : (Ty.ref R).mapFree = true)
    (r : MRhs C (.mem R :: Γ) R) (σ : State C Γ) :
    (declMem R init hm σ >>= fun o => (rebindMem .here r o.st).map (·.st.storage)).result =
    (TRun.declMem R init hm σ >>= fun o =>
      (TRun.rebindMem .here r o.st).map (·.st.storage)) := by
  simp only [Audit.result_bind, Audit.result_map_direct, declMem_result, rebindMem_result]

section Continuation
variable {β : Type} (σ : State C Γ) (f : Out C σ.H Γ → Audit β)

-- Local and alias updates hand the continuation the actual output.
example {R : RefTy} {p : PrimTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R)
    (j : Idx Γ (.val p)) (v : Val C Γ p) :
    (rebind i r σ >>= f).result = (TRun.rebind i r σ >>= fun o => (f o).result) ∧
    (assignLocal j v σ >>= f).result = (TRun.assignLocal j v σ >>= fun o => (f o).result) := by
  simp only [Audit.result_bind, rebind_result, assignLocal_result, and_self]

-- Compound assignment and increment/decrement, as statements and as assigned values.
example {p : PrimTy} (op : BinOp) (b : IncDec) (l : OpLoc C Γ p) (r : Val C Γ p)
    (i : Idx Γ (.val p)) :
    (opAssign op l r σ >>= f).result = (TRun.opAssign op l r σ >>= fun o => (f o).result) ∧
    (incDec b l σ >>= f).result = (TRun.incDec b l σ >>= fun o => (f o).result) ∧
    (assignIncDec i b l σ >>= f).result =
      (TRun.assignIncDec i b l σ >>= fun o => (f o).result) := by
  simp only [Audit.result_bind, opAssign_result, incDec_result, assignIncDec_result, and_self]

-- Every push form and pop, including the exhausted-array failure inside them.
example {p : PrimTy} (op : BinOp) (d : IncDec) (b : SPath C Γ (.array (.prim p)))
    (v : Option (Src C Γ (.prim p))) (r : Val C Γ p) (i : Idx Γ (.val p)) :
    (push b v σ >>= f).result = (TRun.push b v σ >>= fun o => (f o).result) ∧
    (assignLocalPush i b σ >>= f).result =
      (TRun.assignLocalPush i b σ >>= fun o => (f o).result) ∧
    (pushOpAssign op b r σ >>= f).result =
      (TRun.pushOpAssign op b r σ >>= fun o => (f o).result) ∧
    (pushIncDec d b σ >>= f).result = (TRun.pushIncDec d b σ >>= fun o => (f o).result) ∧
    (pop b σ >>= f).result = (TRun.pop b σ >>= fun o => (f o).result) := by
  simp only [Audit.result_bind, push_result, assignLocalPush_result, pushOpAssign_result,
    pushIncDec_result, pop_result, and_self]

-- Ether moves: transfer reverts where send records its flag.
example (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) :
    (transfer r a σ >>= f).result = (TRun.transfer r a σ >>= fun o => (f o).result) ∧
    (send pv r a σ >>= f).result = (TRun.send pv r a σ >>= fun o => (f o).result) := by
  simp only [Audit.result_bind, transfer_result, send_result, and_self]

-- Memory moves, memory delete and `new`.
example {R : RefTy} {T U : Ty} (l : Loc C Γ (.ref R)) (p : MPath C Γ (.ref R))
    (m : MLoc C Γ T) (r : MSrc C Γ T) (q : MPath C Γ U) (nl : NewLhs C Γ R)
    (n : Simple C Γ .uint) (h : R.newArrOk = true) :
    (assignFromMem l p σ >>= f).result =
      (TRun.assignFromMem l p σ >>= fun o => (f o).result) ∧
    (assignMem m r σ >>= f).result = (TRun.assignMem m r σ >>= fun o => (f o).result) ∧
    (deleteMem q σ >>= f).result = (TRun.deleteMem q σ >>= fun o => (f o).result) ∧
    (assignNew nl n h σ >>= f).result = (TRun.assignNew nl n h σ >>= fun o => (f o).result) := by
  simp only [Audit.result_bind, assignFromMem_result, assignMem_result, deleteMem_result,
    assignNew_result, and_self]

-- A failed `require` or `assert` skips the continuation with the actual halt and
-- keeps the inputs its condition hashed.
example (c : Val C Γ .bool) (e : THalt) (h : TRun.require c σ = .error e) :
    (require c σ >>= f).result = .error e ∧ (require c σ >>= f).inputs = (require c σ).inputs :=
  ⟨by rw [Audit.result_bind, require_result, h]; rfl,
   Audit.failed_bind _ f ((require_result c σ).trans h)⟩

example (c : Val C Γ .bool) (e : THalt) (h : TRun.assert c σ = .error e) :
    (assert c σ >>= f).result = .error e ∧ (assert c σ >>= f).inputs = (assert c σ).inputs :=
  ⟨by rw [Audit.result_bind, assert_result, h]; rfl,
   Audit.failed_bind _ f ((assert_result c σ).trans h)⟩

end Continuation

end Solidity.Semantics.IntrinsicStorage.Observe.Run.Checks
