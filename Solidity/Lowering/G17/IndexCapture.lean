import Solidity.Lowering.V07.ReferenceEffects

/-! Indexed native access after reference capture and local rebinding. The
captured object identity is retained for every array shape and primitive type.
This is an operational ingredient for indexAccess, not yet Source transport,
a heap/world relation, or coverage of storage/mapping/calldata indexing. -/
namespace Solidity.Lowering.G17.IndexCapture
open V07
variable {C : Contract} {Γ : Ctx} {R : RefTy} {p : PrimTy}

private def capturePrefix (i a : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) :
    Prog C Γ (.mem R :: Γ) :=
  (memoryCapture i hm).join
    (.cons (.rebindMem (.there i) (.alias (.var (.there a) hm))) .nil)

private theorem prefix_run (target : State C Γ) (i a : Idx Γ (.mem R))
    (hm : (Ty.ref R).mapFree = true) (old assigned : HRef target.H R)
    (readI : TEnv.get i target.env = some old) (readA : TEnv.get a target.env = some assigned) :
    (capturePrefix i a hm).run target =
      .ok (⟨(target.setLocal i (some assigned)).push (t := .mem R) (some old),List.prefix_refl _⟩) := by
  unfold capturePrefix memoryCapture
  change (Prog.cons _ (.cons _ .nil)).run target = _
  rw [Prog.run_cons_ok (memory_declaration_run target i hm old readI)]
  rw [Prog.run_cons_ok (memory_rebind_run (target.push (t := .mem R) (some old))
    (.there i) (.there a) hm assigned readA),Prog.run_nil]
  rfl

def readOperand (i a : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (array : ArrTy R (.prim p)) (index : Val C Γ .uint) :
    DeferredSource.Operand C Γ (.prim p) :=
  ⟨_,capturePrefix i a hm,.val (.readMem (.index array (.var .here hm) (index.wk (.drop .refl))))⟩

/-- The index is evaluated after rebinding, but the indexed object is the
captured reference. Bounds failures use the existing heap lookup/revert law.
No result of the desired read is an input premise. -/
theorem read_run (target : State C Γ) (i a : Idx Γ (.mem R))
    (hm : (Ty.ref R).mapFree = true) (old assigned : HRef target.H R)
    (readI : TEnv.get i target.env = some old) (readA : TEnv.get a target.env = some assigned)
    (array : ArrTy R (.prim p)) (index : Val C Γ .uint) :
    (readOperand i a hm array index).run target = (do
      let k ← index.evalT (target.setLocal i (some assigned))
      let value ← TRes.ofOpt (target.heap.index old array k)
      pure ((⟨target.setLocal i (some assigned),List.prefix_refl _⟩ : Out C target.H Γ),SVal.prim value)) := by
  have scope : (capturePrefix (C := C) i a hm).ext = (.push .refl : Ext Γ (.mem R :: Γ)) := Subsingleton.elim _ _
  unfold readOperand DeferredSource.Operand.run
  rw [prefix_run target i a hm old assigned readI readA]
  simp only [scope,bind,Except.bind]
  simp only [Src.valueT,Val.evalT,MLoc.addrT,MPath.mvalT,State.push,TEnv.get]
  have weak := Val.evalT_wk (.drop (t := .mem R) .refl)
    (target.setLocal i (some assigned)) (some old,(target.setLocal i (some assigned)).env) index
  change (index.wk (.drop .refl)).evalT
    ((target.setLocal i (some assigned)).push (t := .mem R) (some old)) =
      index.evalT (target.setLocal i (some assigned)) at weak
  simp only [State.push] at weak
  rw [weak]
  cases index.evalT (target.setLocal i (some assigned)) with
  | error err => rfl
  | ok k =>
    simp only [bind,Except.bind,pure,Except.pure,Heap.readAddr]
    dsimp only [State.setLocal]
    cases TRes.ofOpt (target.heap.index old array k) <;> rfl

/-- A write through the captured base; the RHS and index retain their existing
native evaluation order at the reached caller. -/
def writeCode (i a : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (array : ArrTy R (.prim p)) (index : Val C Γ .uint) (value : Val C Γ p) :
    Prog C Γ (.mem R :: Γ) :=
  (capturePrefix i a hm).join (.cons (.assignMem
    (.index array (.var .here hm) (index.wk (.drop .refl)))
    (.val (value.wk (.drop .refl)))) .nil)

/-- Capturing the reference retains the referent for indexed writes, even
when the original caller slot has been rebound to another object. -/
theorem write_run (target : State C Γ) (i a : Idx Γ (.mem R))
    (hm : (Ty.ref R).mapFree = true) (old assigned : HRef target.H R)
    (readI : TEnv.get i target.env = some old) (readA : TEnv.get a target.env = some assigned)
    (array : ArrTy R (.prim p)) (index : Val C Γ .uint) (value : Val C Γ p) :
    (writeCode i a hm array index value).run target = (do
      let v ← value.evalT (target.setLocal i (some assigned))
      let k ← index.evalT (target.setLocal i (some assigned))
      let hp ← TRes.ofOpt (target.heap.setIndex old array k v)
      pure (⟨((target.setLocal i (some assigned)).withHeap hp).push (t := .mem R) (some old),
        List.prefix_refl _⟩ : Out C target.H (.mem R :: Γ))) := by
  let post := target.setLocal i (some assigned)
  let captured := post.push (t := .mem R) (some old)
  let statement : Stmt C (.mem R :: Γ) (.mem R :: Γ) := .assignMem
    (.index array (.var .here hm) (index.wk (.drop .refl))) (.val (value.wk (.drop .refl)))
  have start := prefix_run target i a hm old assigned readI readA
  change (capturePrefix i a hm).runR target = .ok (⟨captured,List.prefix_refl _⟩) at start
  have joined := DeferredSource.join_run (capturePrefix i a hm) (.cons statement .nil) target
  change (writeCode i a hm array index value).run target = _ at joined
  rw [joined]
  unfold TRun.seq
  rw [start]
  dsimp only []
  have single := singleton_run captured statement
  change (Prog.cons statement .nil).runR captured = statement.runR captured at single
  rw [single]
  change (TRun.assignMem _ _ captured).map
    (fun (out : Out C target.H (.mem R :: Γ)) => (⟨out.st,out.ext⟩ : Out C target.H (.mem R :: Γ))) = _
  simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT]
  have weakV := Val.evalT_wk (.drop (t := .mem R) .refl) post (some old,post.env) value
  have weakK := Val.evalT_wk (.drop (t := .mem R) .refl) post (some old,post.env) index
  change (value.wk (.drop .refl)).evalT captured = value.evalT post at weakV
  change (index.wk (.drop .refl)).evalT captured = index.evalT post at weakK
  rw [weakV,weakK]
  have head : TEnv.get Idx.here captured.env = some old := rfl
  rw [head]
  simp only [bind,Except.bind,pure,Except.pure,Heap.writeAddr]
  change _ = (do
    let v ← value.evalT post
    let k ← index.evalT post
    let hp ← TRes.ofOpt (target.heap.setIndex old array k v)
    pure (⟨(post.withHeap hp).push (t := .mem R) (some old),List.prefix_refl _⟩ : Out C target.H (.mem R :: Γ)))
  cases value.evalT post with
  | error err => rfl
  | ok v =>
    cases index.evalT post with
    | error err => rfl
    | ok k =>
      simp only [bind,Except.bind]
      dsimp only [captured,post,State.push,State.setLocal]
      cases TRes.ofOpt (target.heap.setIndex old array k v) <;> rfl

#print axioms prefix_run
#print axioms read_run
#print axioms write_run

end Solidity.Lowering.G17.IndexCapture
