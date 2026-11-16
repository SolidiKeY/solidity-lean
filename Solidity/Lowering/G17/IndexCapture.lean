import Solidity.Lowering.G17.OperandStore
import Solidity.Lowering.V07.ReferenceEffects
import Solidity.Lowering.V07.ShortCircuit

/-! Indexed native access after reference capture and local rebinding. The captured object identity is retained for every array shape and primitive type. This is an operational ingredient for indexAccess, not yet Source transport, a heap/world relation, or coverage of storage/mapping/calldata indexing. The separate Source-only laws factor child results; they are not correspondence theorems. Capture the old identity before rebinding the caller slot; the fresh slot keeps it while the caller slot is rebound. read_run: The index is evaluated after rebinding, but the indexed object is the captured reference. Bounds failures use the existing heap lookup/revert law. No result of the desired read is an input premise. writeCode: A write through the captured base; the RHS and index retain their existing native evaluation order at the reached caller. write_run: Capturing the reference retains the referent for indexed writes, even when the original caller slot has been rebound to another object. effectfulIndexCode_run: Capture reference identity before an arbitrary index prefix; retain reached caller/heap effects and halts, with both private captures protected from aliasing. source_capture_all: Source array capture composes all child results and exact reached failures; the earlier success-only law below remains a derived specialization, without a Source/native relation. -/
namespace Solidity.Lowering.G17.IndexCapture
open V07
variable {C : Contract} {Γ : Ctx} {R : RefTy} {p : PrimTy}

def captureCode (i a : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true) :
    Prog C Γ (.mem R :: Γ) :=
  (memoryCapture i hm).join
    (.cons (.rebindMem (.there i) (.alias (.var (.there a) hm))) .nil)

theorem capture_run (target : State C Γ) (i a : Idx Γ (.mem R))
    (hm : (Ty.ref R).mapFree = true) (old assigned : HRef target.H R)
    (readI : TEnv.get i target.env = some old) (readA : TEnv.get a target.env = some assigned) :
    (captureCode i a hm).run target =
      .ok (⟨(target.setLocal i (some assigned)).push (t := .mem R) (some old),List.prefix_refl _⟩) := by
  unfold captureCode memoryCapture
  change (Prog.cons _ (.cons _ .nil)).run target = _
  rw [Prog.run_cons_ok (memory_declaration_run target i hm old readI)]
  rw [Prog.run_cons_ok (memory_rebind_run (target.push (t := .mem R) (some old))
    (.there i) (.there a) hm assigned readA),Prog.run_nil]
  rfl

def readOperand (i a : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (array : ArrTy R (.prim p)) (index : Val C Γ .uint) :
    DeferredSource.Operand C Γ (.prim p) :=
  ⟨_,captureCode i a hm,.val (.readMem (.index array (.var .here hm) (index.wk (.drop .refl))))⟩


theorem read_run (target : State C Γ) (i a : Idx Γ (.mem R))
    (hm : (Ty.ref R).mapFree = true) (old assigned : HRef target.H R)
    (readI : TEnv.get i target.env = some old) (readA : TEnv.get a target.env = some assigned)
    (array : ArrTy R (.prim p)) (index : Val C Γ .uint) :
    (readOperand i a hm array index).run target = (do
      let k ← index.evalT (target.setLocal i (some assigned))
      let value ← TRes.ofOpt (target.heap.index old array k)
      pure ((⟨target.setLocal i (some assigned),List.prefix_refl _⟩ : Out C target.H Γ),SVal.prim value)) := by
  have scope : (captureCode (C := C) i a hm).ext = (.push .refl : Ext Γ (.mem R :: Γ)) := Subsingleton.elim _ _
  unfold readOperand DeferredSource.Operand.run
  rw [capture_run target i a hm old assigned readI readA]
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


def writeCode (i a : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (array : ArrTy R (.prim p)) (index : Val C Γ .uint) (value : Val C Γ p) :
    Prog C Γ (.mem R :: Γ) :=
  (captureCode i a hm).join (.cons (.assignMem
    (.index array (.var .here hm) (index.wk (.drop .refl)))
    (.val (value.wk (.drop .refl)))) .nil)


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
  have start := capture_run target i a hm old assigned readI readA
  change (captureCode i a hm).runR target = .ok (⟨captured,List.prefix_refl _⟩) at start
  have joined := DeferredSource.join_run (captureCode i a hm) (.cons statement .nil) target
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

def effectfulIndexCode (i : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (index : DeferredSource.Operand C Γ (.prim .uint)) :
    Prog C Γ (.val .uint :: .mem R :: Γ) :=
  (memoryCapture i hm).join
    (.cons (.declLocal .uint (.user "captured_index") none)
      (.cons (storePrimitiveOperand .here ((index.wk (.drop .refl)).wk (.drop .refl))) .nil))

private theorem index_after_capture (index : DeferredSource.Operand C Γ (.prim .uint))
    (target : State C Γ) (old : HRef target.H R) :
    (index.wk (.drop .refl)).run (target.push (t := .mem R) (some old)) =
      (index.run target).map (fun (out,value) =>
        ((⟨out.st.push (t := .mem R) (some (HRef.wk out.ext old)),out.ext⟩ :
          Out C target.H (.mem R :: Γ)),value)) := by
  have weak := DeferredSource.Operand.run_wk index (.drop (t := .mem R) .refl)
    target (some old,target.env)
  simpa only [liftedT₂,Out.lift,State.lift,State.push,TEnv.put,TEnv.wk,LTy.TDenote.wk,
    Option.map_some] using weak


theorem effectfulIndexCode_run (target : State C Γ) (i : Idx Γ (.mem R))
    (hm : (Ty.ref R).mapFree = true) (old : HRef target.H R)
    (read : TEnv.get i target.env = some old)
    (index : DeferredSource.Operand C Γ (.prim .uint)) :
    (effectfulIndexCode i hm index).run target =
      (index.run target).map (fun (out,value) => match value with
        | .prim k => (⟨(out.st.push (t := .mem R) (some (HRef.wk out.ext old))).push (t := .val .uint) k,
            out.ext⟩ : Out C target.H (.val .uint :: .mem R :: Γ))) := by
  unfold effectfulIndexCode
  rw [DeferredSource.join_run]
  have first := memory_capture_run target i hm old read
  change (memoryCapture i hm).runR target = _ at first
  unfold TRun.seq
  rw [first]
  dsimp only []
  have reserve : (Stmt.declLocal .uint (.user "captured_index") none).run
      (target.push (t := .mem R) (some old)) =
      .ok (⟨(target.push (t := .mem R) (some old)).push (t := .val .uint) (PrimTy.dflt .uint),
        List.prefix_refl _⟩) := rfl
  have reserved := Prog.run_cons_ok
    (P := .cons (storePrimitiveOperand .here ((index.wk (.drop .refl)).wk (.drop .refl))) .nil) reserve
  change (Prog.cons (.declLocal .uint (.user "captured_index") none)
    (.cons (storePrimitiveOperand .here ((index.wk (.drop .refl)).wk (.drop .refl))) .nil)).runR
      (target.push (t := .mem R) (some old)) = _ at reserved
  rw [reserved]
  dsimp only [Prog.run]
  have single := singleton_run
    ((target.push (t := .mem R) (some old)).push (t := .val .uint) (PrimTy.dflt .uint))
    (storePrimitiveOperand .here ((index.wk (.drop .refl)).wk (.drop .refl)))
  change (Prog.cons (storePrimitiveOperand .here ((index.wk (.drop .refl)).wk (.drop .refl))) .nil).runR
    ((target.push (t := .mem R) (some old)).push (t := .val .uint) (PrimTy.dflt .uint)) = _ at single
  rw [single]
  dsimp only [Stmt.run]
  have stored := storePrimitive_fresh_run (index.wk (.drop (t := .mem R) .refl))
    (target.push (t := .mem R) (some old)) (PrimTy.dflt .uint)
  change (storePrimitiveOperand .here ((index.wk (.drop .refl)).wk (.drop .refl))).runR
    ((target.push (t := .mem R) (some old)).push (t := .val .uint) (PrimTy.dflt .uint)) = _ at stored
  rw [stored,index_after_capture]
  cases run : index.run target with
  | error err => rfl
  | ok result =>
    obtain ⟨out,value⟩ := result
    cases value with
    | prim k => rfl

#print axioms index_after_capture
#print axioms effectfulIndexCode_run

theorem source_capture_all {E : Source.Env} {srcΓ : Source.RCtx}
    {location : Source.DataLoc} {element indexTy : Source.STy} {length : Option Nat}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (base : Source.RExpr E srcΓ (.array location element length))
    (index : Source.RExpr E srcΓ indexTy) (hi : indexTy.isIndex = true)
    (source middle after : Source.EMState E srcΓ)
    (baseResult : Source.R (Source.RVal E.layout (.array location element length)))
    (indexResult : Source.R (Source.RVal E.layout indexTy))
    (baseRun : (Source.evalE G F fuel base).run source = (baseResult,middle))
    (indexRun : (Source.evalE G F fuel index).run middle = (indexResult,after)) :
    let selected (captured : Source.Val E.layout (.array location element length)) :
        Source.EM E srcΓ (Source.Loc E.layout srcΓ element) := do
      let value ← Source.EM.lift indexResult
      let k ← Source.indexNat value
      Source.indexLoc F captured k
    (Source.evalE G F (fuel+1) (.indexArray base index hi)).run source =
      (match (generalizing := false) baseResult with
       | .error halt => (.error halt,middle)
       | .ok (.val captured) =>
         (do let loc ← selected captured; return Source.RVal.val (τ := element) (← Source.readLoc F loc)).run after) ∧
    ∀ writable : location ≠ .calldata,
      (Source.evalLoc G F (fuel+1) (.indexArray base writable index hi)).run source =
        (match (generalizing := false) baseResult with
         | .error halt => (.error halt,middle)
         | .ok (.val captured) => (selected captured).run after) := by
  dsimp only
  constructor
  · rw [Source.evalE,Source.Hoare.run_bind,baseRun]
    cases baseResult with
    | error halt => rfl
    | ok value =>
      cases value with
      | val captured =>
        dsimp only []
        rw [Source.Hoare.run_bind,source_getV_run]
        dsimp only []
        rw [Source.Hoare.run_bind,indexRun]
        cases indexResult with
        | error halt => rfl
        | ok value => simp only [Source.EM.lift,pure_bind,bind_assoc]
  · intro writable
    rw [Source.evalLoc,Source.Hoare.run_bind,baseRun]
    cases baseResult with
    | error halt => rfl
    | ok value =>
      cases value with
      | val captured =>
        dsimp only []
        rw [Source.Hoare.run_bind,source_getV_run]
        dsimp only []
        rw [Source.Hoare.run_bind,indexRun]
        cases indexResult <;> rfl

theorem source_capture_order {E : Source.Env} {srcΓ : Source.RCtx}
    {location : Source.DataLoc} {element indexTy : Source.STy} {length : Option Nat}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (base : Source.RExpr E srcΓ (.array location element length))
    (index : Source.RExpr E srcΓ indexTy) (hi : indexTy.isIndex = true)
    (source middle after : Source.EMState E srcΓ)
    (captured : Source.Val E.layout (.array location element length))
    (indexValue : Source.RVal E.layout indexTy)
    (baseRun : (Source.evalE G F fuel base).run source = (.ok (.val captured),middle))
    (indexRun : (Source.evalE G F fuel index).run middle = (.ok indexValue,after)) :
    let selected : Source.EM E srcΓ (Source.Loc E.layout srcΓ element) := do
      let k ← Source.indexNat indexValue
      Source.indexLoc F captured k
    (Source.evalE G F (fuel+1) (.indexArray base index hi)).run source =
      (do let loc ← selected; return Source.RVal.val (τ := element) (← Source.readLoc F loc)).run after ∧
    ∀ writable : location ≠ .calldata,
      (Source.evalLoc G F (fuel+1) (.indexArray base writable index hi)).run source = selected.run after := by
  have all := source_capture_all G F fuel base index hi source middle after
    (.ok (.val captured)) (.ok indexValue) baseRun indexRun
  simpa only [Source.EM.lift,pure_bind] using all

#print axioms source_capture_all
#print axioms source_capture_order
#print axioms capture_run
#print axioms read_run
#print axioms write_run

end Solidity.Lowering.G17.IndexCapture
