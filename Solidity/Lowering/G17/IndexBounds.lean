import Solidity.Lowering.G17.IndexCapture
import Solidity.Syntax.Checked
import Solidity.Lowering.V08.AbiObservations
import Solidity.Backend.Failure.Observe
import Solidity.Theory.Typed.Mem

/-! Bounds checks from the existing checked-program metadata. The guard
reads captured simple indices and a live reference; it introduces no Source
heap relation and makes no claim about admission or a whole lowering pass. -/
namespace Solidity.Lowering.G17.IndexBounds
variable {C : Contract} {Γ : Ctx} {R : RefTy} {p : PrimTy}

private def code (array : ArrTy R (.prim p)) (base : Idx Γ (.mem R))
    (hm : (Ty.ref R).mapFree = true) (index : Simple C Γ .uint) : Prog C Γ Γ :=
  (Checked.mIdxPG array (.var base hm) (.simple index)).foldr
    (fun guard tail => .cons (panicStmt guard.1 guard.2) tail) .nil

private theorem panic_run (target : State C Γ) (g : Val C Γ .bool) (b : Bool)
    (test : g.evalT target = .ok b) :
    (panicStmt 0x32 g).run target = if b then
      .ok (⟨target,List.prefix_refl _⟩ : Out C target.H Γ)
    else .error (THalt.ofData (Source.panicData .index)) := by
  cases b
  · change TRun.ite g _ _ _ _ target = _
    have literal := Backend.Failure.revert_bytes_intrinsic target (Semantics.encodePanic 0x32)
    simp only [TRun.ite,test,boolT,ok_bind,Bool.false_eq_true,if_false,TRun.seq,literal]
    rw [V08.panicData_transport .index]
    rfl
  · change TRun.ite g _ _ _ _ target = _
    simp only [TRun.ite,test,boolT,TRun.nil]
    rfl

private theorem dynamic_test (target : State C Γ) {E : Ty}
    (base : Idx Γ (.mem (.array E))) (hm : (Ty.ref (.array E)).mapFree = true)
    (old : HRef target.H (.array E)) (read : TEnv.get base target.env = some old)
    (index : Simple C Γ .uint) :
    (Checked.cmpU .lt rfl rfl (.simple index) (.mlen (.var base hm) rfl)).evalT target =
      .ok (decide ((index.evalT target).val.toNat < target.heap.len old .dyn)) := by
  simp only [Checked.cmpU,Val.evalT,MPath.mvalT,read,bind,Except.bind,pure,Except.pure]
  change Except.ok (decide ((index.evalT target).val < (target.heap.len old .dyn : Int))) = _
  have lower := (index.evalT target).property
  simp only [PrimTy.inRange,decide_eq_true_eq] at lower
  by_cases h : (index.evalT target).val.toNat < target.heap.len old .dyn
  · have hi : (index.evalT target).val < (target.heap.len old .dyn : Int) := by omega
    simp only [h,hi,decide_true]
  · have hi : ¬ (index.evalT target).val < (target.heap.len old .dyn : Int) := by omega
    simp only [h,hi,decide_false]

private theorem fixed_test (target : State C Γ) (n : Nat)
    (fits : PrimTy.uint.inRange (n : Int) = true) (index : Simple C Γ .uint) :
    (Checked.cmpU .lt rfl rfl (.simple index) (Checked.litU n fits)).evalT target =
      .ok (decide ((index.evalT target).val.toNat < n)) := by
  change Except.ok (decide ((index.evalT target).val < (n : Int))) = _
  have lower := (index.evalT target).property
  simp only [PrimTy.inRange,decide_eq_true_eq] at lower
  by_cases h : (index.evalT target).val.toNat < n
  · have hi : (index.evalT target).val < (n : Int) := by omega
    simp only [h,hi,decide_true]
  · have hi : ¬ (index.evalT target).val < (n : Int) := by omega
    simp only [h,hi,decide_false]

private theorem bounds_run (target : State C Γ) (array : ArrTy R (.prim p))
    (base : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (old : HRef target.H R) (read : TEnv.get base target.env = some old)
    (index : Simple C Γ .uint) :
    (code array base hm index).run target =
      if (index.evalT target).val.toNat < target.heap.len old array then
        .ok (⟨target,List.prefix_refl _⟩ : Out C target.H Γ)
      else .error (THalt.ofData (Source.panicData .index)) := by
  cases array with
  | dyn =>
    unfold code
    change (Prog.cons (panicStmt 0x32 _) .nil).run target = _
    rw [V07.singleton_run,panic_run target _ _ (dynamic_test target base hm old read index)]
    simp only [decide_eq_true_eq]
  | fixed =>
    rename_i n
    have length : target.heap.len old (.fixed (n := n)) = n := by
      simp only [Heap.len,MObj.elems_fixed]
      exact (target.heap.get old).property
    rw [length]
    unfold code
    simp only [Checked.mIdxPG]
    split
    · rename_i fits
      change (Prog.cons (panicStmt 0x32 _) .nil).run target = _
      rw [V07.singleton_run,panic_run target _ _ (fixed_test target n fits index)]
      simp only [decide_eq_true_eq]
    · rename_i outside
      have lower := (index.evalT target).property
      simp only [PrimTy.inRange,decide_eq_true_eq] at lower
      have large : 2^256 ≤ n := by
        simp only [PrimTy.inRange,decide_eq_true_eq] at outside
        omega
      have inside : (index.evalT target).val.toNat < n := by omega
      rw [if_pos inside]
      rfl

/-- Guard metadata is run after the base identity and index input have been
captured, before the final memory read. -/
def readOperand (i a : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (array : ArrTy R (.prim p)) (index : Simple C Γ .uint) :
    DeferredSource.Operand C Γ (.prim p) :=
  ⟨_,(IndexCapture.captureCode i a hm).join
      (code array .here hm (index.wk (.drop .refl))),
    .val (.readMem (.index array (.var .here hm) (.simple (index.wk (.drop .refl)))))⟩

/-- Reuse the repository's checked-program transformation for stores whose
index and assigned scalar have already been captured. -/
def writeCode (i a : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (array : ArrTy R (.prim p)) (index : Simple C Γ .uint) (value : Simple C Γ p) :
    Prog C Γ (.mem R :: Γ) :=
  (IndexCapture.writeCode i a hm array (.simple index) (.simple value)).withPanics

private theorem guards_join {Δ : Ctx} (guards : Checked.PGuards C Γ) (tail : Prog C Γ Δ) :
    (guards.foldr (fun guard rest => Prog.cons (panicStmt guard.1 guard.2) rest) .nil).join tail =
      guards.foldr (fun guard rest => Prog.cons (panicStmt guard.1 guard.2) rest) tail := by
  induction guards with
  | nil => rfl
  | cons guard guards ih =>
    simp only [List.foldr_cons,Prog.join,ih]

private theorem join_assoc : {Γ Δ Ε Ζ : Ctx} → (P : Prog C Γ Δ) → (Q : Prog C Δ Ε) →
    (S : Prog C Ε Ζ) → P.join (Q.join S) = (P.join Q).join S
  | _,_,_,_,.nil,Q,S => rfl
  | _,_,_,_,.cons s P,Q,S => by
    change Prog.cons s (P.join (Q.join S)) = Prog.cons s ((P.join Q).join S)
    rw [join_assoc P Q S]

private theorem write_shape (i a : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (array : ArrTy R (.prim p)) (index : Simple C Γ .uint) (value : Simple C Γ p) :
    writeCode i a hm array index value = (IndexCapture.captureCode i a hm).join
      ((code array .here hm (index.wk (.drop .refl))).join
        (.cons (.assignMem (.index array (.var .here hm) (.simple (index.wk (.drop .refl))))
          (.val (.simple (value.wk (.drop .refl))))) .nil)) := by
  unfold writeCode code
  rw [guards_join]
  rfl

private theorem prefix_run (target : State C Γ) (i a : Idx Γ (.mem R))
    (hm : (Ty.ref R).mapFree = true) (old assigned : HRef target.H R)
    (readI : TEnv.get i target.env = some old) (readA : TEnv.get a target.env = some assigned)
    (array : ArrTy R (.prim p)) (index : Simple C Γ .uint) :
    ((IndexCapture.captureCode i a hm).join
      (code array .here hm (index.wk (.drop .refl)))).run target =
      if (index.evalT (target.setLocal i (some assigned))).val.toNat < target.heap.len old array then
        .ok (⟨(target.setLocal i (some assigned)).push (t := .mem R) (some old),
          List.prefix_refl _⟩ : Out C target.H (.mem R :: Γ))
      else .error (THalt.ofData (Source.panicData .index)) := by
  rw [DeferredSource.join_run]
  unfold TRun.seq
  let post := target.setLocal i (some assigned)
  let captured := post.push (t := .mem R) (some old)
  have start := IndexCapture.capture_run target i a hm old assigned readI readA
  change (IndexCapture.captureCode i a hm).runR target =
    .ok (⟨captured,List.prefix_refl _⟩ : Out C target.H (.mem R :: Γ)) at start
  rw [start]
  dsimp only []
  have test := bounds_run captured array .here hm old rfl (index.wk (.drop .refl))
  change (code array .here hm (index.wk (.drop .refl))).runR captured = _ at test
  rw [test]
  have weak := Simple.evalT_wk (.drop (t := .mem R) .refl) post (some old,post.env) index
  change (index.wk (.drop .refl)).evalT captured = index.evalT post at weak
  rw [weak]
  have heap : captured.heap = target.heap := rfl
  rw [heap]
  split <;> rfl

/-- In bounds the guarded read is the original captured read. Out of bounds
it emits the exact Source panic payload, rather than an empty native revert.
No access-success result is assumed. -/
theorem read_run (target : State C Γ) (i a : Idx Γ (.mem R))
    (hm : (Ty.ref R).mapFree = true) (old assigned : HRef target.H R)
    (readI : TEnv.get i target.env = some old) (readA : TEnv.get a target.env = some assigned)
    (array : ArrTy R (.prim p)) (index : Simple C Γ .uint) :
    (readOperand i a hm array index).run target =
      if (index.evalT (target.setLocal i (some assigned))).val.toNat < target.heap.len old array then
        (IndexCapture.readOperand i a hm array (.simple index)).run target
      else .error (THalt.ofData (Source.panicData .index)) := by
  unfold readOperand DeferredSource.Operand.run IndexCapture.readOperand
  rw [prefix_run target i a hm old assigned readI readA array index]
  by_cases inside : (index.evalT (target.setLocal i (some assigned))).val.toNat < target.heap.len old array
  · simp only [inside,if_true,bind,Except.bind]
    rw [IndexCapture.capture_run target i a hm old assigned readI readA]
    have same : ((IndexCapture.captureCode (C := C) i a hm).join
        (code array .here hm (index.wk (.drop .refl)))).ext =
        (IndexCapture.captureCode (C := C) i a hm).ext := Subsingleton.elim _ _
    rw [same]
    rfl
  · simp only [inside,if_false,bind,Except.bind]

/-- The actual checked-program store preserves the original successful
captured store and gives a bounds failure its exact 0x32 payload. -/
theorem write_run (target : State C Γ) (i a : Idx Γ (.mem R))
    (hm : (Ty.ref R).mapFree = true) (old assigned : HRef target.H R)
    (readI : TEnv.get i target.env = some old) (readA : TEnv.get a target.env = some assigned)
    (array : ArrTy R (.prim p)) (index : Simple C Γ .uint) (value : Simple C Γ p) :
    (writeCode i a hm array index value).run target =
      if (index.evalT (target.setLocal i (some assigned))).val.toNat < target.heap.len old array then
        (IndexCapture.writeCode i a hm array (.simple index) (.simple value)).run target
      else .error (THalt.ofData (Source.panicData .index)) := by
  rw [write_shape,join_assoc,DeferredSource.join_run]
  unfold TRun.seq
  have checked := prefix_run target i a hm old assigned readI readA array index
  change ((IndexCapture.captureCode i a hm).join
    (code array .here hm (index.wk (.drop .refl)))).runR target = _ at checked
  rw [checked]
  by_cases inside : (index.evalT (target.setLocal i (some assigned))).val.toNat < target.heap.len old array
  · simp only [inside,if_true]
    unfold IndexCapture.writeCode
    rw [DeferredSource.join_run]
    unfold TRun.seq
    have captured := IndexCapture.capture_run target i a hm old assigned readI readA
    change (IndexCapture.captureCode i a hm).runR target = _ at captured
    rw [captured]
    rfl
  · simp only [inside,if_false]

#print axioms panic_run
#print axioms dynamic_test
#print axioms fixed_test
#print axioms bounds_run
#print axioms guards_join
#print axioms join_assoc
#print axioms write_shape
#print axioms prefix_run
#print axioms read_run
#print axioms write_run

end Solidity.Lowering.G17.IndexBounds
