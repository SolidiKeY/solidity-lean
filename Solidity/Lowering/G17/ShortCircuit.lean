import Solidity.Lowering.G17.OperandStore
import Solidity.Lowering.V07.ShortCircuit
import Solidity.Lowering.V07.ReferenceEffects

/-! One Boolean-operator family: evaluate the left operand once, retain its caller effects, and run the right operand only when its value requires it. Both prefixes are arbitrary interpreted programs, including heap growth and halts. The private Boolean binder never aliases a caller binding. -/
namespace Solidity.Lowering.G17
open V07
variable {C : Contract} {Γ : Ctx}

/-- Store into a fresh Boolean capture while retaining the operand's caller. -/
theorem store_fresh_run (e : DeferredSource.Operand C Γ (.prim .bool))
    (target : State C Γ) (previous : Bool) :
    (storeOperand .here (e.wk (.drop .refl))).run
      (target.push (t := .val .bool) previous) =
    (e.run target).map (fun (out,value) => match value with
      | .prim b => (⟨out.st.push (t := .val .bool) b,out.ext⟩ : Out C target.H (.val .bool :: Γ))) := by
  have same : storeOperand .here (e.wk (.drop .refl)) =
      storePrimitiveOperand .here (e.wk (.drop .refl)) := by
    cases e with
    | mk Δ code value => cases value <;> rfl
  rw [same,storePrimitive_fresh_run]
  cases run : e.run target with
  | error err => rfl
  | ok result =>
    obtain ⟨out,value⟩ := result
    cases value with
    | prim b => rfl

private def rightCode (right : DeferredSource.Operand C Γ (.prim .bool)) :
    Prog C (.val .bool :: Γ) (.val .bool :: Γ) :=
  .cons (storeOperand .here (right.wk (.drop .refl))) .nil

private def branchCode (conj : Bool) (right : DeferredSource.Operand C Γ (.prim .bool)) :
    Prog C (.val .bool :: Γ) (.val .bool :: Γ) :=
  .cons (.ite (.simple (.local .here))
    (if conj then rightCode right else .nil) (if conj then .nil else rightCode right)) .nil

private theorem rightCode_run (right : DeferredSource.Operand C Γ (.prim .bool))
    (target : State C Γ) (b : Bool) :
    (rightCode right).runC (target.push (t := .val .bool) b) =
      (right.run target).map (fun (out,value) => match value with
        | .prim c => (⟨out.st.push (t := .val .bool) c,out.ext⟩ : Out C target.H (.val .bool :: Γ))) := by
  have single := V07.singleton_run (target.push (t := .val .bool) b)
    (storeOperand .here (right.wk (.drop .refl)))
  simp only [Prog.run,Stmt.run,Prog.runR_eq,Stmt.runR_eq] at single
  change (rightCode right).runC (target.push (t := .val .bool) b) = _ at single
  rw [single]
  have stored := store_fresh_run right target b
  simpa only [Stmt.run,Stmt.runR_eq] using stored

private theorem branchCode_run (conj : Bool) (right : DeferredSource.Operand C Γ (.prim .bool))
    (target : State C Γ) (b : Bool) :
    (branchCode conj right).runC (target.push (t := .val .bool) b) =
      if needsRight conj b then
        (right.run target).map (fun (out,value) => match value with
          | .prim c => (⟨out.st.push (t := .val .bool) c,out.ext⟩ : Out C target.H (.val .bool :: Γ)))
      else .ok ⟨target.push (t := .val .bool) b,List.prefix_refl _⟩ := by
  cases conj <;> cases b
  · change TRun.seq (TRun.ite (.simple (.local .here)) _ TRun.nil
      (rightCode right).ext (rightCode right).runC) TRun.nil (target.push (t := .val .bool) false) = _
    unfold TRun.seq TRun.ite
    simp only [Val.evalT,Simple.evalT,TEnv.get,boolT,
      Bool.false_eq_true,if_false,bind,Except.bind]
    have scope : (rightCode right).ext = .refl := Subsingleton.elim _ _
    rw [scope,rightCode_run]
    cases run : right.run target with
    | error err => rfl
    | ok result =>
      obtain ⟨out,value⟩ := result
      cases value with
      | prim c => rfl
  · rfl
  · rfl
  · change TRun.seq (TRun.ite (.simple (.local .here)) (rightCode right).ext
      (rightCode right).runC _ TRun.nil) TRun.nil (target.push (t := .val .bool) true) = _
    unfold TRun.seq TRun.ite
    simp only [Val.evalT,Simple.evalT,TEnv.get,boolT,
      if_true,bind,Except.bind]
    have scope : (rightCode right).ext = .refl := Subsingleton.elim _ _
    rw [scope,rightCode_run]
    cases run : right.run target with
    | error err => rfl
    | ok result =>
      obtain ⟨out,value⟩ := result
      cases value with
      | prim c => rfl

def shortOperand (conj : Bool) (left right : DeferredSource.Operand C Γ (.prim .bool)) :
    DeferredSource.Operand C Γ (.prim .bool) :=
  ⟨.val .bool :: Γ,
    .cons (.declLocal .bool (.user "g17_short") none)
      (.cons (storeOperand .here (left.wk (.drop .refl))) (branchCode conj right)),
    .val (.simple (.local .here))⟩

/-- Operational lazy composition for both Boolean operators. No RHS execution premise is needed on a skipped branch. All reached caller effects survive. -/
theorem shortOperand_run (conj : Bool) (left right : DeferredSource.Operand C Γ (.prim .bool))
    (target : State C Γ) :
    (shortOperand conj left right).run target = (do
      let (a,value) ← left.run target
      match value with
      | .prim b =>
        if needsRight conj b then
          let (z,value) ← right.run a.st
          pure ((⟨z.st,a.ext.trans z.ext⟩ : Out C target.H Γ),value)
        else pure (a,.prim b)) := by
  change (do
    let a ← (shortOperand conj left right).code.run target
    let v ← (shortOperand conj left right).value.valueT a.st
    pure ((⟨a.st.drop (shortOperand conj left right).code.ext,a.ext⟩ : Out C target.H Γ),v)) = _
  have scope : (shortOperand conj left right).code.ext = (.push .refl : Ext Γ (.val .bool :: Γ)) :=
    Subsingleton.elim _ _
  rw [scope]
  simp only [Prog.run,Prog.runR_eq]
  change (do
    let a ← TRun.seq (TRun.declLocal .bool none)
      (TRun.seq (storeOperand .here (left.wk (.drop .refl))).runC (branchCode conj right).runC) target
    let v ← (Src.val (.simple (.local .here)) : Src C (.val .bool :: Γ) (.prim .bool)).valueT a.st
    pure ((⟨a.st.drop (.push .refl),a.ext⟩ : Out C target.H Γ),v)) = _
  have firstRun := store_fresh_run left target false
  simp only [Stmt.run,Stmt.runR_eq] at firstRun
  have initial : TRun.declLocal .bool none target =
      .ok (⟨target.push (t := .val .bool) false,List.prefix_refl _⟩) := by rfl
  unfold TRun.seq
  rw [initial]
  dsimp only []
  rw [firstRun]
  cases first : left.run target with
  | error err => rfl
  | ok result =>
    obtain ⟨a,value⟩ := result
    cases value with
    | prim b =>
      dsimp only [Except.map,bind,Except.bind]
      rw [branchCode_run]
      cases take : needsRight conj b with
      | false => rfl
      | true =>
        cases second : right.run a.st with
        | error err => rfl
        | ok result =>
          obtain ⟨z,value⟩ := result
          cases value with
          | prim c => rfl

#print axioms store_fresh_run
#print axioms rightCode_run
#print axioms branchCode_run
#print axioms shortOperand_run

end Solidity.Lowering.G17
